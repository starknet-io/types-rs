use proc_macro::TokenStream;
use quote::quote;
use std::ops::Neg;
use syn::{Error, Expr, ExprLit, ExprUnary, Lit, LitInt, Result, parse_macro_input};

use lambdaworks_math::{
    field::{
        element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
    },
    traits::ByteConversion,
    unsigned_integer::element::UnsignedInteger,
};

type LambdaFieldElement = FieldElement<Stark252PrimeField>;

enum HandleExprOutput {
    ComptimeFelt(LambdaFieldElement),
    Runtime,
}

#[proc_macro]
pub fn felt(input: TokenStream) -> TokenStream {
    let expr = parse_macro_input!(input as Expr);

    match handle_expr(&expr) {
        Ok(HandleExprOutput::ComptimeFelt(field_element)) => {
            generate_const_felt_token_stream_from_lambda_field_element(field_element).into()
        }
        Ok(HandleExprOutput::Runtime) => quote! {
            match Felt::try_from(#expr) {
                Ok(f) => f,
                Err(e) => panic!("Invalid Felt value: {}", e),
            }
        }
        .into(),
        Err(error) => error.to_compile_error().into(),
    }
}

/// Take the lambda class type for field element, extract its limbs and generate the token stream for a const value of itself
fn generate_const_felt_token_stream_from_lambda_field_element(
    value: LambdaFieldElement,
) -> proc_macro2::TokenStream {
    let limbs = value.to_raw().limbs;
    let r0 = limbs[0];
    let r1 = limbs[1];
    let r2 = limbs[2];
    let r3 = limbs[3];

    quote! {
        {
            const __FELT_VALUE: Felt = Felt::from_raw([#r0, #r1, #r2, #r3]);
            __FELT_VALUE
        }
    }
}

fn handle_expr(expr: &syn::Expr) -> Result<HandleExprOutput> {
    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            Lit::Bool(lit_bool) => Ok(HandleExprOutput::ComptimeFelt(match lit_bool.value() {
                false => LambdaFieldElement::from(&UnsignedInteger::from_u64(0)),
                true => LambdaFieldElement::from(&UnsignedInteger::from_u64(1)),
            })),

            Lit::Int(lit_int) => handle_lit_int(lit_int),

            Lit::Str(lit_str) => {
                let value = lit_str.value();

                let (is_neg, value) = if let Some(striped) = value.strip_prefix('-') {
                    (true, striped)
                } else {
                    (false, value.as_str())
                };

                let lfe = if value.starts_with("0x") || value.starts_with("0X") {
                    UnsignedInteger::from_hex(value).map(|x| LambdaFieldElement::from(&x))
                } else {
                    UnsignedInteger::from_dec_str(value).map(|x| LambdaFieldElement::from(&x))
                };

                let lfe = match lfe {
                    Ok(v) => v,
                    Err(_) => {
                        return Err(Error::new_spanned(
                            lit_str,
                            "Invalid string literal for Felt conversion",
                        ));
                    }
                };

                Ok(HandleExprOutput::ComptimeFelt(if is_neg {
                    lfe.neg()
                } else {
                    lfe
                }))
            }

            Lit::ByteStr(lit_byte_str) => {
                let bytes = lit_byte_str.value();

                if bytes.len() > 31 {
                    return Err(Error::new_spanned(
                        lit_byte_str,
                        "Short string must be at most 31 characters",
                    ));
                }

                if !bytes.is_ascii() {
                    return Err(Error::new_spanned(
                        lit_byte_str,
                        "Short string must contain only ASCII characters",
                    ));
                }

                let mut buffer = [0u8; 32];
                buffer[(32 - bytes.len())..].copy_from_slice(&bytes);

                match LambdaFieldElement::from_bytes_be(&buffer) {
                    Ok(field_element) => Ok(HandleExprOutput::ComptimeFelt(field_element)),
                    Err(_) => Err(Error::new_spanned(
                        lit_byte_str,
                        "Failed to convert byte string to Felt",
                    )),
                }
            }

            Lit::Char(lit_char) => {
                let char = lit_char.value();

                if !char.is_ascii() {
                    return Err(Error::new_spanned(
                        lit_char,
                        "Only ASCII characters are supported",
                    ));
                }

                let mut buffer = [0u8];
                char.encode_utf8(&mut buffer);

                Ok(HandleExprOutput::ComptimeFelt(LambdaFieldElement::from(
                    &UnsignedInteger::from(u16::from(buffer[0])),
                )))
            }

            Lit::Byte(lit_byte) => {
                let char = lit_byte.value();

                Ok(HandleExprOutput::ComptimeFelt(LambdaFieldElement::from(
                    &UnsignedInteger::from(u16::from(char)),
                )))
            }

            Lit::CStr(_) | Lit::Float(_) | Lit::Verbatim(_) => {
                Err(Error::new_spanned(expr_lit, "Unsupported literal type"))
            }

            // `Lit` is a non-exhaustive enum
            _ => Err(Error::new_spanned(expr_lit, "Unknown literal type")),
        },

        Expr::Unary(expr_unary) => handle_expr_unary(expr_unary),

        _ => Ok(HandleExprOutput::Runtime),
    }
}

fn handle_lit_int(lit_int: &LitInt) -> Result<HandleExprOutput> {
    let value = match lit_int.base10_parse::<u128>() {
        Ok(v) => v,
        Err(_) => {
            return Err(Error::new_spanned(
                lit_int,
                "Invalid integer literal for Felt conversion",
            ));
        }
    };

    Ok(HandleExprOutput::ComptimeFelt(LambdaFieldElement::from(
        &UnsignedInteger::from(value),
    )))
}

fn handle_expr_unary(expr_unary: &ExprUnary) -> Result<HandleExprOutput> {
    let ExprUnary {
        attrs: _attrs,
        op,
        expr,
    } = expr_unary;
    match op {
        syn::UnOp::Not(_) => match &**expr {
            Expr::Lit(ExprLit {
                lit: Lit::Bool(lit_bool),
                ..
            }) => Ok(HandleExprOutput::ComptimeFelt(match lit_bool.value() {
                false => LambdaFieldElement::from(&UnsignedInteger::from_u64(1)),
                true => LambdaFieldElement::from(&UnsignedInteger::from_u64(0)),
            })),
            Expr::Lit(ExprLit {
                lit: Lit::Int(_lit_int),
                ..
            }) => Err(Error::new_spanned(
                expr,
                "The `!` logical inversion operator is applicable to the `Felt` type",
            )),
            Expr::Lit(_) => Err(Error::new_spanned(
                expr,
                "The `!` logical inversion operator is only allowed before booleans in literal expressions",
            )),
            _ => Ok(HandleExprOutput::Runtime),
        },
        syn::UnOp::Neg(_) => match &**expr {
            Expr::Lit(ExprLit {
                attrs: _attrs,
                lit: Lit::Int(lit_int),
            }) => match handle_lit_int(lit_int)? {
                HandleExprOutput::ComptimeFelt(field_element) => {
                    Ok(HandleExprOutput::ComptimeFelt(field_element.neg()))
                }
                HandleExprOutput::Runtime => Ok(HandleExprOutput::Runtime),
            },
            Expr::Unary(expr_unary) => handle_expr_unary(expr_unary),
            _ => Ok(HandleExprOutput::Runtime),
        },
        syn::UnOp::Deref(_star) => Err(Error::new_spanned(
            expr,
            "Deref unary type `*` not supported",
        )),
        _ => Err(Error::new_spanned(expr, "Unknown unary type")),
    }
}
