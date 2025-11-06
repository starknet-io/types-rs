use proc_macro::TokenStream;
use quote::quote;
use std::ops::Neg;
use syn::{Expr, ExprLit, ExprUnary, Lit, parse_macro_input};

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
        HandleExprOutput::ComptimeFelt(field_element) => {
            generate_const_felt_token_stream_from_lambda_field_element(field_element).into()
        }
        HandleExprOutput::Runtime => quote! {
            match Felt::try_from(#expr) {
                Ok(f) => f,
                Err(_) => panic!("Invalid Felt value"),
            }
        }
        .into(),
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

fn handle_expr(expr: &syn::Expr) -> HandleExprOutput {
    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            Lit::Bool(lit_bool) => HandleExprOutput::ComptimeFelt(match lit_bool.value() {
                false => LambdaFieldElement::from_hex_unchecked("0x0"),
                true => LambdaFieldElement::from_hex_unchecked("0x1"),
            }),

            Lit::Int(lit_int) => {
                let value = lit_int.base10_parse::<u128>().unwrap();

                HandleExprOutput::ComptimeFelt(LambdaFieldElement::from(&UnsignedInteger::from(
                    value,
                )))
            }

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
                }
                .unwrap();

                HandleExprOutput::ComptimeFelt(if is_neg { lfe.neg() } else { lfe })
            }

            Lit::ByteStr(lit_byte_str) => {
                let bytes = lit_byte_str.value();

                assert!(
                    bytes.len() <= 31,
                    "Short string must be at most 31 characters"
                );
                assert!(
                    bytes.is_ascii(),
                    "Short string must contain only ASCII characters"
                );

                let mut buffer = [0u8; 32];
                buffer[(32 - bytes.len())..].copy_from_slice(&bytes);

                HandleExprOutput::ComptimeFelt(LambdaFieldElement::from_bytes_be(&buffer).unwrap())
            }
            Lit::Char(lit_char) => {
                let char = lit_char.value();

                assert!(char.is_ascii(), "Only ASCII characters are handled");

                let mut buffer = [0u8];
                char.encode_utf8(&mut buffer);

                HandleExprOutput::ComptimeFelt(LambdaFieldElement::from(&UnsignedInteger::from(
                    u16::from(buffer[0]),
                )))
            }
            Lit::Byte(lit_byte) => {
                let char = lit_byte.value();

                HandleExprOutput::ComptimeFelt(LambdaFieldElement::from(&UnsignedInteger::from(
                    u16::from(char),
                )))
            }
            Lit::CStr(_) | Lit::Float(_) | Lit::Verbatim(_) => panic!("Literal type not handled"),
            // `Lit` is a non-exhaustive enum
            _ => panic!("Unkown literal type. Not handled"),
        },

        // Negative (`-`) prefixed values
        Expr::Unary(ExprUnary {
            attrs: _attrs,
            op: syn::UnOp::Neg(_),
            expr,
        }) => match handle_expr(expr) {
            HandleExprOutput::ComptimeFelt(field_element) => {
                HandleExprOutput::ComptimeFelt(field_element.neg())
            }
            HandleExprOutput::Runtime => HandleExprOutput::Runtime,
        },
        Expr::Unary(ExprUnary {
            attrs: _attrs,
            op: syn::UnOp::Not(_),
            expr,
        }) => match &**expr {
            Expr::Lit(ExprLit {
                lit: Lit::Bool(lit_bool),
                ..
            }) => HandleExprOutput::ComptimeFelt(match lit_bool.value() {
                false => LambdaFieldElement::from_hex_unchecked("0x1"),
                true => LambdaFieldElement::from_hex_unchecked("0x0"),
            }),
            Expr::Lit(_) => panic!(
                "The `!` logical inversion operatior in only allowed before booleans in literal expressions."
            ),
            _ => HandleExprOutput::Runtime,
        },

        _ => HandleExprOutput::Runtime,
    }
}
