use proc_macro::TokenStream;
use quote::quote;
use syn::{Expr, Lit, parse_macro_input};

#[proc_macro]
pub fn felt(input: TokenStream) -> TokenStream {
    let expr = parse_macro_input!(input as Expr);

    match &expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            Lit::Str(lit_str) => {
                let value = lit_str.value();

                // Check if it's a hex string (starts with 0x or 0X)
                if value.starts_with("0x") || value.starts_with("0X") {
                    // Hex string: use const fn for compile-time validation
                    quote! {
                        {
                            const __FELT_VALUE: Felt = Felt::from_hex_unwrap(#lit_str);
                            __FELT_VALUE
                        }
                    }
                    .into()
                } else {
                    // Check for valid decimal format (optional leading minus, then digits)
                    let is_valid = if let Some(stripped) = value.strip_prefix('-') {
                        !stripped.is_empty() && stripped.chars().all(|c| c.is_ascii_digit())
                    } else {
                        !value.is_empty() && value.chars().all(|c| c.is_ascii_digit())
                    };

                    if !is_valid {
                        return syn::Error::new_spanned(
                            lit_str,
                            format!("Invalid Felt decimal string literal: '{}'. Expected decimal digits (0-9), optionally prefixed with '-'.", value)
                        )
                        .to_compile_error()
                        .into();
                    }

                    // Valid format, generate runtime parsing code
                    quote! {
                        match <Felt as ::core::str::FromStr>::from_str(#lit_str) {
                            Ok(f) => f,
                            Err(_) => panic!(concat!("Invalid Felt decimal string literal: ", #lit_str)),
                        }
                    }
                    .into()
                }
            }

            Lit::Bool(lit_bool) => quote! {
                match #lit_bool {
                    true => Felt::ONE,
                    false => Felt::ZERO,
                }
            }
            .into(),

            Lit::Int(lit_int) => quote! {
                Felt::from(#lit_int)
            }
            .into(),

            _ => panic!("Unsupported literal type for felt! macro"),
        },

        // Handle negative integer literals: -42, -123, etc.
        Expr::Unary(expr_unary) if matches!(expr_unary.op, syn::UnOp::Neg(_)) => {
            if let Expr::Lit(syn::ExprLit {
                lit: Lit::Int(lit_int),
                ..
            }) = &*expr_unary.expr
            {
                // Negative integer literal
                quote! {
                    Felt::from(-#lit_int)
                }
                .into()
            } else {
                // Some other unary negation, treat as expression
                quote! {
                    match <Felt as ::core::str::FromStr>::from_str(&#expr) {
                        Ok(f) => f,
                        Err(_) => panic!("Invalid Felt value"),
                    }
                }
                .into()
            }
        }

        // Anything else is handled as a string and will fail if it is not one
        _ => quote! {
            match Felt::try_from(#expr) {
                Ok(f) => f,
                Err(_) => panic!("Invalid Felt value"),
            }
        }
        .into(),
    }
}
