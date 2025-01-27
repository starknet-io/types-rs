use proc_macro::TokenStream;
use quote::quote;
use starknet_types_core::felt::Felt;
use syn::{parse_macro_input, LitStr};

#[proc_macro]
pub fn felt(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as LitStr);

    let str_value = input.value();

    let felt_value = if str_value.starts_with("0x") {
        Felt::from_hex(&str_value).expect("invalid Felt value")
    } else {
        Felt::from_dec_str(&str_value).expect("invalid Felt value")
    };

    let felt_bytes = felt_value.to_bytes_be();

    quote! {
        Felt::from_bytes_be(&[#(#felt_bytes),*])
    }
    .into()
}
