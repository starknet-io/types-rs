/// Handy macro to initialize `Felt`
//
/// Accepts:
/// - booleans
/// - positive and negative number literals (eg. `5`, `12u8`, `-77`, `-2007i32`)
/// - positive and negative decimal string literals (eg. `"5"`, `"-12"`)
/// - positive hexadecimal string literal (eg. `"0x0"`, `"0x42"`)
/// - variables of any type that implements `TryFrom<T> for Felt` (eg. `u32`, `i128`, `&str`, `String`)
/// - functions and closure which return type implements `TryFrom<T> for Felt` (eg. `|x| x * 42`, `fn ret42() -> u32 { 42 }` )
/// - code block (eg. `{40 + 2}`) and more generaly any expression that returns as types that implements `TryFrom<T> for Felt`
///
/// Use in `const` expression is only possible using literal `bool` and literal hex string
/// because the other types rely on non-`const` function for conversion (eg. `From::from` for numbers).
#[macro_export]
macro_rules! felt {
    ($($tt:tt)*) => {{
         let felt: $crate::felt::Felt = felt_macro::felt!($($tt)*);
         felt
    }};
}

#[cfg(test)]
mod tests {
    use crate::felt::Felt;

    #[test]
    fn felt_macro() {
        // Bools
        assert_eq!(felt!(false), Felt::ZERO);
        assert_eq!(felt!(true), Felt::ONE);

        // Primitive numbers
        assert_eq!(felt!(42), Felt::from(42));
        assert_eq!(felt!(42u8), Felt::from(42));
        assert_eq!(felt!(42i8), Felt::from(42));
        assert_eq!(felt!(42u128), Felt::from(42));
        assert_eq!(felt!(-42), Felt::ZERO - Felt::from(42));
        assert_eq!(felt!(-42i8), Felt::ZERO - Felt::from(42));

        // Statis &str
        assert_eq!(felt!("42"), Felt::from(42));
        assert_eq!(felt!("-42"), Felt::ZERO - Felt::from(42));
        assert_eq!(felt!("0x42"), Felt::from_hex_unwrap("0x42"));

        // Variables
        let x = true;
        assert_eq!(felt!(x), Felt::ONE);
        let x = "42";
        assert_eq!(felt!(x), Felt::from(42));
        let x = String::from("42");
        assert_eq!(felt!(x), Felt::from(42));
        let x = 42u32;
        assert_eq!(felt!(x), Felt::from(42));
        let x = -42;
        assert_eq!(felt!(x), Felt::ZERO - Felt::from(42));

        // Expresions
        let double_closure = |x| x * 2;
        assert_eq!(felt!(double_closure(5)), Felt::from(10));
        assert_eq!(felt!({ 40 + 2 }), Felt::from(42));

        // Constants
        const X: &str = "42";
        assert_eq!(felt!(X), Felt::from(42));
        const Y: u32 = 42;
        assert_eq!(felt!(Y), Felt::from(42));

        // Use in const expressions
        const _: Felt = felt!("0x42");
        const _: Felt = felt!(true);
        const _: Felt = felt!(false);
    }
}
