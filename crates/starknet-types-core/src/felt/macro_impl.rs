/// Handy macro to initialize `Felt`
//
/// Accepts:
/// - booleans
/// - positive and negative number literals (eg. `5`, `12u8`, `-77`, `-2007i32`)
/// - positive and negative decimal string literals (eg. `"5"`, `"-12"`)
/// - positive and negative hexadecimal string literal (eg. `"0x0"`, `"0x42"`)
/// - bytes strings, chars, and bytes, all handled as cairo short strings (eg. `'A'`, `b'A'`, `"AAA"`)
/// - variables of any type that implements `TryFrom<T> for Felt` (eg. `u32`, `i128`, `&str`, `String`)
/// - functions and closure which return type implements `TryFrom<T> for Felt` (eg. `|x| x * 42`, `fn ret42() -> u32 { 42 }` )
/// - code block (eg. `{40 + 2}`) and more generally any expression that returns as types that implements `TryFrom<T> for Felt`
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
    #[cfg(feature = "alloc")]
    pub extern crate alloc;

    use core::ops::Neg;

    use crate::felt::Felt;

    #[test]
    #[allow(double_negations)]
    #[allow(clippy::nonminimal_bool)]
    fn felt_macro() {
        // Bools
        assert_eq!(felt!(false), Felt::ZERO);
        assert_eq!(felt!(true), Felt::ONE);
        assert_eq!(felt!(-true), Felt::from(-1));
        assert_eq!(felt!(!true), Felt::ZERO);
        assert_eq!(felt!(!!true), Felt::ONE);
        assert_eq!(felt!(!!!true), Felt::ZERO);
        assert_eq!(felt!(false | true), Felt::ONE);
        assert_eq!(felt!(true & false), Felt::ZERO);

        // Primitive numbers
        assert_eq!(felt!(42), Felt::from(42));
        assert_eq!(felt!(42u8), Felt::from(42));
        assert_eq!(felt!(42i8), Felt::from(42));
        assert_eq!(felt!(42u128), Felt::from(42));
        assert_eq!(felt!(-42), Felt::ZERO - Felt::from(42));
        assert_eq!(felt!(-42i8), Felt::ZERO - Felt::from(42));
        assert_eq!(felt!(-0x42), Felt::ZERO - Felt::from(0x42));
        assert_eq!(felt!(0b1010), Felt::from(0b1010));
        assert_eq!(felt!(0o777), Felt::from(0o777));

        // Static &str
        assert_eq!(felt!("42"), Felt::from(42));
        assert_eq!(felt!("-42"), Felt::ZERO - Felt::from(42));
        assert_eq!(felt!("0x42"), Felt::from_hex_unwrap("0x42"));
        assert_eq!(felt!("-0x42"), Felt::ZERO - Felt::from_hex_unwrap("0x42"));

        // Negated literals
        assert_eq!(felt!(-"42"), Felt::ZERO - Felt::from(42));
        assert_eq!(felt!(-"-42"), Felt::from(42));
        assert_eq!(felt!(-true), Felt::from(-1));

        // Byte string (handles as cairo short strings)
        assert_eq!(
            felt!(b"SN_MAIN"),
            Felt::from_raw([
                502562008147966918,
                18446744073709551615,
                18446744073709551615,
                17696389056366564951,
            ])
        );
        assert_eq!(
            felt!(b"SN_SEPOLIA"),
            Felt::from_raw([
                507980251676163170,
                18446744073709551615,
                18446744073708869172,
                1555806712078248243,
            ])
        );
        assert_eq!(felt!(b"aa"), Felt::from_hex_unwrap("0x6161"));
        assert_eq!(felt!(-b"ab"), Felt::from_hex_unwrap("0x6162").neg());

        // ASCII chars and bytes, handles as 1 char long cairo short strings
        assert_eq!(felt!('0'), Felt::from(b'0'));
        assert_eq!(felt!('A'), felt!(b"A"));
        assert_eq!(felt!('A'), felt!(b'A'));
        assert_eq!(felt!(-'A'), Felt::from(-65));

        // Variables
        let x = true;
        assert_eq!(felt!(x), Felt::ONE);
        assert_eq!(felt!(!x), Felt::ZERO);
        let x = "42";
        assert_eq!(felt!(x), Felt::from(42));
        let x = alloc::string::String::from("42");
        assert_eq!(felt!(x), Felt::from(42));
        let x = 42u32;
        assert_eq!(felt!(x), Felt::from(42));
        let x = -42;
        assert_eq!(felt!(x), Felt::from(-42));
        assert_eq!(felt!(-x), Felt::from(42));
        assert_eq!(felt!(--x), Felt::from(-42));

        // Expressions
        let double_closure = |x| x * 2;
        assert_eq!(felt!(double_closure(5)), Felt::from(10));
        assert_eq!(felt!(40 + 2), Felt::from(42));
        assert_eq!(felt!(-{ 40 + 2 }), Felt::from(-42));
        let x = 42;
        assert_eq!(felt!({ (40 + 2 == x) | true }), Felt::ONE);
        #[cfg(feature = "alloc")]
        {
            use alloc::string::String;
            let x = String::from("105");
            assert_eq!(felt!(x), Felt::from(105));
        }
        let x = "0x313";
        assert_eq!(felt!(x), Felt::from(0x313));
        let x = true;
        assert_eq!(felt!(!x), Felt::from(0));

        // Constants
        const X: &str = "42";
        assert_eq!(felt!(X), Felt::from(42));
        const Y: u32 = 42;
        assert_eq!(felt!(Y), Felt::from(42));

        // Use in const expressions
        const _: Felt = felt!("0x42");
        const _: Felt = felt!("-0x42");
        const _: Felt = felt!("67");
        const _: Felt = felt!(-"-69");
        const _: Felt = felt!(42);
        const _: Felt = felt!(-42i16);
        const _: Felt = felt!(--0x2i128);
        const _: Felt = felt!(-0b101010);
        const _: Felt = felt!(42i32);
        const _: Felt = felt!(42i32);
        const _: Felt = felt!(true);
        const _: Felt = felt!(!false);
        const _: Felt = felt!(-true);
    }
}
