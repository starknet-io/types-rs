#![no_main]

use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::{Felt, NonZeroFelt};

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    let one = Felt::ONE;

    let (a, b) = data;

    // Check a/a  = 1
    if a != zero {
        let a_non_zero = NonZeroFelt::try_from(a).unwrap();
        assert_eq!(a.field_div(&a_non_zero), one);
    }

    // Check a / 1 = a
    assert_eq!(a.field_div(&NonZeroFelt::try_from(one).unwrap()), a);

    // Check a * a^-1 = 1
    if a != zero {
        assert_eq!(one, a * a.inverse().unwrap(),);
    }

    // Check a / b = a * b^-1
    if b != zero {
        let b_non_zero = NonZeroFelt::try_from(b).unwrap();
        let b_inverse = b.inverse().unwrap();
        assert_eq!(a.field_div(&b_non_zero), a * b_inverse);
    }

    // Check (a / b) / b  = a / (b * b)
    if b != zero {
        let b_non_zero = NonZeroFelt::try_from(b).unwrap();
        let b_times_b_non_zero = NonZeroFelt::try_from(b * b).unwrap();
        assert_eq!(
            a.field_div(&b_non_zero).field_div(&b_non_zero),
            a.field_div(&b_times_b_non_zero),
        );
    }

    // Check a / b = (a.to_biguint() * b^-1.to_biguint()) % PRIME
    if b != zero {
        let b_non_zero = NonZeroFelt::try_from(b).unwrap();
        let b_inverse = b.inverse().unwrap();
        assert_eq!(
            a.field_div(&b_non_zero),
            Felt::from(a.to_biguint() * b_inverse.to_biguint()),
        );
    }
});
