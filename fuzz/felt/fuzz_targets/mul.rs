#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::{Felt, NonZeroFelt};

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    let one = Felt::ONE;
    let (a, b) = data;

    // Check a * 1 = a
    assert_eq!(a * one, a, "multiplicative identity failed");
    assert_eq!(b * one, b, "multiplicative identity failed");

    // Check 1 * a = a
    assert_eq!(one * a, a, "multiplicative identity failed");
    assert_eq!(one * b, b, "multiplicative identity failed");

    // Check a * 0 = 0
    assert_eq!(a * zero, zero, "zero product failed");
    assert_eq!(b * zero, zero, "zero product failed");

    // Check 0 * a = a
    assert_eq!(zero * a, zero, "zero product failed");
    assert_eq!(zero * b, zero, "zero product failed");

    // Check a * max = max - a + 1
    assert_eq!(a * Felt::MAX, Felt::MAX - a + 1, "overflow failed");

    // Check a * b = b * a
    assert_eq!(a * b, b * a, "commutativity failed");
});
