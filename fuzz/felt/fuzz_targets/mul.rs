#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    let one = Felt::ONE;
    let (a, b) = data;

    // Check a * 1 = a
    assert_eq!(a * one, a);
    assert_eq!(b * one, b);

    // Check 1 * a = a
    assert_eq!(one * a, a);
    assert_eq!(one * b, b);

    // Check a * 0 = 0
    assert_eq!(a * zero, zero);
    assert_eq!(b * zero, zero);

    // Check 0 * a = a
    assert_eq!(zero * a, zero);
    assert_eq!(zero * b, zero);

    // Check a * max = max - a + 1
    assert_eq!(a * Felt::MAX, Felt::MAX - a + 1);

    // Check a * b = b * a
    assert_eq!(a * b, b * a);

    // Check a * b = (a.to_biguint() * b.to_biguint()) % PRIME
    assert_eq!(a * b, Felt::from(a.to_biguint() * b.to_biguint()));

    assert_eq!(a.square(), a * a);
    assert_eq!(b.square(), b * b);
});
