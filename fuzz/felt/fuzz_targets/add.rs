#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

fuzz_target!(|data: (Felt, Felt, Felt)| {
    let zero = Felt::ZERO;
    let (a, b, c) = data;

    // Check a + 0 = a
    assert_eq!(a + zero, a, "zero addition failed");
    assert_eq!(b + zero, b, "zero addition failed");

    // Check a + (-a) = 0
    assert_eq!(a + (-a), zero, "unary addition failed");
    assert_eq!(b + (-b), zero, "unary addition failed");

    // Check a + b = a - (-b)
    assert_eq!(a + b, a - (-b), "addition failed");

    // Check a + a = a - (-a)
    assert_eq!(a + a, a - (-a), "addition failed");
    assert_eq!(b + b, b - (-b), "addition failed");

    // Check a + a = 2 * a
    assert_eq!(a + a, Felt::TWO * a, "doubling failed");

    // Check a + b = b + a
    assert_eq!(a + b, b + a, "commutativity failed");

    // Check (a + b) + c = a + (b + c)
    assert_eq!((a + b) + c, a + (b + c), "associativity failed");

    // Check a + max = a - 1
    assert_eq!(a + Felt::MAX, a - Felt::ONE, "overflow failed");
});
