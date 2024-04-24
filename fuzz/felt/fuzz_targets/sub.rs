#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    let (a, b) = data;

    // Check a - 0 = a
    assert_eq!(a - zero, a, "zero subtraction failed");
    assert_eq!(b - zero, b, "zero subtraction failed");

    // Check a - a = 0
    assert_eq!(a - a, zero, "unary subtraction failed");
    assert_eq!(b - b, zero, "unary subtraction failed");

    // Check a - b = a + (-b)
    assert_eq!(a - b, a + (-b), "subtraction failed");

    // Check a - a = a + (-a)
    assert_eq!(a - a, a + (-a), "subtraction failed");
    assert_eq!(b - b, b + (-b), "subtraction failed");

    // Check 0 - a = max - a + 1
    assert_eq!(zero - a, Felt::MAX - a + Felt::ONE, "overflow failed");

});
