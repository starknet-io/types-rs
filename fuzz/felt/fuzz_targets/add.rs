#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    let (a, b) = data;
    // Check a + 0 = a
    assert_eq!(a + zero, a, "Zero addition failed");
    assert_eq!(b + zero, b, "Zero addition failed");

    // Check a + (-a) = 0
    assert_eq!(a + (-a), zero, "Unary addition failed");
    assert_eq!(b + (-b), zero, "Unary addition failed");

    // Check a + b = a - (-b)
    assert_eq!(a + b, a - (-b), "addition failed");

    // Check a + a = a - (-a)
    assert_eq!(a + a, a - (-a), "addition failed");
    assert_eq!(b + b, b - (-b), "addition failed");

    // Check a + a = 2 * a
    assert_eq!(a + a, Felt::TWO * a, "Doubling failed");
});
