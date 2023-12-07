#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    // Check a + 0 = a
    assert_eq!(data.0 + zero, data.0, "Zero addition failed");
    assert_eq!(data.1 + zero, data.1, "Zero addition failed");

    // Check a + (-a) = 0
    assert_eq!(data.0 + (-data.0), zero, "Unary addition failed");
    assert_eq!(data.1 + (-data.1), zero, "Unary addition failed");

    // Check a + b = a - (-b)
    assert_eq!(data.0 + data.1, data.0 - (-data.1), "addition failed");
    // Check a + a = a - (-a)
    assert_eq!(data.0 + data.0, data.0 - (-data.0), "addition failed");
    assert_eq!(data.1 + data.1, data.1 - (-data.1), "addition failed");
    // Check a + a = 2 * a
    assert_eq!(data.0 + data.0, Felt::TWO * data.0, "Doubling failed");
});
