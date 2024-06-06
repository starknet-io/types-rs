#![no_main]
use libfuzzer_sys::fuzz_target;
use starknet_types_core::felt::Felt;

fuzz_target!(|data: (Felt, Felt)| {
    let zero = Felt::ZERO;
    let one = Felt::ONE;
    let max = Felt::MAX;
    let (a, b) = data;

    // Check a + 0 = a
    assert_eq!(a + zero, a);
    assert_eq!(b + zero, b);

    // Check a - 0 = a
    assert_eq!(a - zero, a);
    assert_eq!(b - zero, b);

    // Check a - a = 0
    assert_eq!(a - a, zero);
    assert_eq!(b - b, zero);

    // Check a + (-a) = 0
    assert_eq!(a + (-a), zero);
    assert_eq!(b + (-b), zero);

    // Check a + b = a - (-b)
    assert_eq!(a + b, a - (-b));

    // Check a + a = a - (-a)
    assert_eq!(a + a, a - (-a));
    assert_eq!(b + b, b - (-b));

    // Check a + a = 2 * a
    assert_eq!(a + a, Felt::TWO * a);
    assert_eq!(b + b, Felt::TWO * b);

    // Check a + b = b + a
    assert_eq!(a + b, b + a);

    // Check (a + b) + b = a + (b + b)
    assert_eq!((a + b) + b, a + (b + b));

    // Check a + max = a - 1
    assert_eq!(a + max, a - one);
    assert_eq!(b + max, b - one);

    // Check 0 - a = max - a + 1
    assert_eq!(zero - a, max - a + one);
    assert_eq!(zero - b, max - b + one);

    // Check a + b = (a.to_biguint() + b.to_biguint()) % PRIME
    assert_eq!(a + b, Felt::from(a.to_biguint() + b.to_biguint()));

    // a.double = a + a
    assert_eq!(a.double(), a + a);
    assert_eq!(b.double(), b + b);
});
