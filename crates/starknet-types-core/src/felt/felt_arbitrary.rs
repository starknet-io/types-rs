use lambdaworks_math::{field::element::FieldElement, unsigned_integer::element::UnsignedInteger};
use proptest::prelude::*;

use crate::felt::Felt;
const FIELD_HIGH: u128 = (1 << 123) + (17 << 64); // this is equal to 10633823966279327296825105735305134080
const FIELD_LOW: u128 = 1;

/// Returns a [`Strategy`] that generates any valid Felt
/// This is used to generate input values for proptests
fn any_felt() -> impl Strategy<Value = Felt> {
    (0..=FIELD_HIGH)
        // turn range into `impl Strategy`
        .prop_map(|x| x)
        // choose second 128-bit limb capped by first one
        .prop_flat_map(|high| {
            let low = if high == FIELD_HIGH {
                (0..FIELD_LOW).prop_map(|x| x).sboxed()
            } else {
                any::<u128>().sboxed()
            };
            (Just(high), low)
        })
        // turn (u128, u128) into limbs array and then into Felt
        .prop_map(|(high, low)| {
            let limbs = [
                (high >> 64) as u64,
                (high & ((1 << 64) - 1)) as u64,
                (low >> 64) as u64,
                (low & ((1 << 64) - 1)) as u64,
            ];
            FieldElement::new(UnsignedInteger::from_limbs(limbs))
        })
        .prop_map(Felt)
}

/// Returns a [`Strategy`] that generates any nonzero Felt
/// This is used to generate input values for proptests
pub fn nonzero_felt() -> impl Strategy<Value = Felt> {
    any_felt().prop_filter("is zero", |&x| x != Felt::ZERO)
}

impl Arbitrary for Felt {
    type Parameters = ();

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        any_felt().sboxed()
    }

    type Strategy = SBoxedStrategy<Self>;
}
