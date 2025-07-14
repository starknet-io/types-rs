use crate::felt::Felt;
use arbitrary::{self, Arbitrary, Unstructured};
use lambdaworks_math::field::element::FieldElement;
use lambdaworks_math::unsigned_integer::element::UnsignedInteger;

impl Arbitrary<'_> for Felt {
    // Creates an arbitrary `Felt` from unstructured input for fuzzing.
    // It uses the default implementation to create the internal limbs and then
    // uses the usual constructors from `lambdaworks-math`.
    fn arbitrary(u: &mut Unstructured) -> arbitrary::Result<Self> {
        let limbs = <[u64; 4]>::arbitrary(u)?;
        let uint = UnsignedInteger::from_limbs(limbs);
        let felt = FieldElement::new(uint);
        Ok(Felt(felt))
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <[u64; 4]>::size_hint(depth)
    }
}
