use lambdaworks_math::field::{
    element::FieldElement, errors::FieldError,
    fields::mersenne31::extensions::Degree4ExtensionField,
};
use num_traits::{Inv, One, Zero};

use super::QM31;

impl Zero for QM31 {
    fn zero() -> Self {
        Self(FieldElement::<Degree4ExtensionField>::zero())
    }

    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }
}
impl One for QM31 {
    fn one() -> Self {
        Self(FieldElement::<Degree4ExtensionField>::one())
    }
}
impl Inv for QM31 {
    type Output = Result<QM31, FieldError>;

    fn inv(self) -> Self::Output {
        self.inverse()
    }
}
