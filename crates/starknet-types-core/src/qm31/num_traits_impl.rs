use lambdaworks_math::field::{
    element::FieldElement, errors::FieldError,
    fields::mersenne31::extensions::Degree4ExtensionField,
};
use num_traits::{Inv, One, Pow, Zero};

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
impl Pow<u8> for QM31 {
    type Output = Self;

    fn pow(self, rhs: u8) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u16> for QM31 {
    type Output = Self;

    fn pow(self, rhs: u16) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u32> for QM31 {
    type Output = Self;

    fn pow(self, rhs: u32) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u64> for QM31 {
    type Output = Self;

    fn pow(self, rhs: u64) -> Self::Output {
        Self(self.0.pow(rhs as u128))
    }
}
impl Pow<u128> for QM31 {
    type Output = Self;

    fn pow(self, rhs: u128) -> Self::Output {
        Self(self.0.pow(rhs))
    }
}
