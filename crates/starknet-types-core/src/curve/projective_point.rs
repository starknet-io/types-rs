use crate::felt::Felt;
use core::ops;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
use lambdaworks_math::elliptic_curve::traits::{EllipticCurveError, FromAffine};
use lambdaworks_math::field::element::FieldElement;
use lambdaworks_math::field::fields::fft_friendly::stark_252_prime_field::Stark252PrimeField;
use lambdaworks_math::unsigned_integer::traits::IsUnsignedInteger;

use crate::curve::affine_point::AffinePoint;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectivePoint(pub(crate) ShortWeierstrassProjectivePoint<StarkCurve>);

impl ProjectivePoint {
    pub fn new(x: Felt, y: Felt, z: Felt) -> ProjectivePoint {
        Self(ShortWeierstrassProjectivePoint::new([x.0, y.0, z.0]))
    }

    pub fn identity() -> ProjectivePoint {
        Self(ShortWeierstrassProjectivePoint::neutral_element())
    }

    pub fn to_affine_point(
        projective_point: &ProjectivePoint,
    ) -> Result<AffinePoint, EllipticCurveError> {
        Ok(AffinePoint(ShortWeierstrassProjectivePoint::from_affine(
            *projective_point.0.x(),
            *projective_point.0.y(),
        )?))
    }

    /// Returns the `x` coordinate of the point.
    pub fn x(&self) -> &FieldElement<Stark252PrimeField> {
        self.0.x()
    }

    /// Returns the `y` coordinate of the point.
    pub fn y(&self) -> &FieldElement<Stark252PrimeField> {
        self.0.y()
    }

    /// Returns the `z` coordinate of the point.
    pub fn z(&self) -> &FieldElement<Stark252PrimeField> {
        self.0.z()
    }
}

impl ops::Add<&ProjectivePoint> for &ProjectivePoint {
    type Output = ProjectivePoint;

    fn add(self, rhs: &ProjectivePoint) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with(&rhs.0))
    }
}

impl ops::AddAssign<&ProjectivePoint> for ProjectivePoint {
    fn add_assign(&mut self, rhs: &ProjectivePoint) {
        self.0 = self.0.operate_with(&rhs.0);
    }
}

impl ops::Mul<&Felt> for &ProjectivePoint {
    type Output = ProjectivePoint;

    fn mul(self, rhs: &Felt) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with_self(rhs.0.representative()))
    }
}

impl<T> ops::Mul<T> for &ProjectivePoint
where
    T: IsUnsignedInteger, // Asumiendo que "exponent" es una trait
{
    type Output = ProjectivePoint;

    fn mul(self, rhs: T) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with_self(rhs))
    }
}
