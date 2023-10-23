use crate::curve::projective_point::ProjectivePoint;
use crate::felt::Felt;
use core::ops;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
use lambdaworks_math::elliptic_curve::traits::{EllipticCurveError, FromAffine};
use lambdaworks_math::field::element::FieldElement;
use lambdaworks_math::field::fields::fft_friendly::stark_252_prime_field::Stark252PrimeField;
use lambdaworks_math::unsigned_integer::traits::IsUnsignedInteger;

pub struct AffinePoint(pub(crate) ShortWeierstrassProjectivePoint<StarkCurve>);

impl AffinePoint {
    pub fn new(x: Felt, y: Felt) -> Result<AffinePoint, EllipticCurveError> {
        Ok(Self(ShortWeierstrassProjectivePoint::from_affine(
            x.0, y.0,
        )?))
    }

    pub fn identity() -> AffinePoint {
        Self(ShortWeierstrassProjectivePoint::neutral_element())
    }

    /// Returns the `x` coordinate of the point.
    pub fn x(&self) -> &FieldElement<Stark252PrimeField> {
        self.0.x()
    }

    /// Returns the `y` coordinate of the point.
    pub fn y(&self) -> &FieldElement<Stark252PrimeField> {
        self.0.y()
    }
}

impl ops::Add<&AffinePoint> for &AffinePoint {
    type Output = AffinePoint;

    fn add(self, rhs: &AffinePoint) -> AffinePoint {
        AffinePoint(self.0.operate_with(&rhs.0))
    }
}

impl ops::AddAssign<&AffinePoint> for AffinePoint {
    fn add_assign(&mut self, rhs: &AffinePoint) {
        self.0 = self.0.operate_with(&rhs.0);
    }
}

impl ops::Mul<&Felt> for &AffinePoint {
    type Output = AffinePoint;

    fn mul(self, rhs: &Felt) -> AffinePoint {
        AffinePoint(self.0.operate_with_self(rhs.0.representative()))
    }
}

impl<T> ops::Mul<T> for &AffinePoint
where
    T: IsUnsignedInteger, // Asumiendo que "exponent" es una trait
{
    type Output = AffinePoint;

    fn mul(self, rhs: T) -> AffinePoint {
        AffinePoint(self.0.operate_with_self(rhs))
    }
}

impl From<AffinePoint> for ProjectivePoint {
    fn from(affine_point: AffinePoint) -> ProjectivePoint {
        ProjectivePoint(affine_point.0)
    }
}
