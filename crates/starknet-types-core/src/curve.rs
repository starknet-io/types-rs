use crate::felt::Felt;
use core::ops;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
use lambdaworks_math::elliptic_curve::traits::{EllipticCurveError, FromAffine};

// TODO sacar pub
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectivePoint(ShortWeierstrassProjectivePoint<StarkCurve>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffinePoint(ShortWeierstrassProjectivePoint<StarkCurve>);

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

impl AffinePoint {
    pub fn new(x: Felt, y: Felt) -> Result<AffinePoint, EllipticCurveError> {
        Ok(Self(ShortWeierstrassProjectivePoint::from_affine(
            x.0, y.0,
        )?))
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

impl From<AffinePoint> for ProjectivePoint {
    fn from(affine_point: AffinePoint) -> ProjectivePoint {
        ProjectivePoint(affine_point.0)
    }
}
