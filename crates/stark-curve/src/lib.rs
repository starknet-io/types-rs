use core::ops;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
use stark_felt::Felt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectivePoint(ShortWeierstrassProjectivePoint<StarkCurve>);

impl ProjectivePoint {
    pub fn new(x: Felt, y: Felt, z: Felt) -> ProjectivePoint {
        Self(ShortWeierstrassProjectivePoint::new([x.0, y.0, z.0]))
    }

    pub fn identity() -> ProjectivePoint {
        Self(ShortWeierstrassProjectivePoint::neutral_element())
    }
}

impl ops::AddAssign<&ProjectivePoint> for ProjectivePoint {
    fn add_assign(&mut self, rhs: &ProjectivePoint) {
        self.0 = self.0.operate_with(&rhs.0);
    }
}
