use crate::felt::Felt;
use core::ops;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
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

    /// Creates the same point in affine coordinates. That is,
    /// returns [x / z: y / z: 1] where `self` is [x: y: z].
    /// Panics if `self` is the point at infinity.
    pub fn to_affine(&self) -> AffinePoint {
        AffinePoint(self.0.to_affine())
    }

    /// Returns the `x` coordinate of the point.
    pub fn x(&self) -> Felt {
        Felt(*self.0.x())
    }

    /// Returns the `y` coordinate of the point.
    pub fn y(&self) -> Felt {
        Felt(*self.0.y())
    }

    /// Returns the `z` coordinate of the point.
    pub fn z(&self) -> Felt {
        Felt(*self.0.z())
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

impl ops::Mul<Felt> for &ProjectivePoint {
    type Output = ProjectivePoint;

    fn mul(self, rhs: Felt) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with_self(rhs.0.representative()))
    }
}

impl<T> ops::Mul<T> for &ProjectivePoint
where
    T: IsUnsignedInteger,
{
    type Output = ProjectivePoint;

    fn mul(self, rhs: T) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with_self(rhs))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn projective_point_identity() {
        let identity = ProjectivePoint::identity();

        assert_eq!(
            identity,
            ProjectivePoint::new(Felt::from(0), Felt::from(1), Felt::from(0))
        )
    }

    #[test]
    fn add_operations() {
        let projective_point_1 = ProjectivePoint::new(
            Felt::from_dec_str(
                "874739451078007766457464989774322083649278607533249481151382481072868806602",
            )
            .unwrap(),
            Felt::from_dec_str(
                "152666792071518830868575557812948353041420400780739481342941381225525861407",
            )
            .unwrap(),
            Felt::from(1),
        );
        let projective_point_2 = projective_point_1.clone();
        let result = (&projective_point_1 + &projective_point_2).to_affine();

        assert_eq!(
            result,
            AffinePoint::new(
                Felt::from_dec_str(
                    "3324833730090626974525872402899302150520188025637965566623476530814354734325",
                )
                .unwrap(),
                Felt::from_dec_str(
                    "3147007486456030910661996439995670279305852583596209647900952752170983517249",
                )
                .unwrap()
            )
            .unwrap()
        )
    }

    #[test]
    fn add_assign_operations() {
        let mut projective_point_1 = ProjectivePoint::new(
            Felt::from_dec_str(
                "874739451078007766457464989774322083649278607533249481151382481072868806602",
            )
            .unwrap(),
            Felt::from_dec_str(
                "152666792071518830868575557812948353041420400780739481342941381225525861407",
            )
            .unwrap(),
            Felt::from(1),
        );
        let projective_point_2 = projective_point_1.clone();
        projective_point_1 += &projective_point_2;

        let result = projective_point_1.to_affine();

        assert_eq!(
            result.x(),
            Felt::from_dec_str(
                "3324833730090626974525872402899302150520188025637965566623476530814354734325",
            )
            .unwrap()
        );

        assert_eq!(
            result.y(),
            Felt::from_dec_str(
                "3147007486456030910661996439995670279305852583596209647900952752170983517249",
            )
            .unwrap()
        );
    }

    #[test]
    fn mul_operations() {
        let identity = ProjectivePoint::identity();

        assert_eq!(&identity * 11_u16, identity);
        assert_eq!(
            &identity * Felt::from_dec_str("8731298391798138132780",).unwrap(),
            identity
        );

        let projective_point_1 = ProjectivePoint::new(
            Felt::from_dec_str(
                "685118385380464480289795596422487144864558069280897344382334516257395969277",
            )
            .unwrap(),
            Felt::from_dec_str(
                "2157469546853095472290556201984093730375838368522549154974787195581425752638",
            )
            .unwrap(),
            Felt::from(1),
        );

        let result = (&projective_point_1 * 1812_u32).to_affine();

        assert_eq!(
            result,
            AffinePoint::new(
                Felt::from_dec_str(
                    "3440268448213322209285127313797148367487473316555419755705577898182859853039",
                )
                .unwrap(),
                Felt::from_dec_str(
                    "1596323783766236796787317367695486687781666659527154739146733884430376982452",
                )
                .unwrap()
            )
            .unwrap()
        )
    }
}
