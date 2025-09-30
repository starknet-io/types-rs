use crate::curve::affine_point::AffinePoint;
use crate::curve::curve_errors::CurveError;
use crate::felt::Felt;
use core::ops;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
use lambdaworks_math::elliptic_curve::traits::EllipticCurveError::InvalidPoint;
use lambdaworks_math::elliptic_curve::traits::FromAffine;
use lambdaworks_math::unsigned_integer::traits::IsUnsignedInteger;

/// Represents a projective point on the Stark elliptic curve.
#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectivePoint(pub(crate) ShortWeierstrassProjectivePoint<StarkCurve>);

impl ProjectivePoint {
    pub fn new(x: Felt, y: Felt, z: Felt) -> Result<ProjectivePoint, CurveError> {
        Ok(Self(ShortWeierstrassProjectivePoint::new([x.0, y.0, z.0])?))
    }

    /// Creates a new short Weierstrass projective point, assuming the coordinates are valid.
    ///
    /// The coordinates are valid if the equation `y^2 * z = x^3 + a * x * z^2 + b * z^3`
    /// holds, Where `a` and `b` are the short Weierstrass coefficients of the Stark
    /// curve. Furthermore, the coordinates in the form `[0, _, 0]` all satisfy the
    /// equation, and should be always transformed to the infinity value `[0, 1, 0]`.
    ///
    /// SAFETY: Failing to guarantee this assumptions could lead to a runtime panic
    /// while operating with the value.
    pub const fn new_unchecked(x: Felt, y: Felt, z: Felt) -> ProjectivePoint {
        Self(ShortWeierstrassProjectivePoint::new_unchecked([
            x.0, y.0, z.0,
        ]))
    }

    /// The point at infinity.
    pub fn identity() -> ProjectivePoint {
        Self(ShortWeierstrassProjectivePoint::neutral_element())
    }

    pub fn is_identity(&self) -> bool {
        self == &Self::identity()
    }

    /// Creates the same point in affine coordinates. That is,
    /// returns (x * inv_z, y* inv_z,  1)
    /// where `self` is the point (x, y, z) and inv_z is the multiplicative inverse of z
    pub fn to_affine(&self) -> Result<AffinePoint, CurveError> {
        if self.z() == Felt::ZERO {
            return Err(CurveError::EllipticCurveError(InvalidPoint));
        }
        Ok(AffinePoint(self.0.to_affine()))
    }

    pub fn from_affine(x: Felt, y: Felt) -> Result<Self, CurveError> {
        Ok(Self(
            ShortWeierstrassProjectivePoint::from_affine(x.0, y.0)
                .map_err(CurveError::EllipticCurveError)?,
        ))
    }

    /// Constructs a new projective point without checking whether the coordinates specify a point in the subgroup.
    /// This method should be used with caution, as it does not validate whether the provided coordinates
    /// correspond to a valid point on the curve.
    pub fn from_affine_unchecked(x: Felt, y: Felt) -> Self {
        Self(ShortWeierstrassProjectivePoint::new_unchecked([
            x.0,
            y.0,
            Felt::ONE.0,
        ]))
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

    pub fn double(&self) -> Self {
        Self(self.0.double())
    }
}

impl TryFrom<AffinePoint> for ProjectivePoint {
    type Error = CurveError;

    fn try_from(affine_point: AffinePoint) -> Result<Self, Self::Error> {
        Self::from_affine(affine_point.x(), affine_point.y())
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

impl ops::Add<&AffinePoint> for &ProjectivePoint {
    type Output = ProjectivePoint;

    fn add(self, rhs: &AffinePoint) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with_affine(&rhs.0))
    }
}

impl ops::AddAssign<&AffinePoint> for ProjectivePoint {
    fn add_assign(&mut self, rhs: &AffinePoint) {
        self.0 = self.0.operate_with_affine(&rhs.0);
    }
}

impl ops::Add<AffinePoint> for ProjectivePoint {
    type Output = ProjectivePoint;

    fn add(self, rhs: AffinePoint) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with_affine(&rhs.0))
    }
}

impl ops::AddAssign<AffinePoint> for ProjectivePoint {
    fn add_assign(&mut self, rhs: AffinePoint) {
        self.0 = self.0.operate_with_affine(&rhs.0);
    }
}

impl ops::Add<ProjectivePoint> for ProjectivePoint {
    type Output = ProjectivePoint;

    fn add(self, rhs: ProjectivePoint) -> ProjectivePoint {
        ProjectivePoint(self.0.operate_with(&rhs.0))
    }
}

impl ops::AddAssign<ProjectivePoint> for ProjectivePoint {
    fn add_assign(&mut self, rhs: ProjectivePoint) {
        self.0 = self.0.operate_with(&rhs.0);
    }
}

impl core::ops::Neg for &ProjectivePoint {
    type Output = ProjectivePoint;

    fn neg(self) -> ProjectivePoint {
        ProjectivePoint(self.0.neg())
    }
}

impl core::ops::Sub<&ProjectivePoint> for &ProjectivePoint {
    type Output = ProjectivePoint;

    fn sub(self, rhs: &ProjectivePoint) -> ProjectivePoint {
        self + &-rhs
    }
}

impl core::ops::SubAssign<&ProjectivePoint> for ProjectivePoint {
    fn sub_assign(&mut self, rhs: &ProjectivePoint) {
        *self += &-rhs;
    }
}

impl core::ops::Sub<ProjectivePoint> for ProjectivePoint {
    type Output = ProjectivePoint;

    fn sub(self, rhs: ProjectivePoint) -> ProjectivePoint {
        &self - &rhs
    }
}

impl core::ops::SubAssign<ProjectivePoint> for ProjectivePoint {
    fn sub_assign(&mut self, rhs: ProjectivePoint) {
        *self -= &rhs;
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
    fn try_from_affine() {
        let projective_point = ProjectivePoint::new_unchecked(
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
        let affine_point = projective_point.clone().to_affine().unwrap();

        assert_eq!(
            TryInto::<ProjectivePoint>::try_into(affine_point).unwrap(),
            projective_point
        );
    }

    #[test]
    fn try_from_affine_invalid_point() {
        let affine_point = AffinePoint::new_unchecked(
            Felt::from_dec_str(
                "4739451078007766457464989774322083649278607533249481151382481072868806602",
            )
            .unwrap(),
            Felt::from_dec_str(
                "152666792071518830868575557812948353041420400780739481342941381225525861407",
            )
            .unwrap(),
        );

        assert!(matches!(
            TryInto::<ProjectivePoint>::try_into(affine_point),
            Err(CurveError::EllipticCurveError(_))
        ));
    }

    #[test]
    fn from_affine_unchecked() {
        let a = AffinePoint::new(
            Felt::from_dec_str(
                "3324833730090626974525872402899302150520188025637965566623476530814354734325",
            )
            .unwrap(),
            Felt::from_dec_str(
                "3147007486456030910661996439995670279305852583596209647900952752170983517249",
            )
            .unwrap(),
        )
        .unwrap();

        assert_eq!(
            ProjectivePoint::from_affine_unchecked(a.x(), a.y()),
            ProjectivePoint::from_affine(a.x(), a.y()).unwrap()
        );
    }

    #[test]
    fn projective_point_identity() {
        let identity = ProjectivePoint::identity();
        assert!(identity.is_identity());
        assert_eq!(
            identity,
            ProjectivePoint::new_unchecked(Felt::from(0), Felt::from(1), Felt::from(0))
        );

        assert_eq!(
            identity.to_affine(),
            Err(CurveError::EllipticCurveError(InvalidPoint))
        );

        let a = ProjectivePoint::new_unchecked(
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
        assert!(!a.is_identity());
    }

    #[test]
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn add_operations() {
        let projective_point_1 = ProjectivePoint::new_unchecked(
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
        let result = (&projective_point_1 + &projective_point_2)
            .to_affine()
            .unwrap();

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
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn add_operations_with_affine() {
        let projective_point = ProjectivePoint::new_unchecked(
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
        let affine_point = projective_point.clone().to_affine().unwrap();
        let result = (&projective_point + &affine_point).to_affine().unwrap();

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
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn add_operations_with_affine_no_pointer() {
        let projective_point = ProjectivePoint::new_unchecked(
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
        let affine_point = projective_point.clone().to_affine().unwrap();
        let result = (projective_point + affine_point).to_affine().unwrap();

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
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn add_assign_operations() {
        let mut projective_point_1 = ProjectivePoint::new_unchecked(
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

        let result = projective_point_1.to_affine().unwrap();

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
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn add_assign_operations_with_affine() {
        let mut projective_point = ProjectivePoint::new_unchecked(
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
        let affine_point = projective_point.clone().to_affine().unwrap();
        projective_point += &affine_point;

        let result = projective_point.to_affine().unwrap();

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
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn add_assign_operations_with_affine_no_pointer() {
        let mut projective_point = ProjectivePoint::new_unchecked(
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
        let affine_point = projective_point.clone().to_affine().unwrap();
        projective_point += affine_point;

        let result = projective_point.to_affine().unwrap();

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
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn mul_operations() {
        let identity = ProjectivePoint::identity();

        assert_eq!(&identity * 11_u16, identity);
        assert_eq!(
            &identity * Felt::from_dec_str("8731298391798138132780",).unwrap(),
            identity
        );

        let projective_point_1 = ProjectivePoint::new_unchecked(
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

        let result = (&projective_point_1 * 1812_u32).to_affine().unwrap();

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

    #[test]
    fn mul_by_scalar_operations_with_felt() {
        let a = ProjectivePoint::new_unchecked(
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
        let b = Felt::from(1812);

        let mut expected = a.clone();

        for _ in 0..1811 {
            expected += a.clone();
        }

        assert_eq!((&a * b).to_affine().unwrap(), expected.to_affine().unwrap());
    }

    #[test]
    // Results checked against starknet-rs https://github.com/xJonathanLEI/starknet-rs/
    fn double_operations() {
        let projective_point = ProjectivePoint::new_unchecked(
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

        assert_eq!(
            projective_point.double().to_affine().unwrap(),
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
        );
    }

    #[test]
    fn neg_operations() {
        let a = ProjectivePoint::new_unchecked(
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

        let b = ProjectivePoint::new_unchecked(
            Felt::from_dec_str(
                "685118385380464480289795596422487144864558069280897344382334516257395969277",
            )
            .unwrap(),
            -Felt::from_dec_str(
                "2157469546853095472290556201984093730375838368522549154974787195581425752638",
            )
            .unwrap(),
            Felt::from(1),
        );

        assert_eq!(-&a, b);
    }

    #[test]
    fn sub_operations_pointers() {
        let mut a = ProjectivePoint::new_unchecked(
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
        let b = a.clone();

        assert_eq!(&ProjectivePoint::identity() - &a, -&a);
        assert_eq!(&a - &a, ProjectivePoint::identity());
        assert_eq!(&(&a - &a) + &a, a);
        a -= &b;
        assert_eq!(a, ProjectivePoint::identity());
    }

    #[test]
    fn sub_operations() {
        let mut a = ProjectivePoint::new_unchecked(
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
        let b = a.clone();

        assert_eq!(ProjectivePoint::identity() - a.clone(), -&a);
        assert_eq!(a.clone() - a.clone(), ProjectivePoint::identity());
        assert_eq!(a.clone() - a.clone() + a.clone(), a);
        a -= b;
        assert_eq!(a, ProjectivePoint::identity());
    }
}
