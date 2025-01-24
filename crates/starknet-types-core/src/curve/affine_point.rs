use crate::{curve::curve_errors::CurveError, felt::Felt};
use lambdaworks_math::{
    cyclic_group::IsGroup,
    elliptic_curve::{
        short_weierstrass::{
            curves::stark_curve::StarkCurve, point::ShortWeierstrassProjectivePoint,
        },
        traits::{FromAffine, IsEllipticCurve},
    },
};

/// Represents a point on the Stark elliptic curve.
/// Doc: https://docs.starkware.co/starkex/crypto/stark-curve.html
#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffinePoint(pub(crate) ShortWeierstrassProjectivePoint<StarkCurve>);

impl AffinePoint {
    pub fn new(x: Felt, y: Felt) -> Result<AffinePoint, CurveError> {
        Ok(Self(ShortWeierstrassProjectivePoint::from_affine(
            x.0, y.0,
        )?))
    }

    /// Constructs a new affine point without checking whether the coordinates specify a point in the subgroup.
    /// This method should be used with caution, as it does not validate whether the provided coordinates
    /// correspond to a valid point on the curve.
    pub const fn new_unchecked(x: Felt, y: Felt) -> AffinePoint {
        Self(ShortWeierstrassProjectivePoint::new([
            x.0,
            y.0,
            Felt::ONE.0,
        ]))
    }

    /// The point at infinity.
    pub fn identity() -> AffinePoint {
        Self(ShortWeierstrassProjectivePoint::neutral_element())
    }

    pub fn is_identity(&self) -> bool {
        self == &Self::identity()
    }

    /// Returns the `x` coordinate of the point.
    pub fn x(&self) -> Felt {
        Felt(*self.0.x())
    }

    /// Returns the `y` coordinate of the point.
    pub fn y(&self) -> Felt {
        Felt(*self.0.y())
    }

    // Returns the generator point of the StarkCurve
    pub fn generator() -> Self {
        AffinePoint(StarkCurve::generator())
    }
}

impl core::ops::Neg for &AffinePoint {
    type Output = AffinePoint;

    fn neg(self) -> AffinePoint {
        AffinePoint(self.0.neg())
    }
}

impl core::ops::Add<AffinePoint> for AffinePoint {
    type Output = AffinePoint;

    fn add(self, rhs: Self) -> Self::Output {
        AffinePoint(self.0.operate_with_affine(&rhs.0))
    }
}

impl core::ops::Mul<Felt> for &AffinePoint {
    type Output = AffinePoint;

    // Add the point (`self`) to itself for `scalar` many times
    fn mul(self, rhs: Felt) -> AffinePoint {
        AffinePoint(self.0.operate_with_self(rhs.0.representative()))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn affine_point_new_unchecked() {
        let a = AffinePoint::new(
            Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
            Felt::from_hex_unchecked(
                "0x11a2681208d7c128580162110d9e6ddb0bd34e42ace22dcc7f52f9939e11df6",
            ),
        )
        .unwrap();

        let b = AffinePoint::new_unchecked(
            Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
            Felt::from_hex_unchecked(
                "0x11a2681208d7c128580162110d9e6ddb0bd34e42ace22dcc7f52f9939e11df6",
            ),
        );
        assert!(a.eq(&b));
    }

    #[test]
    fn affine_point_identity() {
        let identity = AffinePoint::identity();

        assert!(identity.is_identity());
        assert_eq!(identity.x(), Felt::from(0));
        assert_eq!(identity.y(), Felt::from(1));

        let a = AffinePoint::new(
            Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
            Felt::from_hex_unchecked(
                "0x11a2681208d7c128580162110d9e6ddb0bd34e42ace22dcc7f52f9939e11df6",
            ),
        );
        assert!(!a.unwrap().is_identity());
    }

    #[test]
    fn affine_neg() {
        assert_eq!(
            -&AffinePoint::new(
                Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
                Felt::from_hex_unchecked(
                    "0x11a2681208d7c128580162110d9e6ddb0bd34e42ace22dcc7f52f9939e11df6"
                ),
            )
            .unwrap(),
            AffinePoint::new(
                Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
                Felt::from_hex_unchecked(
                    "0x6e5d97edf7283fe7a7fe9deef2619224f42cb1bd531dd23380ad066c61ee20b"
                ),
            )
            .unwrap()
        );
        assert_eq!(-&AffinePoint::identity(), AffinePoint::identity());
    }

    #[test]
    fn affine_add() {
        let p = AffinePoint::new(
            Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
            Felt::from_hex_unchecked(
                "0x6e5d97edf7283fe7a7fe9deef2619224f42cb1bd531dd23380ad066c61ee20b",
            ),
        )
        .unwrap();

        assert_eq!(
            p.clone() + p,
            AffinePoint::new(
                Felt::from_hex_unchecked(
                    "0x23a1c9a32dd397fb1e7f758b9089757c1223057aea1d8b52cbec583ad74eaab",
                ),
                Felt::from_hex_unchecked(
                    "0x466880caf4086bac129ae52ee98ddf75b2b394ae7c7ed1a19d9c61aa1f69f62",
                ),
            )
            .unwrap()
        );
    }

    #[test]
    fn affine_mul() {
        let p = AffinePoint::new(
            Felt::from_hex_unchecked("0x2d39148a92f479fb077389d"),
            Felt::from_hex_unchecked(
                "0x6e5d97edf7283fe7a7fe9deef2619224f42cb1bd531dd23380ad066c61ee20b",
            ),
        )
        .unwrap();

        assert_eq!(
            &p * Felt::from(2),
            AffinePoint::new(
                Felt::from_hex_unchecked(
                    "0x23a1c9a32dd397fb1e7f758b9089757c1223057aea1d8b52cbec583ad74eaab",
                ),
                Felt::from_hex_unchecked(
                    "0x466880caf4086bac129ae52ee98ddf75b2b394ae7c7ed1a19d9c61aa1f69f62",
                ),
            )
            .unwrap()
        );
    }
}
