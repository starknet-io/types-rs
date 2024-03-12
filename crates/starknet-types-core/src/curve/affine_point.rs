use crate::curve::curve_errors::CurveError;
use crate::felt::Felt;
use lambdaworks_math::cyclic_group::IsGroup;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use lambdaworks_math::elliptic_curve::short_weierstrass::point::ShortWeierstrassProjectivePoint;
use lambdaworks_math::elliptic_curve::traits::FromAffine;

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
}

impl core::ops::Neg for &AffinePoint {
    type Output = AffinePoint;

    fn neg(self) -> AffinePoint {
        AffinePoint(self.0.neg())
    }
}

#[cfg(test)]
mod test {
    use super::*;

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
}
