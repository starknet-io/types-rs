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

    /// Returns the `x` coordinate of the point.
    pub fn x(&self) -> Felt {
        Felt(*self.0.x())
    }

    /// Returns the `y` coordinate of the point.
    pub fn y(&self) -> Felt {
        Felt(*self.0.y())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn affine_point_identity() {
        let identity = AffinePoint::identity();

        assert_eq!(identity.x(), Felt::from(0));
        assert_eq!(identity.y(), Felt::from(1));
    }
}
