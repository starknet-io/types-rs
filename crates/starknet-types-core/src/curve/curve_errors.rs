use core::fmt::Debug;
use lambdaworks_math::elliptic_curve::traits::EllipticCurveError;

#[derive(Debug, PartialEq, Eq)]
pub enum CurveError {
    EllipticCurveError(EllipticCurveError),
}

impl From<EllipticCurveError> for CurveError {
    fn from(error: EllipticCurveError) -> CurveError {
        CurveError::EllipticCurveError(error)
    }
}
