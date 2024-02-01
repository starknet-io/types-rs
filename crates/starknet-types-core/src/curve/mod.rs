mod affine_point;
mod curve_errors;
mod projective_point;

// use core::any::Any;

// use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
// use lambdaworks_math::elliptic_curve::traits::IsEllipticCurve;

// use crate::felt::Felt;
// use crate::felt::NonZeroFelt;

pub use self::affine_point::*;
pub use self::curve_errors::*;
pub use self::projective_point::*;

// pub enum SignatureVerificationError {
//     InvalidPublicKey,
//     InvalidMessage,
//     InvalidR,
//     InvalidS,
// }
// const EC_ORDER: NonZeroFelt = unsafe {
//     NonZeroFelt::from_raw_const([
//         369010039416812937,
//         9,
//         1143265896874747514,
//         8939893405601011193,
//     ])
// };

// #[inline(always)]
// fn mul_by_bits(x: &AffinePoint, y: &Felt) -> AffinePoint {
//     let x = ProjectivePoint::from_affine(x.x(), x.y()).unwrap();
//     let y: Vec<bool> = y.to_bits_le().into_iter().collect();
//     let z = &x * &y;
//     z.to_affine()
// }
// pub fn verify_signature(
//     public_key: &Felt,
//     msg: &Felt,
//     r: &Felt,
//     s: &Felt,
// ) -> Result<bool, SignatureVerificationError> {
//     if msg >= &Felt::ELEMENT_UPPER_BOUND {
//         return Err(SignatureVerificationError::InvalidMessage);
//     }
//     if r == &Felt::ZERO || r >= &Felt::ELEMENT_UPPER_BOUND {
//         return Err(SignatureVerificationError::InvalidR);
//     }
//     if s == &Felt::ZERO || s >= &Felt::ELEMENT_UPPER_BOUND {
//         return Err(SignatureVerificationError::InvalidS);
//     }

//     let full_public_key = match AffinePoint::from_x(*public_key) {
//         Some(value) => value,
//         None => return Err(SignatureVerificationError::InvalidPublicKey),
//     };

//     let w = s
//         .mod_inverse(&EC_ORDER)
//         .ok_or(SignatureVerificationError::InvalidS)?;
//     if w == Felt::ZERO || w >= Felt::ELEMENT_UPPER_BOUND {
//         return Err(SignatureVerificationError::InvalidS);
//     }

//     let zw = msg.mul_mod(&w, &EC_ORDER);
//     let zw_g = StarkCurve::generator().mul_by_bits(&zw);

//     let rw = r.mul_mod_floor(&w, &EC_ORDER);
//     let rw_q = full_public_key.mul_by_bits(&rw);

//     Ok((&zw_g + &rw_q).x == *r || (&zw_g - &rw_q).x == *r)
// }
