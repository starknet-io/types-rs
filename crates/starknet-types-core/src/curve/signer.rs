use super::{AffinePoint, ProjectivePoint};
use crate::felt::Felt;
use crate::hash::{Pedersen, StarkHash};
use core::fmt::{Display, Formatter, Result as CoreResult};
use core::ops::{Add, Mul};
use crypto_bigint::{ArrayEncoding, ByteArray, Integer as CryptoInteger, U256};
use hmac::digest::Digest;
use lambdaworks_math::elliptic_curve::short_weierstrass::curves::stark_curve::StarkCurve;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};
use sha2::digest::{crypto_common::BlockSizeUser, FixedOutputReset, HashMarker};
use zeroize::{Zeroize, Zeroizing};

const EC_ORDER: Felt = Felt::from_raw([
    369010039416812937,
    9,
    1143265896874747514,
    8939893405601011193,
]);

const EC_ORDER_2: U256 =
    U256::from_be_hex("0800000000000010ffffffffffffffffb781126dcae7b2321e66a241adc64d2f");

const ELEMENT_UPPER_BOUND: Felt = Felt::from_raw([
    576459263475450960,
    18446744073709255680,
    160989183,
    18446743986131435553,
]);

const GENERATOR: AffinePoint = AffinePoint::new_unchecked(
    Felt::from_raw([
        232005955912912577,
        299981207024966779,
        5884444832209845738,
        14484022957141291997,
    ]),
    Felt::from_raw([
        405578048423154473,
        18147424675297964973,
        664812301889158119,
        6241159653446987914,
    ]),
);

pub trait Signer {
    fn ecdsa_sign(
        private_key: &Felt,
        message_hash: &Felt,
    ) -> Result<ExtendedSignature, EcdsaSignError>;
}

impl Signer for StarkCurve {
    fn ecdsa_sign(
        private_key: &Felt,
        message_hash: &Felt,
    ) -> Result<ExtendedSignature, EcdsaSignError> {
        let mut seed = None;
        loop {
            let k = generate_k(private_key, message_hash, seed.as_ref());

            match sign(private_key, message_hash, &k) {
                Ok(sig) => {
                    return Ok(sig);
                }
                Err(SignError::InvalidMessageHash) => {
                    return Err(EcdsaSignError::MessageHashOutOfRange)
                }
                Err(SignError::InvalidK) => {
                    // Bump seed and retry
                    seed = match seed {
                        Some(prev_seed) => Some(prev_seed + Felt::ONE),
                        None => Some(Felt::ONE),
                    };
                }
            };
        }
    }
}

#[derive(Debug)]
pub enum EcdsaSignError {
    MessageHashOutOfRange,
}

#[cfg(feature = "std")]
impl std::error::Error for EcdsaSignError {}

impl Display for EcdsaSignError {
    fn fmt(&self, f: &mut Formatter<'_>) -> CoreResult {
        match self {
            Self::MessageHashOutOfRange => write!(f, "message hash out of range"),
        }
    }
}

/// Stark ECDSA signature
#[derive(Debug)]
pub struct Signature {
    /// The `r` value of a signature
    pub r: Felt,
    /// The `s` value of a signature
    pub s: Felt,
}
/// Stark ECDSA signature with `v`
#[derive(Debug)]
pub struct ExtendedSignature {
    /// The `r` value of a signature
    pub r: Felt,
    /// The `s` value of a signature
    pub s: Felt,
    /// The `v` value of a signature
    pub v: Felt,
}

impl From<ExtendedSignature> for Signature {
    fn from(value: ExtendedSignature) -> Self {
        Self {
            r: value.r,
            s: value.s,
        }
    }
}

#[derive(Debug)]
pub enum SignError {
    InvalidMessageHash,
    InvalidK,
}

pub fn compute_hash_on_elements<'a, ESI, II>(data: II) -> Felt
where
    ESI: ExactSizeIterator<Item = &'a Felt>,
    II: IntoIterator<IntoIter = ESI>,
{
    let mut current_hash = Felt::ZERO;
    let data_iter = data.into_iter();
    let data_len = Felt::from(data_iter.len());

    for elem in data_iter {
        current_hash = Pedersen::hash(&current_hash, elem);
    }

    Pedersen::hash(&current_hash, &data_len)
}

/// Computes the public key given a Stark private key.
///
/// ### Arguments
///
/// * `private_key`: The private key
pub fn get_public_key(private_key: &Felt) -> Felt {
    mul_by_bits(&GENERATOR, private_key)
        .to_affine()
        .unwrap()
        .x()
}

/// Computes ECDSA signature given a Stark private key and message hash.
///
/// ### Arguments
///
/// * `private_key`: The private key
/// * `message`: The message hash
/// * `k`: A random `k` value. You **MUST NOT** use the same `k` on different signatures
pub fn sign(private_key: &Felt, message: &Felt, k: &Felt) -> Result<ExtendedSignature, SignError> {
    if message >= &ELEMENT_UPPER_BOUND {
        return Err(SignError::InvalidMessageHash);
    }
    if k == &Felt::ZERO {
        return Err(SignError::InvalidK);
    }

    let full_r = mul_by_bits(&GENERATOR, k).to_affine().unwrap();
    let r = full_r.x();
    if r == Felt::ZERO || r >= ELEMENT_UPPER_BOUND {
        return Err(SignError::InvalidK);
    }

    let k_inv = mod_inverse(k, &EC_ORDER);

    let s = mul_mod_floor(&r, private_key, &EC_ORDER);
    let s = add_unbounded(&s, message);
    let s = bigint_mul_mod_floor(s, &k_inv, &EC_ORDER);
    if s == Felt::ZERO || s >= ELEMENT_UPPER_BOUND {
        return Err(SignError::InvalidK);
    }

    Ok(ExtendedSignature {
        r,
        s,
        v: (full_r.y().to_bigint() & Felt::ONE.to_bigint()).into(),
    })
}

pub fn add_unbounded(augend: &Felt, addend: &Felt) -> BigInt {
    let augend = BigInt::from_bytes_be(num_bigint::Sign::Plus, &augend.to_bytes_be());
    let addend = BigInt::from_bytes_be(num_bigint::Sign::Plus, &addend.to_bytes_be());
    augend.add(addend)
}

pub fn mul_mod_floor(multiplicand: &Felt, multiplier: &Felt, modulus: &Felt) -> Felt {
    let multiplicand = BigInt::from_bytes_be(num_bigint::Sign::Plus, &multiplicand.to_bytes_be());
    bigint_mul_mod_floor(multiplicand, multiplier, modulus)
}

pub fn bigint_mul_mod_floor(multiplicand: BigInt, multiplier: &Felt, modulus: &Felt) -> Felt {
    let multiplier = BigInt::from_bytes_be(num_bigint::Sign::Plus, &multiplier.to_bytes_be());
    let modulus = BigInt::from_bytes_be(num_bigint::Sign::Plus, &modulus.to_bytes_be());

    let result = multiplicand.mul(multiplier).mod_floor(&modulus);

    let (_, buffer) = result.to_bytes_be();
    let mut result = [0u8; 32];
    result[(32 - buffer.len())..].copy_from_slice(&buffer[..]);

    Felt::from_bytes_be(&result)
}

#[inline(always)]
fn mul_by_bits(x: &AffinePoint, y: &Felt) -> ProjectivePoint {
    &ProjectivePoint::from_affine(x.x(), x.y()).unwrap() * *y
}

pub fn mod_inverse(operand: &Felt, modulus: &Felt) -> Felt {
    let operand = BigInt::from_bytes_be(num_bigint::Sign::Plus, &operand.to_bytes_be());
    let modulus = BigInt::from_bytes_be(num_bigint::Sign::Plus, &modulus.to_bytes_be());

    // Ported from:
    //   https://github.com/dignifiedquire/num-bigint/blob/56576b592fea6341b7e1711a1629e4cc1bfc419c/src/algorithms/mod_inverse.rs#L11
    let extended_gcd = operand.extended_gcd(&modulus);
    if extended_gcd.gcd != BigInt::one() {
        panic!("GCD must be one");
    }
    let result = if extended_gcd.x < BigInt::zero() {
        extended_gcd.x + modulus
    } else {
        extended_gcd.x
    };

    let (_, buffer) = result.to_bytes_be();
    let mut result = [0u8; 32];
    result[(32 - buffer.len())..].copy_from_slice(&buffer[..]);

    Felt::from_bytes_be(&result)
}

/// Deterministically generate ephemeral scalar `k` based on RFC 6979.
fn generate_k(private_key: &Felt, message_hash: &Felt, seed: Option<&Felt>) -> Felt {
    let message_hash = U256::from_be_slice(&message_hash.to_bytes_be()).to_be_byte_array();
    let private_key = U256::from_be_slice(&private_key.to_bytes_be());

    let seed_bytes = match seed {
        Some(seed) => seed.to_bytes_be(),
        None => [0u8; 32],
    };

    let mut first_non_zero_index = 32;
    for (ind, element) in seed_bytes.iter().enumerate() {
        if *element != 0u8 {
            first_non_zero_index = ind;
            break;
        }
    }

    let k = generate_k_shifted::<sha2::Sha256, _>(
        &private_key,
        &EC_ORDER_2,
        &message_hash,
        &seed_bytes[first_non_zero_index..],
    );

    let mut buffer = [0u8; 32];
    buffer[..].copy_from_slice(&k.to_be_byte_array()[..]);

    Felt::from_bytes_be(&buffer)
}

// Modified from upstream `rfc6979::generate_k` with a hard-coded right bit shift. The more
// idiomatic way of doing this seems to be to implement `U252` which handles bit truncation
// interally.
// TODO: change to use upstream `generate_k` directly.
#[inline]
fn generate_k_shifted<D, I>(x: &I, n: &I, h: &ByteArray<I>, data: &[u8]) -> Zeroizing<I>
where
    D: Default + Digest + BlockSizeUser + FixedOutputReset + HashMarker,
    I: ArrayEncoding + CryptoInteger + Zeroize,
{
    let mut x = x.to_be_byte_array();
    let mut hmac_drbg = rfc6979::HmacDrbg::<D>::new(&x, h, data);
    x.zeroize();

    loop {
        let mut bytes = ByteArray::<I>::default();
        hmac_drbg.fill_bytes(&mut bytes);
        let k = I::from_be_byte_array(bytes) >> 4;

        if (!k.is_zero() & k.ct_lt(n)).into() {
            return Zeroizing::new(k);
        }
    }
}
