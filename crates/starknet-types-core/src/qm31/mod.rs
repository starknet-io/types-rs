use std::fmt;

use lambdaworks_math::field::{
    element::FieldElement,
    fields::mersenne31::{extensions::Degree4ExtensionField, field::MERSENNE_31_PRIME_FIELD_ORDER},
};

use crate::felt::Felt;

/// A value in the Degree-4 (quadruple) extension of the Mersenne 31 field.
///
/// Each QM31 value is represented by two values in the Degree-2 (complex)
/// extension, and each of these is represented by two values in the base
/// field. Thus, a QM31 is represented by four M31 coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QM31(pub FieldElement<Degree4ExtensionField>);

#[derive(Debug, Clone, Copy)]
pub struct InvalidQM31Packing(pub Felt);

#[cfg(feature = "std")]
impl std::error::Error for InvalidQM31Packing {}

impl fmt::Display for InvalidQM31Packing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "felt is not a packed QM31: {}", self.0)
    }
}

impl QM31 {
    /// Packs the [QM31] into a [Felt].
    ///
    /// Stores the four M31 coordinates in the first 144 bits of a Felt. Each
    /// coordinate takes 36 bits, and the resulting felt is equal to:
    /// `C1 + C2 << 36 + C3 << 72 + C4 << 108`
    ///
    /// Why the stride between coordinates is 36 instead of 31? In Stwo, Felt
    /// elements are stored in memory as 28 M31s, each representing 9 bits
    /// (that representation is efficient for multiplication). 36 is the first
    /// multiple of 9 that is greater than 31.
    pub fn pack_into_felt(&self) -> Felt {
        // Take CM31 coordinates from QM31.
        let [a, b] = self.0.value();

        // Take M31 Coordinates from both CM31.
        let [c1, c2] = a.value();
        let [c3, c4] = b.value();

        // Pack as: c1 + c2 << 36 + c3 << 36*2 + c4 << 36*3.
        let lo = c1.to_raw() as u128 + ((c2.to_raw() as u128) << 36);
        let hi = c3.to_raw() as u128 + ((c4.to_raw() as u128) << 36);
        let mut felt_bytes = [0u8; 32];
        felt_bytes[0..9].copy_from_slice(&lo.to_le_bytes()[0..9]);
        felt_bytes[9..18].copy_from_slice(&hi.to_le_bytes()[0..9]);
        Felt::from_bytes_le(&felt_bytes)
    }

    /// Unpacks a [QM31] from the [Felt]
    ///
    /// See the method [QM31::pack_into_felt] for a detailed explanation on the
    /// packing format.
    pub fn unpack_from_felt(felt: &Felt) -> Result<QM31, InvalidQM31Packing> {
        const MASK_36: u64 = (1 << 36) - 1;
        const MASK_8: u64 = (1 << 8) - 1;

        let digits = felt.to_le_digits();

        // The QM31 is packed in the first 144 bits,
        // the remaining bits must be zero.
        if digits[3] != 0 || digits[2] >= 1 << 16 {
            return Err(InvalidQM31Packing(*felt));
        }

        // Unpack as: c1 + c2 << 36 + c3 << 36*2 + c4 << 36*3.
        let c1 = digits[0] & MASK_36;
        let c2 = (digits[0] >> 36) + ((digits[1] & MASK_8) << 28);
        let c3 = (digits[1] >> 8) & MASK_36;
        let c4 = (digits[1] >> 44) + (digits[2] << 20);

        // Even though we use 36 bits for each coordinate,
        // the maximum value is still the field prime.
        for c in [c1, c2, c3, c4] {
            if c >= MERSENNE_31_PRIME_FIELD_ORDER as u64 {
                return Err(InvalidQM31Packing(*felt));
            }
        }

        Ok(QM31(Degree4ExtensionField::const_from_coefficients(
            c1 as u32, c2 as u32, c3 as u32, c4 as u32,
        )))
    }
}

#[cfg(test)]
mod test {
    use lambdaworks_math::field::fields::mersenne31::{
        extensions::Degree4ExtensionField, field::MERSENNE_31_PRIME_FIELD_ORDER,
    };
    use num_bigint::BigInt;

    use crate::{felt::Felt, qm31::QM31};

    #[test]
    fn qm31_packing_and_unpacking() {
        const MAX: u32 = MERSENNE_31_PRIME_FIELD_ORDER - 1;

        let cases = [
            [1, 2, 3, 4],
            [MAX, 0, 0, 0],
            [MAX, MAX, 0, 0],
            [MAX, MAX, MAX, 0],
            [MAX, MAX, MAX, MAX],
        ];

        for [c1, c2, c3, c4] in cases {
            let qm31 = QM31(Degree4ExtensionField::const_from_coefficients(
                c1, c2, c3, c4,
            ));
            let packed_qm31 = qm31.pack_into_felt();
            let unpacked_qm31 = QM31::unpack_from_felt(&packed_qm31).unwrap();

            assert_eq!(qm31, unpacked_qm31)
        }
    }

    #[test]
    fn qm31_packing() {
        const MAX: u32 = MERSENNE_31_PRIME_FIELD_ORDER - 2;

        let cases = [
            [1, 2, 3, 4],
            [MAX, 0, 0, 0],
            [MAX, MAX, 0, 0],
            [MAX, MAX, MAX, 0],
            [MAX, MAX, MAX, MAX],
        ];

        for [c1, c2, c3, c4] in cases {
            let qm31 = QM31(Degree4ExtensionField::const_from_coefficients(
                c1, c2, c3, c4,
            ));
            let packed_qm31 = qm31.pack_into_felt();

            let expected_packing = BigInt::from(c1)
                + (BigInt::from(c2) << 36)
                + (BigInt::from(c3) << 72)
                + (BigInt::from(c4) << 108);

            assert_eq!(packed_qm31, Felt::from(expected_packing))
        }
    }

    #[test]
    fn qm31_invalid_packing() {
        const MAX: u64 = MERSENNE_31_PRIME_FIELD_ORDER as u64 - 1;

        let cases = [
            [MAX + 1, 0, 0, 0],
            [0, MAX + 1, 0, 0],
            [0, 0, MAX + 1, 0],
            [0, 0, 0, MAX + 1],
        ];

        for [c1, c2, c3, c4] in cases {
            let invalid_packing = Felt::from(
                BigInt::from(c1)
                    + (BigInt::from(c2) << 36)
                    + (BigInt::from(c3) << 72)
                    + (BigInt::from(c4) << 108),
            );

            QM31::unpack_from_felt(&invalid_packing).unwrap_err();
        }
    }

    #[test]
    fn qm31_packing_with_high_bits() {
        let invalid_packing = Felt::from(BigInt::from(1) << 200);

        QM31::unpack_from_felt(&invalid_packing).unwrap_err();
    }
}
