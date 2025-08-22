use lambdaworks_math::field::{
    element::FieldElement,
    fields::mersenne31::{extensions::Degree4ExtensionField, field::MERSENNE_31_PRIME_FIELD_ORDER},
};

use crate::felt::Felt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QM31(pub FieldElement<Degree4ExtensionField>);

impl QM31 {
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

    pub fn unpack_from_felt(felt: &Felt) -> QM31 {
        const MASK_36: u64 = (1 << 36) - 1;
        const MASK_8: u64 = (1 << 8) - 1;

        let digits = felt.to_le_digits();

        // As we are packing the QM31 in the first 144 bits, the remaining bits
        // must be zero.
        if digits[3] != 0 || digits[2] >= 1 << 16 {
            panic!("a")
        }

        // Unpack as: c1 + c2 << 36 + c3 << 36*2 + c4 << 36*3.
        let c1 = digits[0] & MASK_36;
        let c2 = (digits[0] >> 36) + ((digits[1] & MASK_8) << 28);
        let c3 = (digits[1] >> 8) & MASK_36;
        let c4 = (digits[1] >> 44) + (digits[2] << 20);

        // Even though we use 36 bits for each coordinate, the maximum value is
        // still the field prime.
        for c in [c1, c2, c3, c4] {
            if c >= MERSENNE_31_PRIME_FIELD_ORDER as u64 {
                panic!("b")
            }
        }

        QM31(Degree4ExtensionField::const_from_coefficients(
            c1 as u32, c2 as u32, c3 as u32, c4 as u32,
        ))
    }
}
