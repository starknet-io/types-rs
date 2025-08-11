use core::fmt;

use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

use crate::felt::Felt;

pub const STWO_PRIME: u64 = (1 << 31) - 1;
const STWO_PRIME_U128: u128 = STWO_PRIME as u128;
const MASK_36: u64 = (1 << 36) - 1;
const MASK_8: u64 = (1 << 8) - 1;

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QM31Felt(pub(crate) FieldElement<Stark252PrimeField>);

impl QM31Felt {
    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Reads four u64 coordinates from a single Felt.
    /// STWO_PRIME fits in 36 bits, hence each coordinate can be represented by 36 bits and a QM31
    /// element can be stored in the first 144 bits of a Felt.
    /// Returns an error if the input has over 144 bits or any coordinate is unreduced.
    fn read_coordinates(&self) -> Result<[u64; 4], QM31Error> {
        let felt: Felt = self.into();
        let limbs = felt.to_le_digits();
        if limbs[3] != 0 || limbs[2] >= 1 << 16 {
            return Err(QM31Error::QM31UnreducedError(Box::new(felt)));
        }
        let coordinates = [
            (limbs[0] & MASK_36),
            ((limbs[0] >> 36) + ((limbs[1] & MASK_8) << 28)),
            ((limbs[1] >> 8) & MASK_36),
            ((limbs[1] >> 44) + (limbs[2] << 20)),
        ];
        for x in coordinates.iter() {
            if *x >= STWO_PRIME {
                return Err(QM31Error::QM31UnreducedError(Box::new(felt)));
            }
        }
        Ok(coordinates)
    }

    /// Create a [QM31Felt] without checking it. If the coordinates cannot be
    /// represented with 144 bits, this can lead to undefined behaviour and big
    /// security issue.
    /// You should always use the [TryFrom] implementation.
    pub fn from_coordinates_unchecked(coordinates: [u64; 4]) -> QM31Felt {
        let bytes_part1 = ((coordinates[0] % STWO_PRIME) as u128
            + (((coordinates[1] % STWO_PRIME) as u128) << 36))
            .to_le_bytes();
        let bytes_part2 = ((coordinates[2] % STWO_PRIME) as u128
            + (((coordinates[3] % STWO_PRIME) as u128) << 36))
            .to_le_bytes();
        let mut result_bytes = [0u8; 32];
        result_bytes[0..9].copy_from_slice(&bytes_part1[0..9]);
        result_bytes[9..18].copy_from_slice(&bytes_part2[0..9]);

        let value = Felt::from_bytes_le(&result_bytes);

        Self(value.0)
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Reduces four u64 coordinates and packs them into a single Felt.
    /// STWO_PRIME fits in 36 bits, hence each coordinate can be represented by 36 bits and a QM31
    /// element can be stored in the first 144 bits of a Felt.
    pub fn from_coordinates(coordinates: [u64; 4]) -> Result<QM31Felt, QM31Error> {
        for x in coordinates.iter() {
            if *x >= STWO_PRIME {
                return Err(QM31Error::QM31InvalidCoordinates(Box::new(coordinates)));
            }
        }

        Ok(Self::from_coordinates_unchecked(coordinates))
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the addition of two QM31 elements in reduced form.
    /// Returns an error if either operand is not reduced.
    pub fn add(&self, rhs: &QM31Felt) -> Result<QM31Felt, QM31Error> {
        let coordinates1 = self.read_coordinates()?;
        let coordinates2 = rhs.read_coordinates()?;
        let result_unreduced_coordinates = [
            coordinates1[0] + coordinates2[0],
            coordinates1[1] + coordinates2[1],
            coordinates1[2] + coordinates2[2],
            coordinates1[3] + coordinates2[3],
        ];
        Self::from_coordinates(result_unreduced_coordinates)
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the negative of a QM31 element in reduced form.
    /// Returns an error if the input is not reduced.
    pub fn neg(&self) -> Result<QM31Felt, QM31Error> {
        let coordinates = self.read_coordinates()?;
        Self::from_coordinates([
            STWO_PRIME - coordinates[0],
            STWO_PRIME - coordinates[1],
            STWO_PRIME - coordinates[2],
            STWO_PRIME - coordinates[3],
        ])
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the subtraction of two QM31 elements in reduced form.
    /// Returns an error if either operand is not reduced.
    pub fn sub(&self, rhs: &QM31Felt) -> Result<QM31Felt, QM31Error> {
        let coordinates1 = self.read_coordinates()?;
        let coordinates2 = rhs.read_coordinates()?;
        let result_unreduced_coordinates = [
            STWO_PRIME + coordinates1[0] - coordinates2[0],
            STWO_PRIME + coordinates1[1] - coordinates2[1],
            STWO_PRIME + coordinates1[2] - coordinates2[2],
            STWO_PRIME + coordinates1[3] - coordinates2[3],
        ];
        Self::from_coordinates(result_unreduced_coordinates)
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the multiplication of two QM31 elements in reduced form.
    /// Returns an error if either operand is not reduced.
    pub fn mul(&self, rhs: &QM31Felt) -> Result<QM31Felt, QM31Error> {
        let coordinates1_u64 = self.read_coordinates()?;
        let coordinates2_u64 = rhs.read_coordinates()?;
        let coordinates1 = coordinates1_u64.map(u128::from);
        let coordinates2 = coordinates2_u64.map(u128::from);

        let result_coordinates = [
            ((5 * STWO_PRIME_U128 * STWO_PRIME_U128 + coordinates1[0] * coordinates2[0]
                - coordinates1[1] * coordinates2[1]
                + 2 * coordinates1[2] * coordinates2[2]
                - 2 * coordinates1[3] * coordinates2[3]
                - coordinates1[2] * coordinates2[3]
                - coordinates1[3] * coordinates2[2])
                % STWO_PRIME_U128) as u64,
            ((STWO_PRIME_U128 * STWO_PRIME_U128
                + coordinates1[0] * coordinates2[1]
                + coordinates1[1] * coordinates2[0]
                + 2 * (coordinates1[2] * coordinates2[3] + coordinates1[3] * coordinates2[2])
                + coordinates1[2] * coordinates2[2]
                - coordinates1[3] * coordinates2[3])
                % STWO_PRIME_U128) as u64,
            2 * STWO_PRIME * STWO_PRIME + coordinates1_u64[0] * coordinates2_u64[2]
                - coordinates1_u64[1] * coordinates2_u64[3]
                + coordinates1_u64[2] * coordinates2_u64[0]
                - coordinates1_u64[3] * coordinates2_u64[1],
            coordinates1_u64[0] * coordinates2_u64[3]
                + coordinates1_u64[1] * coordinates2_u64[2]
                + coordinates1_u64[2] * coordinates2_u64[1]
                + coordinates1_u64[3] * coordinates2_u64[0],
        ];
        Self::from_coordinates(result_coordinates)
    }

    /// M31 utility function, used specifically for Stwo.
    /// M31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the inverse in the M31 field using Fermat's little theorem, i.e., returns
    /// `v^(STWO_PRIME-2) modulo STWO_PRIME`, which is the inverse of v unless v % STWO_PRIME == 0.
    pub fn pow2147483645(v: u64) -> u64 {
        let t0 = (Self::sqn(v, 2) * v) % STWO_PRIME;
        let t1 = (Self::sqn(t0, 1) * t0) % STWO_PRIME;
        let t2 = (Self::sqn(t1, 3) * t0) % STWO_PRIME;
        let t3 = (Self::sqn(t2, 1) * t0) % STWO_PRIME;
        let t4 = (Self::sqn(t3, 8) * t3) % STWO_PRIME;
        let t5 = (Self::sqn(t4, 8) * t3) % STWO_PRIME;
        (Self::sqn(t5, 7) * t2) % STWO_PRIME
    }

    /// M31 utility function, used specifically for Stwo.
    /// M31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes `v^(2^n) modulo STWO_PRIME`.
    fn sqn(v: u64, n: usize) -> u64 {
        let mut u = v;
        for _ in 0..n {
            u = (u * u) % STWO_PRIME;
        }
        u
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the inverse of a QM31 element in reduced form.
    /// Returns an error if the denominator is zero or either operand is not reduced.
    pub fn inverse(&self) -> Result<QM31Felt, QM31Error> {
        let coordinates = self.read_coordinates()?;

        let b2_r = (coordinates[2] * coordinates[2] + STWO_PRIME * STWO_PRIME
            - coordinates[3] * coordinates[3])
            % STWO_PRIME;
        let b2_i = (2 * coordinates[2] * coordinates[3]) % STWO_PRIME;

        let denom_r = (coordinates[0] * coordinates[0] + STWO_PRIME * STWO_PRIME
            - coordinates[1] * coordinates[1]
            + 2 * STWO_PRIME
            - 2 * b2_r
            + b2_i)
            % STWO_PRIME;
        let denom_i =
            (2 * coordinates[0] * coordinates[1] + 3 * STWO_PRIME - 2 * b2_i - b2_r) % STWO_PRIME;

        let denom_norm_squared = (denom_r * denom_r + denom_i * denom_i) % STWO_PRIME;
        let denom_norm_inverse_squared = Self::pow2147483645(denom_norm_squared);

        let denom_inverse_r = (denom_r * denom_norm_inverse_squared) % STWO_PRIME;
        let denom_inverse_i = ((STWO_PRIME - denom_i) * denom_norm_inverse_squared) % STWO_PRIME;

        Self::from_coordinates([
            coordinates[0] * denom_inverse_r + STWO_PRIME * STWO_PRIME
                - coordinates[1] * denom_inverse_i,
            coordinates[0] * denom_inverse_i + coordinates[1] * denom_inverse_r,
            coordinates[3] * denom_inverse_i + STWO_PRIME * STWO_PRIME
                - coordinates[2] * denom_inverse_r,
            2 * STWO_PRIME * STWO_PRIME
                - coordinates[2] * denom_inverse_i
                - coordinates[3] * denom_inverse_r,
        ])
    }

    /// QM31 utility function, used specifically for Stwo.
    /// QM31 operations are to be relocated into https://github.com/lambdaclass/lambdaworks.
    /// Computes the division of two QM31 elements in reduced form.
    /// Returns an error if the input is zero.
    pub fn div(&self, rhs: &QM31Felt) -> Result<QM31Felt, QM31Error> {
        let rhs_inv = rhs.inverse()?;
        self.mul(&rhs_inv)
    }
}

#[derive(Debug)]
pub enum QM31Error {
    QM31UnreducedError(Box<Felt>),
    QM31InvalidCoordinates(Box<[u64; 4]>),
}

#[cfg(feature = "std")]
impl std::error::Error for QM31Error {}

impl fmt::Display for QM31Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QM31Error::QM31UnreducedError(felt) => writeln!(
                f,
                "Number is not a packing of a QM31 in reduced form: {}",
                felt
            ),
            QM31Error::QM31InvalidCoordinates(coords) => writeln!(
                f,
                "Number is not a packing of a QM31 in reduced form: {:#?}",
                coords
            ),
        }
    }
}

impl From<&QM31Felt> for Felt {
    fn from(value: &QM31Felt) -> Self {
        Felt(value.0)
    }
}

impl From<QM31Felt> for Felt {
    fn from(value: QM31Felt) -> Self {
        Felt(value.0)
    }
}

impl TryFrom<Felt> for QM31Felt {
    type Error = QM31Error;
    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        let limbs = value.to_le_digits();
        if limbs[3] != 0 || limbs[2] >= 1 << 16 {
            return Err(QM31Error::QM31UnreducedError(Box::new(value)));
        }
        let coordinates = [
            (limbs[0] & MASK_36),
            ((limbs[0] >> 36) + ((limbs[1] & MASK_8) << 28)),
            ((limbs[1] >> 8) & MASK_36),
            ((limbs[1] >> 44) + (limbs[2] << 20)),
        ];
        Self::from_coordinates(coordinates)
    }
}

impl TryFrom<&Felt> for QM31Felt {
    type Error = QM31Error;
    fn try_from(value: &Felt) -> Result<Self, Self::Error> {
        let limbs = value.to_le_digits();
        if limbs[3] != 0 || limbs[2] >= 1 << 16 {
            return Err(QM31Error::QM31UnreducedError(Box::new(*value)));
        }
        let coordinates = [
            (limbs[0] & MASK_36),
            ((limbs[0] >> 36) + ((limbs[1] & MASK_8) << 28)),
            ((limbs[1] >> 8) & MASK_36),
            ((limbs[1] >> 44) + (limbs[2] << 20)),
        ];
        Self::from_coordinates(coordinates)
    }
}

#[cfg(test)]
mod test {
    use rand::{rngs::SmallRng, Rng, SeedableRng};

    use crate::felt::{
        qm31::{QM31Error, QM31Felt, STWO_PRIME},
        Felt,
    };

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn qm31_packed_reduced_read_coordinates_over_144_bits() {
        let mut felt_bytes = [0u8; 32];
        felt_bytes[18] = 1;
        let felt = Felt::from_bytes_le(&felt_bytes);
        let qm31: QM31Felt = felt.try_into().unwrap();
        assert!(matches!(
            qm31.read_coordinates(),
            Err(QM31Error::QM31UnreducedError(bx)) if *bx == felt
        ));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn qm31_packed_reduced_read_coordinates_unreduced() {
        let mut felt_bytes = [0u8; 32];
        felt_bytes[0] = 0xff;
        felt_bytes[1] = 0xff;
        felt_bytes[2] = 0xff;
        felt_bytes[3] = (1 << 7) - 1;
        let felt = Felt::from_bytes_le(&felt_bytes);
        let qm31: QM31Felt = felt.try_into().unwrap();
        assert!(matches!(
        qm31.read_coordinates(),
        Err(QM31Error::QM31UnreducedError(bx)) if *bx == felt
        ));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_add() {
        let x_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let y_coordinates = [1234567890, 1414213562, 1732050807, 1618033988];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let y = QM31Felt::from_coordinates(y_coordinates).unwrap();
        let res = x.add(&y).unwrap();
        let res_coordinates = res.read_coordinates().unwrap();
        assert_eq!(
            res_coordinates,
            [
                (1414213562 + 1234567890) % STWO_PRIME,
                (1732050807 + 1414213562) % STWO_PRIME,
                (1618033988 + 1732050807) % STWO_PRIME,
                (1234567890 + 1618033988) % STWO_PRIME,
            ]
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_neg() {
        let x_coordinates = [1749652895, 834624081, 1930174752, 2063872165];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let res = x.neg().unwrap();
        let res_coordinates = res.read_coordinates().unwrap();
        assert_eq!(
            res_coordinates,
            [
                STWO_PRIME - x_coordinates[0],
                STWO_PRIME - x_coordinates[1],
                STWO_PRIME - x_coordinates[2],
                STWO_PRIME - x_coordinates[3]
            ]
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_sub() {
        let x_coordinates = [
            (1414213562 + 1234567890) % STWO_PRIME,
            (1732050807 + 1414213562) % STWO_PRIME,
            (1618033988 + 1732050807) % STWO_PRIME,
            (1234567890 + 1618033988) % STWO_PRIME,
        ];
        let y_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let y = QM31Felt::from_coordinates(y_coordinates).unwrap();
        let res = x.sub(&y).unwrap();
        let res_coordinates = res.read_coordinates().unwrap();
        assert_eq!(
            res_coordinates,
            [1234567890, 1414213562, 1732050807, 1618033988]
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_mul() {
        let x_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let y_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let y = QM31Felt::from_coordinates(y_coordinates).unwrap();
        let res = x.mul(&y).unwrap();
        let res_coordinates = res.read_coordinates().unwrap();
        assert_eq!(
            res_coordinates,
            [947980980, 1510986506, 623360030, 1260310989]
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_inv() {
        let x_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let res = x.inverse().unwrap();
        let expected = Felt::from(1).try_into().unwrap();
        assert_eq!(x.mul(&res).unwrap(), expected);

        let x_coordinates = [1, 2, 3, 4];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let res = x.inverse().unwrap();
        let expected = Felt::from(1).try_into().unwrap();
        assert_eq!(x.mul(&res).unwrap(), expected);

        let x_coordinates = [1749652895, 834624081, 1930174752, 2063872165];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let res = x.inverse().unwrap();
        let expected = Felt::from(1).try_into().unwrap();
        assert_eq!(x.mul(&res).unwrap(), expected);
    }

    // TODO: Refactor using proptest and separating particular cases
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_inv_extensive() {
        let mut rng = SmallRng::seed_from_u64(11480028852697973135);
        #[derive(Clone, Copy)]
        enum Configuration {
            Zero,
            One,
            MinusOne,
            Random,
        }
        let configurations = [
            Configuration::Zero,
            Configuration::One,
            Configuration::MinusOne,
            Configuration::Random,
        ];
        let mut cartesian_product = vec![];
        for &a in &configurations {
            for &b in &configurations {
                for &c in &configurations {
                    for &d in &configurations {
                        cartesian_product.push([a, b, c, d]);
                    }
                }
            }
        }

        for test_case in cartesian_product {
            let x_coordinates: [u64; 4] = test_case
                .iter()
                .map(|&x| match x {
                    Configuration::Zero => 0,
                    Configuration::One => 1,
                    Configuration::MinusOne => STWO_PRIME - 1,
                    Configuration::Random => rng.gen_range(0..STWO_PRIME),
                })
                .collect::<Vec<u64>>()
                .try_into()
                .unwrap();
            if x_coordinates == [0, 0, 0, 0] {
                continue;
            }
            let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
            let res = x.inverse().unwrap();
            let expected = Felt::from(1).try_into().unwrap();
            assert_eq!(x.mul(&res).unwrap(), expected);
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_qm31_packed_reduced_div() {
        let x_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let y_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let xy_coordinates = [947980980, 1510986506, 623360030, 1260310989];
        let x = QM31Felt::from_coordinates(x_coordinates).unwrap();
        let y = QM31Felt::from_coordinates(y_coordinates).unwrap();
        let xy = QM31Felt::from_coordinates(xy_coordinates).unwrap();

        let res = xy.div(&y).unwrap();
        assert_eq!(res, x);

        let res = xy.div(&x).unwrap();
        assert_eq!(res, y);
    }
}
