use core::fmt;

use crate::felt::Felt;

pub const STWO_PRIME: u64 = (1 << 31) - 1;
const STWO_PRIME_U128: u128 = STWO_PRIME as u128;

#[derive(Debug)]
pub enum QM31Error {
    FeltTooBig(Felt),
    InvalidInversion,
}

#[cfg(feature = "std")]
impl std::error::Error for QM31Error {}

impl fmt::Display for QM31Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QM31Error::FeltTooBig(felt) => writeln!(
                f,
                "Number used as QM31 since it's more than 144 bits long: {felt}"
            ),
            QM31Error::InvalidInversion => writeln!(f, "Attempt to invert a qm31 equal to zero"),
        }
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QM31Felt([u64; 4]);

impl QM31Felt {
    /// [QM31Felt] constant that's equal to 0.
    pub const ZERO: Self = Self([0, 0, 0, 0]);

    pub fn as_raw(&self) -> [u64; 4] {
        self.0
    }

    /// Create a [QM31Felt] from the raw internal representation. Reduces four u64 coordinates so that the fit in 144 bits.
    pub fn from_raw(coordinates: [u64; 4]) -> QM31Felt {
        Self([
            coordinates[0] % STWO_PRIME,
            coordinates[1] % STWO_PRIME,
            coordinates[2] % STWO_PRIME,
            coordinates[3] % STWO_PRIME,
        ])
    }

    /// Packs the [QM31Felt] coordinates into a Felt.
    pub fn pack_into_felt(&self) -> Felt {
        let coordinates = self.0;

        let bytes_part1 = (coordinates[0] as u128 + ((coordinates[1] as u128) << 36)).to_le_bytes();
        let bytes_part2 = (coordinates[2] as u128 + ((coordinates[3] as u128) << 36)).to_le_bytes();
        let mut result_bytes = [0u8; 32];
        result_bytes[0..9].copy_from_slice(&bytes_part1[0..9]);
        result_bytes[9..18].copy_from_slice(&bytes_part2[0..9]);

        Felt::from_bytes_le(&result_bytes)
    }

    /// Computes the addition of two [QM31Felt] elements in reduced form.
    pub fn add(&self, rhs: &QM31Felt) -> QM31Felt {
        let coordinates1 = self.as_raw();
        let coordinates2 = rhs.as_raw();
        let result_unreduced_coordinates = [
            coordinates1[0] + coordinates2[0],
            coordinates1[1] + coordinates2[1],
            coordinates1[2] + coordinates2[2],
            coordinates1[3] + coordinates2[3],
        ];
        Self::from_raw(result_unreduced_coordinates)
    }

    /// Computes the negative of a [QM31Felt] element in reduced form.
    pub fn neg(&self) -> QM31Felt {
        let coordinates = self.as_raw();
        Self::from_raw([
            STWO_PRIME - coordinates[0],
            STWO_PRIME - coordinates[1],
            STWO_PRIME - coordinates[2],
            STWO_PRIME - coordinates[3],
        ])
    }

    /// Computes the subtraction of two [QM31Felt] elements in reduced form.
    pub fn sub(&self, rhs: &QM31Felt) -> QM31Felt {
        let coordinates1 = self.as_raw();
        let coordinates2 = rhs.as_raw();
        let result_unreduced_coordinates = [
            STWO_PRIME + coordinates1[0] - coordinates2[0],
            STWO_PRIME + coordinates1[1] - coordinates2[1],
            STWO_PRIME + coordinates1[2] - coordinates2[2],
            STWO_PRIME + coordinates1[3] - coordinates2[3],
        ];
        Self::from_raw(result_unreduced_coordinates)
    }

    /// Computes the multiplication of two [QM31Felt] elements in reduced form.
    pub fn mul(&self, rhs: &QM31Felt) -> QM31Felt {
        let coordinates1_u64 = self.as_raw();
        let coordinates2_u64 = rhs.as_raw();
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
        Self::from_raw(result_coordinates)
    }

    /// Computes the inverse in the M31 field using Fermat's little theorem, i.e., returns
    /// `v^(STWO_PRIME-2) modulo STWO_PRIME`, which is the inverse of v unless v % STWO_PRIME == 0.
    fn m31_inverse(v: u64) -> u64 {
        let t0 = (Self::sqn(v, 2) * v) % STWO_PRIME;
        let t1 = (Self::sqn(t0, 1) * t0) % STWO_PRIME;
        let t2 = (Self::sqn(t1, 3) * t0) % STWO_PRIME;
        let t3 = (Self::sqn(t2, 1) * t0) % STWO_PRIME;
        let t4 = (Self::sqn(t3, 8) * t3) % STWO_PRIME;
        let t5 = (Self::sqn(t4, 8) * t3) % STWO_PRIME;
        (Self::sqn(t5, 7) * t2) % STWO_PRIME
    }

    /// Computes `v^(2^n) modulo STWO_PRIME`.
    fn sqn(v: u64, n: usize) -> u64 {
        let mut u = v;
        for _ in 0..n {
            u = (u * u) % STWO_PRIME;
        }
        u
    }

    /// Computes the inverse of a [QM31Felt] element in reduced form.
    /// Returns an error if the operand is equal to zero.
    pub fn inverse(&self) -> Result<QM31Felt, QM31Error> {
        if *self == Self::ZERO {
            return Err(QM31Error::InvalidInversion);
        }

        let coordinates = self.as_raw();

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
        let denom_norm_inverse_squared = Self::m31_inverse(denom_norm_squared);

        let denom_inverse_r = (denom_r * denom_norm_inverse_squared) % STWO_PRIME;
        let denom_inverse_i = ((STWO_PRIME - denom_i) * denom_norm_inverse_squared) % STWO_PRIME;

        Ok(Self::from_raw([
            coordinates[0] * denom_inverse_r + STWO_PRIME * STWO_PRIME
                - coordinates[1] * denom_inverse_i,
            coordinates[0] * denom_inverse_i + coordinates[1] * denom_inverse_r,
            coordinates[3] * denom_inverse_i + STWO_PRIME * STWO_PRIME
                - coordinates[2] * denom_inverse_r,
            2 * STWO_PRIME * STWO_PRIME
                - coordinates[2] * denom_inverse_i
                - coordinates[3] * denom_inverse_r,
        ]))
    }

    /// Computes the division of two [QM31Felt] elements in reduced form. Returns an error
    /// if the rhs value is equal to zero.
    pub fn div(&self, rhs: &QM31Felt) -> Result<QM31Felt, QM31Error> {
        let rhs_inv = rhs.inverse()?;
        Ok(self.mul(&rhs_inv))
    }

    pub fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }
}

impl From<&QM31Felt> for Felt {
    fn from(value: &QM31Felt) -> Self {
        value.pack_into_felt()
    }
}

impl From<QM31Felt> for Felt {
    fn from(value: QM31Felt) -> Self {
        value.pack_into_felt()
    }
}

impl TryFrom<Felt> for QM31Felt {
    type Error = QM31Error;

    fn try_from(value: Felt) -> Result<Self, Self::Error> {
        let limbs = value.to_le_digits();

        // Check value fits in 144 bits. This check is only done here
        // because we are trying to convert a Felt into a QM31Felt. This
        // Felt should represent a packed QM31 which is at most 144 bits long.
        if limbs[3] != 0 || limbs[2] >= 1 << 16 {
            return Err(QM31Error::FeltTooBig(value));
        }

        Ok(Self::from_raw(limbs))
    }
}

impl TryFrom<&Felt> for QM31Felt {
    type Error = QM31Error;

    fn try_from(value: &Felt) -> Result<Self, Self::Error> {
        let limbs = value.to_le_digits();

        // Check value fits in 144 bits. This check is only done here
        // because we are trying to convert a Felt into a QM31Felt. This
        // Felt should represent a packed QM31 which is at most 144 bits long.
        if limbs[3] != 0 || limbs[2] >= 1 << 16 {
            return Err(QM31Error::FeltTooBig(*value));
        }

        Ok(Self::from_raw(limbs))
    }
}

#[cfg(test)]
mod test {
    use core::{u128, u16, u8};

    use proptest::{
        array::uniform4,
        prelude::{BoxedStrategy, Just, Strategy},
        prop_oneof, proptest,
    };

    use crate::felt::{
        qm31::{QM31Error, QM31Felt, STWO_PRIME},
        Felt,
    };

    #[test]
    fn qm31_to_felt_packed() {
        let u64_max_reduced = u64::MAX % STWO_PRIME;

        let value = u8::MAX;
        let felt = Felt::from(value);
        let qm31: QM31Felt = felt.try_into().unwrap();
        let qm31_to_felt = qm31.pack_into_felt();

        assert_eq!(qm31_to_felt, Felt::from(value));

        let value = u16::MAX;
        let felt = Felt::from(value);
        let qm31: QM31Felt = felt.try_into().unwrap();
        let qm31_to_felt = qm31.pack_into_felt();

        assert_eq!(qm31_to_felt, Felt::from(value));

        let value = u32::MAX;
        let felt = Felt::from(value);
        let qm31: QM31Felt = felt.try_into().unwrap();
        let qm31_to_felt = qm31.pack_into_felt();

        assert_eq!(qm31_to_felt, Felt::from(value as u64 % STWO_PRIME));

        let felt = Felt::from(u64::MAX);
        let qm31: QM31Felt = felt.try_into().unwrap();
        let qm31_to_felt = qm31.pack_into_felt();
        dbg!(felt.to_le_digits());

        assert_eq!(qm31_to_felt, Felt::from(u64_max_reduced));

        let felt = Felt::from(u128::MAX);
        let qm31: QM31Felt = felt.try_into().unwrap();
        let qm31_to_felt = qm31.pack_into_felt();

        let mut bytes = [0u8; 32];
        let bytes_part1 =
            ((u64_max_reduced) as u128 + (((u64_max_reduced) as u128) << 36)).to_le_bytes();
        bytes[0..9].copy_from_slice(&bytes_part1[0..9]);

        assert_eq!(qm31_to_felt, Felt::from_bytes_le(&bytes));
    }

    #[test]
    fn qm31_coordinates_over_144_bits() {
        let mut felt_bytes = [0u8; 32];
        felt_bytes[18] = 1;
        let felt = Felt::from_bytes_le(&felt_bytes);
        let qm31: Result<QM31Felt, QM31Error> = felt.try_into();
        assert!(matches!(
            qm31,
            Err(QM31Error::FeltTooBig(bx)) if bx == felt
        ));
    }

    #[test]
    fn test_qm31_packed_reduced_add() {
        let x_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let y_coordinates = [1234567890, 1414213562, 1732050807, 1618033988];
        let x = QM31Felt::from_raw(x_coordinates);
        let y = QM31Felt::from_raw(y_coordinates);
        let res = x.add(&y);
        let res_coordinates = res.as_raw();
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
    fn test_qm31_packed_reduced_neg() {
        let x_coordinates = [1749652895, 834624081, 1930174752, 2063872165];
        let x = QM31Felt::from_raw(x_coordinates);
        let res = x.neg();
        let res_coordinates = res.as_raw();
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
    fn test_qm31_packed_reduced_sub() {
        let x_coordinates = [
            (1414213562 + 1234567890) % STWO_PRIME,
            (1732050807 + 1414213562) % STWO_PRIME,
            (1618033988 + 1732050807) % STWO_PRIME,
            (1234567890 + 1618033988) % STWO_PRIME,
        ];
        let y_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let x = QM31Felt::from_raw(x_coordinates);
        let y = QM31Felt::from_raw(y_coordinates);
        let res = x.sub(&y);
        let res_coordinates = res.as_raw();
        assert_eq!(
            res_coordinates,
            [1234567890, 1414213562, 1732050807, 1618033988]
        );
    }

    #[test]
    fn test_qm31_packed_reduced_mul() {
        let x_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let y_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let x = QM31Felt::from_raw(x_coordinates);
        let y = QM31Felt::from_raw(y_coordinates);
        let res = x.mul(&y);
        let res_coordinates = res.as_raw();
        assert_eq!(
            res_coordinates,
            [947980980, 1510986506, 623360030, 1260310989]
        );
    }

    #[test]
    fn test_qm31_packed_reduced_inv() {
        let x_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let x = QM31Felt::from_raw(x_coordinates);
        let res = x.inverse().unwrap();
        let expected = Felt::from(1).try_into().unwrap();
        assert_eq!(x.mul(&res), expected);

        let x_coordinates = [1, 2, 3, 4];
        let x = QM31Felt::from_raw(x_coordinates);
        let res = x.inverse().unwrap();
        let expected = Felt::from(1).try_into().unwrap();
        assert_eq!(x.mul(&res), expected);

        let x_coordinates = [1749652895, 834624081, 1930174752, 2063872165];
        let x = QM31Felt::from_raw(x_coordinates);
        let res = x.inverse().unwrap();
        let expected = Felt::from(1).try_into().unwrap();
        assert_eq!(x.mul(&res), expected);
    }

    /// Necessary strat to use proptest on the QM31 test
    fn configuration_strat() -> BoxedStrategy<u64> {
        prop_oneof![Just(0), Just(1), Just(STWO_PRIME - 1), 0..STWO_PRIME].boxed()
    }

    proptest! {
        #[test]
        fn qm31_packed_reduced_inv_random(x_coordinates in uniform4(0u64..STWO_PRIME)
                                                            .prop_filter("All configs cant be 0",
                                                            |arr| !arr.iter().all(|x| *x == 0))
        ) {
            let x = QM31Felt::from_raw(x_coordinates);
            let res = x.inverse().unwrap();
            // Expect 1_felt252
            let expected = QM31Felt::from_raw([1,0,0,0]);
            assert_eq!(x.mul(&res), expected);
        }

        #[test]
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
        fn qm31_packed_reduced_inv_extensive(x_coordinates in uniform4(configuration_strat())
                                                            .prop_filter("All configs cant be 0",
                                                            |arr| !arr.iter().all(|x| *x == 0))
                                                            .no_shrink()
        ) {
            let x = QM31Felt::from_raw(x_coordinates);
            let res = x.inverse().unwrap();
            // Expect 1_felt252
            let expected = QM31Felt::from_raw([1,0,0,0]);
            assert_eq!(x.mul(&res), expected);
        }
    }

    #[test]
    fn test_qm31_packed_reduced_div() {
        let x_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let y_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let xy_coordinates = [947980980, 1510986506, 623360030, 1260310989];
        let x = QM31Felt::from_raw(x_coordinates);
        let y = QM31Felt::from_raw(y_coordinates);
        let xy = QM31Felt::from_raw(xy_coordinates);

        let res = xy.div(&y).unwrap();
        assert_eq!(res, x);

        let res = xy.div(&x).unwrap();
        assert_eq!(res, y);
    }
}
