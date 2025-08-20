use core::fmt;

use crate::felt::Felt;

pub const STWO_PRIME: u64 = (1 << 31) - 1;
const STWO_PRIME_U128: u128 = STWO_PRIME as u128;
const MASK_36: u64 = (1 << 36) - 1;
const MASK_8: u64 = (1 << 8) - 1;

#[derive(Debug, Clone, Copy)]
pub enum QM31Error {
    UnreducedFelt(Felt),
    FeltTooBig(Felt),
    InvalidInversion,
}

#[cfg(feature = "std")]
impl std::error::Error for QM31Error {}

impl fmt::Display for QM31Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QM31Error::UnreducedFelt(felt) => write!(
                f,
                "number is not a packing of a QM31 in reduced form: {felt})"
            ),
            QM31Error::FeltTooBig(felt) => write!(
                f,
                "number used as QM31 since it's more than 144 bits long: {felt}"
            ),
            QM31Error::InvalidInversion => write!(f, "attempt to invert a qm31 equal to zero"),
        }
    }
}

/// Definition of a Quadruple Merseene 31.
///
/// The internal representation is composed of 4 limbs, following a big-endian ordering.
/// Each of this limbs can be represented by 36 bits.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QM31([u64; 4]);

impl QM31 {
    /// [QM31] constant that's equal to 0.
    pub const ZERO: Self = Self([0, 0, 0, 0]);

    pub fn inner(&self) -> [u64; 4] {
        self.0
    }

    /// Creates a [QM31] in its reduced form from four u64 coordinates.
    /// 
    /// A coordinate refers to a value in the M31 field.
    pub fn from_coordinates(coordinates: [u64; 4]) -> QM31 {
        Self([
            coordinates[0] % STWO_PRIME,
            coordinates[1] % STWO_PRIME,
            coordinates[2] % STWO_PRIME,
            coordinates[3] % STWO_PRIME,
        ])
    }

    /// Packs the [QM31] coordinates into a Felt.
    ///
    /// A QM31 is composed of 4 coordinates each of which can be represented with 36 bits, meaning
    /// it can be store in a Felt252. This method packs a given QM31 and stores it in the first 144 bits of a Felt252.
    pub fn pack_into_felt(&self) -> Felt {
        let coordinates = self.0;

        let bytes_part1 = (coordinates[0] as u128 + ((coordinates[1] as u128) << 36)).to_le_bytes();
        let bytes_part2 = (coordinates[2] as u128 + ((coordinates[3] as u128) << 36)).to_le_bytes();
        let mut result_bytes = [0u8; 32];
        result_bytes[0..9].copy_from_slice(&bytes_part1[0..9]);
        result_bytes[9..18].copy_from_slice(&bytes_part2[0..9]);

        Felt::from_bytes_le(&result_bytes)
    }

    /// Unpacks the reduced coordinates stored in [Felt] and creates a [QM31].
    pub fn unpack_from_felt(felt: &Felt) -> Result<QM31, QM31Error> {
        let limbs = felt.to_le_digits();

        // Check value fits in 144 bits. This check is only done here
        // because we are trying to convert a Felt into a QM31. This
        // Felt should represent a packed QM31 which is at most 144 bits long.
        if limbs[3] != 0 || limbs[2] >= 1 << 16 {
            return Err(QM31Error::FeltTooBig(*felt));
        }

        // Check if the coordinates were reduced before.
        let coordinates = [
            (limbs[0] & MASK_36),
            ((limbs[0] >> 36) + ((limbs[1] & MASK_8) << 28)),
            ((limbs[1] >> 8) & MASK_36),
            ((limbs[1] >> 44) + (limbs[2] << 20)),
        ];

        for x in coordinates.iter() {
            if *x >= STWO_PRIME {
                return Err(QM31Error::UnreducedFelt(*felt));
            }
        }

        Ok(QM31(coordinates))
    }

    /// Computes the addition of two [QM31] elements in reduced form.
    pub fn add(&self, rhs: &QM31) -> QM31 {
        let coordinates1 = self.inner();
        let coordinates2 = rhs.inner();
        let result_unreduced_coordinates = [
            coordinates1[0] + coordinates2[0],
            coordinates1[1] + coordinates2[1],
            coordinates1[2] + coordinates2[2],
            coordinates1[3] + coordinates2[3],
        ];
        Self::from_coordinates(result_unreduced_coordinates)
    }

    /// Computes the negative of a [QM31] element in reduced form.
    pub fn neg(&self) -> QM31 {
        let coordinates = self.inner();
        Self::from_coordinates([
            STWO_PRIME - coordinates[0],
            STWO_PRIME - coordinates[1],
            STWO_PRIME - coordinates[2],
            STWO_PRIME - coordinates[3],
        ])
    }

    /// Computes the subtraction of two [QM31] elements in reduced form.
    pub fn sub(&self, rhs: &QM31) -> QM31 {
        let coordinates1 = self.inner();
        let coordinates2 = rhs.inner();
        let result_unreduced_coordinates = [
            STWO_PRIME + coordinates1[0] - coordinates2[0],
            STWO_PRIME + coordinates1[1] - coordinates2[1],
            STWO_PRIME + coordinates1[2] - coordinates2[2],
            STWO_PRIME + coordinates1[3] - coordinates2[3],
        ];
        Self::from_coordinates(result_unreduced_coordinates)
    }

    /// Computes the multiplication of two [QM31] elements in reduced form.
    pub fn mul(&self, rhs: &QM31) -> QM31 {
        let coordinates1_u64 = self.inner();
        let coordinates2_u64 = rhs.inner();
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

    /// Computes the inverse in the M31 field using Fermat's little theorem.
    ///
    /// Returns `v^(STWO_PRIME-2) modulo STWO_PRIME`, which is the inverse of v unless v % STWO_PRIME == 0.
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

    /// Computes the inverse of a [QM31] element in reduced form.
    ///
    /// Returns an error if the operand is equal to zero.
    pub fn inverse(&self) -> Result<QM31, QM31Error> {
        if *self == Self::ZERO {
            return Err(QM31Error::InvalidInversion);
        }

        let coordinates = self.inner();

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

        Ok(Self::from_coordinates([
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

    /// Computes the division of two [QM31] elements in reduced form.
    ///  
    /// Returns an error if the rhs value is equal to zero.
    pub fn div(&self, rhs: &QM31) -> Result<QM31, QM31Error> {
        let rhs_inv = rhs.inverse()?;
        Ok(self.mul(&rhs_inv))
    }

    pub fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }
}

#[cfg(test)]
mod test {
    use core::u64;

    use proptest::{
        array::uniform4,
        prelude::{BoxedStrategy, Just, Strategy},
        prop_oneof, proptest,
    };

    use crate::{
        felt::Felt,
        qm31::{QM31Error, QM31, STWO_PRIME},
    };

    #[test]
    fn qm31_to_felt() {
        let coordinates = QM31::from_coordinates([1, 2, 3, 4]);
        let packed_coordinates = coordinates.pack_into_felt();
        let unpacked_coordinates = QM31::unpack_from_felt(&packed_coordinates).unwrap();
        assert_eq!(coordinates, unpacked_coordinates);

        let qm31 = QM31::from_coordinates([u64::MAX, 0, 0, 0]);
        let felt: Felt = qm31.pack_into_felt();
        let felt_to_qm31 = QM31::unpack_from_felt(&felt).unwrap();

        assert_eq!(felt_to_qm31, qm31);

        let qm31 = QM31::from_coordinates([u64::MAX, u64::MAX, 0, 0]);
        let felt: Felt = qm31.pack_into_felt();
        let felt_to_qm31 = QM31::unpack_from_felt(&felt).unwrap();

        assert_eq!(felt_to_qm31, qm31);

        let qm31 = QM31::from_coordinates([u64::MAX, u64::MAX, u64::MAX, 0]);
        let felt: Felt = qm31.pack_into_felt();
        let felt_to_qm31 = QM31::unpack_from_felt(&felt).unwrap();

        assert_eq!(felt_to_qm31, qm31);

        let qm31 = QM31::from_coordinates([u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
        let felt: Felt = qm31.pack_into_felt();
        let felt_to_qm31 = QM31::unpack_from_felt(&felt).unwrap();

        assert_eq!(felt_to_qm31, qm31);
    }

    #[test]
    fn qm31_coordinates_over_144_bits() {
        let mut felt_bytes = [0u8; 32];
        felt_bytes[18] = 1;
        let felt = Felt::from_bytes_le(&felt_bytes);
        let qm31: Result<QM31, QM31Error> = QM31::unpack_from_felt(&felt);
        assert!(matches!(
            qm31,
            Err(QM31Error::FeltTooBig(bx)) if bx == felt
        ));
    }

    #[test]
    fn test_qm31_packed_reduced_add() {
        let x_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let y_coordinates = [1234567890, 1414213562, 1732050807, 1618033988];
        let x = QM31::from_coordinates(x_coordinates);
        let y = QM31::from_coordinates(y_coordinates);
        let res = x.add(&y);
        let res_coordinates = res.inner();
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
        let x = QM31::from_coordinates(x_coordinates);
        let res = x.neg();
        let res_coordinates = res.inner();
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
        let x = QM31::from_coordinates(x_coordinates);
        let y = QM31::from_coordinates(y_coordinates);
        let res = x.sub(&y);
        let res_coordinates = res.inner();
        assert_eq!(
            res_coordinates,
            [1234567890, 1414213562, 1732050807, 1618033988]
        );
    }

    #[test]
    fn test_qm31_packed_reduced_mul() {
        let x_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let y_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let x = QM31::from_coordinates(x_coordinates);
        let y = QM31::from_coordinates(y_coordinates);
        let res = x.mul(&y);
        let res_coordinates = res.inner();
        assert_eq!(
            res_coordinates,
            [947980980, 1510986506, 623360030, 1260310989]
        );
    }

    #[test]
    fn test_qm31_packed_reduced_inv() {
        let x_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let x = QM31::from_coordinates(x_coordinates);
        let res = x.inverse().unwrap();
        let expected = QM31::unpack_from_felt(&Felt::from(1)).unwrap();
        assert_eq!(x.mul(&res), expected);

        let x_coordinates = [1, 2, 3, 4];
        let x = QM31::from_coordinates(x_coordinates);
        let res = x.inverse().unwrap();
        let expected = QM31::unpack_from_felt(&Felt::from(1)).unwrap();
        assert_eq!(x.mul(&res), expected);

        let x_coordinates = [1749652895, 834624081, 1930174752, 2063872165];
        let x = QM31::from_coordinates(x_coordinates);
        let res = x.inverse().unwrap();
        let expected = QM31::unpack_from_felt(&Felt::from(1)).unwrap();
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
            let x = QM31::from_coordinates(x_coordinates);
            let res = x.inverse().unwrap();
            // Expect 1_felt252
            let expected = QM31::from_coordinates([1,0,0,0]);
            assert_eq!(x.mul(&res), expected);
        }

        #[test]
        #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
        fn qm31_packed_reduced_inv_extensive(x_coordinates in uniform4(configuration_strat())
                                                            .prop_filter("All configs cant be 0",
                                                            |arr| !arr.iter().all(|x| *x == 0))
                                                            .no_shrink()
        ) {
            let x = QM31::from_coordinates(x_coordinates);
            let res = x.inverse().unwrap();
            // Expect 1_felt252
            let expected = QM31::from_coordinates([1,0,0,0]);
            assert_eq!(x.mul(&res), expected);
        }
    }

    #[test]
    fn test_qm31_packed_reduced_div() {
        let x_coordinates = [1259921049, 1442249570, 1847759065, 2094551481];
        let y_coordinates = [1414213562, 1732050807, 1618033988, 1234567890];
        let xy_coordinates = [947980980, 1510986506, 623360030, 1260310989];
        let x = QM31::from_coordinates(x_coordinates);
        let y = QM31::from_coordinates(y_coordinates);
        let xy = QM31::from_coordinates(xy_coordinates);

        let res = xy.div(&y).unwrap();
        assert_eq!(res, x);

        let res = xy.div(&x).unwrap();
        assert_eq!(res, y);
    }
}
