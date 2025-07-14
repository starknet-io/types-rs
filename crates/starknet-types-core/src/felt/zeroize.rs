use crate::felt::Felt;

impl zeroize::DefaultIsZeroes for Felt {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zeroing_felt() {
        use zeroize::Zeroize;

        let mut felt = Felt::from_hex_unchecked("0x01");
        felt.zeroize();
        assert_eq!(felt, Felt::ZERO);
    }
}
