use crate::felt::{Felt, FromStrError};
use rand::{CryptoRng, RngCore};
use subtle::ConstantTimeEq;
use zeroize::{Zeroize, Zeroizing};

#[cfg(not(feature = "std"))]
use super::alloc::{boxed::Box, string::String, vec::Vec};

/// A wrapper for a [Felt] that ensures the value is securely zeroized when dropped.
///
/// This type provides secure handling of sensitive [Felt] values (like private keys)
/// by ensuring that the memory is properly cleared when the value is no longer needed.
#[derive(Eq)]
pub struct SecretFelt(Box<Felt>);

impl zeroize::DefaultIsZeroes for Felt {}

impl Zeroize for SecretFelt {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl Drop for SecretFelt {
    fn drop(&mut self) {
        self.zeroize();
    }
}

impl SecretFelt {
    /// Creates a new [SecretFelt] from a [Felt] value and zeroize the original.
    ///
    /// It takes a mutable reference to a [Felt] value, creates a copy,
    /// and then zeroize the original value to ensure it doesn't remain in memory.
    ///
    /// # Warning
    ///
    /// Avoid moving the secret [Felt] in memory and avoid intermediate
    /// operations between the [Felt] creation and the [SecretFelt] initialization
    /// in order to not leave any copies of the value in memory
    ///
    /// # Example
    ///
    /// ```
    /// use starknet_types_core::felt::{Felt, secret_felt::SecretFelt};
    ///
    /// let mut private_key = Felt::from_hex_unwrap("0x2d39148a92f479fb077389d");
    /// let secret_felt = SecretFelt::from_felt(&mut private_key);
    /// // private_key is now zeroized (set to Felt::ZERO)
    /// ```
    pub fn from_felt(secret_felt: &mut Felt) -> Self {
        let boxed_copy = Box::new(*secret_felt);
        secret_felt.zeroize();
        Self(boxed_copy)
    }

    /// Creates a new [SecretFelt] from a hex String and zeroized the original String.
    ///
    ///
    /// # Warning
    /// Make sure the String is initialized in a secure way.
    /// e.g. read from a file.
    ///
    /// # Example
    /// ```
    /// use std::fs;
    /// use starknet_types_core::felt::secret_felt::SecretFelt;
    /// use std::str::FromStr;
    ///
    /// let mut private_key = String::from_str("0x2d39148a92f479fb077389d").unwrap();
    /// let secret_felt = SecretFelt::from_hex_string(&mut private_key).unwrap();
    /// ```
    pub fn from_hex_string(hex: &mut String) -> Result<Self, FromStrError> {
        let secret_felt = Felt::from_hex(hex)?;
        hex.zeroize();
        Ok(Self(Box::new(secret_felt)))
    }

    /// Creates a new [SecretFelt] from its big-endian representation in a Vec<u8> of length 32.
    /// Internally it uses [from_bytes_be](Felt::from_bytes_be).
    /// The input will be zeroized after calling this function
    pub fn from_bytes_be(secret: &mut [u8; 32]) -> Self {
        let secret_felt = Self(Box::new(Felt::from_bytes_be(secret)));
        secret.zeroize();
        secret_felt
    }

    /// Creates a new [SecretFelt] from its little-endian representation in a Vec<u8> of length 32.
    /// Internally it uses [from_bytes_le](Felt::from_bytes_le).
    /// The input will be zeroized after calling this function
    pub fn from_bytes_le(secret: &mut [u8; 32]) -> Self {
        let secret_felt = Self(Box::new(Felt::from_bytes_le(secret)));
        secret.zeroize();
        secret_felt
    }

    /// Create a new [SecretFelt] from cryptographically secure PRNG
    ///
    /// # Example
    /// ```
    /// use starknet_types_core::felt::secret_felt::SecretFelt;
    /// use rand_chacha::ChaCha20Rng;
    /// use rand::SeedableRng;
    ///
    /// let rng = ChaCha20Rng::from_os_rng();
    /// let secret_key = SecretFelt::from_random(rng);
    /// ```
    pub fn from_random<T>(mut rng: T) -> Self
    where
        T: RngCore + CryptoRng,
    {
        let mut buffer = [0u8; 32];
        rng.fill_bytes(&mut buffer);

        let secret_felt = Self(Box::new(Felt::from_bytes_be(&buffer)));
        buffer.zeroize();

        secret_felt
    }

    /// Returns a safe copy of the inner value.
    ///
    /// # Warning
    ///
    /// Be careful not to copy the value elsewhere, as that would defeat
    /// the security guarantees of this type.
    pub fn inner_value(&self) -> Zeroizing<Felt> {
        Zeroizing::new(*self.0.clone())
    }
}

/// Constant time equality check for [SecretFelt]
impl PartialEq for SecretFelt {
    fn eq(&self, other: &Self) -> bool {
        let mut self_limbs = self.0.0.representative().limbs;
        let mut other_limbs = other.0.0.representative().limbs;

        let is_eq: bool = self_limbs.ct_eq(&other_limbs).into();

        self_limbs.zeroize();
        other_limbs.zeroize();

        is_eq
    }
}

#[cfg(test)]
mod test {
    use crate::felt::{Felt, secret_felt::SecretFelt};
    use core::mem::size_of;
    use rand_chacha::{ChaCha20Rng, rand_core::SeedableRng};
    use std::{ops::Deref, str::FromStr};
    use zeroize::Zeroize;

    #[test]
    fn test_zeroize_secret_felt() {
        let mut signing_key = SecretFelt::from_random(ChaCha20Rng::seed_from_u64(1));
        signing_key.zeroize();

        // Get a pointer to the inner Felt
        let ptr = signing_key.inner_value().deref() as *const Felt as *const u8;
        let after_zeroize = unsafe { std::slice::from_raw_parts(ptr, size_of::<Felt>()) };

        // Check that the memory is zeroed
        assert_eq!(
            Felt::from_bytes_be_slice(after_zeroize),
            Felt::ZERO,
            "Memory was not properly zeroized"
        );
    }

    #[test]
    fn test_zeroize_original() {
        let mut private_key = Felt::from_hex_unwrap(
            "0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        );
        let mut signing_key = SecretFelt::from_felt(&mut private_key);
        signing_key.zeroize();

        // Get a pointer to the original memory
        let ptr = private_key.as_ref() as *const Felt as *const u8;
        let after_zeroize = unsafe { std::slice::from_raw_parts(ptr, size_of::<Felt>()) };

        // Check that original value was zeroized
        assert_eq!(
            Felt::from_bytes_be_slice(after_zeroize),
            Felt::ZERO,
            "Original value was not properly zeroized"
        );
    }

    #[test]
    fn test_zeroize_hex_string() {
        let mut private_key =
            String::from_str("0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
                .unwrap();

        let mut signing_key = SecretFelt::from_hex_string(&mut private_key).unwrap();
        signing_key.zeroize();

        let ptr = private_key.as_ptr() as *const Felt as *const u8;
        let after_zeroize = unsafe { std::slice::from_raw_parts(ptr, size_of::<Felt>()) };

        assert_eq!(
            Felt::from_bytes_be_slice(after_zeroize),
            Felt::ZERO,
            "Original value was not properly zeroized"
        );
    }

    #[test]
    fn test_zeroize_on_drop() {
        let mut private_key = Felt::from_hex_unwrap(
            "0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        );

        // make a copy, the initial Felt will be zeroized
        let pk_copy = private_key;

        let raw_ptr;
        {
            let signing_key = SecretFelt::from_felt(&mut private_key);

            let inner_value = *signing_key.0;
            raw_ptr = &inner_value as *const Felt as *const u8;

            // Verify it's not zero before dropping
            let before_drop = unsafe { std::slice::from_raw_parts(raw_ptr, size_of::<Felt>()) };
            assert!(
                !before_drop.iter().all(|&b| b == 0),
                "Memory should not be zeroed yet"
            );
        } // At this point, signing_key has been dropped and zeroized

        // Check that the memory is zeroed after drop
        let after_drop = unsafe { std::slice::from_raw_parts(raw_ptr, size_of::<Felt>()) };

        let felt_after_drop = Felt::from_bytes_be_slice(after_drop);

        // Memory is not zero because the compiler reuse that memory slot
        // but should not be equal to the initial value
        assert_ne!(pk_copy, felt_after_drop);
    }

    #[test]
    fn test_inner_value() {
        let mut private_key = Felt::from_hex_unwrap(
            "0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        );

        // make a copy, the initial Felt will be zeroized
        let pk_copy = private_key;

        let raw_ptr;
        {
            let signing_key = SecretFelt::from_felt(&mut private_key);

            let inner_felt = signing_key.inner_value();

            assert_eq!(*inner_felt, pk_copy);

            raw_ptr = inner_felt.as_ref() as *const Felt as *const u8;
        } // inner_value should be zeroized when is out of scope

        let after_drop = unsafe { std::slice::from_raw_parts(raw_ptr, size_of::<Felt>()) };
        let felt_after_drop = Felt::from_bytes_be_slice(after_drop);

        // Memory is not zero because the compiler reuse that memory slot
        // but should not be equal to the initial value
        assert_ne!(pk_copy, felt_after_drop);
    }

    #[test]
    fn test_partial_eq() {
        let mut private_key1 = [255u8; 32];
        let mut private_key2 = [255u8; 32];
        let mut private_key3 = [254u8; 32];

        let signing_key1 = SecretFelt::from_bytes_be(&mut private_key1);
        let signing_key2 = SecretFelt::from_bytes_be(&mut private_key2);
        let signing_key3 = SecretFelt::from_bytes_be(&mut private_key3);

        assert!(signing_key1.eq(&signing_key2));
        assert!(signing_key1.ne(&signing_key3));
    }
}
