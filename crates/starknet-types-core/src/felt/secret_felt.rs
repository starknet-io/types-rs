use crate::felt::{Felt, FromStrError};
use lambdaworks_math::errors::ByteConversionError;
use zeroize::Zeroize;

/// A wrapper for a [Felt] that ensures the value is securely zeroized when dropped.
///
/// This type provides secure handling of sensitive [Felt] values (like private keys)
/// by ensuring that the memory is properly cleared when the value is no longer needed.
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
    /// # Example
    ///
    /// ```
    /// use starknet_types_core::felt::{Felt, secret_felt::SecretFelt};
    ///
    /// let mut private_key = Felt::from_hex_unchecked("0x123...");
    /// let secret_felt = SecretFelt::from_felt(&mut private_key);
    /// // private_key is now zeroized (set to Felt::ZERO)
    /// ```
    pub fn from_felt(secret_scalar: &mut Felt) -> Self {
        let boxed_copy = Box::new(*secret_scalar);
        secret_scalar.zeroize();
        Self(boxed_copy)
    }

    /// Creates a new [SecretFelt] from a hex String and zeroized the original String.
    ///
    /// # Example
    /// ```
    /// use starknet_types_core::felt::secret_felt::SecretFelt;
    /// use std::str::FromStr;
    ///
    /// // make sure the String is initialized in a secure way
    /// let mut private_key = String::from_utf8(vec![255,255,..]).unwrap();
    /// let secret_felt = SecretFelt::from_hex_string(&mut private_key);
    /// ```
    pub fn from_hex_string(hex: &mut String) -> Result<Self, FromStrError> {
        let secret_felt = Felt::from_hex(&hex)?;
        hex.zeroize();
        Ok(Self(Box::new(secret_felt)))
    }

    /// Creates a new [SecretFelt] from its big-endian representation in a Vec<u8> of length 32.
    /// Internally it uses [from_bytes_be](Felt::from_bytes_be).
    pub fn from_bytes_be(secret: &mut Vec<u8>) -> Result<Self, ByteConversionError> {
        let mut value: [u8; 32] = secret
            .as_slice()
            .try_into()
            .map_err(|_| ByteConversionError::InvalidValue)?;
        let secret_felt = Self(Box::new(Felt::from_bytes_be(&value)));
        secret.zeroize();
        value.zeroize();
        Ok(secret_felt)
    }

    /// Creates a new [SecretFelt] from its little-endian representation in a Vec<u8> of length 32.
    /// Internally it uses [from_bytes_le](Felt::from_bytes_le).
    pub fn from_bytes_le(secret: &mut Vec<u8>) -> Result<Self, ByteConversionError> {
        let mut value: [u8; 32] = secret
            .as_slice()
            .try_into()
            .map_err(|_| ByteConversionError::InvalidValue)?;
        let secret_felt = Self(Box::new(Felt::from_bytes_le(&value)));
        secret.zeroize();
        value.zeroize();
        Ok(secret_felt)
    }

    /// Provides reference access to the secret scalar.
    ///
    /// # Warning
    ///
    /// Be careful not to copy the value elsewhere, as that would defeat
    /// the security guarantees of this type.
    pub fn secret_scalar(&self) -> &Felt {
        &self.0
    }
}

#[cfg(test)]
mod test {
    use crate::felt::{secret_felt::SecretFelt, Felt};
    use core::mem::size_of;
    use std::str::FromStr;
    use zeroize::Zeroize;

    #[test]
    fn test_zeroize_secret_felt() {
        let mut private_key = Felt::from_hex_unchecked(
            "0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        );

        let mut signing_key = SecretFelt::from_felt(&mut private_key);
        signing_key.zeroize();

        // Get a pointer to the inner Felt
        let ptr = signing_key.secret_scalar() as *const Felt as *const u8;
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
        let mut private_key = Felt::from_hex_unchecked(
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
            String::from_str(&"0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
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
        // Create a raw pointer to track the memory
        let mut private_key = Felt::from_hex_unchecked(
            "0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        );

        let pk_clone = private_key.clone();

        // pointer to the memory that will be zeroed
        let raw_ptr;

        {
            let signing_key = SecretFelt::from_felt(&mut private_key);

            raw_ptr = signing_key.secret_scalar() as *const Felt as *const u8;

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
        assert_ne!(pk_clone, felt_after_drop);
    }
}
