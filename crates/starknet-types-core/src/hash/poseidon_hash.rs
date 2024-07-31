use crate::felt::Felt;

use super::Poseidon;

#[derive(Debug, Default)]

pub struct PoseidonHasher {
    state: [Felt; 3],
    buffer: Option<Felt>,
}

impl PoseidonHasher {
    /// Creates a new [`PoseidonHasher`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Absorbs message into the hash.
    pub fn update(&mut self, msg: Felt) {
        match self.buffer.take() {
            Some(previous_message) => {
                self.state[0] += previous_message;
                self.state[1] += msg;
                Poseidon::hades_permutation(&mut self.state);
            }
            None => {
                self.buffer = Some(msg);
            }
        }
    }

    /// Finishes and returns hash.
    pub fn finalize(mut self) -> Felt {
        // Applies padding
        match self.buffer.take() {
            Some(last_message) => {
                self.state[0] += last_message;
                self.state[1] += Felt::ONE;
            }
            None => {
                self.state[0] += Felt::ONE;
            }
        }
        Poseidon::hades_permutation(&mut self.state);

        self.state[0]
    }
}

/// Computes the Starknet Poseidon hash of x and y.
pub fn poseidon_hash(x: Felt, y: Felt) -> Felt {
    let mut state = [x, y, Felt::TWO];
    Poseidon::hades_permutation(&mut state);

    state[0]
}

/// Computes the Starknet Poseidon hash of a single [`Felt`].
pub fn poseidon_hash_single(x: Felt) -> Felt {
    let mut state = [x, Felt::ZERO, Felt::ONE];
    Poseidon::hades_permutation(&mut state);

    state[0]
}

/// Computes the Starknet Poseidon hash of an arbitrary number of [`Felt`]s.
///
/// Using this function is the same as using [`PoseidonHasher`].
pub fn poseidon_hash_many<'a, I: IntoIterator<Item = &'a Felt>>(msgs: I) -> Felt {
    let mut state = [Felt::ZERO, Felt::ZERO, Felt::ZERO];
    let mut iter = msgs.into_iter();

    loop {
        match iter.next() {
            Some(v) => state[0] += *v,
            None => {
                state[0] += Felt::ONE;
                break;
            }
        }

        match iter.next() {
            Some(v) => state[1] += *v,
            None => {
                state[1] += Felt::ONE;
                break;
            }
        }

        Poseidon::hades_permutation(&mut state);
    }
    Poseidon::hades_permutation(&mut state);

    state[0]
}
