# starknet-types-core

Core types representation for Starknet.

## Overview

The `starknet-types-core` crate provides:
* The universal `Felt` (Field Element) type for Cairo and STARK proofs. It was created to reduce the fragmentation in the Starknet Rust ecosystem by providing a standardized representation of the `Felt` type.

## Features

### Always on
- Standardized `Felt` type: Simplify your codebase by using our standardized `Felt` type. Optimized for performance: The `Felt` type has been optimized for high-performance applications.
- No_std support ✅

### Serde
- Provides a Serialization and Deserialization implementations for the `Felt` type
- No_std support ✅

### Parity Scale Codec
- Provides Serialization and Deserialization implementations for the `Felt` type within the Parity serialization framework
- No_std support ✅

### Arbitrary
- Provides an Arbitrary implementations for the `Felt` type

### Curve
- Add the `AffinePoint` and `ProjectivePoint` structs, which represent points on the Stark curve for performing elliptic curve operations.
- No_std support ✅

### Hash
- Implements Pedersen hashing for Felts and Felts array

## Examples

Here are some examples of how to use the `starknet-types-core` types:

```rust
    let felt = Felt::from(18);
    let projective_point = ProjectivePoint::new(Felt::from(0), Felt::from(1), Felt::from(0));
    let affine_point = AffinePoint::new(Felt::from(0), Felt::from(1)).unwrap();
```

## Usage

Include `starknet-types-core` in your library by adding the following to your `Cargo.toml`:

```toml
[dependencies]
starknet-types-core = { version = "0.0.3", git = "https://github.com/starknet-io/types-rs", default-features = false, features = [
    "alloc",
    "serde",
    "arbitrary",
    "curve",
    "hash",
] }
```

## Build from source

Clone the repository and navigate to the starknet-types-core directory. Then run:

```bash
cargo build --release
```

## Testing

Clone the repository and navigate to the starknet-types-core directory. Then run:

```bash
cargo test
```

## Contributing

Contributions are welcome! Please read our [contributing guidelines](CONTRIBUTING.md) for more information.

## License

This repository is licensed under the MIT License, see [LICENSE](LICENSE) for more information.
