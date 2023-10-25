# starknet-types-core

Core types representation for Starknet.

## Overview

The `starknet-types-core` crate provides:
* The universal `Felt` (Field Element) type for Cairo and STARK proofs. It was created to reduce the fragmentation in the Starknet Rust ecosystem by providing a standardized representation of the `Felt` type.
* The `AffinePoint` and `ProjectivePoint` structs, that represent a point in the Stark curve with which you can operate

## Features

- Standardized `Felt` type: Simplify your codebase by using our standardized `Felt` type.
- Optimized for performance: The `Felt` type has been optimized for high-performance applications.

## Examples

Here are some examples of how to use the `Felt` type:

```rust
    let x = Felt::from(18)
```

## Usage

Include `starknet-types-core` in your library by adding the following to your `Cargo.toml`:

```toml
[dependencies]
starknet-types-core = { version = "0.0.3", git = "https://github.com/starknet-io/types-rs" }
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
