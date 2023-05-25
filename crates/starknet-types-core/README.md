# starknet-types-core

`starknet-types-core` is a crate focusing on Starknet types related to computation and execution. This crate is part of an initiative to standardize the representation of the `Felt` type in Rust, reducing code complexity and improving performance across the Starknet Rust ecosystem.

The types in this crate require performance and optimization for specific arithmetic and cryptographic operations, making it ideal for computational tasks within the Starknet ecosystem.

## Usage

Include `starknet-types-core` in your library by adding the following to your `Cargo.toml`:

```toml
[dependencies]
starknet-types-core = { version = "0.0.2", git = "https://github.com/starknet-io/types-rs" }
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
