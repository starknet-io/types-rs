# types-rs

 🐺  Starknet Rust types 🦀

 [![GitHub Workflow Status](https://github.com/starknet-io/types-rs/actions/workflows/test.yml/badge.svg)](https://github.com/starknet-io/types-rs/actions/workflows/test.yml)
[![Project license](https://img.shields.io/github/license/starknet-io/types-rs.svg?style=flat-square)](LICENSE)
[![Pull Requests welcome](https://img.shields.io/badge/PRs-welcome-ff69b4.svg?style=flat-square)](https://github.com/starknet-io/types-rs/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22)
[![Rust docs](https://docs.rs/stark-felt/badge.svg)](https://docs.rs/stark-felt)
[![Rust crate](https://img.shields.io/crates/v/stark-felt.svg)](https://crates.io/crates/stark-felt)

This repository is an initiative by a group of maintainers to address the fragmentation in the Starknet Rust ecosystem and improve its interoperability. The key motivation behind this repository is to standardize the representation of the `Felt` (Field Element) type in Rust, which is massively used as the core and atomic type of the Cairo language and its Virtual Machine.

The `Felt` type is currently defined in many different crates and repositories, resulting in increased code complexity and performance issues due to the need for numerous conversions. This repository aims to mitigate these issues by providing a universal `Felt` type in Rust.

## Crates

This repository hosts three crates:

- `stark-felt`: This crate provides the universal Felt (Field Element) type for Cairo and STARK proofs.

- `starknet-types-core`: This crate focuses on Starknet types related to computation and execution, requiring performance and optimization for specific arithmetic and cryptographic operations.

- `starknet-types-rpc`: This crate deals with Starknet types used in RPC communication, serde, and transport.

## Usage

You can include any of these crates in your library via crates.io or as a git dependency. For example, to include the `stark-felt` crate, add the following to your `Cargo.toml`:

As a crates.io dependency:

```toml
[dependencies]
stark-felt = "0.0.3"
```

As a git dependency:

```toml
[dependencies]
stark-felt = { git = "https://github.com/starknet-io/types-rs" }
```

## Build from source

To build the crates from source, clone the repository and run the following command:

```bash
cargo build --release
```

## Testing

To run the tests, clone the repository and run the following command:

```bash
cargo test
```

## Contributing

Contributions are welcome! Please read our [contributing guidelines](CONTRIBUTING.md) for more information.

## License

This repository is licensed under the MIT License, see [LICENSE](LICENSE) for more information.
