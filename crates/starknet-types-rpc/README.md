# starknet-types-rpc

```markdown
# starknet-types-rpc

`starknet-types-rpc` is a crate dealing with Starknet types used in RPC communication, serde, and transport. This crate is part of an initiative to standardize the representation of the `Felt` type in Rust, reducing code complexity and improving performance across the Starknet Rust ecosystem.

## Usage

Include `starknet-types-rpc` in your library by adding the following to your `Cargo.toml`:

```toml
[dependencies]
starknet-types-rpc = { version = "0.0.2", git = "https://github.com/starknet-io/types-rs" }
```

## Build from source

The crate is built in two steps:

### Generating bindings against the Starknet OpenRPC specification

The specification is hosted on Starknet's repository ([link](https://github.com/starkware-libs/starknet-specs/blob/master/api/starknet_api_openrpc.json)).

Bindings are generated using [`openrpc-gen`](https://github.com/nils-mathieu/openrpc-gen).

After having built `openrpc-gen`, you can use the following command to generate the final generated
Rust files:

```bash
make all
```

NOTE: Currently the `starknet_trace_api_openrpc` file requires a modification for `starknet_simulateTransactions` (nested `schema` in the result, see previous version for infos)

*Note that this first step is normally already done for you upon cloning the repository.*

### Building the generated files

Once this is done, you can build the crate with:

```bash
cargo build --release
```

## Testing

Clone the repository and navigate to the starknet-types-rpc directory. Then run:

```bash
cargo test
```

## Contributing

Contributions are welcome! Please read our [contributing guidelines](CONTRIBUTING.md) for more information.

## License

This repository is licensed under the MIT License, see [LICENSE](LICENSE) for more information.
