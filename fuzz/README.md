# Fuzzing

This directory contains the fuzzing infrastructure for the `types-rs` project.

## Setup
```
cargo install cargo-fuzz
```

## Running the fuzzers
* cd into one of the directories, e.g., `cd felt`
* list the available fuzz targets, e.g., `cargo fuzz list --fuzz-dir=.`
* run the fuzzer, e.g., `cargo +nightly fuzz run add_fuzzer  --fuzz-dir=.`