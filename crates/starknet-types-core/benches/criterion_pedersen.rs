use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use starknet_types_core::felt::Felt;
use starknet_types_core::hash::Pedersen;
use starknet_types_core::hash::StarkHash;

fn pedersen_benchmarks(c: &mut Criterion) {
    let mut rng = ChaCha8Rng::seed_from_u64(2);
    let mut felt1: [u8; 32] = Default::default();
    rng.fill_bytes(&mut felt1);
    let mut felt2: [u8; 32] = Default::default();
    rng.fill_bytes(&mut felt2);

    let x = Felt::from_bytes_be(&felt1);
    let y = Felt::from_bytes_be(&felt2);
    let mut group = c.benchmark_group("Pedersen Benchmark");
    // let pedersen = black_box(Pedersen::default());

    // Benchmark with black_box is 0.41% faster
    group.bench_function("Hashing with black_box", |bench| {
        bench.iter(|| black_box(Pedersen::hash(&x, &y)))
    });
}
criterion_group!(pedersen, pedersen_benchmarks);
criterion_main!(pedersen);
