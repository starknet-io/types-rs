use criterion::{BatchSize, BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use starknet_types_core::felt::Felt;
use starknet_types_core::hash::{Pedersen, Poseidon, StarkHash};

const SEED: u64 = 3;

fn rnd_felt(rng: &mut ChaCha8Rng) -> Felt {
    let mut felt: [u8; 32] = Default::default();
    let first_non_zero = rng.gen_range(0..32);
    rng.fill_bytes(&mut felt[first_non_zero..32]);
    Felt::from_bytes_be(&felt)
}

fn rnd_felts(rng: &mut ChaCha8Rng, n: usize) -> Vec<Felt> {
    (0..n).map(|_| rnd_felt(rng)).collect()
}

fn rnd_pair_of_felts(rng: &mut ChaCha8Rng) -> (Felt, Felt) {
    (rnd_felt(rng), rnd_felt(rng))
}

fn poseidon_hash(c: &mut Criterion) {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED);
    let mut group = c.benchmark_group("Poseidon");

    group.bench_function("hash", |bench| {
        bench.iter_batched(
            || rnd_pair_of_felts(&mut rng),
            |(x, y)| black_box(Poseidon::hash(&x, &y)),
            BatchSize::SmallInput,
        );
    });
}

fn poseidon_hash_array(c: &mut Criterion) {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED);

    let mut group = c.benchmark_group("Poseidon");

    for n in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("hash_array", n), n, |bench, &n| {
            bench.iter_batched(
                || rnd_felts(&mut rng, n),
                |felts| black_box(Poseidon::hash_array(&felts)),
                BatchSize::SmallInput,
            );
        });
    }
}

fn pedersen_hash(c: &mut Criterion) {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED);
    let mut group = c.benchmark_group("Pedersen");

    group.bench_function("hash", |bench| {
        bench.iter_batched(
            || rnd_pair_of_felts(&mut rng),
            |(x, y)| black_box(Pedersen::hash(&x, &y)),
            BatchSize::SmallInput,
        );
    });
}

fn pedersen_hash_array(c: &mut Criterion) {
    let mut rng = ChaCha8Rng::seed_from_u64(SEED);

    let mut group = c.benchmark_group("Pedersen");

    for n in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("hash_array", n), n, |bench, &n| {
            bench.iter_batched(
                || rnd_felts(&mut rng, n),
                |felts| black_box(Pedersen::hash_array(&felts)),
                BatchSize::SmallInput,
            );
        });
    }
}

criterion_group!(
    hashes,
    pedersen_hash,
    pedersen_hash_array,
    poseidon_hash,
    poseidon_hash_array
);
criterion_main!(hashes);
