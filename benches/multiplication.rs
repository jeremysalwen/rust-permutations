#[macro_use]
extern crate bencher;
extern crate permutation;
extern crate rand;

use bencher::Bencher;
use permutation::Permutation;
use rand::{distributions::Uniform, Rng};

fn random_permutation(n: usize, forward: bool) -> Permutation {
    let range = Uniform::from(0u64..u64::MAX);
    permutation::sort(
        rand::thread_rng()
            .sample_iter(range)
            .take(n)
            .collect::<Vec<u64>>(),
    )
    .normalize(!forward)
}

fn f_f_mult_n10(b: &mut Bencher) {
    let p1 = random_permutation(10, true);
    let p2 = random_permutation(10, true);
    b.iter(|| &p1 * &p2);
}

fn b_f_mult_n10(b: &mut Bencher) {
    let p1 = random_permutation(10, false);
    let p2 = random_permutation(10, true);
    b.iter(|| &p1 * &p2);
}
fn single_alloc_mult_n10(b: &mut Bencher) {
    let p1 = random_permutation(10, false);
    let p2 = random_permutation(10, true);
    b.iter(|| permutation::single_allocation_inv_mul_per(&p1, &p2));
}
fn single_alloc_mult2_n10(b: &mut Bencher) {
    let p1 = random_permutation(10, false);
    let p2 = random_permutation(10, true);
    b.iter(|| permutation::single_allocation_inv_mul2(&p1, &p2));
}
fn f_b_mult_n10(b: &mut Bencher) {
    let p1 = random_permutation(10, true);
    let p2 = random_permutation(10, false);
    b.iter(|| &p1 * &p2);
}

fn b_b_mult_n10(b: &mut Bencher) {
    let p1 = random_permutation(10, false);
    let p2 = random_permutation(10, false);
    b.iter(|| &p1 * &p2);
}

fn f_f_mult_n100(b: &mut Bencher) {
    let p1 = random_permutation(100, true);
    let p2 = random_permutation(100, true);
    b.iter(|| &p1 * &p2);
}

fn b_f_mult_n100(b: &mut Bencher) {
    let p1 = random_permutation(100, false);
    let p2 = random_permutation(100, true);
    b.iter(|| &p1 * &p2);
}

fn single_alloc_mult_n100(b: &mut Bencher) {
    let p1 = random_permutation(100, false);
    let p2 = random_permutation(100, true);
    b.iter(|| permutation::single_allocation_inv_mul_per(&p1, &p2));
}
fn single_alloc_mult2_n100(b: &mut Bencher) {
    let p1 = random_permutation(100, false);
    let p2 = random_permutation(100, true);
    b.iter(|| permutation::single_allocation_inv_mul2(&p1, &p2));
}

fn f_b_mult_n100(b: &mut Bencher) {
    let p1 = random_permutation(100, true);
    let p2 = random_permutation(100, false);
    b.iter(|| &p1 * &p2);
}

fn b_b_mult_n100(b: &mut Bencher) {
    let p1 = random_permutation(100, false);
    let p2 = random_permutation(100, false);
    b.iter(|| &p1 * &p2);
}

fn f_f_mult_n1000(b: &mut Bencher) {
    let p1 = random_permutation(1000, true);
    let p2 = random_permutation(1000, true);
    b.iter(|| &p1 * &p2);
}

fn b_f_mult_n1000(b: &mut Bencher) {
    let p1 = random_permutation(1000, false);
    let p2 = random_permutation(1000, true);
    b.iter(|| &p1 * &p2);
}
fn single_alloc_mult_n1000(b: &mut Bencher) {
    let p1 = random_permutation(1000, false);
    let p2 = random_permutation(1000, true);
    b.iter(|| permutation::single_allocation_inv_mul_per(&p1, &p2));
}
fn single_alloc_mult2_n1000(b: &mut Bencher) {
    let p1 = random_permutation(1000, false);
    let p2 = random_permutation(1000, true);
    b.iter(|| permutation::single_allocation_inv_mul2(&p1, &p2));
}

fn f_b_mult_n1000(b: &mut Bencher) {
    let p1 = random_permutation(1000, true);
    let p2 = random_permutation(1000, false);
    b.iter(|| &p1 * &p2);
}

fn b_b_mult_n1000(b: &mut Bencher) {
    let p1 = random_permutation(1000, false);
    let p2 = random_permutation(1000, false);
    b.iter(|| &p1 * &p2);
}

fn f_f_mult_n10000(b: &mut Bencher) {
    let p1 = random_permutation(10000, true);
    let p2 = random_permutation(10000, true);
    b.iter(|| &p1 * &p2);
}

fn b_f_mult_n10000(b: &mut Bencher) {
    let p1 = random_permutation(10000, false);
    let p2 = random_permutation(10000, true);
    b.iter(|| &p1 * &p2);
}
fn single_alloc_mult_n10000(b: &mut Bencher) {
    let p1 = random_permutation(10000, false);
    let p2 = random_permutation(10000, true);
    b.iter(|| permutation::single_allocation_inv_mul_per(&p1, &p2));
}
fn single_alloc_mult2_n10000(b: &mut Bencher) {
    let p1 = random_permutation(10000, false);
    let p2 = random_permutation(10000, true);
    b.iter(|| permutation::single_allocation_inv_mul2(&p1, &p2));
}
fn f_b_mult_n10000(b: &mut Bencher) {
    let p1 = random_permutation(10000, true);
    let p2 = random_permutation(10000, false);
    b.iter(|| &p1 * &p2);
}

fn b_b_mult_n10000(b: &mut Bencher) {
    let p1 = random_permutation(10000, false);
    let p2 = random_permutation(10000, false);
    b.iter(|| &p1 * &p2);
}

fn invert_in_place_10(b: &mut Bencher) {
    let mut p1 = random_permutation(10, true);
    b.iter(|| p1.invert_representation());
}
fn invert_in_place_100(b: &mut Bencher) {
    let mut p1 = random_permutation(100, true);
    b.iter(|| p1.invert_representation());
}
fn invert_in_place_1000(b: &mut Bencher) {
    let mut p1 = random_permutation(1000, true);
    b.iter(|| p1.invert_representation());
}
fn invert_in_place_10000(b: &mut Bencher) {
    let mut p1 = random_permutation(10000, true);
    b.iter(|| p1.invert_representation());
}

fn invert_10(b: &mut Bencher) {
    let mut p1 = random_permutation(10, true);
    let one = Permutation::one(p1.len());
    b.iter(|| p1 = &p1 * &one);
}
fn invert_100(b: &mut Bencher) {
    let mut p1 = random_permutation(100, true);
    let one = Permutation::one(p1.len());
    b.iter(|| p1 = &p1 * &one);
}
fn invert_1000(b: &mut Bencher) {
    let mut p1 = random_permutation(1000, true);
    let one = Permutation::one(p1.len());
    b.iter(|| p1 = &p1 * &one);
}
fn invert_10000(b: &mut Bencher) {
    let mut p1 = random_permutation(10000, true);
    let one = Permutation::one(p1.len());
    b.iter(|| p1 = &p1 * &one);
}

benchmark_group!(
    mul,
    f_f_mult_n10,
    b_f_mult_n10,
    f_b_mult_n10,
    b_b_mult_n10,
    single_alloc_mult_n10,
    single_alloc_mult2_n10,
    f_f_mult_n100,
    b_f_mult_n100,
    f_b_mult_n100,
    b_b_mult_n100,
    single_alloc_mult_n100,
    single_alloc_mult2_n100,
    f_f_mult_n1000,
    b_f_mult_n1000,
    f_b_mult_n1000,
    b_b_mult_n1000,
    single_alloc_mult_n1000,
    single_alloc_mult2_n1000,
    f_f_mult_n10000,
    b_f_mult_n10000,
    f_b_mult_n10000,
    b_b_mult_n10000,
    single_alloc_mult_n10000,
    single_alloc_mult2_n10000,
);

benchmark_group!(
    inv,
    invert_in_place_10,
    invert_in_place_100,
    invert_in_place_1000,
    invert_in_place_10000,
    invert_10,
    invert_100,
    invert_1000,
    invert_10000
);
benchmark_main!(mul, inv);
