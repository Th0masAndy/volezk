mod utils;
use ark_ec::bls12::Bls12Config;
use ark_ec::Group;
use ark_ff::FftField;
use ark_std::UniformRand;
use utils::algebra::field::mersenne61_ext::Mersenne61Ext;
use utils::algebra::field::MyField;
type Fr = <ark_ec::short_weierstrass::Projective<
        <ark_bls12_377::Config as Bls12Config>::G1Config,
    > as Group>::ScalarField;

use utils::timer::*;

pub fn sumcheck<F: MyField>(evaluation: &Vec<F>, challenge: &Vec<F>) -> Vec<(F, F)> {
    let mut result = Vec::new();
    let mut last_round = evaluation.clone();
    let n: usize = evaluation.len().trailing_zeros() as usize;
    for i in 0..n {
        let parts = last_round.split_at(last_round.len() / 2);
        result.push((parts.0.iter().sum(), parts.1.iter().sum()));
        let this_round = parts
            .0
            .iter()
            .zip(parts.1.iter())
            .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
            .collect::<Vec<_>>();
        last_round = this_round;
    }
    debug_assert!(last_round.len() == 1);
    // The last round yields (0, result).
    result.push((F::ZERO, last_round[0]));
    result
}

pub fn sumcheck_product<F: MyField>(
    evaluation_f: &Vec<F>,
    evaluation_g: &Vec<F>,
    challenge: &Vec<F>,
) -> Vec<(F, F, F)> {
    let mut result = Vec::new();
    let mut last_round_f = evaluation_f.clone();
    let mut last_round_g = evaluation_g.clone();
    let n = evaluation_f.len().trailing_zeros() as usize;
    let fp2 = F::from_int(2_u64);
    for i in 0..n {
        let parts_f = last_round_f.split_at(last_round_f.len() / 2);
        let parts_g = last_round_g.split_at(last_round_g.len() / 2);
        // t=0
        let part0_sum = parts_f
            .0
            .iter()
            .zip(parts_g.0.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y);
        // t=1
        let part1_sum = parts_f
            .1
            .iter()
            .zip(parts_g.1.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y);
        // t=2,
        // in which case, the evaluation of f and g is not present in the bookkeeping table,
        // we need to calculate them from (1-t)*x0+t*x1
        let part2_f: Vec<_> = parts_f
            .0
            .iter()
            .zip(parts_f.1.iter())
            .map(|(x, y)| -*x + *y * fp2)
            .collect();
        let part2_g: Vec<_> = parts_g
            .0
            .iter()
            .zip(parts_g.1.iter())
            .map(|(x, y)| -*x + *y * fp2)
            .collect();
        let part2_sum = part2_f
            .iter()
            .zip(part2_g.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y);
        result.push((part0_sum, part1_sum, part2_sum));
        last_round_f = parts_f
            .0
            .iter()
            .zip(parts_f.1.iter())
            .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
            .collect::<Vec<_>>();
        last_round_g = parts_g
            .0
            .iter()
            .zip(parts_g.1.iter())
            .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
            .collect::<Vec<_>>();
    }
    debug_assert!(last_round_f.len() == 1);
    // The last round yields (0, result).
    result.push((F::ZERO, last_round_f[0] * last_round_g[0], F::ZERO));
    result
}

pub fn sumcheck_product_degree4<F: MyField>(
    evaluation_f: &Vec<F>,
    evaluation_g: &Vec<F>,
    evaluation_h: &Vec<F>,
    evaluation_k: &Vec<F>,
    challenge: &Vec<F>,
) -> Vec<(F, F, F, F, F)> {
    let mut result = Vec::new();
    let mut last_round_f = evaluation_f.clone();
    let mut last_round_g = evaluation_g.clone();
    // let mut last_round_h = evaluation_h.clone();
    // let mut last_round_k = evaluation_k.clone();
    let n = evaluation_f.len().trailing_zeros() as usize;
    let fp2 = F::from_int(2_u64);
    let fp3 = F::from_int(3_u64);
    let fp4 = F::from_int(4_u64);
    let neg_fp2 = -fp2;
    let neg_fp3 = -fp3;
    for i in 0..n {
        let parts_f = last_round_f.split_at(last_round_f.len() / 2);
        let parts_g = last_round_g.split_at(last_round_g.len() / 2);
        // let parts_h = last_round_h.split_at(last_round_h.len() / 2);
        // let parts_k = last_round_k.split_at(last_round_k.len() / 2);
        let part0_sum = parts_f
            .0
            .iter()
            .zip(parts_g.0.iter())
            // .zip(parts_h.0.iter())
            // .zip(parts_k.0.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y * *y * *y);

        let part1_sum = parts_f
            .1
            .iter()
            .zip(parts_g.1.iter())
            // .zip(parts_h.1.iter())
            // .zip(parts_k.1.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y * *y * *y);

        let part2_f: Vec<_> = parts_f
            .0
            .iter()
            .zip(parts_f.1.iter())
            .map(|(x, y)| -*x + *y * fp2)
            .collect();
        let part2_g: Vec<_> = parts_g
            .0
            .iter()
            .zip(parts_g.1.iter())
            .map(|(x, y)| -*x + *y * fp2)
            .collect();
        // let part2_h: Vec<_> = parts_h
        //     .0
        //     .iter()
        //     .zip(parts_h.1.iter())
        //     .map(|(x, y)| -*x + *y * fp2)
        //     .collect();
        // let part2_h = part2_g.clone();
        // let part2_k = part2_g.clone();
        // let part2_k: Vec<_> = parts_k
        //     .0
        //     .iter()
        //     .zip(parts_k.1.iter())
        //     .map(|(x, y)| -*x + *y * fp2)
        //     .collect();

        let part2_sum = part2_f
            .iter()
            .zip(part2_g.iter())
            // .zip(part2_h.iter())
            // .zip(part2_k.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y * *y * *y);

        let part3_f: Vec<_> = parts_f
            .0
            .iter()
            .zip(parts_f.1.iter())
            .map(|(x, y)| *x * neg_fp2 + *y * fp3)
            .collect();
        let part3_g: Vec<_> = parts_g
            .0
            .iter()
            .zip(parts_g.1.iter())
            .map(|(x, y)| *x * neg_fp2 + *y * fp3)
            .collect();
        // let part3_h = part3_g.clone();
        // let part3_k = part3_g.clone();
        // let part3_h: Vec<_> = parts_h
        //     .0
        //     .iter()
        //     .zip(parts_h.1.iter())
        //     .map(|(x, y)| *x * neg_fp2 + *y * fp3)
        //     .collect();
        // let part3_k: Vec<_> = parts_k
        //     .0
        //     .iter()
        //     .zip(parts_k.1.iter())
        //     .map(|(x, y)| *x * neg_fp2 + *y * fp3)
        //     .collect();
        let part3_sum = part3_f
            .iter()
            .zip(part3_g.iter())
            // .zip(part3_h.iter())
            // .zip(part3_k.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y * *y * *y);

        let part4_f: Vec<_> = parts_f
            .0
            .iter()
            .zip(parts_f.1.iter())
            .map(|(x, y)| *x * neg_fp3 + *y * fp4)
            .collect();
        let part4_g: Vec<_> = parts_g
            .0
            .iter()
            .zip(parts_g.1.iter())
            .map(|(x, y)| *x * neg_fp3 + *y * fp4)
            .collect();
        // let part4_h = part4_g.clone();
        // let part4_k = part4_g.clone();
        // let part4_h: Vec<_> = parts_h
        //     .0
        //     .iter()
        //     .zip(parts_h.1.iter())
        //     .map(|(x, y)| *x * neg_fp3 + *y * fp4)
        //     .collect();
        // let part4_k: Vec<_> = parts_k
        //     .0
        //     .iter()
        //     .zip(parts_k.1.iter())
        //     .map(|(x, y)| *x * neg_fp3 + *y * fp4)
        //     .collect();
        let part4_sum = part4_f
            .iter()
            .zip(part4_g.iter())
            // .zip(part4_h.iter())
            // .zip(part4_k.iter())
            .fold(F::ZERO, |acc, (x, y)| acc + *x * *y * *y * *y);

        result.push((part0_sum, part1_sum, part2_sum, part3_sum, part4_sum));

        last_round_f = parts_f
            .0
            .iter()
            .zip(parts_f.1.iter())
            .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
            .collect::<Vec<_>>();
        last_round_g = parts_g
            .0
            .iter()
            .zip(parts_g.1.iter())
            .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
            .collect::<Vec<_>>();
        // last_round_h = last_round_g.clone();
        // last_round_k = last_round_g.clone();
        // last_round_h = parts_h
        //     .0
        //     .iter()
        //     .zip(parts_h.1.iter())
        //     .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
        //     .collect::<Vec<_>>();
        // last_round_k = parts_k
        //     .0
        //     .iter()
        //     .zip(parts_k.1.iter())
        //     .map(|(a, b)| *a * (F::ONE - challenge[i]) + *b * challenge[i])
        //     .collect::<Vec<_>>();
    }
    debug_assert!(last_round_f.len() == 1);
    // The last round yields (0, result).
    result.push((
        F::ZERO,
        last_round_f[0] * last_round_g[0] * last_round_g[0] * last_round_g[0],
        F::ZERO,
        F::ZERO,
        F::ZERO,
    ));
    result
}

pub fn sumcheck_ckecker<F: MyField>(h: F, proof: Vec<(F, F, F, F, F)>, challenge: Vec<F>) -> bool {
    if proof[0].0 + proof[0].1 != h {
        return false;
    }
    let n: usize = challenge.len();

    for i in 1..n {
        let x = challenge[i - 1];
        let e = proof[i - 1].0;
        let d = -proof[i - 1].0 * F::from_int(50_u64) / F::from_int(24_u64)
            + proof[i - 1].1 * F::from_int(24_u64) / F::from_int(6_u64)
            - proof[i - 1].2 * F::from_int(12_u64) / F::from_int(4_u64)
            + proof[i - 1].3 * F::from_int(8_u64) / F::from_int(6_u64)
            - proof[i - 1].4 * F::from_int(6_u64) / F::from_int(24_u64);
        let c = proof[i - 1].0 * F::from_int(35_u64) / F::from_int(24_u64)
            - proof[i - 1].1 * F::from_int(26_u64) / F::from_int(6_u64)
            + proof[i - 1].2 * F::from_int(19_u64) / F::from_int(4_u64)
            - proof[i - 1].3 * F::from_int(14_u64) / F::from_int(6_u64)
            + proof[i - 1].4 * F::from_int(11_u64) / F::from_int(24_u64);

        let b = -proof[i - 1].0 * F::from_int(10_u64) / F::from_int(24_u64)
            + proof[i - 1].1 * F::from_int(9_u64) / F::from_int(6_u64)
            - proof[i - 1].2 * F::from_int(8_u64) / F::from_int(4_u64)
            + proof[i - 1].3 * F::from_int(7_u64) / F::from_int(6_u64)
            - proof[i - 1].4 * F::from_int(6_u64) / F::from_int(24_u64);
        let a = proof[i - 1].0 * F::from_int(1_u64) / F::from_int(24_u64)
            - proof[i - 1].1 * F::from_int(1_u64) / F::from_int(6_u64)
            + proof[i - 1].2 * F::from_int(1_u64) / F::from_int(4_u64)
            - proof[i - 1].3 * F::from_int(1_u64) / F::from_int(6_u64)
            + proof[i - 1].4 * F::from_int(1_u64) / F::from_int(24_u64);

        // assert_eq!(c, proof[i - 1].0);
        // assert_eq!(a + b + c, proof[i - 1].1);
        // assert_eq!(
        //     a * F::from_int(4_u64) + b * F::from_int(2_u64) + c,
        //     proof[i - 1].2
        // );

        let target = a * x * x * x * x + b * x * x * x + c * x * x + d * x + e;
        if proof[i].0 + proof[i].1 != target {
            println!("{}-th proof fails to verify.", i);
            return false;
        }
    }
    // Now check the oracle query
    // if result[N-1].1 != query(random) {
    //     return false;
    // }
    true
}

fn main() {
    let logn = 13;
    let n = 1 << logn;

    // let table_f = (0..n)
    //     .map(|_| Fr::rand(&mut ark_std::test_rng()))
    //     .collect::<Vec<_>>();

    // let challenge = (0..logn)
    //     .map(|_| Fr::rand(&mut ark_std::test_rng()))
    //     .collect::<Vec<_>>();

    // let sc = start_timer!("Local SumcheckProduct");
    // let p = sumcheck_product_degree4(&table_f, &table_f, &table_f, &table_f, &challenge);
    // end_timer!(sc);

    // let h = table_f.iter().map(|x| x * x * x * x).sum();
    // assert!(sumcheck_ckecker(h, p, challenge));

    let table_f = (0..n)
        .map(|_| Mersenne61Ext::random_element())
        .collect::<Vec<_>>();

    let challenge = (0..logn)
        .map(|_| Mersenne61Ext::random_element())
        .collect::<Vec<_>>();

    let sc = start_timer!("Local SumcheckProduct");
    let p = sumcheck_product_degree4(&table_f, &table_f, &table_f, &table_f, &challenge);
    end_timer!(sc);

    let h = table_f.iter().map(|x| *x * *x * *x * *x).sum();
    assert!(sumcheck_ckecker(h, p, challenge));
}
