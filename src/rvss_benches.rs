// SPDX-License-Identifier: Apache-2.0

use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use rand::thread_rng;

mod rvss_benches {
    use super::*;
    use fastcrypto::groups::{bls12381, GroupElement, MultiScalarMul, Scalar as GScalar};
    use itertools::Itertools;
    use research_rvss::rvss::{Gadget, Point, Scalar, RVSS};
    use std::hint::black_box;

    fn exps(c: &mut Criterion) {
        let mut group: BenchmarkGroup<_> = c.benchmark_group("ops");

        // Single exponentiation in BLS12-381 G1 and G2 (reference microbenchmarks).
        {
            let x = bls12381::G1Element::generator() * bls12381::Scalar::rand(&mut thread_rng());
            let y = bls12381::Scalar::rand(&mut thread_rng());
            group.bench_function("g1 exp", move |b| b.iter(|| x * y));
        }
        {
            let x = bls12381::G2Element::generator() * bls12381::Scalar::rand(&mut thread_rng());
            let y = bls12381::Scalar::rand(&mut thread_rng());
            group.bench_function("g2 exp", move |b| b.iter(|| x * y));
        }

        // MSM vs. sequential exponentiation on the active curve (`Point`), to quantify the
        // multi-scalar-multiplication speedup at 128 and 1024 elements.
        for m in [128usize, 1024] {
            let scalars = (0..m).map(|_| Scalar::rand(&mut thread_rng())).collect_vec();
            let points = (0..m)
                .map(|_| Point::generator() * Scalar::rand(&mut thread_rng()))
                .collect_vec();
            let (s_seq, p_seq) = (scalars.clone(), points.clone());

            group.bench_function(format!("msm m={}", m).as_str(), move |b| {
                b.iter(|| black_box(Point::multi_scalar_mul(&scalars, &points).unwrap()))
            });
            group.bench_function(format!("sequential m={}", m).as_str(), move |b| {
                b.iter(|| {
                    let mut acc = Point::zero();
                    for i in 0..m {
                        acc = acc + p_seq[i] * s_seq[i];
                    }
                    black_box(acc)
                })
            });
        }
    }

    fn gadget(c: &mut Criterion) {
        const KS: [usize; 3] = [80, 100, 120];
        let mut create: BenchmarkGroup<_> = c.benchmark_group("gadget");

        for k in KS {
            let h = Point::generator();
            let omega = Scalar::rand(&mut thread_rng());

            create.bench_function(format!("create k={}", k).as_str(), |b| {
                b.iter(|| Gadget::new(k, h, omega))
            });

            let gadget = Gadget::new(k, h, omega);
            create.bench_function(format!("verify k={}", k).as_str(), |b| {
                b.iter(|| gadget.verify(k).unwrap())
            });
        }
    }

    fn rvss(c: &mut Criterion) {
        let ns = [64, 128, 256, 512, 1024, 2048];
        let ks = [80];
        let mut create: BenchmarkGroup<_> = c.benchmark_group("rvss");

        for n in ns {
            for k in ks {
                let sk = (1..=n)
                    .map(|_| GScalar::rand(&mut thread_rng()))
                    .collect_vec();
                let pks = sk
                    .iter()
                    .map(|sk_i| Point::generator() * sk_i)
                    .collect_vec();
                let t = (n / 3) * 2;
                let omega = GScalar::rand(&mut thread_rng());

                create.bench_function(format!("create t={}, n={}, k={}", t, n, k).as_str(), |b| {
                    b.iter(|| RVSS::new(k, t, omega, &pks))
                });

                let rvss = RVSS::new(k, t, omega, &pks);
                println!(
                    "rvss msg with n {}, size {}",
                    n,
                    bcs::to_bytes(&rvss).unwrap().len()
                );
                create.bench_function(format!("verify t={}, n={}, k={}", t, n, k).as_str(), |b| {
                    b.iter(|| rvss.verify(k, t, &pks).unwrap())
                });

                create.bench_function(format!("decrypt t={}, n={}, k={}", t, n, k).as_str(), |b| {
                    b.iter(|| rvss.optimistic_decrypt(10, &sk[10]).unwrap())
                });
            }
        }
    }

    fn unhappy(c: &mut Criterion) {
        let ns = [64, 128, 256, 512, 1024, 2048];
        let k = 80;
        let mut group: BenchmarkGroup<_> = c.benchmark_group("unhappy");

        for n in ns {
            let sk = (1..=n)
                .map(|_| GScalar::rand(&mut thread_rng()))
                .collect_vec();
            let pks = sk
                .iter()
                .map(|sk_i| Point::generator() * sk_i)
                .collect_vec();
            let t = (n / 3) * 2;
            let num = t + 1;
            let omega = GScalar::rand(&mut thread_rng());
            let rvss = RVSS::new(k, t, omega, &pks);

            // (a) generate a DLEQ fraud proof
            group.bench_function(format!("fraud-proof-create n={}", n).as_str(), |b| {
                b.iter(|| black_box(rvss.decrypt_with_proof(0, &sk[0], &pks[0])))
            });

            let proofs = (0..num)
                .map(|i| {
                    let (s_hat, proof) = rvss.decrypt_with_proof(i, &sk[i], &pks[i]);
                    (i, s_hat, proof)
                })
                .collect_vec();
            let indices = (1..=num).collect_vec();
            let points = proofs.iter().map(|(_, s, _)| *s).collect_vec();

            // (b) verify t+1 DLEQ fraud proofs
            group.bench_function(format!("verify-{}-fraud-proofs n={}", num, n).as_str(), |b| {
                b.iter(|| {
                    for (i, s_hat, proof) in &proofs {
                        rvss.verify_fraud_proof(*i, s_hat, &pks[*i], proof).unwrap();
                    }
                })
            });

            // (c) interpolation in the exponent (a (t+1)-wide MSM)
            group.bench_function(format!("interpolate-exp num={} n={}", num, n).as_str(), |b| {
                b.iter(|| black_box(RVSS::interpolate_in_exponent(&indices, &points).unwrap()))
            });

            // (d) gadget decryption
            let g_omega = RVSS::interpolate_in_exponent(&indices, &points).unwrap();
            group.bench_function(format!("gadget-decrypt k={} n={}", k, n).as_str(), |b| {
                b.iter(|| black_box(rvss.gadget_decrypt(k, g_omega).unwrap()))
            });

            // total reconstruction (c + d)
            group.bench_function(format!("reconstruct-total n={}", n).as_str(), |b| {
                b.iter(|| black_box(rvss.reconstruct(k, &indices, &points).unwrap()))
            });
        }
    }

    criterion_group! {
        name = rvss_benches;
        config = Criterion::default().sample_size(10);
        targets =
            exps,
            gadget,
            rvss,
            unhappy
    }
}

criterion_main!(rvss_benches::rvss_benches);
