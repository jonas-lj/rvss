use either::Either;
use fastcrypto_tbls::random_oracle::RandomOracle;
use fastcrypto::serde_helpers::ToFromByteArray;
use fastcrypto::{
    error::{FastCryptoError, FastCryptoResult},
    groups::{GroupElement, HashToGroupElement, Scalar as GScalar},
};
use fastcrypto_tbls::dl_verification::verify_pairs;
use fastcrypto_tbls::polynomial::Poly;
use itertools::Itertools;
use rand::{thread_rng, RngCore};
use serde::Serialize;

/////// Implementation of the RVSS protocol for performance testing ONLY ///////

// Note: the per-instance random-oracle contexts of the paper (Section 2) are not implemented.
// Here we use fixed labels without a session id or party identities.
// Adding the context only changes the hashed prefix and does not affect the measured costs.

// Switch the group by commenting and uncommenting the following lines

/////// BLS12-381 test ///////
use fastcrypto::groups::MultiScalarMul;
use fastcrypto::groups::bls12381;
pub type Point = bls12381::G1Element;
pub type Scalar = bls12381::Scalar;

/////// Ristretto255 test ///////
// use fastcrypto::groups::{ristretto255, MultiScalarMul};
// pub type Point = ristretto255::RistrettoPoint;
// pub type Scalar = ristretto255::RistrettoScalar;

//////// Recovery gadget ////////

#[derive(Serialize)]
pub struct Gadget {
    h: Point,
    h_omega: Point,
    t: Vec<(Point, Vec<u8>)>,
    u: Vec<Either<Point, Scalar>>,
}

impl Gadget {
    pub fn new(k: usize, h: Point, omega: Scalar) -> Self {
        let ro = RandomOracle::new("gadget");
        let h_omega = h * omega;
        let g = Point::generator();

        let r = (0..k)
            .map(|_i| Scalar::rand(&mut thread_rng()))
            .collect_vec();
        let t = r
            .iter()
            .enumerate()
            .map(|(j, r_j)| {
                let g_j = g * *r_j;
                let h_j = h * *r_j;
                let hash = &ro.evaluate(&(j, &g_j))[0..32];
                let t_j = hash
                    .iter()
                    .zip(r_j.to_byte_array())
                    .map(|(&x1, x2)| x1 ^ x2)
                    .collect();
                (h_j, t_j)
            })
            .collect_vec();

        let d = ro.evaluate(&(g, h, h_omega, &t));
        // d == 1^k with neg probability

        let u = (0..k)
            .map(|i| {
                if d[i / 8] & (1 << (i % 8)) == 0 {
                    Either::Left(g * r[i])
                } else {
                    Either::Right(r[i] - omega)
                }
            })
            .collect();

        Self { h, h_omega, t, u }
    }

    pub fn verify(&self, k: usize) -> FastCryptoResult<()> {
        let ro = RandomOracle::new("gadget");
        let g = Point::generator();

        if self.t.len() != k || self.u.len() != k {
            return Err(FastCryptoError::InvalidInput);
        }

        // We check all exponents in a batch
        let mut tuples_1 = Vec::new();
        let mut tuples_2 = Vec::new();

        let d = ro.evaluate(&(g, self.h, self.h_omega, &self.t));
        for i in 0..k {
            let bit = d[i / 8] & (1 << (i % 8));
            if bit == 0 {
                if let Either::Left(u_j) = self.u[i] {
                    let hash = &ro.evaluate(&(i, &u_j))[0..32];
                    // An opened tuple whose pad does not decode to a scalar is invalid
                    let r_j = unpad_scalar(hash, &self.t[i].1)?;
                    // check that g_j = g * r_j
                    tuples_1.push((r_j, u_j));
                    // check that t_j = h * r_j
                    tuples_2.push((r_j, self.t[i].0));
                } else {
                    return Err(FastCryptoError::InvalidProof);
                }
            } else {
                if let Either::Right(u_j) = self.u[i] {
                    tuples_2.push((u_j, self.t[i].0 - self.h_omega));
                } else {
                    return Err(FastCryptoError::InvalidProof);
                }
            }
        }
        verify_pairs(&g, &tuples_1, &mut thread_rng())?;
        verify_pairs(&self.h, &tuples_2, &mut thread_rng())
    }
    
    pub fn decrypt(&self, k: usize, g_omega: Point) -> FastCryptoResult<Scalar> {
        let ro = RandomOracle::new("gadget");
        let g = Point::generator();
        if self.t.len() != k || self.u.len() != k {
            return Err(FastCryptoError::InvalidInput);
        }
        let d = ro.evaluate(&(g, self.h, self.h_omega, &self.t));
        for i in 0..k {
            if d[i / 8] & (1 << (i % 8)) != 0 {
                if let Either::Right(diff) = self.u[i] {
                    // diff = r_i - omega, so g^{r_i} = g^diff * g^omega.
                    let g_ri = g * diff + g_omega;
                    let hash = &ro.evaluate(&(i, &g_ri))[0..32];
                    // A tuple whose pad does not decode is invalid. Skip it rather than fail,
                    // since a single valid unopened tuple suffices.
                    if let Ok(r_i) = unpad_scalar(hash, &self.t[i].1) {
                        if self.h * r_i == self.t[i].0 {
                            return Ok(r_i - diff);
                        }
                    }
                }
            }
        }
        Err(FastCryptoError::InvalidProof)
    }

    #[cfg(test)]
    pub fn t(&mut self) -> &mut Vec<(Point, Vec<u8>)> {
        &mut self.t
    }
}

//////// Low degree zk proof ////////

#[derive(Serialize)]
pub struct LDProof {
    x: Vec<[Point; 2]>,
    z: Poly<Scalar>,
}

impl LDProof {
    pub fn new(
        g1: &[Point],
        g2: &[Point],
        h1: &[Point],
        h2: &[Point],
        t: usize,
        w: &Poly<Scalar>,
    ) -> LDProof {
        assert!(g1.len() == g2.len());
        assert!(g1.len() == h1.len());
        assert!(g1.len() == h2.len());
        assert!(w.degree() <= t);

        let ro = RandomOracle::new("mldei");

        let r = Poly::rand(t as u16, &mut thread_rng());
        let r_values = eval_at_share_points(&r, g1.len() - 1);

        let x = g1
            .iter()
            .zip(g2.iter())
            .zip(r_values)
            .map(|((base1, base2), r_j)| [base1 * r_j, base2 * r_j])
            .collect_vec();

        // The evaluation points are fixed by the vector length, so they need not be hashed
        let e: Scalar = Scalar::hash_to_group_element(&ro.evaluate(&(g1, g2, h1, h2, t, &x)));
        let neg_e = -e;
        let z = r + &(w.clone() * &neg_e);

        LDProof { x, z }
    }

    pub fn verify(
        &self,
        g1: &[Point],
        g2: &[Point],
        h1: &[Point],
        h2: &[Point],
        t: usize,
    ) -> FastCryptoResult<()> {
        let ro = RandomOracle::new("mldei");
        let mut rng = thread_rng();

        if self.z.degree() > t {
            return Err(FastCryptoError::InvalidProof);
        }
        if self.x.is_empty() || self.x.len() != g1.len() {
            return Err(FastCryptoError::InvalidInput);
        }

        let e = Scalar::hash_to_group_element(&ro.evaluate(&(g1, g2, h1, h2, t, &self.x)));

        let r = (0..self.x.len())
            .map(|_| {
                [
                    Scalar::from(rng.next_u64() as u128),
                    Scalar::from(rng.next_u64() as u128),
                ]
            })
            .collect::<Vec<_>>();

        let z_values = eval_at_share_points(&self.z, self.x.len() - 1);

        let mut scalars = Vec::new();
        let mut points = Vec::new();

        let g = [g1, g2];
        let h = [h1, h2];

        for i in 0..self.x.len() {
            let z = z_values[i];
            for j in 0..2 {
                scalars.push(z * r[i][j]);
                points.push(g[j][i]);

                scalars.push(e * r[i][j]);
                points.push(h[j][i]);

                scalars.push(-r[i][j]);
                points.push(self.x[i][j]);
            }
        }

        let msm = Point::multi_scalar_mul(&scalars[..], &points[..]).expect("valid sizes");

        if msm == Point::zero() {
            return Ok(());
        } else {
            return Err(FastCryptoError::InvalidProof);
        }
    }

    #[cfg(test)]
    pub fn x(&mut self) -> &mut Vec<[Point; 2]> {
        &mut self.x
    }
}

// DLEQ proof (DDH-NIZK) for the unhappy path
#[derive(Serialize)]
pub struct DLEQProof {
    a: Point,
    b: Point,
    z: Scalar,
}

impl DLEQProof {
    pub fn new(x: &Scalar, g: &Point, h: &Point, x_g: &Point, x_h: &Point) -> Self {
        let ro = RandomOracle::new("rvss").extend("dleq");
        let r = Scalar::rand(&mut thread_rng());
        let a = g * r;
        let b = h * r;
        let c: Scalar = Scalar::hash_to_group_element(&ro.evaluate(&(g, h, x_g, x_h, &a, &b)));
        let z = r + c * x;
        Self { a, b, z }
    }

    pub fn verify(
        &self,
        g: &Point,
        h: &Point,
        x_g: &Point,
        x_h: &Point,
    ) -> FastCryptoResult<()> {
        let ro = RandomOracle::new("rvss").extend("dleq");
        let c: Scalar =
            Scalar::hash_to_group_element(&ro.evaluate(&(g, h, x_g, x_h, &self.a, &self.b)));
        if *g * self.z == self.a + *x_g * c && *h * self.z == self.b + *x_h * c {
            Ok(())
        } else {
            Err(FastCryptoError::InvalidProof)
        }
    }
}

//////// The RVSS protocol (share and verify) ////////

// Note: RVSS.Setup (Fig. 4) -- which generates each party's encryption keypair (sk_i, ek_i)
// together with a proof of knowledge PoK(sk_i, ek_i), and registers only keys with valid
// proofs -- is not implemented here. It is a small, one-time, per-party cost outside the
// Share/Verify hot path.
#[derive(Serialize)]
pub struct RVSS {
    v: Vec<Point>,
    c_hat: Vec<Point>,
    c: Vec<[u8; 32]>,
    gadget: Gadget,
    mldei_proof: LDProof,
}

impl RVSS {
    pub fn new(
        k: usize, // security parameter for the recovery gadget
        t: usize,
        omega: Scalar,
        pks: &[Point],
    ) -> RVSS {
        let ro = RandomOracle::new("rvss");
        let mut rng = thread_rng();
        let (g, h) = Self::bases();

        let poly = Poly::rand_fixed_c0(t as u16, omega, &mut rng);

        let mut v = Vec::new();
        let mut c = Vec::new();
        let mut c_hat = Vec::new();

        let shares = eval_at_share_points(&poly, pks.len());
        for (j, pk) in pks.iter().enumerate() {
            let s_j = shares[j + 1];
            let s_hat_j = g * s_j;
            let v_j = h * s_j;
            let c_hat_j = pk * s_j;
            let c_j: [u8; 32] = ro.evaluate(&(j, &s_hat_j))[0..32]
                .iter()
                .zip(&s_j.to_byte_array())
                .map(|(x1, &x2)| x1 ^ x2)
                .collect_vec()
                .try_into()
                .unwrap();

            v.push(v_j);
            c_hat.push(c_hat_j);
            c.push(c_j);
        }

        let gadget = Gadget::new(k, h, omega);
        let h_omega = h * omega; // v_0 = h^omega, the recovery gadget's commitment

        let (g1, g2, h1, h2) = Self::mldei_vectors(h, h_omega, pks, &c_hat, &v);
        // Evaluation points A = {0, share_point(0), ..., share_point(n-1)}, where point 0
        // carries v_0 = h^omega
        let mldei_proof = LDProof::new(&g1, &g2, &h1, &h2, t, &poly);

        RVSS {
            v,
            c_hat,
            c,
            gadget,
            mldei_proof,
        }
    }

    pub fn verify(&self, k: usize, t: usize, pks: &[Point]) -> FastCryptoResult<()> {
        let n = pks.len();
        if self.v.len() != n || self.c_hat.len() != n || self.c.len() != n {
            return Err(FastCryptoError::InvalidInput);
        }
        let (_g, h) = Self::bases();
        let (g1, g2, h1, h2) =
            Self::mldei_vectors(h, self.gadget.h_omega, pks, &self.c_hat, &self.v);
        self.mldei_proof.verify(&g1, &g2, &h1, &h2, t)?;
        self.gadget.verify(k)?;

        Ok(())
    }

    // To measure performance in the case of an honest dealer
    pub fn optimistic_decrypt(&self, i: usize, sk: &Scalar) -> FastCryptoResult<Scalar> {
        let ro = RandomOracle::new("rvss");
        let (_g, h) = Self::bases();
        let c_i = self.c[i];
        let c_hat_i = self.c_hat[i];
        let sk_inv = sk.inverse().unwrap();
        let s_hat_j = c_hat_i * sk_inv;

        let s_i = ro.evaluate(&(i, &s_hat_j))[0..32]
            .iter()
            .zip(&c_i)
            .map(|(x1, &x2)| x1 ^ x2)
            .collect_vec();
        let s_i = Scalar::from_byte_array(&s_i[0..32].try_into().unwrap())?;
        if h * s_i != self.v[i] {
            return Err(FastCryptoError::InvalidProof);
        }
        Ok(s_i)
    }

    pub fn decrypt_with_proof(
        &self,
        i: usize,
        sk: &Scalar,
        pk: &Point,
    ) -> (Point, DLEQProof) {
        let g = Point::generator();
        let s_hat_i = self.c_hat[i] * sk.inverse().unwrap();
        let proof = DLEQProof::new(sk, &g, &s_hat_i, pk, &self.c_hat[i]);
        (s_hat_i, proof)
    }

    pub fn verify_fraud_proof(
        &self,
        i: usize,
        s_hat_i: &Point,
        pk: &Point,
        proof: &DLEQProof,
    ) -> FastCryptoResult<()> {
        let g = Point::generator();
        proof.verify(&g, s_hat_i, pk, &self.c_hat[i])
    }

    // `indices` are 1-based party indices; party i's evaluation point is share_point(i - 1).
    // That equals w_N^bitrev_m(i - 1) for any domain size N = 2^m >= i, so all points are looked
    // up in the powers of w_N for the smallest such N instead of computing each one separately.
    fn lagrange_coeffs_for_c0(indices: &[usize]) -> Vec<Scalar> {
        let size = indices.iter().max().map_or(1, |&i| i.next_power_of_two());
        let log_size = size.trailing_zeros();
        let powers = domain_powers(log_size, size);
        let xs = indices
            .iter()
            .map(|&i| powers[bitrev(i - 1, log_size)])
            .collect_vec();
        xs.iter()
            .enumerate()
            .map(|(i, &xi)| {
                let mut num = Scalar::from(1u128);
                let mut den = Scalar::from(1u128);
                for (j, &xj) in xs.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    num = num * xj;
                    den = den * (xj - xi);
                }
                num * den.inverse().unwrap()
            })
            .collect_vec()
    }

    pub fn interpolate_in_exponent(
        indices: &[usize],
        points: &[Point],
    ) -> FastCryptoResult<Point> {
        let coeffs = Self::lagrange_coeffs_for_c0(indices);
        Point::multi_scalar_mul(&coeffs, points)
    }
    
    pub fn gadget_decrypt(&self, k: usize, g_omega: Point) -> FastCryptoResult<Scalar> {
        self.gadget.decrypt(k, g_omega)
    }

    /// Full unhappy-path reconstruction of omega: interpolate g^omega from the
    /// decrypted backup shares, then run gadget decryption.
    pub fn reconstruct(
        &self,
        k: usize,
        indices: &[usize],
        points: &[Point],
    ) -> FastCryptoResult<Scalar> {
        let g_omega = Self::interpolate_in_exponent(indices, points)?;
        self.gadget.decrypt(k, g_omega)
    }

    fn bases() -> (Point, Point) {
        let ro = RandomOracle::new("base");
        let g = Point::generator();
        let h = Point::hash_to_group_element(&ro.evaluate(&(g, g)));
        (g, h)
    }

    fn mldei_vectors(
        h: Point,
        h_omega: Point,
        pks: &[Point],
        c_hat: &[Point],
        v: &[Point],
    ) -> (Vec<Point>, Vec<Point>, Vec<Point>, Vec<Point>) {
        let g1 = std::iter::once(h).chain(pks.iter().copied()).collect_vec();
        let g2 = (0..=pks.len()).map(|_| h).collect_vec();
        let h1 = std::iter::once(h_omega).chain(c_hat.iter().copied()).collect_vec();
        let h2 = std::iter::once(h_omega).chain(v.iter().copied()).collect_vec();
        (g1, g2, h1, h2)
    }

    #[cfg(test)]
    pub fn c_hat(&mut self) -> &mut Vec<Point> {
        &mut self.c_hat
    }
}

//////// Evaluation points and FFT ////////

// Party j (0-based) gets the evaluation point w^bitrev32(j), where w is a primitive
// 2^TWO_ADICITY-th root of unity. For N = 2^m and j < N this equals w_N^bitrev_m(j) with
// w_N = w^(2^(32-m)), so the first N parties are exactly the N-th roots of unity and all shares
// can be computed with one radix-2 FFT. Only works for BLS12-381 (Ristretto255's scalar field
// has 2-adicity 2).
const TWO_ADICITY: u32 = 32;

// w = 7^((r-1)/2^32) in the BLS12-381 scalar field, big-endian
const ROOT_OF_UNITY: [u8; 32] = [
    0x16, 0xa2, 0xa1, 0x9e, 0xdf, 0xe8, 0x1f, 0x20, 0xd0, 0x9b, 0x68, 0x19, 0x22, 0xc8, 0x13, 0xb4,
    0xb6, 0x36, 0x83, 0x50, 0x8c, 0x22, 0x80, 0xb9, 0x38, 0x29, 0x97, 0x1f, 0x43, 0x9f, 0x0d, 0x2b,
];

// w^e by square-and-multiply
fn root_pow(mut e: u64) -> Scalar {
    let mut base = Scalar::from_byte_array(&ROOT_OF_UNITY).expect("valid scalar");
    let mut acc = Scalar::from(1u128);
    while e > 0 {
        if e & 1 == 1 {
            acc = acc * base;
        }
        base = base * base;
        e >>= 1;
    }
    acc
}

// Reverse the lowest `bits` bits of `i`
fn bitrev(i: usize, bits: u32) -> usize {
    (i as u32).reverse_bits().checked_shr(32 - bits).unwrap_or(0) as usize
}

// The first `count` powers of w_N, the primitive N-th root of unity for N = 2^log_size
fn domain_powers(log_size: u32, count: usize) -> Vec<Scalar> {
    assert!(log_size <= TWO_ADICITY);
    let w_n = root_pow(1u64 << (TWO_ADICITY - log_size));
    std::iter::successors(Some(Scalar::from(1u128)), |x| Some(*x * w_n))
        .take(count)
        .collect_vec()
}

// Party j's evaluation point, computed directly. The protocol code gets the same points from
// the FFT domain instead; this is the reference definition used by the tests.
#[cfg(test)]
fn share_point(j: usize) -> Scalar {
    root_pow(bitrev(j, TWO_ADICITY) as u64)
}

// Returns [poly(0), poly(share_point(0)), ..., poly(share_point(n-1))] using one radix-2 FFT
// over the smallest power-of-two domain that fits both the n parties and the coefficients.
fn eval_at_share_points(poly: &Poly<Scalar>, n: usize) -> Vec<Scalar> {
    let degree = poly.degree();
    let size = n.max(degree + 1).next_power_of_two();
    let log_size = size.trailing_zeros();
    assert!(log_size <= TWO_ADICITY);

    let mut a = vec![Scalar::zero(); size];
    for (i, c) in poly.as_vec().iter().take(degree + 1).enumerate() {
        a[bitrev(i, log_size)] = *c;
    }

    let twiddles = domain_powers(log_size, size / 2);

    // Iterative Cooley-Tukey. Afterwards a[k] = poly(w_N^k).
    let mut len = 2;
    while len <= size {
        let half = len / 2;
        let step = size / len;
        for chunk in a.chunks_mut(len) {
            for k in 0..half {
                let u = chunk[k];
                let v = chunk[k + half] * twiddles[k * step];
                chunk[k] = u + v;
                chunk[k + half] = u - v;
            }
        }
        len *= 2;
    }

    std::iter::once(*poly.c0())
        .chain((0..n).map(|j| a[bitrev(j, log_size)]))
        .collect()
}

// Multi-scalar multiplication that first merges repeated points by summing their scalars.
// Points are compared by their byte encoding. Logs the number of removed duplicates.
pub fn multi_scalar_mul_dedup(scalars: &[Scalar], points: &[Point]) -> FastCryptoResult<Point> {
    if scalars.len() != points.len() {
        return Err(FastCryptoError::InvalidInput);
    }
    let (dedup_points, dedup_scalars): (Vec<_>, Vec<_>) = points
        .iter()
        .zip(scalars)
        .map(|(p, s)| (p.to_byte_array(), (*p, *s)))
        .into_grouping_map()
        .fold_first(|(p, acc), _, (_, s)| (p, acc + s))
        .into_values()
        .unzip();
    let removed = points.len() - dedup_points.len();
    if removed > 0 {
        eprintln!(
            "multi_scalar_mul_dedup: deduplicated {} of {} points",
            removed,
            points.len()
        );
    }
    Point::multi_scalar_mul(&dedup_scalars, &dedup_points)
}

// Remove the one-time pad `pad` from `padded` and decode the result as a scalar. Fails if the
// lengths differ or the result is not the canonical encoding of an element of Z_q.
fn unpad_scalar(pad: &[u8], padded: &[u8]) -> FastCryptoResult<Scalar> {
    if pad.len() != padded.len() {
        return Err(FastCryptoError::InvalidInput);
    }
    let bytes: [u8; 32] = pad
        .iter()
        .zip(padded)
        .map(|(x1, x2)| x1 ^ x2)
        .collect_vec()
        .try_into()
        .map_err(|_| FastCryptoError::InvalidInput)?;
    Scalar::from_byte_array(&bytes)
}

// Following tests check the e2e functionalities and a few malformed inputs, not all edge cases

#[test]
fn test_multi_scalar_mul_dedup() {
    let g = Point::generator();
    let h = g * Scalar::rand(&mut thread_rng());
    let points = vec![g, h, g, g, h];
    let scalars = (0..points.len())
        .map(|_| Scalar::rand(&mut thread_rng()))
        .collect_vec();
    assert_eq!(
        multi_scalar_mul_dedup(&scalars, &points).unwrap(),
        Point::multi_scalar_mul(&scalars, &points).unwrap()
    );
}

#[test]
fn test_gadget() {
    let h = Point::generator();
    let omega = Scalar::rand(&mut thread_rng());
    let mut gadget = Gadget::new(128, h, omega);
    gadget.verify(128).unwrap();

    gadget.t()[0].0 = Point::generator();
    gadget.verify(128).unwrap_err();
}

// Build a gadget whose tuple 0 is malformed (under the correct key its pad decodes to
// 0xff..ff, which is not a canonical scalar) and is opened iff `opened`. The other tuples are
// valid.
#[cfg(test)]
fn gadget_with_malformed_tuple(k: usize, h: Point, omega: Scalar, opened: bool) -> Gadget {
    let ro = RandomOracle::new("gadget");
    let g = Point::generator();
    let h_omega = h * omega;
    loop {
        let r = (0..k)
            .map(|_| Scalar::rand(&mut thread_rng()))
            .collect_vec();
        let t = r
            .iter()
            .enumerate()
            .map(|(j, r_j)| {
                let hash = &ro.evaluate(&(j, &(g * *r_j)))[0..32];
                let plain = if j == 0 {
                    [0xff; 32]
                } else {
                    r_j.to_byte_array()
                };
                let t_j: Vec<u8> = hash.iter().zip(plain).map(|(&x1, x2)| x1 ^ x2).collect();
                (h * *r_j, t_j)
            })
            .collect_vec();
        let d = ro.evaluate(&(g, h, h_omega, &t));
        if (d[0] & 1 == 0) != opened {
            continue;
        }
        let u = (0..k)
            .map(|i| {
                if d[i / 8] & (1 << (i % 8)) == 0 {
                    Either::Left(g * r[i])
                } else {
                    Either::Right(r[i] - omega)
                }
            })
            .collect();
        return Gadget { h, h_omega, t, u };
    }
}

#[test]
fn test_gadget_malformed_input() {
    let k = 80;
    let (g, h) = RVSS::bases();
    let omega = Scalar::rand(&mut thread_rng());
    let g_omega = g * omega;

    gadget_with_malformed_tuple(k, h, omega, true)
        .verify(k)
        .unwrap_err();

    let gadget = gadget_with_malformed_tuple(k, h, omega, false);
    gadget.verify(k).unwrap();
    assert_eq!(gadget.decrypt(k, g_omega).unwrap(), omega);

    let mut gadget = Gadget::new(k, h, omega);
    gadget.u.pop();
    gadget.verify(k).unwrap_err();
    gadget.decrypt(k, g_omega).unwrap_err();
}

#[test]
fn test_mldei() {
    let bases1 = (1..=100)
        .map(|i| Point::generator() * Scalar::from(i as u128))
        .collect_vec();
    let bases2 = (1..=100)
        .map(|i| Point::generator() * Scalar::from(i as u128))
        .collect_vec();

    let t: usize = 31;
    let p = Poly::rand(t as u16, &mut thread_rng());
    let evals = eval_at_share_points(&p, 99);
    let exponents1 = (0..100).map(|i| bases1[i] * evals[i]).collect_vec();
    let exponents2 = (0..100).map(|i| bases2[i] * evals[i]).collect_vec();

    let mut proof = LDProof::new(&bases1, &bases2, &exponents1, &exponents2, t, &p);
    proof
        .verify(&bases1, &bases2, &exponents1, &exponents2, t)
        .unwrap();

    proof
        .verify(&bases1, &bases2, &exponents1, &exponents2, t + 1)
        .unwrap_err();

    proof.x()[0][0] = Point::generator();
    proof
        .verify(&bases1, &bases2, &exponents1, &exponents2, t)
        .unwrap_err();
}

#[test]
fn test_eval_at_share_points() {
    // w has order exactly 2^32
    assert_eq!(root_pow(1 << 31), -Scalar::from(1u128));

    // A party's point does not depend on the domain size it is looked up in
    for log_size in [0, 3, 7] {
        let powers = domain_powers(log_size, 1 << log_size);
        for j in 0..(1 << log_size) {
            assert_eq!(powers[bitrev(j, log_size)], share_point(j));
        }
    }

    for (t, n) in [(0, 1), (3, 5), (31, 100), (40, 20), (66, 64)] {
        let p = Poly::rand(t as u16, &mut thread_rng());
        let horner = |x: Scalar| {
            p.as_vec()
                .iter()
                .rev()
                .fold(Scalar::zero(), |acc, c| acc * x + c)
        };
        let expected = std::iter::once(Scalar::zero())
            .chain((0..n).map(share_point))
            .map(horner)
            .collect_vec();
        assert_eq!(eval_at_share_points(&p, n), expected);
    }
}

#[test]
fn test_rvss() {
    let k = 128;
    let n = 100;
    let t = (n / 3) * 2;

    let pks = (1..=n)
        .map(|i| Point::generator() * Scalar::from(i as u128))
        .collect_vec();

    let omega = Scalar::rand(&mut thread_rng());
    let mut rvss = RVSS::new(k, t, omega, &pks);
    rvss.verify(k, t, &pks).unwrap();

    rvss.optimistic_decrypt(10, &Scalar::from(11u128)).unwrap();

    rvss.c_hat()[0] = Point::generator();
    rvss.verify(k, t, &pks).unwrap_err();

    let mut rvss = RVSS::new(k, t, omega, &pks);
    rvss.v.pop();
    rvss.verify(k, t, &pks).unwrap_err();
}

#[test]
fn test_dleq() {
    let g = Point::generator();
    let h = Point::generator() * Scalar::from(7u128);
    let x = Scalar::rand(&mut thread_rng());
    let x_g = g * x;
    let x_h = h * x;

    let proof = DLEQProof::new(&x, &g, &h, &x_g, &x_h);
    proof.verify(&g, &h, &x_g, &x_h).unwrap();

    let bad = g * Scalar::rand(&mut thread_rng());
    proof.verify(&g, &h, &bad, &x_h).unwrap_err();
}

#[test]
fn test_unhappy_reconstruct() {
    let k = 128;
    let n = 100;
    let t = (n / 3) * 2;

    let sk = (1..=n).map(|i| Scalar::from(i as u128)).collect_vec();
    let pks = sk.iter().map(|s| Point::generator() * s).collect_vec();

    let omega = Scalar::rand(&mut thread_rng());
    let rvss = RVSS::new(k, t, omega, &pks);

    let num = t + 1;
    let mut indices = Vec::new();
    let mut points = Vec::new();
    for i in 0..num {
        let (s_hat_i, proof) = rvss.decrypt_with_proof(i, &sk[i], &pks[i]);
        rvss.verify_fraud_proof(i, &s_hat_i, &pks[i], &proof).unwrap();
        indices.push(i + 1);
        points.push(s_hat_i);
    }

    let recovered = rvss.reconstruct(k, &indices, &points).unwrap();
    assert_eq!(recovered, omega);
}
