//! NTT over Goldilocks: fast multiplication, subgroup interpolation, coset LDE.
//!
//! `p - 1 = 2^32 * (2^32 - 1)`, so F_p* has a subgroup of order 2^k for every k <= 32.

use crate::field::{Fp, P};
use crate::poly::Poly;

const MULTIPLICATIVE_GENERATOR: Fp = Fp(7);
pub const TWO_ADICITY: u32 = 32;

/// A primitive 2^log_n-th root of unity.
pub fn root_of_unity(log_n: u32) -> Fp {
    assert!(
        log_n <= TWO_ADICITY,
        "domain size 2^{log_n} exceeds Goldilocks's 2-adicity of {TWO_ADICITY}"
    );
    let root_max = MULTIPLICATIVE_GENERATOR.pow((P - 1) >> TWO_ADICITY);
    root_max.pow(1u64 << (TWO_ADICITY - log_n))
}

/// The evaluation domain {w^0, w^1, ..., w^(n-1)} for n = 2^log_n.
pub fn domain(log_n: u32) -> Vec<Fp> {
    let n = 1usize << log_n;
    let w = root_of_unity(log_n);
    let mut result = Vec::with_capacity(n);
    let mut cur = Fp::ONE;
    for _ in 0..n {
        result.push(cur);
        cur *= w;
    }
    result
}

pub fn coset_domain(log_n: u32, offset: Fp) -> Vec<Fp> {
    domain(log_n).into_iter().map(|w_i| offset * w_i).collect()
}

fn bit_reverse_permute(a: &mut [Fp]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let bits = n.trailing_zeros();
    for i in 0..n {
        let j = ((i as u32).reverse_bits() >> (32 - bits)) as usize;
        if i < j {
            a.swap(i, j);
        }
    }
}

/// Iterative in-place Cooley-Tukey (I)NTT. `a.len()` must be a power of two.
fn ntt_core(a: &mut [Fp], invert: bool) {
    let n = a.len();
    assert!(n.is_power_of_two() && n > 0, "NTT length must be a nonzero power of two");
    bit_reverse_permute(a);

    let mut len = 2usize;
    while len <= n {
        let mut w_len = root_of_unity(len.trailing_zeros());
        if invert {
            w_len = w_len.inv().expect("root of unity is never zero");
        }
        let half = len / 2;
        for chunk in a.chunks_mut(len) {
            let mut w = Fp::ONE;
            for i in 0..half {
                let u = chunk[i];
                let v = chunk[i + half] * w;
                chunk[i] = u + v;
                chunk[i + half] = u - v;
                w *= w_len;
            }
        }
        len <<= 1;
    }

    if invert {
        let n_inv = Fp::new(n as u64).inv().expect("n < p, so it's invertible");
        for x in a.iter_mut() {
            *x *= n_inv;
        }
    }
}

/// In-place forward NTT: coefficients -> evaluations at `domain(log2(n))`.
pub fn ntt(a: &mut [Fp]) {
    ntt_core(a, false);
}

/// In-place inverse NTT: evaluations at `domain(log2(n))` -> coefficients.
pub fn intt(a: &mut [Fp]) {
    ntt_core(a, true);
}

/// Subgroup evaluations -> polynomial. `evals.len()` must be a power of two.
pub fn interpolate_subgroup(evals: &[Fp]) -> Poly {
    let mut coeffs = evals.to_vec();
    intt(&mut coeffs);
    Poly::new(coeffs)
}

/// Multiplies via NTT: pad to a power of two, transform, multiply pointwise, invert.
pub fn poly_mul_ntt(a: &Poly, b: &Poly) -> Poly {
    if a.is_zero() || b.is_zero() {
        return Poly::zero();
    }
    let result_len = a.coeffs.len() + b.coeffs.len() - 1;
    let n = result_len.next_power_of_two();

    let mut fa = a.coeffs.clone();
    fa.resize(n, Fp::ZERO);
    let mut fb = b.coeffs.clone();
    fb.resize(n, Fp::ZERO);

    ntt(&mut fa);
    ntt(&mut fb);
    for i in 0..n {
        fa[i] *= fb[i];
    }
    intt(&mut fa);

    fa.truncate(result_len);
    Poly::new(fa)
}

/// Evaluates `poly` over the coset `{offset * w^i}` without going point-by-point.
pub fn coset_lde(poly: &Poly, log_l: u32, offset: Fp) -> Vec<Fp> {
    let l = 1usize << log_l;
    assert!(
        poly.coeffs.len() <= l,
        "LDE domain (2^{log_l}) must be at least as large as the polynomial"
    );

    let mut coeffs = Vec::with_capacity(l);
    let mut offset_pow = Fp::ONE;
    for &c in &poly.coeffs {
        coeffs.push(c * offset_pow);
        offset_pow *= offset;
    }
    coeffs.resize(l, Fp::ZERO);

    ntt(&mut coeffs);
    coeffs
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn arb_fp() -> impl Strategy<Value = Fp> {
        (0..P).prop_map(Fp)
    }

    #[test]
    fn generator_has_full_2_adic_order() {
        let half = MULTIPLICATIVE_GENERATOR.pow((P - 1) / 2);
        assert_ne!(half, Fp::ONE, "generator is a QR; can't derive a 2^32 root of unity from it");
    }

    #[test]
    fn root_of_unity_has_claimed_order() {
        for log_n in [1u32, 2, 3, 8, 16] {
            let w = root_of_unity(log_n);
            let n = 1u64 << log_n;
            assert_eq!(w.pow(n), Fp::ONE, "w^n != 1 for log_n={log_n}");
            assert_ne!(w.pow(n / 2), Fp::ONE, "w has order dividing n/2 for log_n={log_n}");
        }
    }

    #[test]
    fn ntt_intt_roundtrip() {
        let mut a: Vec<Fp> = (0..16u64).map(Fp::new).collect();
        let original = a.clone();
        ntt(&mut a);
        intt(&mut a);
        assert_eq!(a, original);
    }

    #[test]
    fn ntt_matches_naive_evaluation() {
        let coeffs: Vec<Fp> = (1..=8u64).map(Fp::new).collect();
        let poly = Poly::new(coeffs.clone());
        let mut transformed = coeffs;
        ntt(&mut transformed);

        let dom = domain(3); // log_n = 3 -> n = 8
        for (i, &x) in dom.iter().enumerate() {
            assert_eq!(transformed[i], poly.eval(x), "mismatch at domain point {i}");
        }
    }

    #[test]
    fn interpolate_subgroup_inverts_ntt() {
        let poly = Poly::new((0..8u64).map(Fp::new).collect());
        let evals = coset_lde(&poly, 3, Fp::ONE); // offset=1 => plain subgroup domain
        let recovered = interpolate_subgroup(&evals);
        assert_eq!(recovered, poly);
    }

    #[test]
    fn coset_lde_matches_naive_evaluation() {
        let poly = Poly::new((0..5u64).map(Fp::new).collect());
        let offset = Fp::new(7);
        let log_l = 4; // extend a degree-4 poly onto a size-16 coset
        let evals = coset_lde(&poly, log_l, offset);
        let dom = coset_domain(log_l, offset);
        for (i, &x) in dom.iter().enumerate() {
            assert_eq!(evals[i], poly.eval(x), "mismatch at coset point {i}");
        }
    }

    proptest! {
        #[test]
        fn poly_mul_ntt_matches_naive(
            a in proptest::collection::vec(arb_fp(), 0..12),
            b in proptest::collection::vec(arb_fp(), 0..12),
        ) {
            let pa = Poly::new(a);
            let pb = Poly::new(b);
            prop_assert_eq!(poly_mul_ntt(&pa, &pb), pa.naive_mul(&pb));
        }
    }
}
