//! Dense univariate polynomials over Goldilocks, coefficients lowest-degree first.

use crate::field::Fp;
use crate::ntt;
use std::ops::{Add, Neg, Sub};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Poly {
    /// coeffs[i] is the coefficient of x^i. No trailing zeros; zero poly is `[]`.
    pub coeffs: Vec<Fp>,
}

impl Poly {
    pub fn new(mut coeffs: Vec<Fp>) -> Self {
        while coeffs.last() == Some(&Fp::ZERO) {
            coeffs.pop();
        }
        Poly { coeffs }
    }

    pub fn zero() -> Self {
        Poly { coeffs: vec![] }
    }

    pub fn constant(c: Fp) -> Self {
        Poly::new(vec![c])
    }

    /// The monic linear polynomial (x - root).
    pub fn linear_factor(root: Fp) -> Self {
        Poly::new(vec![-root, Fp::ONE])
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() { None } else { Some(self.coeffs.len() - 1) }
    }

    /// Horner evaluation.
    pub fn eval(&self, x: Fp) -> Fp {
        let mut acc = Fp::ZERO;
        for &c in self.coeffs.iter().rev() {
            acc = acc * x + c;
        }
        acc
    }

    pub fn scale(&self, c: Fp) -> Poly {
        Poly::new(self.coeffs.iter().map(|&x| x * c).collect())
    }

    /// O(n^2) multiplication, kept to cross-check the NTT path in tests.
    pub fn naive_mul(&self, other: &Poly) -> Poly {
        if self.is_zero() || other.is_zero() {
            return Poly::zero();
        }
        let mut result = vec![Fp::ZERO; self.coeffs.len() + other.coeffs.len() - 1];
        for (i, &a) in self.coeffs.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, &b) in other.coeffs.iter().enumerate() {
                result[i + j] += a * b;
            }
        }
        Poly::new(result)
    }

    /// NTT-based multiplication.
    pub fn mul(&self, other: &Poly) -> Poly {
        ntt::poly_mul_ntt(self, other)
    }

    /// Long division: `self = quotient * divisor + remainder`.
    pub fn div_rem(&self, divisor: &Poly) -> (Poly, Poly) {
        assert!(!divisor.is_zero(), "division by the zero polynomial");
        let div_deg = divisor.degree().unwrap();
        let lead_inv = divisor.coeffs[div_deg]
            .inv()
            .expect("leading coefficient is nonzero by construction");

        let mut remainder = self.coeffs.clone();
        if remainder.len() <= div_deg {
            return (Poly::zero(), Poly::new(remainder));
        }

        let mut quotient = vec![Fp::ZERO; remainder.len() - div_deg];
        for i in (0..quotient.len()).rev() {
            let coeff = remainder[i + div_deg] * lead_inv;
            quotient[i] = coeff;
            if !coeff.is_zero() {
                for (j, &dj) in divisor.coeffs.iter().enumerate() {
                    remainder[i + j] -= coeff * dj;
                }
            }
        }
        (Poly::new(quotient), Poly::new(remainder))
    }

    /// Lagrange interpolation through arbitrary (x, y) pairs. O(n^2)
    pub fn interpolate(points: &[(Fp, Fp)]) -> Poly {
        let mut result = Poly::zero();
        for (i, &(xi, yi)) in points.iter().enumerate() {
            let mut basis = Poly::constant(Fp::ONE);
            let mut denom = Fp::ONE;
            for (j, &(xj, _)) in points.iter().enumerate() {
                if i == j {
                    continue;
                }
                basis = basis.naive_mul(&Poly::linear_factor(xj));
                denom *= xi - xj;
            }
            let scale = yi * denom.inv().expect("duplicate x-coordinate in interpolation points");
            result = &result + &basis.scale(scale);
        }
        result
    }
}

impl Add<&Poly> for &Poly {
    type Output = Poly;
    fn add(self, rhs: &Poly) -> Poly {
        let len = self.coeffs.len().max(rhs.coeffs.len());
        let mut result = vec![Fp::ZERO; len];
        for (i, &c) in self.coeffs.iter().enumerate() {
            result[i] += c;
        }
        for (i, &c) in rhs.coeffs.iter().enumerate() {
            result[i] += c;
        }
        Poly::new(result)
    }
}

impl Sub<&Poly> for &Poly {
    type Output = Poly;
    fn sub(self, rhs: &Poly) -> Poly {
        let len = self.coeffs.len().max(rhs.coeffs.len());
        let mut result = vec![Fp::ZERO; len];
        for (i, &c) in self.coeffs.iter().enumerate() {
            result[i] += c;
        }
        for (i, &c) in rhs.coeffs.iter().enumerate() {
            result[i] -= c;
        }
        Poly::new(result)
    }
}

impl Neg for &Poly {
    type Output = Poly;
    fn neg(self) -> Poly {
        Poly::new(self.coeffs.iter().map(|&c| -c).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn arb_fp() -> impl Strategy<Value = Fp> {
        (0..crate::field::P).prop_map(Fp)
    }

    fn arb_poly(len_range: std::ops::Range<usize>) -> impl Strategy<Value = Poly> {
        proptest::collection::vec(arb_fp(), len_range).prop_map(Poly::new)
    }

    #[test]
    fn eval_matches_hand_computation() {
        // p(x) = 3 + 2x + x^2
        let p = Poly::new(vec![Fp::new(3), Fp::new(2), Fp::new(1)]);
        assert_eq!(p.eval(Fp::new(5)), Fp::new(3 + 2 * 5 + 25));
    }

    #[test]
    fn trailing_zero_coeffs_are_trimmed() {
        let p = Poly::new(vec![Fp::new(1), Fp::new(2), Fp::ZERO, Fp::ZERO]);
        assert_eq!(p.degree(), Some(1));
    }

    #[test]
    fn div_rem_reconstructs_dividend() {
        // (x^2 - 1) / (x - 1) = x + 1, remainder 0
        let dividend = Poly::new(vec![-Fp::ONE, Fp::ZERO, Fp::ONE]);
        let divisor = Poly::linear_factor(Fp::ONE);
        let (q, r) = dividend.div_rem(&divisor);
        assert_eq!(q, Poly::new(vec![Fp::ONE, Fp::ONE]));
        assert!(r.is_zero());
    }

    #[test]
    fn div_rem_with_nonzero_remainder() {
        // (x^2 + 1) / (x - 1): quotient x+1, remainder 2
        let dividend = Poly::new(vec![Fp::ONE, Fp::ZERO, Fp::ONE]);
        let divisor = Poly::linear_factor(Fp::ONE);
        let (q, r) = dividend.div_rem(&divisor);
        let reconstructed = &q.naive_mul(&divisor) + &r;
        assert_eq!(reconstructed, dividend);
    }

    #[test]
    fn interpolate_recovers_known_polynomial() {
        // p(x) = x^2
        let points: Vec<(Fp, Fp)> = (0..5)
            .map(|x| (Fp::new(x), Fp::new(x * x)))
            .collect();
        let p = Poly::interpolate(&points);
        for x in 0..10u64 {
            assert_eq!(p.eval(Fp::new(x)), Fp::new(x * x));
        }
    }

    proptest! {
        #[test]
        fn add_then_sub_roundtrips(a in arb_poly(0..6), b in arb_poly(0..6)) {
            let sum = &a + &b;
            prop_assert_eq!(&sum - &b, a);
        }

        #[test]
        fn div_rem_satisfies_division_identity(a in arb_poly(0..8), b in arb_poly(1..5)) {
            if !b.is_zero() {
                let (q, r) = a.div_rem(&b);
                if let Some(rd) = r.degree() {
                    prop_assert!(rd < b.degree().unwrap());
                }
                let reconstructed = &q.naive_mul(&b) + &r;
                prop_assert_eq!(reconstructed, a);
            }
        }
    }
}
