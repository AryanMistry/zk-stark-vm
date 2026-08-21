//! The Goldilocks field: F_p for p = 2^64 - 2^32 + 1.
//!
//! This prime is used by Plonky2/Winterfell because it fits in a u64 while
//! still admitting a specialized reduction (no generic 128-bit `%`), and its
//! multiplicative group has 2-adicity 32 (a subgroup of order 2^32), which is
//! exactly what NTT-based polynomial arithmetic needs later.
//!
//! Reduction derivation: since p = 2^64 - 2^32 + 1, we have 2^64 = p + (2^32 - 1),
//! so 2^64 mod p = 2^32 - 1. Writing EPSILON = 2^32 - 1, every time a computation
//! would carry a factor of 2^64, that factor can be replaced by EPSILON instead of
//! doing a full division.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub const P: u64 = 0xFFFF_FFFF_0000_0001; // 2^64 - 2^32 + 1
const EPSILON: u64 = (1u64 << 32) - 1; // 2^64 mod P

#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct Fp(pub u64);

impl Fp {
    pub const ZERO: Fp = Fp(0);
    pub const ONE: Fp = Fp(1);

    #[inline]
    pub fn new(value: u64) -> Self {
        if value < P { Fp(value) } else { Fp(value - P) }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    pub fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Fp::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc *= base;
            }
            base = base * base;
            exp >>= 1;
        }
        acc
    }

    /// Multiplicative inverse via Fermat's little theorem: a^(p-2) = a^-1.
    pub fn inv(self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(self.pow(P - 2))
        }
    }

    /// Reduces a 128-bit product into a canonical field element.
    ///
    /// Splits x = x_hi * 2^64 + x_lo, then x_hi = x_hi_hi * 2^32 + x_hi_lo.
    /// Using 2^64 ≡ EPSILON (mod p) twice gives:
    ///   x ≡ x_lo - x_hi_hi + x_hi_lo * EPSILON  (mod p)
    #[inline]
    fn reduce128(x: u128) -> Self {
        let x_lo = x as u64;
        let x_hi = (x >> 64) as u64;
        let x_hi_hi = x_hi >> 32;
        let x_hi_lo = x_hi & EPSILON;

        // t0 = x_lo - x_hi_hi (mod p); x_hi_hi < 2^32 so this underflows at most once.
        let (diff, borrow) = x_lo.overflowing_sub(x_hi_hi);
        let t0 = if borrow { diff.wrapping_sub(EPSILON) } else { diff };

        // t1 = x_hi_lo * EPSILON; both factors < 2^32 so this fits in u64 with room to spare.
        let t1 = x_hi_lo * EPSILON;

        let (sum, overflow) = t0.overflowing_add(t1);
        let mut result = if overflow { sum.wrapping_add(EPSILON) } else { sum };

        if result >= P {
            result -= P;
        }
        Fp(result)
    }

    /// Samples a uniformly random field element.
    pub fn random(rng: &mut impl rand::Rng) -> Self {
        loop {
            let bits = rng.random::<u64>();
            if bits < P {
                return Fp(bits);
            }
        }
    }
}

/// Inverts every element of `values` (all must be nonzero) using Montgomery's
/// batch inversion trick.
pub fn batch_inverse(values: &[Fp]) -> Vec<Fp> {
    let n = values.len();
    let mut prefix = Vec::with_capacity(n);
    let mut acc = Fp::ONE;
    for &v in values {
        prefix.push(acc);
        acc *= v;
    }
    let mut acc_inv = acc.inv().expect("batch_inverse requires every input to be nonzero");

    let mut result = vec![Fp::ZERO; n];
    for i in (0..n).rev() {
        result[i] = prefix[i] * acc_inv;
        acc_inv *= values[i];
    }
    result
}

impl Add for Fp {
    type Output = Fp;
    #[inline]
    fn add(self, rhs: Fp) -> Fp {
        let (sum, overflow) = self.0.overflowing_add(rhs.0);
        let mut result = if overflow { sum.wrapping_add(EPSILON) } else { sum };
        if result >= P {
            result -= P;
        }
        Fp(result)
    }
}

impl Sub for Fp {
    type Output = Fp;
    #[inline]
    fn sub(self, rhs: Fp) -> Fp {
        let (diff, borrow) = self.0.overflowing_sub(rhs.0);
        let result = if borrow { diff.wrapping_add(P) } else { diff };
        Fp(result)
    }
}

impl Neg for Fp {
    type Output = Fp;
    #[inline]
    fn neg(self) -> Fp {
        Fp::ZERO - self
    }
}

impl Mul for Fp {
    type Output = Fp;
    #[inline]
    fn mul(self, rhs: Fp) -> Fp {
        Fp::reduce128((self.0 as u128) * (rhs.0 as u128))
    }
}

impl AddAssign for Fp {
    fn add_assign(&mut self, rhs: Fp) {
        *self = *self + rhs;
    }
}
impl SubAssign for Fp {
    fn sub_assign(&mut self, rhs: Fp) {
        *self = *self - rhs;
    }
}
impl MulAssign for Fp {
    fn mul_assign(&mut self, rhs: Fp) {
        *self = *self * rhs;
    }
}

impl From<u64> for Fp {
    fn from(v: u64) -> Self {
        Fp::new(v)
    }
}

impl fmt::Debug for Fp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Fp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for Fp {
    fn default() -> Self {
        Fp::ZERO
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// A slow-but-obviously-correct reference reduction, used only to
    /// cross-check the fast path in tests.
    fn naive_reduce(x: u128) -> u64 {
        (x % (P as u128)) as u64
    }

    fn arb_fp() -> impl Strategy<Value = Fp> {
        (0..P).prop_map(Fp)
    }

    #[test]
    fn basic_arithmetic() {
        let a = Fp::new(5);
        let b = Fp::new(3);
        assert_eq!((a + b).0, 8);
        assert_eq!((a - b).0, 2);
        assert_eq!((a * b).0, 15);
        assert_eq!((b - a).0, P - 2); // wraps around
    }

    #[test]
    fn zero_and_one_identities_fixed() {
        let a = Fp::new(123456789);
        assert_eq!(a + Fp::ZERO, a);
        assert_eq!(a * Fp::ONE, a);
        assert_eq!(a * Fp::ZERO, Fp::ZERO);
    }

    #[test]
    fn edge_values() {
        let max = Fp(P - 1);
        assert_eq!(max + Fp::ONE, Fp::ZERO); // wraps at the modulus
        assert_eq!(Fp::ZERO - Fp::ONE, max);
        assert_eq!(max * max, Fp::ONE); // (-1) * (-1) = 1
    }

    #[test]
    fn batch_inverse_matches_individual_inverses() {
        let values: Vec<Fp> = (1..=20u64).map(Fp::new).collect();
        let batched = batch_inverse(&values);
        for (v, inv) in values.iter().zip(&batched) {
            assert_eq!(*inv, v.inv().unwrap());
        }
    }

    #[test]
    fn batch_inverse_of_empty_is_empty() {
        assert!(batch_inverse(&[]).is_empty());
    }

    #[test]
    fn inverse_of_zero_is_none() {
        assert!(Fp::ZERO.inv().is_none());
    }

    proptest! {
        #[test]
        fn add_matches_naive(a in 0u64..P, b in 0u64..P) {
            let expected = naive_reduce(a as u128 + b as u128);
            prop_assert_eq!((Fp(a) + Fp(b)).0, expected);
        }

        #[test]
        fn sub_matches_naive(a in 0u64..P, b in 0u64..P) {
            let expected = naive_reduce(a as u128 + P as u128 - b as u128);
            prop_assert_eq!((Fp(a) - Fp(b)).0, expected);
        }

        #[test]
        fn mul_matches_naive(a in 0u64..P, b in 0u64..P) {
            let expected = naive_reduce(a as u128 * b as u128);
            prop_assert_eq!((Fp(a) * Fp(b)).0, expected);
        }

        #[test]
        fn add_commutative(a in arb_fp(), b in arb_fp()) {
            prop_assert_eq!(a + b, b + a);
        }

        #[test]
        fn add_associative(a in arb_fp(), b in arb_fp(), c in arb_fp()) {
            prop_assert_eq!((a + b) + c, a + (b + c));
        }

        #[test]
        fn mul_commutative(a in arb_fp(), b in arb_fp()) {
            prop_assert_eq!(a * b, b * a);
        }

        #[test]
        fn mul_associative(a in arb_fp(), b in arb_fp(), c in arb_fp()) {
            prop_assert_eq!((a * b) * c, a * (b * c));
        }

        #[test]
        fn distributive(a in arb_fp(), b in arb_fp(), c in arb_fp()) {
            prop_assert_eq!(a * (b + c), a * b + a * c);
        }

        #[test]
        fn additive_inverse(a in arb_fp()) {
            prop_assert_eq!(a + (-a), Fp::ZERO);
        }

        #[test]
        fn multiplicative_inverse(a in arb_fp()) {
            if !a.is_zero() {
                let inv = a.inv().unwrap();
                prop_assert_eq!(a * inv, Fp::ONE);
            }
        }

        #[test]
        fn sub_then_add_roundtrips(a in arb_fp(), b in arb_fp()) {
            prop_assert_eq!((a - b) + b, a);
        }

        #[test]
        fn batch_inverse_matches_naive(values in proptest::collection::vec(1u64..P, 1..30)) {
            let fps: Vec<Fp> = values.into_iter().map(Fp::new).collect();
            let batched = batch_inverse(&fps);
            let naive: Vec<Fp> = fps.iter().map(|v| v.inv().unwrap()).collect();
            prop_assert_eq!(batched, naive);
        }
    }
}
