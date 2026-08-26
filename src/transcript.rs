//! Fiat-Shamir: challenges derived by hashing everything absorbed so far.
//!
//! A blake3 sponge — squeezing re-absorbs its output, so two squeezes never repeat.

use crate::field::{Fp, P};

pub struct Transcript {
    hasher: blake3::Hasher,
}

impl Transcript {
    /// `label` domain-separates this from transcripts of other protocols.
    pub fn new(label: &[u8]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(label);
        Transcript { hasher }
    }

    pub fn absorb_bytes(&mut self, data: &[u8]) {
        self.hasher.update(data);
    }

    pub fn absorb_fp(&mut self, x: Fp) {
        self.absorb_bytes(&x.0.to_le_bytes());
    }

    pub fn absorb_fps(&mut self, xs: &[Fp]) {
        for &x in xs {
            self.absorb_fp(x);
        }
    }

    pub fn absorb_digest(&mut self, digest: &[u8; 32]) {
        self.absorb_bytes(digest);
    }

    /// Reads pseudorandom bytes, then folds them back in so the next squeeze differs.
    fn squeeze(&mut self, out: &mut [u8]) {
        let mut xof = self.hasher.finalize_xof();
        xof.fill(out);
        self.hasher.update(out);
    }

    pub fn challenge_bytes(&mut self, n: usize) -> Vec<u8> {
        let mut out = vec![0u8; n];
        self.squeeze(&mut out);
        out
    }

    /// Uniform field element via rejection sampling, seeded from the transcript.
    pub fn challenge_fp(&mut self) -> Fp {
        loop {
            let mut buf = [0u8; 8];
            self.squeeze(&mut buf);
            let bits = u64::from_le_bytes(buf);
            if bits < P {
                return Fp(bits);
            }
        }
    }

    pub fn challenge_fps(&mut self, n: usize) -> Vec<Fp> {
        (0..n).map(|_| self.challenge_fp()).collect()
    }

    /// Uniform index in `0..bound`. Power-of-two `bound`, so masking is exact.
    pub fn challenge_index(&mut self, bound: usize) -> usize {
        assert!(bound.is_power_of_two(), "challenge_index requires a power-of-two bound");
        let mut buf = [0u8; 8];
        self.squeeze(&mut buf);
        (u64::from_le_bytes(buf) as usize) & (bound - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_transcript_is_deterministic() {
        let mut t1 = Transcript::new(b"test");
        t1.absorb_fp(Fp::new(42));
        let c1 = t1.challenge_fp();

        let mut t2 = Transcript::new(b"test");
        t2.absorb_fp(Fp::new(42));
        let c2 = t2.challenge_fp();

        assert_eq!(c1, c2);
    }

    #[test]
    fn different_absorbed_data_gives_different_challenges() {
        let mut t1 = Transcript::new(b"test");
        t1.absorb_fp(Fp::new(42));

        let mut t2 = Transcript::new(b"test");
        t2.absorb_fp(Fp::new(43));

        assert_ne!(t1.challenge_fp(), t2.challenge_fp());
    }

    #[test]
    fn different_labels_give_different_challenges() {
        let mut t1 = Transcript::new(b"protocol-a");
        let mut t2 = Transcript::new(b"protocol-b");
        assert_ne!(t1.challenge_fp(), t2.challenge_fp());
    }

    #[test]
    fn successive_challenges_differ() {
        let mut t = Transcript::new(b"test");
        let c1 = t.challenge_fp();
        let c2 = t.challenge_fp();
        let c3 = t.challenge_fp();
        assert_ne!(c1, c2);
        assert_ne!(c2, c3);
    }

    #[test]
    fn challenge_fp_is_canonical() {
        let mut t = Transcript::new(b"test");
        for _ in 0..200 {
            assert!(t.challenge_fp().0 < P);
        }
    }

    #[test]
    fn challenge_index_respects_bound() {
        let mut t = Transcript::new(b"test");
        for _ in 0..200 {
            let idx = t.challenge_index(64);
            assert!(idx < 64);
        }
    }

    #[test]
    fn transcript_order_matters() {
        let mut t1 = Transcript::new(b"test");
        t1.absorb_fp(Fp::new(1));
        t1.absorb_fp(Fp::new(2));

        let mut t2 = Transcript::new(b"test");
        t2.absorb_fp(Fp::new(2));
        t2.absorb_fp(Fp::new(1));

        assert_ne!(t1.challenge_fp(), t2.challenge_fp());
    }
}
