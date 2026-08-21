//! FRI (Fast Reed-Solomon IOP of Proximity): proves that a claimed table of
//! evaluations is close to *some* polynomial of a target low degree, without
//! revealing the polynomial.
//!
//! The idea: split f(x) = f_even(x^2) + x * f_odd(x^2). Given a random
//! challenge beta, the "folded" polynomial f'(y) = f_even(y) + beta*f_odd(y)
//! has half the degree of f, and — crucially — f' can be evaluated at y=x^2
//! using only f(x) and f(-x):
//!
//!   f_even(x^2) = (f(x) + f(-x)) / 2
//!   f_odd(x^2)  = (f(x) - f(-x)) / (2x)
//!
//! So the prover can fold a whole evaluation table in half, layer by layer,
//! without ever reconstructing the polynomial's coefficients. Each layer is
//! Merkle-committed; the folding challenge for layer l is drawn from the
//! transcript *after* committing layer l, so the prover can't choose evals
//! to fit a challenge it already knows (Fiat-Shamir).
//!
//! Folding stops once the claimed degree bound reaches 1 (constant), at
//! which point the remaining evaluations should all be equal — that's the
//! base case the whole recursion bottoms out on, and it's checked directly
//! instead of via a Merkle commitment.
//!
//! The domain halves alongside the polynomial: if x ranges over a coset
//! {offset * w^i} of a order-n subgroup, then x^2 ranges over the coset
//! {offset^2 * (w^2)^i} of the order-n/2 subgroup, and w^(n/2) = -1 gives
//! the (x, -x) pairing used above (indices i and i + n/2).

use crate::field::Fp;
use crate::merkle::{Digest, MerkleProof, MerkleTree};
use crate::transcript::Transcript;
use serde::{Deserialize, Serialize};

pub struct FriConfig {
    /// Rate = 1 / blowup_factor. Must be a power of two. Folding stops once
    /// the evaluation table shrinks to exactly this size (degree bound 1).
    pub blowup_factor: usize,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FriStepOpening {
    pub even: Fp,
    pub odd: Fp,
    pub even_proof: MerkleProof,
    pub odd_proof: MerkleProof,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FriProof {
    pub layer_roots: Vec<Digest>,
    pub final_evals: Vec<Fp>,
    /// Outer index: query. Inner index: layer.
    pub query_proofs: Vec<Vec<FriStepOpening>>,
}

/// Takes `x`'s inverse directly rather than computing it internally, so
/// callers folding a whole layer can batch-invert every point's `x` in one
/// pass instead of paying for `half` separate Fermat inversions.
fn fold_pair(f_x: Fp, f_neg_x: Fp, x_inv: Fp, beta: Fp) -> Fp {
    let two_inv = Fp::new(2).inv().unwrap();
    let even = (f_x + f_neg_x) * two_inv;
    let odd = (f_x - f_neg_x) * two_inv * x_inv;
    even + beta * odd
}

fn fold_evaluations(evals: &[Fp], domain: &[Fp], beta: Fp) -> Vec<Fp> {
    let half = evals.len() / 2;
    let x_invs = crate::field::batch_inverse(&domain[..half]);
    (0..half).map(|i| fold_pair(evals[i], evals[i + half], x_invs[i], beta)).collect()
}

fn next_domain(domain: &[Fp]) -> Vec<Fp> {
    let half = domain.len() / 2;
    domain[..half].iter().map(|&x| x * x).collect()
}

/// The result of the FRI commit phase: every folded layer's Merkle tree and
/// evaluations, kept around so queries can be opened against them.
pub struct FriCommitment {
    pub layer_roots: Vec<Digest>,
    pub final_evals: Vec<Fp>,
    layer_trees: Vec<MerkleTree>,
    layer_evals: Vec<Vec<Fp>>,
    /// Size of the first (unfolded) layer — callers need this to sample
    /// query indices in the right range.
    pub n0: usize,
}

/// Runs just the FRI commit phase (repeated folding, one Merkle commitment
/// per layer, challenges drawn from the transcript as each layer commits).
/// Split out from `prove` so a caller — the STARK prover — can sample query
/// indices itself, after this absorbs into the transcript but before
/// anything else does, and reuse those same indices to open a *different*
/// commitment (the trace) at consistent positions.
pub fn commit(evals: Vec<Fp>, domain: Vec<Fp>, config: &FriConfig, transcript: &mut Transcript) -> FriCommitment {
    assert_eq!(evals.len(), domain.len());
    assert!(evals.len().is_power_of_two());
    assert!(evals.len().is_multiple_of(config.blowup_factor));

    let n0 = evals.len();
    let mut cur_evals = evals;
    let mut cur_domain = domain;
    let mut layer_trees: Vec<MerkleTree> = Vec::new();
    let mut layer_evals: Vec<Vec<Fp>> = Vec::new();
    let mut layer_roots = Vec::new();

    while cur_evals.len() > config.blowup_factor {
        let leaves: Vec<Vec<Fp>> = cur_evals.iter().map(|&e| vec![e]).collect();
        let tree = MerkleTree::new(&leaves);
        let root = tree.root();
        transcript.absorb_digest(&root);
        layer_roots.push(root);

        let beta = transcript.challenge_fp();

        layer_evals.push(cur_evals.clone());
        layer_trees.push(tree);

        cur_evals = fold_evaluations(&cur_evals, &cur_domain, beta);
        cur_domain = next_domain(&cur_domain);
    }

    let final_evals = cur_evals;
    for &v in &final_evals {
        transcript.absorb_fp(v);
    }

    FriCommitment { layer_roots, final_evals, layer_trees, layer_evals, n0 }
}

/// Draws `num_queries` indices in `0..n0/2` from the transcript (or a
/// single `0` if the input needed no folding layers at all). Must be called
/// at the same point in both prover's and verifier's transcript sequence:
/// after everything commit/recompute-challenges absorbed, before anything
/// else is.
pub fn sample_query_indices(transcript: &mut Transcript, n0: usize, num_queries: usize) -> Vec<usize> {
    (0..num_queries).map(|_| if n0 <= 1 { 0 } else { transcript.challenge_index(n0 / 2) }).collect()
}

/// Opens every committed layer at the given query indices.
pub fn open(commitment: &FriCommitment, query_indices: &[usize]) -> Vec<Vec<FriStepOpening>> {
    let num_layers = commitment.layer_roots.len();
    query_indices
        .iter()
        .map(|&start_idx| {
            let mut idx = start_idx;
            (0..num_layers)
                .map(|l| {
                    let evals_l = &commitment.layer_evals[l];
                    let half = evals_l.len() / 2;
                    let pair_idx = idx % half;
                    let step = FriStepOpening {
                        even: evals_l[pair_idx],
                        odd: evals_l[pair_idx + half],
                        even_proof: commitment.layer_trees[l].open(pair_idx),
                        odd_proof: commitment.layer_trees[l].open(pair_idx + half),
                    };
                    idx = pair_idx;
                    step
                })
                .collect()
        })
        .collect()
}

/// Runs the full FRI commit + query phases and returns the proof. `evals`
/// are the claimed low-degree function's values over `domain` (typically a
/// coset LDE produced by `ntt::coset_lde`); both must have the same
/// power-of-two length, a multiple of `config.blowup_factor`.
pub fn prove(evals: Vec<Fp>, domain: Vec<Fp>, config: &FriConfig, transcript: &mut Transcript) -> FriProof {
    let commitment = commit(evals, domain, config, transcript);
    let query_indices = sample_query_indices(transcript, commitment.n0, config.num_queries);
    let query_proofs = open(&commitment, &query_indices);
    FriProof { layer_roots: commitment.layer_roots, final_evals: commitment.final_evals, query_proofs }
}

/// Everything the verifier derives from replaying the commit phase: the
/// per-layer folding challenges and evaluation domains, needed to check
/// query openings.
pub struct FriChallenges {
    betas: Vec<Fp>,
    domains: Vec<Vec<Fp>>,
    pub n0: usize,
}

/// Replays the commit-phase transcript absorption (layer roots, then final
/// evals) to independently derive the same folding challenges the prover
/// used, and checks the proof's structure: the right number of layers, and
/// a final layer that's actually constant (degree 0, the base case FRI
/// bottoms out on). Returns `None` if anything here is malformed.
pub fn recompute_challenges(proof: &FriProof, domain: &[Fp], config: &FriConfig, transcript: &mut Transcript) -> Option<FriChallenges> {
    let n0 = domain.len();
    let expected_layers = (n0 / config.blowup_factor).trailing_zeros() as usize;
    if proof.layer_roots.len() != expected_layers {
        return None;
    }

    let mut betas = Vec::with_capacity(proof.layer_roots.len());
    for root in &proof.layer_roots {
        transcript.absorb_digest(root);
        betas.push(transcript.challenge_fp());
    }
    for &v in &proof.final_evals {
        transcript.absorb_fp(v);
    }

    if proof.final_evals.len() != config.blowup_factor {
        return None;
    }
    let &constant = proof.final_evals.first()?;
    if !proof.final_evals.iter().all(|&v| v == constant) {
        return None;
    }

    let num_layers = proof.layer_roots.len();
    let mut domains = Vec::with_capacity(num_layers);
    let mut cur_domain = domain.to_vec();
    for _ in 0..num_layers {
        domains.push(cur_domain.clone());
        cur_domain = next_domain(&cur_domain);
    }

    Some(FriChallenges { betas, domains, n0 })
}

/// Checks that every query opening is internally consistent: Merkle proofs
/// verify against the claimed layer roots, at the positions the query
/// indices actually imply, and folding each layer's opened pair with its
/// challenge reproduces the next layer's (or the final layer's) value.
pub fn verify_queries(proof: &FriProof, challenges: &FriChallenges, query_indices: &[usize]) -> bool {
    if proof.query_proofs.len() != query_indices.len() {
        return false;
    }
    let num_layers = proof.layer_roots.len();

    for (steps, &start_idx) in proof.query_proofs.iter().zip(query_indices) {
        if steps.len() != num_layers {
            return false;
        }
        let mut idx = start_idx;
        let mut expected: Option<Fp> = None;

        for (l, step) in steps.iter().enumerate() {
            let half = challenges.domains[l].len() / 2;
            let pair_idx = idx % half;

            if step.even_proof.index != pair_idx || step.odd_proof.index != pair_idx + half {
                return false;
            }
            if !step.even_proof.verify(proof.layer_roots[l], &[step.even]) {
                return false;
            }
            if !step.odd_proof.verify(proof.layer_roots[l], &[step.odd]) {
                return false;
            }

            if let Some(exp) = expected {
                let actual = if idx < half { step.even } else { step.odd };
                if actual != exp {
                    return false;
                }
            }

            let x = challenges.domains[l][pair_idx];
            let x_inv = x.inv().expect("domain points are never zero");
            expected = Some(fold_pair(step.even, step.odd, x_inv, challenges.betas[l]));
            idx = pair_idx;
        }

        if let Some(exp) = expected
            && proof.final_evals.get(idx) != Some(&exp)
        {
            return false;
        }
    }

    true
}

/// Verifies a FRI proof against the public `domain` (the same one the
/// prover started from) and `config`. Replays the transcript to
/// independently derive the same folding challenges and query indices the
/// prover used.
pub fn verify(proof: &FriProof, domain: &[Fp], config: &FriConfig, transcript: &mut Transcript) -> bool {
    let Some(challenges) = recompute_challenges(proof, domain, config, transcript) else {
        return false;
    };
    let query_indices = sample_query_indices(transcript, challenges.n0, config.num_queries);
    verify_queries(proof, &challenges, &query_indices)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt;
    use crate::poly::Poly;
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    fn config() -> FriConfig {
        FriConfig { blowup_factor: 4, num_queries: 20 }
    }

    #[test]
    fn honest_low_degree_proof_verifies() {
        let mut rng = StdRng::seed_from_u64(1);
        let degree_bound = 16usize; // polynomial degree < 16
        let coeffs: Vec<Fp> = (0..degree_bound).map(|_| Fp::random(&mut rng)).collect();
        let poly = Poly::new(coeffs);

        let cfg = config();
        let log_n = (degree_bound * cfg.blowup_factor).trailing_zeros();
        let offset = Fp::new(7);
        let domain = ntt::coset_domain(log_n, offset);
        let evals = ntt::coset_lde(&poly, log_n, offset);

        let mut prover_transcript = Transcript::new(b"fri-test");
        let proof = prove(evals, domain.clone(), &cfg, &mut prover_transcript);

        let mut verifier_transcript = Transcript::new(b"fri-test");
        assert!(verify(&proof, &domain, &cfg, &mut verifier_transcript));
    }

    #[test]
    fn non_low_degree_evaluations_are_rejected() {
        let mut rng = StdRng::seed_from_u64(2);
        let cfg = config();
        let log_n = (16 * cfg.blowup_factor).trailing_zeros();
        let offset = Fp::new(7);
        let domain = ntt::coset_domain(log_n, offset);
        // Random values are, with overwhelming probability, not close to
        // any low-degree polynomial.
        let evals: Vec<Fp> = (0..domain.len()).map(|_| Fp::random(&mut rng)).collect();

        let mut prover_transcript = Transcript::new(b"fri-test");
        let proof = prove(evals, domain.clone(), &cfg, &mut prover_transcript);

        let mut verifier_transcript = Transcript::new(b"fri-test");
        assert!(!verify(&proof, &domain, &cfg, &mut verifier_transcript));
    }

    #[test]
    fn tampered_query_opening_is_rejected() {
        let mut rng = StdRng::seed_from_u64(3);
        let degree_bound = 8usize;
        let coeffs: Vec<Fp> = (0..degree_bound).map(|_| Fp::random(&mut rng)).collect();
        let poly = Poly::new(coeffs);

        let cfg = config();
        let log_n = (degree_bound * cfg.blowup_factor).trailing_zeros();
        let offset = Fp::new(7);
        let domain = ntt::coset_domain(log_n, offset);
        let evals = ntt::coset_lde(&poly, log_n, offset);

        let mut prover_transcript = Transcript::new(b"fri-test");
        let mut proof = prove(evals, domain.clone(), &cfg, &mut prover_transcript);
        proof.query_proofs[0][0].even += Fp::ONE;

        let mut verifier_transcript = Transcript::new(b"fri-test");
        assert!(!verify(&proof, &domain, &cfg, &mut verifier_transcript));
    }

    #[test]
    fn tampered_final_layer_is_rejected() {
        let mut rng = StdRng::seed_from_u64(4);
        let degree_bound = 8usize;
        let coeffs: Vec<Fp> = (0..degree_bound).map(|_| Fp::random(&mut rng)).collect();
        let poly = Poly::new(coeffs);

        let cfg = config();
        let log_n = (degree_bound * cfg.blowup_factor).trailing_zeros();
        let offset = Fp::new(7);
        let domain = ntt::coset_domain(log_n, offset);
        let evals = ntt::coset_lde(&poly, log_n, offset);

        let mut prover_transcript = Transcript::new(b"fri-test");
        let mut proof = prove(evals, domain.clone(), &cfg, &mut prover_transcript);
        proof.final_evals[0] += Fp::ONE;

        let mut verifier_transcript = Transcript::new(b"fri-test");
        assert!(!verify(&proof, &domain, &cfg, &mut verifier_transcript));
    }

    #[test]
    fn tampered_root_is_rejected() {
        let mut rng = StdRng::seed_from_u64(5);
        let degree_bound = 8usize;
        let coeffs: Vec<Fp> = (0..degree_bound).map(|_| Fp::random(&mut rng)).collect();
        let poly = Poly::new(coeffs);

        let cfg = config();
        let log_n = (degree_bound * cfg.blowup_factor).trailing_zeros();
        let offset = Fp::new(7);
        let domain = ntt::coset_domain(log_n, offset);
        let evals = ntt::coset_lde(&poly, log_n, offset);

        let mut prover_transcript = Transcript::new(b"fri-test");
        let mut proof = prove(evals, domain.clone(), &cfg, &mut prover_transcript);
        proof.layer_roots[0][0] ^= 0xFF;

        let mut verifier_transcript = Transcript::new(b"fri-test");
        assert!(!verify(&proof, &domain, &cfg, &mut verifier_transcript));
    }

    #[test]
    fn fold_pair_matches_even_odd_decomposition() {
        // p(x) = 1 + 2x + 3x^2 + 4x^3 => p_even(y) = 1 + 3y, p_odd(y) = 2 + 4y
        let p_even = Poly::new(vec![Fp::new(1), Fp::new(3)]);
        let p_odd = Poly::new(vec![Fp::new(2), Fp::new(4)]);
        let x = Fp::new(5);
        let beta = Fp::new(9);

        let p = Poly::new(vec![Fp::new(1), Fp::new(2), Fp::new(3), Fp::new(4)]);
        let f_x = p.eval(x);
        let f_neg_x = p.eval(-x);

        let folded = fold_pair(f_x, f_neg_x, x.inv().unwrap(), beta);
        let expected = p_even.eval(x * x) + beta * p_odd.eval(x * x);
        assert_eq!(folded, expected);
    }

    #[test]
    fn degree_zero_input_needs_no_layers() {
        let mut rng = StdRng::seed_from_u64(6);
        let cfg = FriConfig { blowup_factor: 4, num_queries: 5 };
        let log_n = 2u32; // domain size 4 == blowup_factor, so degree bound is already 1
        let offset = Fp::new(7);
        let domain = ntt::coset_domain(log_n, offset);
        let constant = Fp::random(&mut rng);
        let evals = vec![constant; domain.len()];

        let mut prover_transcript = Transcript::new(b"fri-test");
        let proof = prove(evals, domain.clone(), &cfg, &mut prover_transcript);
        assert!(proof.layer_roots.is_empty());

        let mut verifier_transcript = Transcript::new(b"fri-test");
        assert!(verify(&proof, &domain, &cfg, &mut verifier_transcript));
    }
}
