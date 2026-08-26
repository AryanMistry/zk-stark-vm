//! Replays the prover's transcript to re-derive every challenge, then checks the
//! trace openings, the composition value FRI claims, and FRI's fold consistency.

use super::{CompositionContext, LDE_OFFSET, StarkConfig, StarkProof};
use crate::air::Air;
use crate::fri::{self, FriConfig};
use crate::ntt;
use crate::transcript::Transcript;

pub fn verify<A: Air>(air: &A, trace_len: usize, proof: &StarkProof, config: &StarkConfig) -> bool {
    if !trace_len.is_power_of_two() {
        return false;
    }
    let n = trace_len;
    let log_n = n.trailing_zeros();
    let width = air.trace_width();

    if proof.ood_current.len() != width || proof.ood_next.len() != width {
        return false;
    }

    let mut transcript = Transcript::new(b"zk-stark-vm");
    transcript.absorb_digest(&proof.trace_root);

    let w_n = ntt::root_of_unity(log_n);
    let z = transcript.challenge_fp();
    let z_shifted = z * w_n;

    transcript.absorb_fps(&proof.ood_current);
    transcript.absorb_fps(&proof.ood_next);

    let boundary_constraints = air.boundary_constraints();
    let alphas = transcript.challenge_fps(air.num_transition_constraints());
    let betas = transcript.challenge_fps(boundary_constraints.len());
    let gammas_current = transcript.challenge_fps(width);
    let gammas_next = transcript.challenge_fps(width);

    let w_n_pow_last = w_n.pow((n - 1) as u64);
    let boundary = boundary_constraints
        .into_iter()
        .zip(betas)
        .map(|(bc, beta)| {
            let w_pow_row = w_n.pow(bc.row as u64);
            (bc, beta, w_pow_row)
        })
        .collect();

    let ctx = CompositionContext {
        air,
        n,
        w_n_pow_last,
        z,
        z_shifted,
        alphas,
        boundary,
        ood_current: &proof.ood_current,
        ood_next: &proof.ood_next,
        gammas_current,
        gammas_next,
    };

    // Derived, not read off the proof: the prover can't pick a weaker domain.
    let blowup = config.lde_blowup(n, air.max_constraint_degree());
    let log_m = log_n + blowup.trailing_zeros();
    let m = 1usize << log_m;
    let domain = ntt::coset_domain(log_m, LDE_OFFSET);

    let fri_config = FriConfig { blowup_factor: config.fri_rate, num_queries: config.num_queries };
    let Some(challenges) = fri::recompute_challenges(&proof.fri_proof, &domain, &fri_config, &mut transcript) else {
        return false;
    };
    let query_indices = fri::sample_query_indices(&mut transcript, challenges.n0, config.num_queries);

    if proof.trace_openings.len() != query_indices.len() {
        return false;
    }

    for (q, (opening, &idx)) in proof.trace_openings.iter().zip(&query_indices).enumerate() {
        if opening.current.len() != width || opening.next.len() != width {
            return false;
        }
        let next_idx = (idx + blowup) % m;
        if opening.current_proof.index != idx || opening.next_proof.index != next_idx {
            return false;
        }
        if !opening.current_proof.verify(proof.trace_root, &opening.current) {
            return false;
        }
        if !opening.next_proof.verify(proof.trace_root, &opening.next) {
            return false;
        }

        let expected = ctx.evaluate(&opening.current, &opening.next, domain[idx]);

        let composition_claim = if proof.fri_proof.layer_roots.is_empty() {
            proof.fri_proof.final_evals.get(idx).copied()
        } else {
            proof.fri_proof.query_proofs.get(q).and_then(|steps| steps.first()).map(|s| s.even)
        };
        let Some(composition_claim) = composition_claim else { return false };
        if composition_claim != expected {
            return false;
        }
    }

    fri::verify_queries(&proof.fri_proof, &challenges, &query_indices)
}
