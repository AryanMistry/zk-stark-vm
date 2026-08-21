//! Trace -> low-degree extension -> commitment -> composition polynomial
//! -> FRI proof. See `stark/mod.rs` for the shared composition logic and
//! `air.rs`/`vm/constraints.rs` for what's actually being proven.

use super::{CompositionContext, LDE_OFFSET, StarkConfig, StarkProof, TraceOpening};
use crate::air::Air;
use crate::field::Fp;
use crate::fri::{self, FriConfig, FriProof};
use crate::merkle::MerkleTree;
use crate::ntt;
use crate::transcript::Transcript;

pub fn prove<A: Air>(air: &A, trace: &[Vec<Fp>], config: &StarkConfig) -> StarkProof {
    let n = trace.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();
    let width = air.trace_width();
    for row in trace {
        assert_eq!(row.len(), width);
    }

    // 1. Interpolate every trace column into a polynomial.
    let trace_polys: Vec<_> = (0..width)
        .map(|j| {
            let column: Vec<Fp> = trace.iter().map(|row| row[j]).collect();
            ntt::interpolate_subgroup(&column)
        })
        .collect();

    // 2. Low-degree-extend every column onto the (larger) coset domain.
    let log_m = log_n + config.lde_blowup.trailing_zeros();
    let m = 1usize << log_m;
    let blowup = config.lde_blowup;
    let domain = ntt::coset_domain(log_m, LDE_OFFSET);
    let trace_lde: Vec<Vec<Fp>> = trace_polys.iter().map(|p| ntt::coset_lde(p, log_m, LDE_OFFSET)).collect();

    // 3. Commit the trace LDE: one leaf per domain point, holding every
    // column's value there, so one Merkle proof opens a whole row.
    let leaves: Vec<Vec<Fp>> = (0..m).map(|i| (0..width).map(|j| trace_lde[j][i]).collect()).collect();
    let trace_tree = MerkleTree::new(&leaves);
    let trace_root = trace_tree.root();

    let mut transcript = Transcript::new(b"zk-stark-vm");
    transcript.absorb_digest(&trace_root);

    // 4. DEEP: sample an out-of-domain point and its "next row" shift.
    let w_n = ntt::root_of_unity(log_n);
    let z = transcript.challenge_fp();
    let z_shifted = z * w_n;

    // 5. Reveal the trace polynomials' true evaluations there.
    let ood_current: Vec<Fp> = trace_polys.iter().map(|p| p.eval(z)).collect();
    let ood_next: Vec<Fp> = trace_polys.iter().map(|p| p.eval(z_shifted)).collect();
    transcript.absorb_fps(&ood_current);
    transcript.absorb_fps(&ood_next);

    // 6. Random coefficients combining every constraint (and every
    // per-column DEEP consistency check) into one polynomial.
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
        ood_current: &ood_current,
        ood_next: &ood_next,
        gammas_current,
        gammas_next,
    };

    // 7. Composition polynomial, evaluated pointwise over the LDE domain.
    let composition_lde = ctx.evaluate_domain(
        |i| {
            let current_row: Vec<Fp> = (0..width).map(|j| trace_lde[j][i]).collect();
            let next_row: Vec<Fp> = (0..width).map(|j| trace_lde[j][(i + blowup) % m]).collect();
            (current_row, next_row)
        },
        &domain,
    );

    // 8. FRI-prove the composition is low degree.
    let fri_config = FriConfig { blowup_factor: config.fri_rate, num_queries: config.num_queries };
    let commitment = fri::commit(composition_lde, domain.clone(), &fri_config, &mut transcript);
    let query_indices = fri::sample_query_indices(&mut transcript, commitment.n0, config.num_queries);
    let query_proofs = fri::open(&commitment, &query_indices);
    let fri_proof =
        FriProof { layer_roots: commitment.layer_roots, final_evals: commitment.final_evals, query_proofs };

    // 9. Open the trace commitment at the exact same query indices, so the
    // verifier can recompute the composition value FRI claims and check it
    // was really derived from the committed trace.
    let trace_openings = query_indices
        .iter()
        .map(|&idx| {
            let next_idx = (idx + blowup) % m;
            TraceOpening {
                current: leaves[idx].clone(),
                current_proof: trace_tree.open(idx),
                next: leaves[next_idx].clone(),
                next_proof: trace_tree.open(next_idx),
            }
        })
        .collect();

    StarkProof { trace_root, ood_current, ood_next, trace_openings, fri_proof }
}
