//! The STARK: trace -> LDE -> commitment -> composition polynomial -> FRI.
//!
//! Succinctness and zero-knowledge are separate. FRI buys the first; `prover::blind`
//! masks the trace for the second, but only its direct openings — not FRI's folded
//! layers, and with no simulator argument. Not "proven zero-knowledge".

pub mod prover;
pub mod verifier;

use crate::air::{Air, BoundaryConstraint};
use crate::field::Fp;
use crate::fri::FriProof;
use crate::merkle::{Digest, MerkleProof};
use serde::{Deserialize, Serialize};

/// The LDE blowup sizes the extension domain (`M = N * blowup`); `fri_rate` sets
/// the degree bound FRI enforces (`M / fri_rate`). See [`StarkConfig::lde_blowup`].
pub struct StarkConfig {
    /// Only a floor — the real blowup is derived, not chosen.
    pub min_lde_blowup: usize,
    pub fri_rate: usize,
    pub num_queries: usize,
    /// Blind trace polynomials before commitment so openings reveal nothing.
    pub blinding: bool,
}

impl StarkConfig {
    pub fn toy() -> Self {
        StarkConfig { min_lde_blowup: 8, fri_rate: 2, num_queries: 24, blinding: true }
    }

    /// Same parameters with blinding off, so its cost can be measured.
    pub fn toy_without_blinding() -> Self {
        StarkConfig { blinding: false, ..StarkConfig::toy() }
    }

    /// Random coefficients per blinded trace polynomial: enough to mask every
    /// revealed evaluation (two out-of-domain, plus two per query).
    pub fn blinding_degree(&self) -> usize {
        if self.blinding { 2 + 2 * self.num_queries } else { 0 }
    }

    /// Derived, not chosen: composition degree is `D*(N+k-1) + 1 - N`, and FRI needs
    /// `blowup > fri_rate * that / N`. Short traces pay most, since `k` is fixed.
    pub fn lde_blowup(&self, n: usize, max_constraint_degree: usize) -> usize {
        let k = self.blinding_degree();
        let composition_degree = max_constraint_degree * (n + k - 1) + 1 - n;
        // FRI accepts degree < bound, so leave one more than the degree.
        let needed = (self.fri_rate * (composition_degree + 1)).div_ceil(n);
        needed.max(self.min_lde_blowup).next_power_of_two()
    }
}

pub(crate) const LDE_OFFSET: Fp = Fp(7);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceOpening {
    pub current: Vec<Fp>,
    pub current_proof: MerkleProof,
    pub next: Vec<Fp>,
    pub next_proof: MerkleProof,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StarkProof {
    pub trace_root: Digest,
    /// Trace column values at a random out-of-domain point z.
    pub ood_current: Vec<Fp>,
    /// Trace column values at z * w (the "next row" shift).
    pub ood_next: Vec<Fp>,
    pub trace_openings: Vec<TraceOpening>,
    pub fri_proof: FriProof,
}

/// Shared by prover and verifier so the composition formula can't diverge.
pub(crate) struct CompositionContext<'a, A: Air> {
    pub air: &'a A,
    pub n: usize,
    pub w_n_pow_last: Fp,
    pub z: Fp,
    pub z_shifted: Fp,
    pub alphas: Vec<Fp>,
    pub boundary: Vec<(BoundaryConstraint, Fp, Fp)>, // (constraint, beta, w_n^row)
    pub ood_current: &'a [Fp],
    pub ood_next: &'a [Fp],
    pub gammas_current: Vec<Fp>,
    pub gammas_next: Vec<Fp>,
}

impl<'a, A: Air> CompositionContext<'a, A> {
    fn denominators(&self, x: Fp) -> Vec<Fp> {
        let mut d = Vec::with_capacity(2 + self.boundary.len());
        d.push(x.pow(self.n as u64) - Fp::ONE);
        for (_, _, w_pow_row) in &self.boundary {
            d.push(x - *w_pow_row);
        }
        d.push(x - self.z);
        d.push(x - self.z_shifted);
        d
    }

    /// Combines one point's terms using inverses in `denominators` order.
    fn combine(&self, current_row: &[Fp], next_row: &[Fp], x: Fp, inverses: &[Fp]) -> Fp {
        let constraint_values = self.air.transition_constraints(current_row, next_row);
        let transition_term =
            self.alphas.iter().zip(&constraint_values).fold(Fp::ZERO, |acc, (&a, &c)| acc + a * c);
        let denom = x - self.w_n_pow_last;
        let transition_contribution = transition_term * denom * inverses[0];

        let mut idx = 1;
        let boundary_contribution = self.boundary.iter().fold(Fp::ZERO, |acc, (bc, beta, _)| {
            let inv = inverses[idx];
            idx += 1;
            acc + *beta * (current_row[bc.column] - bc.value) * inv
        });

        let deep_current_sum = self
            .gammas_current
            .iter()
            .zip(current_row)
            .zip(self.ood_current)
            .fold(Fp::ZERO, |acc, ((&g, &t), &o)| acc + g * (t - o));
        let deep_current = deep_current_sum * inverses[idx];
        idx += 1;

        let deep_next_sum = self
            .gammas_next
            .iter()
            .zip(current_row)
            .zip(self.ood_next)
            .fold(Fp::ZERO, |acc, ((&g, &t), &o)| acc + g * (t - o));
        let deep_next = deep_next_sum * inverses[idx];

        transition_contribution + boundary_contribution + deep_current + deep_next
    }

    /// Evaluates the composition at a single point.
    pub fn evaluate(&self, current_row: &[Fp], next_row: &[Fp], x: Fp) -> Fp {
        let denoms = self.denominators(x);
        let inverses = crate::field::batch_inverse(&denoms);
        self.combine(current_row, next_row, x, &inverses)
    }

    /// Evaluates over the whole domain, batch-inverting every denominator at once.
    pub fn evaluate_domain(&self, rows: impl Fn(usize) -> (Vec<Fp>, Vec<Fp>), domain: &[Fp]) -> Vec<Fp> {
        let per_point = 3 + self.boundary.len();
        let mut all_denoms = Vec::with_capacity(domain.len() * per_point);
        for &x in domain {
            all_denoms.extend(self.denominators(x));
        }
        let all_inverses = crate::field::batch_inverse(&all_denoms);

        domain
            .iter()
            .enumerate()
            .map(|(i, &x)| {
                let (current_row, next_row) = rows(i);
                let point_inverses = &all_inverses[i * per_point..(i + 1) * per_point];
                self.combine(&current_row, &next_row, x, point_inverses)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::constraints::VmAir;
    use crate::vm::trace::generate_trace;
    use crate::vm::{fibonacci_program, REG_B};

    fn fib_reference(n: u64) -> u64 {
        let (mut a, mut b) = (0u64, 1u64);
        for _ in 0..n {
            let tmp = a + b;
            a = b;
            b = tmp;
        }
        b
    }

    #[test]
    fn honest_fibonacci_proof_verifies() {
        let program = fibonacci_program();
        let n = 5u64;
        let (trace, output) = generate_trace(&program, Fp::new(n));
        assert_eq!(output, Fp::new(fib_reference(n)));

        let air = VmAir::new(program, Fp::new(n), output, trace.rows.len() - 1);
        let config = StarkConfig::toy();

        let proof = prover::prove(&air, &trace.rows, &config);
        assert!(verifier::verify(&air, trace.rows.len(), &proof, &config));
    }

    #[test]
    fn wrong_claimed_output_is_rejected() {
        let program = fibonacci_program();
        let n = 5u64;
        let (trace, output) = generate_trace(&program, Fp::new(n));

        let honest_air = VmAir::new(program.clone(), Fp::new(n), output, trace.rows.len() - 1);
        let config = StarkConfig::toy();
        let proof = prover::prove(&honest_air, &trace.rows, &config);

        let lying_air = VmAir::new(program, Fp::new(n), output + Fp::ONE, trace.rows.len() - 1);
        assert!(!verifier::verify(&lying_air, trace.rows.len(), &proof, &config));
    }

    #[test]
    fn tampered_trace_is_rejected() {
        let program = fibonacci_program();
        let n = 5u64;
        let (mut trace, output) = generate_trace(&program, Fp::new(n));
        // Break one transition somewhere in the middle of execution.
        trace.rows[3][crate::vm::trace::COL_REG + REG_B] += Fp::ONE;

        let air = VmAir::new(program, Fp::new(n), output, trace.rows.len() - 1);
        let config = StarkConfig::toy();
        let proof = prover::prove(&air, &trace.rows, &config);

        assert!(!verifier::verify(&air, trace.rows.len(), &proof, &config));
    }

    #[test]
    fn tampered_proof_opening_is_rejected() {
        let program = fibonacci_program();
        let n = 5u64;
        let (trace, output) = generate_trace(&program, Fp::new(n));

        let air = VmAir::new(program, Fp::new(n), output, trace.rows.len() - 1);
        let config = StarkConfig::toy();
        let mut proof = prover::prove(&air, &trace.rows, &config);
        proof.trace_openings[0].current[0] += Fp::ONE;

        assert!(!verifier::verify(&air, trace.rows.len(), &proof, &config));
    }

    #[test]
    fn wrong_opcode_at_correct_pc_is_rejected() {
        let program = fibonacci_program();
        let n = 10u64;
        let (mut trace, output) = generate_trace(&program, Fp::new(n));
        let row = &mut trace.rows[3];
        let val_a = row[crate::vm::trace::COL_VAL_A];
        let val_b = row[crate::vm::trace::COL_VAL_B];
        row[crate::vm::trace::COL_OP + crate::vm::Opcode::Add.index()] = Fp::ZERO;
        row[crate::vm::trace::COL_OP + crate::vm::Opcode::Sub.index()] = Fp::ONE;
        row[crate::vm::trace::COL_WRITE_VALUE] = val_a - val_b;

        let air = VmAir::new(program, Fp::new(n), output, trace.rows.len() - 1);
        let config = StarkConfig::toy();
        let proof = prover::prove(&air, &trace.rows, &config);

        assert!(!verifier::verify(&air, trace.rows.len(), &proof, &config));
    }

    // --- blinding / zero-knowledge ---

    #[test]
    fn unblinded_proof_still_verifies() {
        let program = fibonacci_program();
        let (trace, output) = generate_trace(&program, Fp::new(5));
        let air = VmAir::new(program, Fp::new(5), output, trace.rows.len() - 1);
        let config = StarkConfig::toy_without_blinding();

        let proof = prover::prove(&air, &trace.rows, &config);
        assert!(verifier::verify(&air, trace.rows.len(), &proof, &config));
    }

    #[test]
    fn blinding_makes_proofs_nondeterministic() {
        let program = fibonacci_program();
        let (trace, output) = generate_trace(&program, Fp::new(5));
        let air = VmAir::new(program, Fp::new(5), output, trace.rows.len() - 1);
        let config = StarkConfig::toy();

        let a = prover::prove(&air, &trace.rows, &config);
        let b = prover::prove(&air, &trace.rows, &config);

        // Same trace, different proofs: the blinding randomness is fresh.
        assert_ne!(a.trace_root, b.trace_root);
        assert_ne!(a.ood_current, b.ood_current);
        assert!(verifier::verify(&air, trace.rows.len(), &a, &config));
        assert!(verifier::verify(&air, trace.rows.len(), &b, &config));
    }

    #[test]
    fn without_blinding_proofs_are_deterministic() {
        // Control for the test above: unblinded, the prover has no randomness.
        let program = fibonacci_program();
        let (trace, output) = generate_trace(&program, Fp::new(5));
        let air = VmAir::new(program, Fp::new(5), output, trace.rows.len() - 1);
        let config = StarkConfig::toy_without_blinding();

        let a = prover::prove(&air, &trace.rows, &config);
        let b = prover::prove(&air, &trace.rows, &config);
        assert_eq!(a, b);
    }

    #[test]
    fn lde_blowup_grows_to_absorb_blinding() {
        let blinded = StarkConfig::toy();
        let plain = StarkConfig::toy_without_blinding();

        // Short traces pay most: k is a large fraction of the trace length.
        assert!(blinded.lde_blowup(64, 4) > plain.lde_blowup(64, 4));
        // Long traces amortise it away entirely.
        assert_eq!(blinded.lde_blowup(4096, 4), plain.lde_blowup(4096, 4));

        // The derived bound must clear the composition degree.
        for n in [8usize, 64, 256, 4096] {
            for cfg in [&blinded, &plain] {
                let k = cfg.blinding_degree();
                let composition_degree = 4 * (n + k - 1) + 1 - n;
                let fri_bound = n * cfg.lde_blowup(n, 4) / cfg.fri_rate;
                assert!(fri_bound > composition_degree, "n={n} bound={fri_bound} deg={composition_degree}");
            }
        }
    }

    /// Reconstructs a trace column from the proof alone. `None` if too few points.
    fn reconstruct_column_from_proof<A: crate::air::Air>(
        air: &A,
        proof: &StarkProof,
        trace_len: usize,
        column: usize,
        config: &StarkConfig,
    ) -> Option<Vec<Fp>> {
        let log_n = trace_len.trailing_zeros();
        let blowup = config.lde_blowup(trace_len, air.max_constraint_degree());
        let log_m = log_n + blowup.trailing_zeros();
        let domain = crate::ntt::coset_domain(log_m, LDE_OFFSET);

        // Every opening is a (domain point, value) pair sitting in the clear.
        let mut seen: std::collections::BTreeMap<usize, Fp> = std::collections::BTreeMap::new();
        for opening in &proof.trace_openings {
            seen.insert(opening.current_proof.index, opening.current[column]);
            seen.insert(opening.next_proof.index, opening.next[column]);
        }
        if seen.len() < trace_len {
            return None;
        }

        // Unblinded degree < trace_len, so trace_len points determine it.
        let points: Vec<(Fp, Fp)> =
            seen.into_iter().take(trace_len).map(|(idx, v)| (domain[idx], v)).collect();
        let recovered = crate::poly::Poly::interpolate(&points);

        let w_n = crate::ntt::root_of_unity(log_n);
        Some((0..trace_len).map(|r| recovered.eval(w_n.pow(r as u64))).collect())
    }

    #[test]
    fn unblinded_proof_leaks_the_trace() {
        // 8 rows vs ~50 revealed evaluations: the column falls out by interpolation.
        let program = fibonacci_program();
        let (trace, output) = generate_trace(&program, Fp::ZERO);
        let n = trace.rows.len();
        assert_eq!(n, 8, "this test wants the smallest trace");

        let air = VmAir::new(program, Fp::ZERO, output, n - 1);
        let config = StarkConfig::toy_without_blinding();
        let proof = prover::prove(&air, &trace.rows, &config);

        let col = crate::vm::trace::COL_PC;
        let recovered = reconstruct_column_from_proof(&air, &proof, n, col, &config)
            .expect("proof revealed enough points to interpolate");
        let actual: Vec<Fp> = trace.rows.iter().map(|row| row[col]).collect();

        assert_eq!(recovered, actual, "the pc column should be fully recoverable without blinding");
    }

    #[test]
    fn blinded_proof_does_not_leak_the_trace() {
        // Same attack with blinding on: degree n+k-1, so n points don't pin it down.
        let program = fibonacci_program();
        let (trace, output) = generate_trace(&program, Fp::ZERO);
        let n = trace.rows.len();

        let air = VmAir::new(program, Fp::ZERO, output, n - 1);
        let config = StarkConfig::toy();
        let proof = prover::prove(&air, &trace.rows, &config);

        let col = crate::vm::trace::COL_PC;
        let recovered = reconstruct_column_from_proof(&air, &proof, n, col, &config)
            .expect("proof revealed enough points to interpolate");
        let actual: Vec<Fp> = trace.rows.iter().map(|row| row[col]).collect();

        assert_ne!(recovered, actual, "blinding should defeat this reconstruction");
    }
}
