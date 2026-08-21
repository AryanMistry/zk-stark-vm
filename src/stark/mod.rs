pub mod prover;
pub mod verifier;

use crate::air::{Air, BoundaryConstraint};
use crate::field::Fp;
use crate::fri::FriProof;
use crate::merkle::{Digest, MerkleProof};
use serde::{Deserialize, Serialize};

/// `lde_blowup` and `fri_rate` are split because they serve different
/// purposes: `lde_blowup` sizes the low-degree-extension domain the trace
/// and composition polynomial live on (`M = N * lde_blowup`), while
/// `fri_rate` is FRI's own rate, i.e. the degree bound FRI enforces is
/// `M / fri_rate`. That bound has to exceed the composition polynomial's
/// *true* degree — dominated by the highest-arithmetic-degree transition
/// constraint (degree 4, from JMPIF's is-nonzero gadget) divided by the
/// degree-(N-1) vanishing polynomial, giving true degree ~3N. The defaults
/// below (`8 / 2 = 4N`) leave comfortable headroom over that ~3N bound.
pub struct StarkConfig {
    pub lde_blowup: usize,
    pub fri_rate: usize,
    pub num_queries: usize,
}

impl StarkConfig {
    pub fn toy() -> Self {
        StarkConfig { lde_blowup: 8, fri_rate: 2, num_queries: 24 }
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

/// Everything needed to evaluate the composition polynomial at one point,
/// given that point's current/next row values. Shared between the prover
/// (which calls this once per LDE domain point) and the verifier (which
/// calls it once per FRI query) so they can never accidentally diverge.
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

    /// Combines this point's constraint/boundary/DEEP terms using
    /// precomputed inverses (in the order `denominators` produced them).
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

    /// Evaluates the composition at every point in `domain`, batch-inverting
    /// every denominator needed across the *entire* domain in one pass.
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
}
