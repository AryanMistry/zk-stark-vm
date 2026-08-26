//! The `Air` trait: a computation as a trace table plus algebraic constraints.
//!
//! Transition constraints relate a row to the next and must vanish on every pair;
//! boundary constraints pin a fixed value at a fixed (row, column).

use crate::field::Fp;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundaryConstraint {
    pub row: usize,
    pub column: usize,
    pub value: Fp,
}

pub trait Air {
    fn trace_width(&self) -> usize;

    /// Evaluates every transition constraint at one pair of consecutive rows.
    fn transition_constraints(&self, current: &[Fp], next: &[Fp]) -> Vec<Fp>;

    fn boundary_constraints(&self) -> Vec<BoundaryConstraint>;

    /// Most trace values multiplied together in any one constraint
    fn max_constraint_degree(&self) -> usize;

    fn num_transition_constraints(&self) -> usize {
        let zeros = vec![Fp::ZERO; self.trace_width()];
        self.transition_constraints(&zeros, &zeros).len()
    }
}

#[derive(Debug)]
pub enum ConstraintViolation {
    Transition { row: usize, constraint_index: usize, value: Fp },
    Boundary { row: usize, column: usize, expected: Fp, actual: Fp },
}

/// Checks that a trace satisfies the AIR's transition and boundary constraints.
pub fn check_trace(air: &impl Air, trace: &[Vec<Fp>]) -> Result<(), ConstraintViolation> {
    for row in trace {
        assert_eq!(row.len(), air.trace_width());
    }

    for i in 0..trace.len().saturating_sub(1) {
        let values = air.transition_constraints(&trace[i], &trace[i + 1]);
        for (constraint_index, &value) in values.iter().enumerate() {
            if !value.is_zero() {
                return Err(ConstraintViolation::Transition { row: i, constraint_index, value });
            }
        }
    }

    for bc in air.boundary_constraints() {
        let actual = trace[bc.row][bc.column];
        if actual != bc.value {
            return Err(ConstraintViolation::Boundary {
                row: bc.row,
                column: bc.column,
                expected: bc.value,
                actual,
            });
        }
    }

    Ok(())
}
