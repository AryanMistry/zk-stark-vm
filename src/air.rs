//! The `Air` trait: an Algebraic Intermediate Representation for STARKs.
//!
//! An AIR describes a computation as a table (the "trace") where every row
//! is a step of the computation, plus two kinds of algebraic constraints:
//!
//! - transition constraints: polynomial relations between a row and the
//!   next row, which must evaluate to zero for every consecutive pair of
//!   rows in a valid trace (e.g. "if this row's opcode is ADD, the next
//!   row's destination register equals the sum of the two operands").
//! - boundary constraints: a fixed value at a fixed (row, column), pinning
//!   down public inputs/outputs (e.g. "row 0, column pc == 0").

use crate::field::Fp;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundaryConstraint {
    pub row: usize,
    pub column: usize,
    pub value: Fp,
}

pub trait Air {
    fn trace_width(&self) -> usize;

    /// Evaluates every transition constraint polynomial at one pair of
    /// consecutive rows. A trace satisfies the AIR iff every entry is zero
    /// for every consecutive row pair.
    fn transition_constraints(&self, current: &[Fp], next: &[Fp]) -> Vec<Fp>;

    fn boundary_constraints(&self) -> Vec<BoundaryConstraint>;

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
