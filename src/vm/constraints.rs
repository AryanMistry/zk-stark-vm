//! `VmAir`: transition + boundary constraints for the toy VM, as literal
//! polynomial relations over trace row values — see `trace.rs` for the
//! column layout these index into.


use super::trace::*;
use super::{Instruction, NUM_MEMORY, NUM_REGISTERS, Opcode, REG_ZERO};
use crate::air::{Air, BoundaryConstraint};
use crate::field::Fp;

pub struct VmAir {
    pub input: Fp,
    pub output: Fp,
    pub last_row: usize,
    program: Vec<Instruction>,
    // Precomputed once per program: the
    // constant vector, indexed by program address, that each instruction
    // field's fetch-consistency constraint dot-products against.
    prog_opcode: Vec<Fp>,
    prog_dst: Vec<Fp>,
    prog_a: Vec<Fp>,
    prog_b: Vec<Fp>,
    prog_target: Vec<Fp>,
    prog_index: Vec<Fp>,
}

impl VmAir {
    pub fn new(program: Vec<Instruction>, input: Fp, output: Fp, last_row: usize) -> Self {
        let prog_opcode = program.iter().map(|i| Fp::new(i.opcode.index() as u64)).collect();
        let prog_dst = program.iter().map(|i| Fp::new(i.dst.unwrap_or(REG_ZERO) as u64)).collect();
        let prog_a = program.iter().map(|i| Fp::new(i.a as u64)).collect();
        let prog_b = program.iter().map(|i| Fp::new(i.b as u64)).collect();
        let prog_target = program.iter().map(|i| i.target).collect();
        let prog_index = (0..program.len()).map(|k| Fp::new(k as u64)).collect();
        VmAir { input, output, last_row, program, prog_opcode, prog_dst, prog_a, prog_b, prog_target, prog_index }
    }
}

fn op(row: &[Fp], opcode: Opcode) -> Fp {
    row[COL_OP + opcode.index()]
}

fn dot(sel: &[Fp], values: &[Fp]) -> Fp {
    sel.iter().zip(values).fold(Fp::ZERO, |acc, (&s, &v)| acc + s * v)
}

impl Air for VmAir {
    fn trace_width(&self) -> usize {
        trace_width(self.program.len())
    }

    fn transition_constraints(&self, c: &[Fp], n: &[Fp]) -> Vec<Fp> {
        let mut cs = Vec::new();

        // --- opcode one-hot: exactly one opcode active per row ---
        let op_flags: Vec<Fp> = (0..Opcode::COUNT).map(|k| c[COL_OP + k]).collect();
        for &f in &op_flags {
            cs.push(f * (f - Fp::ONE));
        }
        cs.push(op_flags.iter().fold(-Fp::ONE, |acc, &f| acc + f));

        // --- operand register selects: always a proper one-hot vector ---
        let a_sel: Vec<Fp> = (0..NUM_REGISTERS).map(|k| c[COL_A_SEL + k]).collect();
        let b_sel: Vec<Fp> = (0..NUM_REGISTERS).map(|k| c[COL_B_SEL + k]).collect();
        for &s in a_sel.iter().chain(b_sel.iter()) {
            cs.push(s * (s - Fp::ONE));
        }
        cs.push(a_sel.iter().fold(-Fp::ONE, |acc, &s| acc + s));
        cs.push(b_sel.iter().fold(-Fp::ONE, |acc, &s| acc + s));

        // --- destination register select: one-hot iff a register-writing opcode is active ---
        let dst_sel: Vec<Fp> = (0..NUM_REGISTERS).map(|k| c[COL_DST_SEL + k]).collect();
        for &s in &dst_sel {
            cs.push(s * (s - Fp::ONE));
        }
        let writes_register = op(c, Opcode::Add) + op(c, Opcode::Sub) + op(c, Opcode::Mul) + op(c, Opcode::Load);
        cs.push(dst_sel.iter().fold(-writes_register, |acc, &s| acc + s));

        // --- memory address select: one-hot iff LOAD or STORE is active ---
        let addr_sel: Vec<Fp> = (0..NUM_MEMORY).map(|k| c[COL_ADDR_SEL + k]).collect();
        for &s in &addr_sel {
            cs.push(s * (s - Fp::ONE));
        }
        let touches_memory = op(c, Opcode::Load) + op(c, Opcode::Store);
        cs.push(addr_sel.iter().fold(-touches_memory, |acc, &s| acc + s));

        // --- register reads / address decode consistency ---
        let registers: Vec<Fp> = (0..NUM_REGISTERS).map(|k| c[COL_REG + k]).collect();
        let memory: Vec<Fp> = (0..NUM_MEMORY).map(|k| c[COL_MEM + k]).collect();
        let val_a = c[COL_VAL_A];
        let val_a_inv = c[COL_VAL_A_INV];
        let val_b = c[COL_VAL_B];
        let write_value = c[COL_WRITE_VALUE];

        cs.push(val_a - dot(&a_sel, &registers));
        cs.push(val_b - dot(&b_sel, &registers));
        let addr_index_value: Fp =
            addr_sel.iter().enumerate().fold(Fp::ZERO, |acc, (k, &s)| acc + Fp::new(k as u64) * s);
        cs.push(touches_memory * (val_a - addr_index_value));

        // --- val_a_inv soundness: forces val_a*val_a_inv to be a genuine is-nonzero indicator ---
        cs.push(val_a * (Fp::ONE - val_a * val_a_inv));

        // --- ALU / write_value per opcode ---
        cs.push(op(c, Opcode::Add) * (write_value - (val_a + val_b)));
        cs.push(op(c, Opcode::Sub) * (write_value - (val_a - val_b)));
        cs.push(op(c, Opcode::Mul) * (write_value - val_a * val_b));
        cs.push(op(c, Opcode::Load) * (write_value - dot(&addr_sel, &memory)));
        cs.push(op(c, Opcode::Store) * (write_value - val_b));

        // --- pc update per opcode ---
        let pc = c[COL_PC];
        let pc_next = n[COL_PC];
        let target = c[COL_TARGET];
        let straight_line =
            op(c, Opcode::Add) + op(c, Opcode::Sub) + op(c, Opcode::Mul) + op(c, Opcode::Load) + op(c, Opcode::Store);
        cs.push(straight_line * (pc_next - (pc + Fp::ONE)));
        cs.push(op(c, Opcode::Jmp) * (pc_next - target));
        let is_nonzero = val_a * val_a_inv;
        cs.push(
            op(c, Opcode::Jmpif)
                * (is_nonzero * (pc_next - target) + (Fp::ONE - is_nonzero) * (pc_next - (pc + Fp::ONE))),
        );
        cs.push(op(c, Opcode::Halt) * (pc_next - pc));

        // --- register write-back: written register takes write_value, others persist ---
        for k in 0..NUM_REGISTERS {
            let expected = registers[k] + dst_sel[k] * (write_value - registers[k]);
            cs.push(n[COL_REG + k] - expected);
        }

        // --- memory write-back: only STORE actually writes ---
        for k in 0..NUM_MEMORY {
            let expected = memory[k] + op(c, Opcode::Store) * addr_sel[k] * (write_value - memory[k]);
            cs.push(n[COL_MEM + k] - expected);
        }

        // --- instruction fetch: bind this row's opcode/operand selectors to
        // the fixed public program, via a one-hot selector over program
        // addresses. ---
        let prog_sel: Vec<Fp> = (0..self.program.len()).map(|k| c[COL_PROG_SEL + k]).collect();
        for &s in &prog_sel {
            cs.push(s * (s - Fp::ONE));
        }
        cs.push(prog_sel.iter().fold(-Fp::ONE, |acc, &s| acc + s));

        let fetch = |consts: &[Fp]| dot(&prog_sel, consts);
        cs.push(c[COL_PC] - fetch(&self.prog_index));
        let opcode_idx = op_flags.iter().enumerate().fold(Fp::ZERO, |acc, (k, &f)| acc + Fp::new(k as u64) * f);
        cs.push(opcode_idx - fetch(&self.prog_opcode));
        let dst_idx = dst_sel.iter().enumerate().fold(Fp::ZERO, |acc, (k, &s)| acc + Fp::new(k as u64) * s);
        cs.push(dst_idx - fetch(&self.prog_dst));
        let a_idx = a_sel.iter().enumerate().fold(Fp::ZERO, |acc, (k, &s)| acc + Fp::new(k as u64) * s);
        cs.push(a_idx - fetch(&self.prog_a));
        let b_idx = b_sel.iter().enumerate().fold(Fp::ZERO, |acc, (k, &s)| acc + Fp::new(k as u64) * s);
        cs.push(b_idx - fetch(&self.prog_b));
        cs.push(target - fetch(&self.prog_target));

        cs
    }

    fn boundary_constraints(&self) -> Vec<BoundaryConstraint> {
        use super::{REG_A, REG_B, REG_CNT, REG_ONE, REG_TMP, REG_ZERO};
        vec![
            BoundaryConstraint { row: 0, column: COL_PC, value: Fp::ZERO },
            BoundaryConstraint { row: 0, column: COL_REG + REG_ZERO, value: Fp::ZERO },
            BoundaryConstraint { row: 0, column: COL_REG + REG_ONE, value: Fp::ONE },
            BoundaryConstraint { row: 0, column: COL_REG + REG_A, value: Fp::ZERO },
            BoundaryConstraint { row: 0, column: COL_REG + REG_B, value: Fp::ONE },
            BoundaryConstraint { row: 0, column: COL_REG + REG_CNT, value: Fp::ZERO },
            BoundaryConstraint { row: 0, column: COL_REG + REG_TMP, value: Fp::ZERO },
            BoundaryConstraint { row: 0, column: COL_MEM, value: self.input },
            BoundaryConstraint { row: 0, column: COL_MEM + 1, value: Fp::ZERO },
            BoundaryConstraint { row: self.last_row, column: COL_OP + Opcode::Halt.index(), value: Fp::ONE },
            BoundaryConstraint { row: self.last_row, column: COL_MEM + 1, value: self.output },
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::check_trace;
    use crate::vm::{Instruction, Opcode, REG_A, REG_ONE, fibonacci_program};

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
    fn fibonacci_trace_satisfies_air() {
        for n in [0u64, 1, 2, 5, 10, 20] {
            let program = fibonacci_program();
            let (trace, output) = generate_trace(&program, Fp::new(n));
            assert_eq!(output, Fp::new(fib_reference(n)), "wrong output for n={n}");

            let air = VmAir::new(program, Fp::new(n), output, trace.rows.len() - 1);
            assert!(check_trace(&air, &trace.rows).is_ok(), "constraint check failed for n={n}");
        }
    }

    #[test]
    fn tampered_write_value_is_rejected() {
        let program = fibonacci_program();
        let (mut trace, output) = generate_trace(&program, Fp::new(10));
        trace.rows[3][COL_WRITE_VALUE] += Fp::ONE;

        let air = VmAir::new(program, Fp::new(10), output, trace.rows.len() - 1);
        assert!(check_trace(&air, &trace.rows).is_err());
    }

    #[test]
    fn wrong_claimed_output_is_rejected() {
        let program = fibonacci_program();
        let (trace, output) = generate_trace(&program, Fp::new(10));

        let air = VmAir::new(program, Fp::new(10), output + Fp::ONE, trace.rows.len() - 1);
        assert!(check_trace(&air, &trace.rows).is_err());
    }

    #[test]
    fn malformed_opcode_one_hot_is_rejected() {
        let program = fibonacci_program();
        let (mut trace, output) = generate_trace(&program, Fp::new(10));
        // Flip a second opcode bit on, breaking the "exactly one" invariant.
        trace.rows[0][COL_OP + Opcode::Halt.index()] = Fp::ONE;

        let air = VmAir::new(program, Fp::new(10), output, trace.rows.len() - 1);
        assert!(check_trace(&air, &trace.rows).is_err());
    }

    #[test]
    fn mul_opcode_satisfies_constraints() {
        // r2 (REG_A) = r1 (REG_ONE) * r1 (REG_ONE) = 1, then halt.
        let program = vec![
            Instruction { opcode: Opcode::Mul, dst: Some(REG_A), a: REG_ONE, b: REG_ONE, target: Fp::ZERO },
            Instruction { opcode: Opcode::Halt, dst: None, a: 0, b: 0, target: Fp::ZERO },
        ];
        let (trace, _output) = generate_trace(&program, Fp::ZERO);
        assert_eq!(trace.rows[1][COL_REG + REG_A], Fp::ONE);

        let air = VmAir::new(program, Fp::ZERO, Fp::ZERO, trace.rows.len() - 1);
        assert!(check_trace(&air, &trace.rows).is_ok());
    }

    #[test]
    fn wrong_opcode_at_correct_pc_is_rejected() {
        let program = fibonacci_program();
        let (mut trace, output) = generate_trace(&program, Fp::new(10));
        let row = &mut trace.rows[3];
        let val_a = row[COL_VAL_A];
        let val_b = row[COL_VAL_B];
        row[COL_OP + Opcode::Add.index()] = Fp::ZERO;
        row[COL_OP + Opcode::Sub.index()] = Fp::ONE;
        row[COL_WRITE_VALUE] = val_a - val_b;

        let air = VmAir::new(program, Fp::new(10), output, trace.rows.len() - 1);
        assert!(check_trace(&air, &trace.rows).is_err());
    }
}
