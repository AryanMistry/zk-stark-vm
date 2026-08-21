//! Turns a program run into the execution trace `VmAir`'s constraints are  checked against: one row per clock cycle, columns laid out below.

use super::{Instruction, NUM_MEMORY, NUM_REGISTERS, Opcode};
use crate::field::Fp;

pub const COL_PC: usize = 0;
pub const COL_REG: usize = COL_PC + 1;
pub const COL_MEM: usize = COL_REG + NUM_REGISTERS;
pub const COL_OP: usize = COL_MEM + NUM_MEMORY;
pub const COL_DST_SEL: usize = COL_OP + Opcode::COUNT;
pub const COL_A_SEL: usize = COL_DST_SEL + NUM_REGISTERS;
pub const COL_B_SEL: usize = COL_A_SEL + NUM_REGISTERS;
pub const COL_ADDR_SEL: usize = COL_B_SEL + NUM_REGISTERS;
pub const COL_VAL_A: usize = COL_ADDR_SEL + NUM_MEMORY;
pub const COL_VAL_A_INV: usize = COL_VAL_A + 1;
pub const COL_VAL_B: usize = COL_VAL_A_INV + 1;
pub const COL_WRITE_VALUE: usize = COL_VAL_B + 1;
pub const COL_TARGET: usize = COL_WRITE_VALUE + 1;
pub const COL_PROG_SEL: usize = COL_TARGET + 1;

pub fn trace_width(program_len: usize) -> usize {
    COL_PROG_SEL + program_len
}

pub struct TraceTable {
    pub rows: Vec<Vec<Fp>>,
}

fn one_hot(len: usize, index: usize) -> Vec<Fp> {
    let mut v = vec![Fp::ZERO; len];
    v[index] = Fp::ONE;
    v
}

/// Runs `program` on `input` (placed in memory[0]) and records the full execution trace, padded with repeated halt-rows to a power-of-two
/// length. Returns the trace and the program's output (memory[1] after halting).
pub fn generate_trace(program: &[Instruction], input: Fp) -> (TraceTable, Fp) {
    // Fixed VM reset state: r0=0, r1=1, r2=0, r3=1 
    let mut registers = [Fp::ZERO; NUM_REGISTERS];
    registers[super::REG_ONE] = Fp::ONE;
    registers[super::REG_B] = Fp::ONE;
    let mut memory = [Fp::ZERO; NUM_MEMORY];
    memory[0] = input;
    let mut pc: usize = 0;

    let width = trace_width(program.len());
    let mut rows = Vec::new();
    loop {
        let instr = program[pc];
        let val_a = registers[instr.a];
        let val_b = registers[instr.b];
        let val_a_inv = val_a.inv().unwrap_or(Fp::ZERO);

        let addr_sel = if matches!(instr.opcode, Opcode::Load | Opcode::Store) {
            one_hot(NUM_MEMORY, val_a.0 as usize)
        } else {
            vec![Fp::ZERO; NUM_MEMORY]
        };

        let (write_value, mem_write, next_pc): (Fp, Option<usize>, usize) = match instr.opcode {
            Opcode::Add => (val_a + val_b, None, pc + 1),
            Opcode::Sub => (val_a - val_b, None, pc + 1),
            Opcode::Mul => (val_a * val_b, None, pc + 1),
            Opcode::Load => (memory[val_a.0 as usize], None, pc + 1),
            Opcode::Store => (val_b, Some(val_a.0 as usize), pc + 1),
            Opcode::Jmp => (Fp::ZERO, None, instr.target.0 as usize),
            Opcode::Jmpif => {
                let next = if !val_a.is_zero() { instr.target.0 as usize } else { pc + 1 };
                (Fp::ZERO, None, next)
            }
            Opcode::Halt => (Fp::ZERO, None, pc),
        };

        let mut row = vec![Fp::ZERO; width];
        row[COL_PC] = Fp::new(pc as u64);
        row[COL_REG..COL_REG + NUM_REGISTERS].copy_from_slice(&registers);
        row[COL_MEM..COL_MEM + NUM_MEMORY].copy_from_slice(&memory);
        row[COL_OP + instr.opcode.index()] = Fp::ONE;
        if let Some(dst) = instr.dst {
            row[COL_DST_SEL..COL_DST_SEL + NUM_REGISTERS].copy_from_slice(&one_hot(NUM_REGISTERS, dst));
        }
        row[COL_A_SEL..COL_A_SEL + NUM_REGISTERS].copy_from_slice(&one_hot(NUM_REGISTERS, instr.a));
        row[COL_B_SEL..COL_B_SEL + NUM_REGISTERS].copy_from_slice(&one_hot(NUM_REGISTERS, instr.b));
        row[COL_ADDR_SEL..COL_ADDR_SEL + NUM_MEMORY].copy_from_slice(&addr_sel);
        row[COL_VAL_A] = val_a;
        row[COL_VAL_A_INV] = val_a_inv;
        row[COL_VAL_B] = val_b;
        row[COL_WRITE_VALUE] = write_value;
        row[COL_TARGET] = instr.target;
        row[COL_PROG_SEL + pc] = Fp::ONE;
        rows.push(row);

        if let Some(dst) = instr.dst {
            registers[dst] = write_value;
        }
        if let Some(addr) = mem_write {
            memory[addr] = write_value;
        }
        let halted = matches!(instr.opcode, Opcode::Halt);
        pc = next_pc;

        if halted {
            break;
        }
    }

    let output = memory[1];

    let target_len = (rows.len() + 1).next_power_of_two();
    let last = rows.last().unwrap().clone();
    while rows.len() < target_len {
        rows.push(last.clone());
    }

    (TraceTable { rows }, output)
}
