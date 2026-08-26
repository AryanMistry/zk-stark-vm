//! A tiny register VM: the computation whose execution the STARK proves.
//!
//! 6 registers, a 2-word memory, 8 opcodes. `trace::generate_trace` runs a program
//! and records the trace that `constraints::VmAir` is checked against.

pub mod constraints;
pub mod trace;

use crate::field::Fp;

pub const NUM_REGISTERS: usize = 6;
pub const NUM_MEMORY: usize = 2;

pub const REG_ZERO: usize = 0;
pub const REG_ONE: usize = 1;
pub const REG_A: usize = 2;
pub const REG_B: usize = 3;
pub const REG_CNT: usize = 4;
pub const REG_TMP: usize = 5;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Opcode {
    Add,
    Sub,
    Mul,
    Jmp,
    Jmpif,
    Load,
    Store,
    Halt,
}

impl Opcode {
    pub const COUNT: usize = 8;
    pub const ALL: [Opcode; 8] = [
        Opcode::Add,
        Opcode::Sub,
        Opcode::Mul,
        Opcode::Jmp,
        Opcode::Jmpif,
        Opcode::Load,
        Opcode::Store,
        Opcode::Halt,
    ];

    pub fn index(self) -> usize {
        Self::ALL.iter().position(|&op| op == self).unwrap()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Instruction {
    pub opcode: Opcode,
    /// Register written, if any (None for JMP/JMPIF/STORE/HALT).
    pub dst: Option<usize>,
    /// Register read as the first operand. Also doubles as the address
    /// register for LOAD/STORE and the condition register for JMPIF.
    pub a: usize,
    /// Register read as the second operand. Doubles as the source register
    /// for STORE. Ignored (by convention REG_ZERO) where unused.
    pub b: usize,
    /// Jump target, used only by JMP/JMPIF.
    pub target: Fp,
}

impl Instruction {
    fn new(opcode: Opcode, dst: Option<usize>, a: usize, b: usize, target: u64) -> Self {
        Instruction { opcode, dst, a, b, target: Fp::new(target) }
    }
}

/// fibonacci(n) via a real loop: LOAD the input, count down accumulating
/// (a, b) = (F(k), F(k+1)), STORE the result.
pub fn fibonacci_program() -> Vec<Instruction> {
    use Opcode::*;
    vec![
        Instruction::new(Load, Some(REG_CNT), REG_ZERO, REG_ZERO, 0), // 0: cnt = mem[0]
        Instruction::new(Jmpif, None, REG_CNT, REG_ZERO, 3),          // 1: if cnt != 0 goto 3
        Instruction::new(Jmp, None, REG_ZERO, REG_ZERO, 8),           // 2: goto 8
        Instruction::new(Add, Some(REG_TMP), REG_A, REG_B, 0),        // 3: tmp = a + b
        Instruction::new(Add, Some(REG_A), REG_B, REG_ZERO, 0),       // 4: a = b
        Instruction::new(Add, Some(REG_B), REG_TMP, REG_ZERO, 0),     // 5: b = tmp
        Instruction::new(Sub, Some(REG_CNT), REG_CNT, REG_ONE, 0),    // 6: cnt -= 1
        Instruction::new(Jmp, None, REG_ZERO, REG_ZERO, 1),           // 7: goto 1
        Instruction::new(Store, None, REG_ONE, REG_B, 0),             // 8: mem[1] = b
        Instruction::new(Halt, None, REG_ZERO, REG_ZERO, 0),          // 9: halt
    ]
}
