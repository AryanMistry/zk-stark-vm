# zk-stark-vm

A STARK proof system built from scratch in Rust — finite field, NTT, FRI, Merkle
commitments, a Fiat-Shamir transcript, AIR constraints, and a DEEP-ALI-style
composition polynomial — proving correct execution of a small register VM's program,
including real loops and branching, not just straight-line arithmetic.

```
cargo test
cargo run --release --example prove_fibonacci 30
```

```
zk-stark-vm — proving fibonacci(30) via a real loop on the toy VM

program:        10 instructions
trace length:   256 rows (padded to a power of two)
output:         fibonacci(30) = 1346269
prove time:     ~8ms
verify time:    ~1ms
proof size:     ~147 KiB
verified:       true
```

## What's actually being proven

The demo program runs on a small register VM (6 registers, a 2-word memory, 8
opcodes: `ADD SUB MUL JMP JMPIF LOAD STORE HALT`) and computes `fibonacci(n)` via a
real loop — `LOAD` the input from memory, a `JMPIF`-gated countdown, register updates
via `ADD`/`SUB`, `STORE` the result back to memory — so the trace has real, data-dependent
control flow, not an unrolled/fixed sequence of instructions.

The STARK proves: *there exists an execution trace of this specific public program,
starting from the VM's fixed reset state with `n` at memory address 0, that reaches
`HALT` with the claimed output at memory address 1.* The verifier never sees the trace
— only a Merkle root, a handful of out-of-domain evaluations, and FRI query openings —
and runs in roughly constant time regardless of how many loop iterations the trace
actually took.

## Architecture

```
field.rs        Goldilocks field (p = 2^64 - 2^32 + 1): the specialized fast
                 reduction, Fermat inversion, batch inversion.
poly.rs          Dense polynomials: eval, multiply (naive + NTT), long division,
                 Lagrange interpolation.
ntt.rs            NTT/INTT over Goldilocks roots of unity, subgroup interpolation,
                  coset low-degree extension.
merkle.rs         Merkle tree over field-element leaves, domain-separated hashing.
transcript.rs      Fiat-Shamir transcript (absorb / squeeze) — the non-interactivity
                   mechanism every later phase depends on.
fri.rs              FRI: commit (fold + Merkle-commit each layer) and query phases,
                    prover and verifier.
air.rs               The `Air` trait: transition + boundary constraints, and a direct
                     ("raw") checker used by the AIR's own unit tests.
vm/                  The toy VM:
  mod.rs               ISA, register/memory layout, the fibonacci program.
  trace.rs             Program run -> execution trace table.
  constraints.rs       `VmAir`: the VM's opcodes as AIR transition constraints.
stark/                Ties everything together into an actual STARK:
  mod.rs                Shared types (`StarkProof`, `StarkConfig`) and the
                        composition-polynomial logic prover and verifier both call,
                        so they can't accidentally diverge on the formula.
  prover.rs             Trace -> LDE -> commitment -> composition polynomial -> FRI.
  verifier.rs           Replays the transcript, checks trace openings against the
                        composition FRI claims, checks FRI itself.
examples/
  prove_fibonacci.rs    The end-to-end demo above.
```



## Deliberate scope decisions

A few things were consciously left out, each documented in more detail at its point of
use in the code:

- **Instruction fetch** is bound to the specific public program via a *direct one-hot
  lookup* (`vm/constraints.rs`) rather than a randomized permutation/lookup argument.
  For a program this small (a handful of instructions), that's both simpler and
  stronger which is an exact identity rather than a probabilistic check with its own
  soundness-error budget. A much larger table (general-purpose RAM, range checks) is
  where a real lookup argument (Plookup/LogUp-style) would earn its keep instead.
- **Memory** is modeled as a small, fixed-width set of trace columns (2 words) rather
  than through a separate memory-consistency argument. Fine for a toy VM; a
  general-purpose zkVM's random-access memory is a genuinely hard problem this project
  doesn't attempt.
- **No calibrated target security level.** `StarkConfig::toy()`'s LDE blowup, FRI rate,
  and query count are sized generously enough to be *correct* and to keep proof generation fast for a demo, not derived
  from a target bit-security budget the way a production system's parameters would be.
- The trace's last row is excluded from transition-constraint checking (no wraparound
  from the last row back to the first).

## Verification approach

Every phase has unit and property-based tests (`proptest`) colocated in its module,
including cross-checks of optimized code paths (fast field reduction, NTT-based
multiplication, batch inversion) against naive reference implementations. The AIR and
STARK layers additionally have negative tests: a tampered trace, a wrong claimed
output, a tampered proof opening, and a forged opcode that's
internally ALU-consistent but doesn't match the public program at that program counter,
are all rejected. `cargo test` runs all of it.

## License

MIT
