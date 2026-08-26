# zk-stark-vm

A STARK proof system built from scratch in Rust with finite field, NTT, FRI, Merkle
commitments, a Fiat-Shamir transcript, AIR constraints, and a DEEP-ALI-style
composition polynomial proving correct execution of a small register VM's program.

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
blinding:       true (50 random coefficients per column)
verified:       true


```

`cargo run --release --example benchmark` measures how this scales. From 256 to
8192 trace rows (a 32x longer computation) proving takes 38x longer, but
verification only 2.2x and the proof only 1.8x. 

## What's actually being proven

The demo program runs on a small register VM (6 registers, a 2-word memory, 8
opcodes: `ADD SUB MUL JMP JMPIF LOAD STORE HALT`) and computes `fibonacci(n)` via a
real loop (`LOAD` the input from memory, a `JMPIF`-gated countdown, register updates
via `ADD`/`SUB`, `STORE` the result back to memory) so the trace has real, data-dependent
control flow.

The STARK proves that *there exists an execution trace of this specific public program,
starting from the VM's fixed reset state with `n` at memory address 0, that reaches
`HALT` with the claimed output at memory address 1.* The verifier never receives the
trace (other than only a Merkle root, a handful of out-of-domain evaluations, and FRI query
openings) and its cost grows logarithmically in the trace length, not linearly.

## On the "zk" in the name

Succinctness and zero-knowledge are two different properties, and it's worth being
precise about which one is here.

**Succinctness** — a verifier much cheaper than re-running the computation — comes from
FRI and the composition polynomial. That part is real and measurable; see the benchmark
above.

**Zero-knowledge** — revealing nothing about the witness. With the default 24 queries that's ~50 points, so
for any trace shorter than ~50 rows the trace polynomials were *fully reconstructable
from the proof alone*. `stark::tests::unblinded_proof_leaks_the_trace` performs exactly
that reconstruction.

What's implemented now: each trace polynomial `T(x)` is replaced with

```
T'(x) = T(x) + r(x) · Z_H(x)        Z_H(x) = x^N − 1,  deg(r) < 2 + 2·num_queries
```

`Z_H` vanishes on the trace domain, so `T'` agrees with `T` at every real trace row and
every constraint still holds untouched. But the LDE lives on a *coset*, disjoint from
the trace domain, which is exactly where `Z_H ≠ 0`, so every value the proof actually
reveals is masked by fresh randomness. The companion test
`blinded_proof_does_not_leak_the_trace` reruns the same reconstruction and shows it now
fails.


### What privacy costs

Blinding raises the trace polynomial degree from `N−1` to `N+k−1`, which raises the
composition polynomial's degree, which forces a larger evaluation domain. Since `k` is a
fixed amount rather than a proportional one, short traces pay for it and long ones
barely notice:

| trace rows | LDE blowup | prove time | proof size |
|---|---|---|---|
| 64 | 8x → 16x | +92% | +16% |
| 128 | 8x → 16x | +96% | +15% |
| 256 and up | 8x → 8x | ~0% | 0% |

Privacy is nearly free for large computations and expensive for tiny ones. Run
`cargo run --release --example benchmark` to reproduce.

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
  benchmark.rs          Scaling sweep + the cost of blinding; writes benchmark.svg.
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
  than through a separate memory-consistency argument. 
- **No calibrated target security level.** `StarkConfig::toy()`'s FRI rate and query
  count are sized to keep proof generation fast for a demo, not derived from a target
  bit-security budget the way a production system's parameters would be.


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
