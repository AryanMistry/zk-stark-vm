//! End-to-end demo: compile the toy VM's fibonacci-via-loop program, run
//! it, generate a STARK proof of correct execution, serialize it, verify
//! it, and report proof size and prover/verifier timings.


use std::time::Instant;

use zk_stark_vm::field::Fp;
use zk_stark_vm::stark::{StarkConfig, prover, verifier};
use zk_stark_vm::vm::constraints::VmAir;
use zk_stark_vm::vm::fibonacci_program;
use zk_stark_vm::vm::trace::generate_trace;

fn main() {
    let n: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(30);

    println!("zk-stark-vm — proving fibonacci({n}) via a real loop on the toy VM\n");

    let program = fibonacci_program();

    let t_trace = Instant::now();
    let (trace, output) = generate_trace(&program, Fp::new(n));
    let trace_time = t_trace.elapsed();

    let trace_len = trace.rows.len();
    println!("program:        {} instructions", program.len());
    println!("trace length:   {trace_len} rows (padded to a power of two)");
    println!("output:         fibonacci({n}) = {output}");
    println!("trace gen time: {trace_time:?}\n");

    let air = VmAir::new(program, Fp::new(n), output, trace_len - 1);
    let config = StarkConfig::toy();

    let t_prove = Instant::now();
    let proof = prover::prove(&air, &trace.rows, &config);
    let prove_time = t_prove.elapsed();

    let proof_bytes = bincode::serialize(&proof).expect("proof serialization");

    let t_verify = Instant::now();
    let honest_result = verifier::verify(&air, trace_len, &proof, &config);
    let verify_time = t_verify.elapsed();

    println!("prove time:     {prove_time:?}");
    println!("verify time:    {verify_time:?}");
    println!("proof size:     {} bytes ({:.1} KiB)", proof_bytes.len(), proof_bytes.len() as f64 / 1024.0);
    println!("verified:       {honest_result}\n");
    assert!(honest_result, "honest proof failed to verify — this is a bug");

    let mut tampered = proof;
    tampered.ood_current[0] += Fp::ONE;
    let tampered_result = verifier::verify(&air, trace_len, &tampered, &config);
    println!("tampered proof verified: {tampered_result} (expected: false)");
    assert!(!tampered_result, "tampered proof was accepted — this is a soundness bug");

    println!("\nall checks passed.");
}
