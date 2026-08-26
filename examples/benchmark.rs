//! Benchmark sweep: how prove time, verify time, and proof size scale as
//! the execution trace grows.

use std::time::Instant;

use zk_stark_vm::air::Air;
use zk_stark_vm::field::Fp;
use zk_stark_vm::stark::{StarkConfig, prover, verifier};
use zk_stark_vm::vm::constraints::VmAir;
use zk_stark_vm::vm::fibonacci_program;
use zk_stark_vm::vm::trace::generate_trace;

/// Chosen so padded trace lengths land on successive powers of two.
const INPUTS: [u64; 8] = [5, 10, 30, 60, 125, 250, 500, 1000];

struct Measurement {
    n: u64,
    rows: usize,
    blowup: usize,
    prove_ms: f64,
    verify_ms: f64,
    proof_bytes: usize,
}

fn best_of(reps: usize, mut f: impl FnMut()) -> f64 {
    (0..reps)
        .map(|_| {
            let t = Instant::now();
            f();
            t.elapsed().as_secs_f64() * 1000.0
        })
        .fold(f64::INFINITY, f64::min)
}

fn measure(n: u64, config: &StarkConfig) -> Measurement {
    let program = fibonacci_program();
    let (trace, output) = generate_trace(&program, Fp::new(n));
    let rows = trace.rows.len();
    let air = VmAir::new(program, Fp::new(n), output, rows - 1);

    let _ = prover::prove(&air, &trace.rows, config);

    let prove_reps = (4096 / rows).clamp(2, 20);
    let prove_ms = best_of(prove_reps, || {
        let _ = prover::prove(&air, &trace.rows, config);
    });

    let proof = prover::prove(&air, &trace.rows, config);
    let proof_bytes = bincode::serialize(&proof).expect("proof serialization").len();

    let verify_ms = best_of(20, || {
        let verified = verifier::verify(&air, rows, &proof, config);
        assert!(verified, "honest proof failed to verify at n={n} — this is a bug");
    });

    let blowup = config.lde_blowup(rows, air.max_constraint_degree());
    Measurement { n, rows, blowup, prove_ms, verify_ms, proof_bytes }
}

fn main() {
    let out_path = std::env::args().nth(1).unwrap_or_else(|| "benchmark.svg".to_string());
    let config = StarkConfig::toy();

    println!("zk-stark-vm — scaling benchmark");
    println!("(blinding on: trace polynomials are masked before commitment)\n");
    println!("{:>6} {:>7} {:>7} {:>12} {:>12} {:>12}", "n", "rows", "blowup", "prove", "verify", "proof");
    println!("{}", "-".repeat(61));

    let mut results = Vec::new();
    for &n in &INPUTS {
        let m = measure(n, &config);
        println!(
            "{:>6} {:>7} {:>6}x {:>10.2}ms {:>10.2}ms {:>9.1}KiB",
            m.n,
            m.rows,
            m.blowup,
            m.prove_ms,
            m.verify_ms,
            m.proof_bytes as f64 / 1024.0
        );
        results.push(m);
    }

    // Only compare across a shared blowup: spanning that boundary would mix
    // "the trace got longer" with "the domain got wider".
    let last = results.last().expect("at least one measurement");
    let first = results
        .iter()
        .filter(|m| m.blowup == last.blowup)
        .min_by_key(|m| m.rows)
        .expect("at least one measurement");
    let trace_growth = last.rows as f64 / first.rows as f64;
    let prove_growth = last.prove_ms / first.prove_ms;
    let verify_growth = last.verify_ms / first.verify_ms;
    let size_growth = last.proof_bytes as f64 / first.proof_bytes as f64;

    println!("\nfrom {} to {} rows (both at {}x blowup) the trace grew {trace_growth:.0}x:", first.rows, last.rows, last.blowup);
    println!("  prove time   grew {prove_growth:>5.1}x  (quasilinear in trace length)");
    println!("  verify time  grew {verify_growth:>5.1}x  (logarithmic — this is succinctness)");
    println!("  proof size   grew {size_growth:>5.1}x  (logarithmic)");

    // What privacy costs: blinding adds a fixed degree, so short traces pay most.
    let plain = StarkConfig::toy_without_blinding();
    println!("\ncost of blinding (vs. the same parameters with it off):");
    println!("{:>6} {:>7} {:>16} {:>14} {:>14}", "n", "rows", "blowup", "prove", "proof");
    println!("{}", "-".repeat(61));
    for &n in &INPUTS {
        let blinded = results.iter().find(|m| m.n == n).expect("measured above");
        let bare = measure(n, &plain);
        println!(
            "{:>6} {:>7} {:>7}x -> {:>2}x {:>12} {:>13}",
            n,
            bare.rows,
            bare.blowup,
            blinded.blowup,
            format!("{:+.0}%", (blinded.prove_ms / bare.prove_ms - 1.0) * 100.0),
            format!("{:+.0}%", (blinded.proof_bytes as f64 / bare.proof_bytes as f64 - 1.0) * 100.0),
        );
    }

    std::fs::write(&out_path, render_svg(&results)).expect("writing chart");
    println!("\nchart written to {out_path}");
}

const WIDTH: f64 = 900.0;
const HEIGHT: f64 = 620.0;
const LEFT: f64 = 95.0;
const RIGHT: f64 = WIDTH - 190.0;

const TIME_TOP: f64 = 70.0;
const TIME_BOTTOM: f64 = 330.0;
const SIZE_TOP: f64 = 420.0;
const SIZE_BOTTOM: f64 = 560.0;

fn time_y(ms: f64) -> f64 {
    let (lo, hi) = (0.1f64, 1000.0f64);
    let t = (ms.log10() - lo.log10()) / (hi.log10() - lo.log10());
    TIME_BOTTOM - t * (TIME_BOTTOM - TIME_TOP)
}

fn size_y(kib: f64) -> f64 {
    SIZE_BOTTOM - (kib / 300.0) * (SIZE_BOTTOM - SIZE_TOP)
}

fn x_at(i: usize, count: usize) -> f64 {
    LEFT + (i as f64 / (count - 1) as f64) * (RIGHT - LEFT)
}

fn polyline(points: &[(f64, f64)], color: &str) -> String {
    let coords: Vec<String> = points.iter().map(|(x, y)| format!("{x:.1},{y:.1}")).collect();
    format!(
        "<polyline points=\"{}\" fill=\"none\" stroke=\"{color}\" stroke-width=\"2.5\" \
         stroke-linejoin=\"round\" stroke-linecap=\"round\"/>",
        coords.join(" ")
    )
}

fn dots(points: &[(f64, f64)], color: &str) -> String {
    points
        .iter()
        .map(|(x, y)| format!("<circle cx=\"{x:.1}\" cy=\"{y:.1}\" r=\"4\" fill=\"{color}\"/>"))
        .collect()
}

fn render_svg(results: &[Measurement]) -> String {
    let count = results.len();
    let prove: Vec<(f64, f64)> =
        results.iter().enumerate().map(|(i, m)| (x_at(i, count), time_y(m.prove_ms))).collect();
    let verify: Vec<(f64, f64)> =
        results.iter().enumerate().map(|(i, m)| (x_at(i, count), time_y(m.verify_ms))).collect();
    let size: Vec<(f64, f64)> = results
        .iter()
        .enumerate()
        .map(|(i, m)| (x_at(i, count), size_y(m.proof_bytes as f64 / 1024.0)))
        .collect();

    let mut s = String::new();
    s.push_str(&format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{WIDTH}\" height=\"{HEIGHT}\" \
         viewBox=\"0 0 {WIDTH} {HEIGHT}\" font-family=\"ui-sans-serif, system-ui, -apple-system, \
         'Segoe UI', Helvetica, Arial, sans-serif\">"
    ));
    s.push_str(&format!("<rect width=\"{WIDTH}\" height=\"{HEIGHT}\" fill=\"#ffffff\"/>"));

    // Titles.
    s.push_str(&format!(
        "<text x=\"{LEFT}\" y=\"38\" font-size=\"21\" font-weight=\"600\" fill=\"#16161a\">\
         Proving vs. verifying, as the execution trace grows</text>"
    ));
    s.push_str(&format!(
        "<text x=\"{LEFT}\" y=\"58\" font-size=\"13.5\" fill=\"#6a6a75\">\
         zk-stark-vm — STARK proof of a Fibonacci loop on a toy register VM</text>"
    ));

    // --- timing panel ---
    for (ms, label) in [(0.1, "0.1 ms"), (1.0, "1 ms"), (10.0, "10 ms"), (100.0, "100 ms"), (1000.0, "1 s")] {
        let y = time_y(ms);
        s.push_str(&format!(
            "<line x1=\"{LEFT}\" y1=\"{y:.1}\" x2=\"{RIGHT}\" y2=\"{y:.1}\" stroke=\"#e8e8ee\" stroke-width=\"1\"/>"
        ));
        s.push_str(&format!(
            "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"12\" fill=\"#8a8a95\" text-anchor=\"end\">{label}</text>",
            LEFT - 12.0,
            y + 4.0
        ));
    }
    s.push_str(&format!(
        "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"12.5\" font-weight=\"600\" fill=\"#6a6a75\" \
         text-anchor=\"middle\" transform=\"rotate(-90 {:.1} {:.1})\">time (log scale)</text>",
        LEFT - 62.0,
        (TIME_TOP + TIME_BOTTOM) / 2.0,
        LEFT - 62.0,
        (TIME_TOP + TIME_BOTTOM) / 2.0
    ));

    s.push_str(&polyline(&prove, "#d94f42"));
    s.push_str(&dots(&prove, "#d94f42"));
    s.push_str(&polyline(&verify, "#2f7dc4"));
    s.push_str(&dots(&verify, "#2f7dc4"));

    let (px, py) = *prove.last().expect("non-empty");
    s.push_str(&format!(
        "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"14\" font-weight=\"600\" fill=\"#d94f42\">prove</text>",
        px + 14.0,
        py + 5.0
    ));
    let (vx, vy) = *verify.last().expect("non-empty");
    s.push_str(&format!(
        "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"14\" font-weight=\"600\" fill=\"#2f7dc4\">verify</text>",
        vx + 14.0,
        vy + 5.0
    ));

    let first = &results[0];
    let last = &results[count - 1];
    let trace_growth = last.rows as f64 / first.rows as f64;
    let verify_growth = last.verify_ms / first.verify_ms;
    s.push_str(&format!(
        "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"13.5\" fill=\"#2f7dc4\">\
         trace x{trace_growth:.0}  →  verify x{verify_growth:.1}</text>",
        vx + 14.0,
        vy + 26.0
    ));

    s.push_str(&format!(
        "<text x=\"{LEFT}\" y=\"{:.1}\" font-size=\"14\" font-weight=\"600\" fill=\"#16161a\">Proof size</text>",
        SIZE_TOP - 26.0
    ));
    for (kib, label) in [(0.0, "0"), (100.0, "100 KiB"), (200.0, "200 KiB"), (300.0, "300 KiB")] {
        let y = size_y(kib);
        s.push_str(&format!(
            "<line x1=\"{LEFT}\" y1=\"{y:.1}\" x2=\"{RIGHT}\" y2=\"{y:.1}\" stroke=\"#e8e8ee\" stroke-width=\"1\"/>"
        ));
        s.push_str(&format!(
            "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"12\" fill=\"#8a8a95\" text-anchor=\"end\">{label}</text>",
            LEFT - 12.0,
            y + 4.0
        ));
    }
    s.push_str(&polyline(&size, "#6b4fa8"));
    s.push_str(&dots(&size, "#6b4fa8"));
    let (sx, sy) = *size.last().expect("non-empty");
    s.push_str(&format!(
        "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"14\" font-weight=\"600\" fill=\"#6b4fa8\">size</text>",
        sx + 14.0,
        sy + 5.0
    ));

    // Shared x axis labels.
    for (i, m) in results.iter().enumerate() {
        let x = x_at(i, count);
        s.push_str(&format!(
            "<text x=\"{x:.1}\" y=\"{:.1}\" font-size=\"12\" fill=\"#8a8a95\" text-anchor=\"middle\">{}</text>",
            SIZE_BOTTOM + 22.0,
            m.rows
        ));
    }
    s.push_str(&format!(
        "<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"12.5\" font-weight=\"600\" fill=\"#6a6a75\" \
         text-anchor=\"middle\">execution trace length (rows)</text>",
        (LEFT + RIGHT) / 2.0,
        SIZE_BOTTOM + 46.0
    ));

    s.push_str("</svg>");
    s
}
