///  Generate verified Mandelbrot WGSL shader.
///  Just calls gen_mandelbrot_step() and emits the result expressions.

use verus_fractals::gpu_codegen::gen_mandelbrot_step;
use verus_fractals::wgsl_codegen::expr_to_wgsl;
use std::fs;

fn main() {
    let n = 2usize;
    let frac = 32usize;

    let (new_zr, new_zi) = gen_mandelbrot_step(n, frac);

    // Variable names
    let names: Vec<String> = ["zr","zi","cr","ci"].iter()
        .flat_map(|p| (0..n).map(move |k| format!("{}_{}", p, k)))
        .collect();
    let refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();

    // Emit each limb expression
    let mut out = String::new();
    for (k, e) in new_zr.iter().enumerate() {
        out += &format!("let nzr_{k} = u32({});\n", expr_to_wgsl(e, &refs));
    }
    for (k, e) in new_zi.iter().enumerate() {
        out += &format!("let nzi_{k} = u32({});\n", expr_to_wgsl(e, &refs));
    }

    fs::write("verified_mandelbrot.wgsl", &out).unwrap();
    eprintln!("Written verified_mandelbrot.wgsl ({} bytes)", out.len());
}
