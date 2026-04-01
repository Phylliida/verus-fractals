///  Generate verified multi-limb Mandelbrot perturbation WGSL shader.
///
///  Uses the SAME perturbation formula as runtime_perturbation_step,
///  but lowered to N-limb carry-chain/Karatsuba arithmetic.
///  Outputs a .wgsl file.

use verus_fractals::gpu_codegen::gen_perturbation_step_exprs;
use verus_fractals::wgsl_codegen::expr_to_wgsl;
use std::fs;

fn main() {
    let n: usize = 2;   // limbs per value (2 = 64-bit)
    let f: usize = 1;   // fractional limbs

    eprintln!("Generating {}-limb ({}-bit) perturbation step...", n, n * 32);

    // Generate the verified perturbation expressions
    let (new_dr_exprs, new_di_exprs) = gen_perturbation_step_exprs(n, f);

    eprintln!("Generated {} limbs for delta_re', {} for delta_im'",
        new_dr_exprs.len(), new_di_exprs.len());

    // Build variable names
    let mut var_names: Vec<String> = Vec::new();
    for prefix in &["zr", "zi", "dr", "di", "dcr", "dci"] {
        for k in 0..n {
            var_names.push(format!("{}_{}", prefix, k));
        }
    }
    let var_refs: Vec<&str> = var_names.iter().map(|s| s.as_str()).collect();

    // Generate WGSL
    let mut wgsl = String::new();
    wgsl.push_str(&format!(
        "// ═══════════════════════════════════════════════════════════\n\
         // VERIFIED {n}-LIMB PERTURBATION STEP (WGSL)\n\
         // Generated from Verus-proved pipeline:\n\
         //   Ring axioms (170 fns) → ArithLimb (53 fns) → Karatsuba (78 fns) → WGSL\n\
         // Formula: delta' = 2*Z*delta + delta^2 + delta_c  (complex)\n\
         // Precision: {bits}-bit fixed-point ({n} limbs × 32 bits)\n\
         // ═══════════════════════════════════════════════════════════\n\n",
        n = n, bits = n * 32));

    // Variable declarations
    wgsl.push_str("// Input variables (N limbs each, little-endian u32):\n");
    for (i, name) in var_names.iter().enumerate() {
        wgsl.push_str(&format!("//   Var({:2}) = {}  ({})\n", i, name,
            match i / n {
                0 => "Z_ref real",
                1 => "Z_ref imag",
                2 => "delta real",
                3 => "delta imag",
                4 => "delta_c real",
                5 => "delta_c imag",
                _ => "?",
            }));
    }
    wgsl.push_str("\n");

    // Perturbation function
    wgsl.push_str(&format!(
        "fn perturbation_step(\n\
         {params}\n\
         ) -> array<u32, {out_n}> {{\n",
        params = var_names.iter().map(|v| format!("  {}: u32,", v)).collect::<Vec<_>>().join("\n"),
        out_n = 2 * n));

    // Output: new_delta_re
    wgsl.push_str("\n  // new_delta_re (verified carry-chain + Karatsuba)\n");
    for (k, expr) in new_dr_exprs.iter().enumerate() {
        let w = expr_to_wgsl(expr, &var_refs);
        wgsl.push_str(&format!("  let ndr_{} = u32({});\n", k, w));
    }

    // Output: new_delta_im
    wgsl.push_str("\n  // new_delta_im (verified carry-chain + Karatsuba)\n");
    for (k, expr) in new_di_exprs.iter().enumerate() {
        let w = expr_to_wgsl(expr, &var_refs);
        wgsl.push_str(&format!("  let ndi_{} = u32({});\n", k, w));
    }

    // Return
    wgsl.push_str(&format!("\n  return array<u32, {}>(", 2 * n));
    for k in 0..n { wgsl.push_str(&format!("ndr_{}, ", k)); }
    for k in 0..n {
        wgsl.push_str(&format!("ndi_{}", k));
        if k < n - 1 { wgsl.push_str(", "); }
    }
    wgsl.push_str(");\n}\n");

    // Write to file
    let path = "verified_perturbation.wgsl";
    fs::write(path, &wgsl).expect("Failed to write WGSL file");
    eprintln!("Written to {} ({} bytes)", path, wgsl.len());
}
