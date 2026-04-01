///  Generate verified multi-limb Mandelbrot WGSL shader with iteration loop.

use verus_fractals::gpu_codegen::gen_mandelbrot_step;
use verus_fractals::wgsl_codegen::to_wgsl_expr;
use verus_cutedsl_codegen::*;
use std::fs;

fn main() {
    let n = 4usize;
    let frac = 64usize;

    let (new_zr, new_zi) = gen_mandelbrot_step(n, frac);

    // Convert iteration body to WgslExpr
    // The expressions use var names: zr_0..3, zi_0..3, cr_0..3, ci_0..3
    let var_names: Vec<String> = ["zr","zi","cr","ci"].iter()
        .flat_map(|p| (0..n).map(move |k| format!("{}_{}", p, k)))
        .collect();
    let var_refs: Vec<&str> = var_names.iter().map(|s| s.as_str()).collect();

    // Build the WGSL manually with proper buffer reads and params
    let mut shader = String::new();

    shader.push_str(&format!(
"// ═══════════════════════════════════════════════════════════════
// VERIFIED {n}-LIMB ({bits}-BIT) MANDELBROT COMPUTE SHADER
// Generated from: GenericFixedPoint<ArithLimb> → Karatsuba → WGSL
// Pipeline: LimbOps (78 verified) → ArithLimb (53 verified) → emit
// ═══════════════════════════════════════════════════════════════

struct Params {{
  width: u32,
  height: u32,
  max_iter: u32,
  _pad: u32,
}}

@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> c_re: array<u32>;
@group(0) @binding(2) var<storage, read> c_im: array<u32>;
@group(0) @binding(3) var<storage, read_write> output: array<u32>;

@compute @workgroup_size(16, 16, 1)
fn mandelbrot(@builtin(global_invocation_id) gid: vec3<u32>) {{
  let px = gid.x;
  let py = gid.y;
  if (px >= params.width || py >= params.height) {{ return; }}
  let idx = py * params.width + px;

  // Load c from buffer
", n=n, bits=n*32));

    for k in 0..n {
        shader.push_str(&format!("  let cr_{k} = c_re[idx * {n}u + {k}u];\n", k=k, n=n));
    }
    for k in 0..n {
        shader.push_str(&format!("  let ci_{k} = c_im[idx * {n}u + {k}u];\n", k=k, n=n));
    }

    shader.push_str("\n  // Init z = 0\n");
    for k in 0..n {
        shader.push_str(&format!("  var zr_{}: u32 = 0u;\n", k));
    }
    for k in 0..n {
        shader.push_str(&format!("  var zi_{}: u32 = 0u;\n", k));
    }

    shader.push_str("
  var iter: u32 = 0u;
  for (var _i: u32 = 0u; _i < params.max_iter; _i++) {
    // TODO: escape check |z|² > 4

    // ─── Verified iteration: z' = z² + c ───
    // Generated from GenericFixedPoint<ArithLimb>.mul/.sub/.add
    // Each expression is a verified Karatsuba + carry-chain
");

    // Emit verified expressions as temporaries
    for (k, expr) in new_zr.iter().enumerate() {
        let w = to_wgsl_expr(expr).emit(&var_refs, &[]);
        shader.push_str(&format!("    let _nzr_{} = u32({});\n", k, w));
    }
    for (k, expr) in new_zi.iter().enumerate() {
        let w = to_wgsl_expr(expr).emit(&var_refs, &[]);
        shader.push_str(&format!("    let _nzi_{} = u32({});\n", k, w));
    }

    shader.push_str("\n    // Update state\n");
    for k in 0..n {
        shader.push_str(&format!("    zr_{k} = _nzr_{k};\n", k=k));
    }
    for k in 0..n {
        shader.push_str(&format!("    zi_{k} = _nzi_{k};\n", k=k));
    }
    shader.push_str("    iter = _i + 1u;\n");

    shader.push_str("  }\n\n");
    shader.push_str("  // Output iteration count\n");
    shader.push_str("  output[idx] = iter;\n");
    shader.push_str("}\n");

    let path = "verified_mandelbrot.wgsl";
    fs::write(path, &shader).unwrap();
    println!("Written {} ({} bytes, {} lines)", path, shader.len(), shader.lines().count());
}
