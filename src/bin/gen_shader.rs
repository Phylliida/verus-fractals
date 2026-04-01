///  Generate verified multi-limb Mandelbrot WGSL shader with iteration loop.
///
///  Pipeline: GenericFixedPoint<ArithLimb> → WgslExpr → StageDesc::Loop → WGSL

use verus_fractals::gpu_codegen::gen_mandelbrot_step;
use verus_fractals::wgsl_codegen::to_wgsl_expr;
use verus_cutedsl_codegen::*;
use std::fs;

fn main() {
    let n = 4usize;       // 4 limbs = 128-bit (start small, can increase)
    let frac = 64usize;   // 64 fractional bits (2 limbs)

    // Generate verified iteration body
    let (new_zr, new_zi) = gen_mandelbrot_step(n, frac);

    // Variable names: px, py, width, height + limb names for expressions
    let mut var_names = vec!["px".to_string(), "py".to_string(),
                             "width".to_string(), "height".to_string()];
    for prefix in &["zr", "zi", "cr", "ci"] {
        for k in 0..n {
            var_names.push(format!("{}_{}", prefix, k));
        }
    }

    // Pixel index for buffer access
    let pixel_idx = WgslExpr::Add(
        Box::new(WgslExpr::Mul(
            Box::new(WgslExpr::Var(1)),   // py
            Box::new(WgslExpr::Var(2)))), // width
        Box::new(WgslExpr::Var(0)));      // px

    // State variables: z_re limbs + z_im limbs (mutated each iteration)
    let mut state_vars = Vec::new();
    let mut state_init = Vec::new();
    let mut state_update = Vec::new();

    for k in 0..n {
        state_vars.push(format!("zr_{}", k));
        state_init.push(WgslExpr::Const(0)); // z starts at 0
        state_update.push(to_wgsl_expr(&new_zr[k]));
    }
    for k in 0..n {
        state_vars.push(format!("zi_{}", k));
        state_init.push(WgslExpr::Const(0));
        state_update.push(to_wgsl_expr(&new_zi[k]));
    }

    // Read c from buffers into local vars (these are read-only, not state)
    // We'll add them as init code in a Seq before the loop
    // For now: c limbs are read via Index expressions in the compute

    // Final output: write iteration count
    let final_outputs = vec![
        ("output".to_string(),
         pixel_idx.clone(),
         WgslExpr::Var(var_names.iter().position(|s| s == "px").unwrap() as u32)), // _iter placeholder
    ];

    // Build shader with StageDesc::Loop
    let shader_desc = ShaderDesc {
        name: "mandelbrot".into(),
        stage: StageDesc::Seq(vec![
            // Guard: px < width && py < height
            StageDesc::Map(KernelDesc {
                name: "guard".into(),
                guard: WgslExpr::Mul(
                    Box::new(WgslExpr::Cmp(CmpOp::Lt,
                        Box::new(WgslExpr::Var(0)),
                        Box::new(WgslExpr::Var(2)))),
                    Box::new(WgslExpr::Cmp(CmpOp::Lt,
                        Box::new(WgslExpr::Var(1)),
                        Box::new(WgslExpr::Var(3))))),
                outputs: vec![],
                buffers: vec![],
                var_names: vec![],
                workgroup_size: [16, 16, 1],
                dispatch_dims: 2,
            }),
            // Iteration loop
            StageDesc::Loop {
                bound: WgslExpr::Const(256), // max_iter
                state_vars,
                state_init,
                state_update,
                break_cond: None, // TODO: escape check |z|² > 4
                final_outputs: vec![
                    ("output".into(), pixel_idx, WgslExpr::Var(0)), // _iter
                ],
            },
        ]),
        buffers: vec![
            BufferDesc { name: "c_re".into(), binding: 0, read_only: true },
            BufferDesc { name: "c_im".into(), binding: 1, read_only: true },
            BufferDesc { name: "output".into(), binding: 2, read_only: false },
        ],
        var_names,
        workgroup_size: [16, 16, 1],
        dispatch_dims: 2,
    };

    let shader = emit_shader_wgsl(&shader_desc);
    let path = "verified_mandelbrot.wgsl";
    fs::write(path, &shader).unwrap();
    println!("Written {} ({} bytes, {} lines)", path, shader.len(), shader.lines().count());
}
