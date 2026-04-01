///  Generate verified Mandelbrot WGSL shader using the KernelDesc infrastructure.
///
///  Pipeline: GenericFixedPoint<ArithLimb> → RuntimeArithExpr → WgslExpr → KernelDesc → WGSL

use verus_fractals::gpu_codegen::gen_mandelbrot_step;
use verus_fractals::wgsl_codegen::to_wgsl_expr;
use verus_cutedsl_codegen::*;
use std::fs;

fn main() {
    let n = 2usize;      // 2 limbs = 64-bit
    let frac = 32usize;  // 32 fractional bits

    // Minimal output — shader goes to file, not stdout

    // Step 1: Generate verified iteration expressions from Rust code
    let (new_zr, new_zi) = gen_mandelbrot_step(n, frac);

    // Step 2: Build KernelDesc using existing infrastructure
    //
    // Buffer layout:
    //   buf 0: z_re[pixel * N + limb]  (read_write)
    //   buf 1: z_im[pixel * N + limb]  (read_write)
    //   buf 2: c_re[pixel * N + limb]  (read)
    //   buf 3: c_im[pixel * N + limb]  (read)
    //
    // Thread variable: Var(0) = pixel index (tid)
    // Input limbs are read from buffers via Index(buf, tid * N + k)

    // Variable names for limb expressions
    // The ArithExpr Var indices map to buffer reads:
    //   Var(0*N..1*N-1) = z_re limbs → buf 0
    //   Var(1*N..2*N-1) = z_im limbs → buf 1
    //   Var(2*N..3*N-1) = c_re limbs → buf 2
    //   Var(3*N..4*N-1) = c_im limbs → buf 3
    let mut var_names: Vec<String> = Vec::new();
    for prefix in &["zr", "zi", "cr", "ci"] {
        for k in 0..n {
            var_names.push(format!("{}_{}", prefix, k));
        }
    }

    // Build outputs: each result limb writes to the output buffer
    let mut outputs = Vec::new();

    // z_re' limbs → buffer "z_re"
    for (k, expr) in new_zr.iter().enumerate() {
        outputs.push(OutputDesc {
            scatter: WgslExpr::Add(
                Box::new(WgslExpr::Mul(
                    Box::new(WgslExpr::Var(0)),  // tid
                    Box::new(WgslExpr::Const(n as i64)))),
                Box::new(WgslExpr::Const(k as i64))),
            compute: to_wgsl_expr(expr),
            buffer_name: "z_re".into(),
        });
    }

    // z_im' limbs → buffer "z_im"
    for (k, expr) in new_zi.iter().enumerate() {
        outputs.push(OutputDesc {
            scatter: WgslExpr::Add(
                Box::new(WgslExpr::Mul(
                    Box::new(WgslExpr::Var(0)),
                    Box::new(WgslExpr::Const(n as i64)))),
                Box::new(WgslExpr::Const(k as i64))),
            compute: to_wgsl_expr(expr),
            buffer_name: "z_im".into(),
        });
    }

    // 2D dispatch: px = gid.x, py = gid.y
    // pixel_idx = py * width + px
    let pixel_idx = WgslExpr::Add(
        Box::new(WgslExpr::Mul(
            Box::new(WgslExpr::Var(1)),   // py
            Box::new(WgslExpr::Var(2)))), // width
        Box::new(WgslExpr::Var(0)));      // px

    // Rewrite scatter to use 2D pixel index
    for output in &mut outputs {
        // Replace Var(0) (tid) with pixel_idx in scatter
        output.scatter = WgslExpr::Add(
            Box::new(WgslExpr::Mul(
                Box::new(pixel_idx.clone()),
                Box::new(WgslExpr::Const(n as i64)))),
            Box::new(match &output.scatter {
                WgslExpr::Add(_, k) => (**k).clone(), // extract limb offset
                _ => WgslExpr::Const(0),
            }));
    }

    let kernel = KernelDesc {
        name: "mandelbrot_step".into(),
        // Guard: px < width && py < height
        guard: WgslExpr::Mul(  // Mul(Cmp, Cmp) emits as &&
            Box::new(WgslExpr::Cmp(CmpOp::Lt,
                Box::new(WgslExpr::Var(0)),    // px
                Box::new(WgslExpr::Var(2)))),   // width
            Box::new(WgslExpr::Cmp(CmpOp::Lt,
                Box::new(WgslExpr::Var(1)),    // py
                Box::new(WgslExpr::Var(3))))),  // height
        outputs,
        buffers: vec![
            BufferDesc { name: "z_re".into(), binding: 0, read_only: false },
            BufferDesc { name: "z_im".into(), binding: 1, read_only: false },
            BufferDesc { name: "c_re".into(), binding: 2, read_only: true },
            BufferDesc { name: "c_im".into(), binding: 3, read_only: true },
        ],
        var_names: vec!["px".into(), "py".into(), "width".into(), "height".into()],
        workgroup_size: [16, 16, 1],
        dispatch_dims: 2,
    };

    // Step 3: Emit complete WGSL shader
    let shader = emit_kernel_wgsl(&kernel);

    let path = "verified_mandelbrot.wgsl";
    fs::write(path, &shader).unwrap();
    println!("Written {} ({} bytes)", path, shader.len());
}
