#[cfg(verus_keep_ghost)]
pub mod complex;

#[cfg(verus_keep_ghost)]
pub mod mandelbrot;

#[cfg(verus_keep_ghost)]
pub mod bla;

#[cfg(verus_keep_ghost)]
pub mod bla_kernels;

#[cfg(verus_keep_ghost)]
pub mod mandelbrot_stage;

#[cfg(verus_keep_ghost)]
pub mod gpu_fixed_point;

#[cfg(verus_keep_ghost)]
pub mod gpu_ring_test;

pub mod gpu_codegen;
pub mod wgsl_codegen;

// gpu_perturbation_entry: verified kernel logic
// The actual GPU kernel is in verus-mandelbrot/src/gpu_perturbation_entry.rs
// (transpiler-compatible, not directly Verus-verifiable due to GPU annotations).
// The perturbation math proofs are in verus-mandelbrot/src/gpu_mandelbrot_kernel.rs
// (249 verified, 0 errors).
