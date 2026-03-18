#[cfg(verus_keep_ghost)]
use crate::fractal::*;
use crate::runtime::complex::*;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;
use vstd::prelude::*;

verus! {

pub struct IterationResult {
    pub escaped: bool,
    pub iteration: u32,
    pub final_z: Complex,
}

pub fn check_escape_runtime(z: Complex) -> (out: bool) {
    let abs_sq = complex_abs_sq(z);
    abs_sq > 4.0
}

pub fn iterate_mandelbrot(
    c: Complex,
    max_iters: u32,
) -> (out: IterationResult) {
    let mut zr = 0.0;
    let mut zi = 0.0;
    let mut zr2 = 0.0;
    let mut zi2 = 0.0;

    let mut iter: u32 = 0;
    while iter < max_iters
        invariant
            0 <= iter <= max_iters,
    {
        zi = 2.0 * zr * zi + c.1;
        zr = zr2 - zi2 + c.0;
        zr2 = zr * zr;
        zi2 = zi * zi;

        if zr2 + zi2 > 4.0 {
            return IterationResult {
                escaped: true,
                iteration: iter,
                final_z: (zr, zi),
            };
        }

        iter = iter + 1;
    }

    IterationResult {
        escaped: false,
        iteration: max_iters,
        final_z: (zr, zi),
    }
}

pub fn iterate_mandelbrot_with_perturbation(
    ref_orbit: &Vec<(f64, f64)>,
    delta_c: Complex,
    max_iters: u32,
) -> (out: IterationResult) {
    let mut delta_r = 0.0;
    let mut delta_i = 0.0;
    let mut iter: u32 = 0;

    while iter < max_iters
        invariant
            0 <= iter <= max_iters,
            iter as usize <= ref_orbit.len(),
    {
        let zr = ref_orbit[iter as usize].0;
        let zi = ref_orbit[iter as usize].1;

        let two_delta_r = 2.0 * delta_r;
        let two_delta_i = 2.0 * delta_i;

        let delta_r_sq = delta_r * delta_r;
        let delta_i_sq = delta_i * delta_i;

        let new_delta_r = two_delta_r * zr - two_delta_i * zi
            + delta_r_sq - delta_i_sq + delta_c.0;
        let new_delta_i = two_delta_r * zi + two_delta_i * zr
            + 2.0 * delta_r * delta_i + delta_c.1;

        delta_r = new_delta_r;
        delta_i = new_delta_i;

        let abs_sq_delta = delta_r * delta_r + delta_i * delta_i;
        if abs_sq_delta > 4.0 {
            return IterationResult {
                escaped: true,
                iteration: iter,
                final_z: (zr + delta_r, zi + delta_i),
            };
        }

        iter = iter + 1;
    }

    let final_zr = if ref_orbit.len() > 0 { ref_orbit[ref_orbit.len() - 1].0 } else { 0.0 };
    let final_zi = if ref_orbit.len() > 0 { ref_orbit[ref_orbit.len() - 1].1 } else { 0.0 };

    IterationResult {
        escaped: false,
        iteration: max_iters,
        final_z: (final_zr + delta_r, final_zi + delta_i),
    }
}

}
