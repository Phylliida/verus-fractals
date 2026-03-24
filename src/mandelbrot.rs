use vstd::prelude::*;
use verus_fixed_point::fixed_point::FixedPoint;
use crate::complex::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Mandelbrot iteration spec
// ══════════════════════════════════════════════════════════════

/// Mandelbrot orbit: z_{k+1} = z_k² + c, starting from z_0 = 0.
/// Returns z after `steps` iterations, in widened format.
pub open spec fn mandelbrot_orbit(
    c: ComplexFP, steps: nat,
    n: nat, frac: nat,
) -> ComplexFP
    decreases steps,
{
    if steps == 0 {
        ComplexFP::zero(n, frac)
    } else {
        let z_prev = mandelbrot_orbit(c, (steps - 1) as nat, n, frac);
        z_prev.mandelbrot_step(c)
    }
}

/// Escape predicate: |z|² > escape_radius² (typically 4.0).
/// Uses norm_sq which returns a widened FixedPoint.
/// `threshold` is the escape radius squared in the same widened format.
pub open spec fn escaped(z: ComplexFP, threshold: FixedPoint) -> bool {
    // z.norm_sq() > threshold as fixed-point comparison
    z.norm_sq().lt_spec(threshold) == false
    && z.norm_sq().eqv_spec(threshold) == false
}

/// Mandelbrot escape time: number of iterations before escape, or max_iter if never escapes.
pub open spec fn escape_time(
    c: ComplexFP, max_iter: nat,
    n: nat, frac: nat,
    threshold: FixedPoint,
) -> nat
    decreases max_iter,
{
    escape_time_from(c, ComplexFP::zero(n, frac), max_iter, n, frac, threshold, 0)
}

/// Escape time starting from a given z, with iteration counter.
pub open spec fn escape_time_from(
    c: ComplexFP, z: ComplexFP,
    remaining: nat,
    n: nat, frac: nat,
    threshold: FixedPoint,
    count: nat,
) -> nat
    decreases remaining,
{
    if remaining == 0 {
        count
    } else if escaped(z, threshold) {
        count
    } else {
        let z_next = z.mandelbrot_step(c);
        // z_next is in widened format; reduce back to working format
        // (in practice, the caller handles reduction)
        escape_time_from(c, z_next, (remaining - 1) as nat, n, frac, threshold, count + 1)
    }
}

// ══════════════════════════════════════════════════════════════
// Pixel-to-complex mapping
// ══════════════════════════════════════════════════════════════

/// Map pixel coordinates to complex plane coordinates (spec level).
/// c_re = x_min + px * (x_max - x_min) / width
/// c_im = y_min + py * (y_max - y_min) / height
///
/// In fixed-point: pre-compute dx = (x_max - x_min) and scale = dx / width.
/// Then c_re = x_min + px * scale.
///
/// For the kernel, this is just ArithExpr arithmetic:
///   c_re = x_min + (px * dx) / width   (all integer / fixed-point)
pub open spec fn pixel_to_complex_re(
    px: nat, x_min: FixedPoint, dx: FixedPoint, width: nat,
) -> FixedPoint
    recommends width > 0,
{
    // px * dx gives a widened result; then divide by width
    // For now, spec-level only — the actual kernel uses ArithExpr
    x_min  // placeholder: full implementation needs fixed-point division
}

// ══════════════════════════════════════════════════════════════
// Properties
// ══════════════════════════════════════════════════════════════

/// Mandelbrot orbit at step 0 is zero.
pub proof fn lemma_orbit_zero(c: ComplexFP, n: nat, frac: nat)
    ensures mandelbrot_orbit(c, 0, n, frac) == ComplexFP::zero(n, frac),
{}

/// Mandelbrot orbit at step k+1 is z_k² + c.
pub proof fn lemma_orbit_step(c: ComplexFP, k: nat, n: nat, frac: nat)
    ensures
        mandelbrot_orbit(c, k + 1, n, frac)
            == mandelbrot_orbit(c, k, n, frac).mandelbrot_step(c),
{}

/// If z has already escaped, escape_time returns the current count.
pub proof fn lemma_escape_immediate(
    c: ComplexFP, z: ComplexFP,
    remaining: nat, n: nat, frac: nat,
    threshold: FixedPoint, count: nat,
)
    requires escaped(z, threshold),
    ensures escape_time_from(c, z, remaining, n, frac, threshold, count) == count,
{
    if remaining == 0 {
    } else {
        // escaped(z, threshold) is true, so we return count
    }
}

/// Escape time is bounded by max_iter.
pub proof fn lemma_escape_time_bounded(
    c: ComplexFP, max_iter: nat,
    n: nat, frac: nat,
    threshold: FixedPoint,
)
    ensures escape_time(c, max_iter, n, frac, threshold) <= max_iter,
{
    lemma_escape_time_from_bounded(
        c, ComplexFP::zero(n, frac), max_iter, n, frac, threshold, 0);
}

proof fn lemma_escape_time_from_bounded(
    c: ComplexFP, z: ComplexFP,
    remaining: nat, n: nat, frac: nat,
    threshold: FixedPoint, count: nat,
)
    ensures escape_time_from(c, z, remaining, n, frac, threshold, count) <= count + remaining,
    decreases remaining,
{
    if remaining == 0 {
    } else if escaped(z, threshold) {
    } else {
        let z_next = z.mandelbrot_step(c);
        lemma_escape_time_from_bounded(
            c, z_next, (remaining - 1) as nat, n, frac, threshold, count + 1);
    }
}

} // verus!
