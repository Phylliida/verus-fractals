use vstd::prelude::*;
use verus_fixed_point::fixed_point::FixedPoint;
use crate::complex::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  Mandelbrot iteration spec
//  ══════════════════════════════════════════════════════════════

///  Mandelbrot orbit after `steps` iterations.
///  z_{k+1} = z_k² + c, z_0 = (0, 0).
///
///  Note: each step widens the format (mul doubles limbs/frac).
///  In practice, reduce_down is applied after each step to keep working format.
///  This spec tracks the exact (widened) values for proof purposes.
pub open spec fn mandelbrot_orbit_step(
    z: ComplexFP, c_wide: ComplexFP,
) -> ComplexFP {
    z.mandelbrot_step(c_wide)
}

///  Escape predicate: norm_sq(z) > threshold.
///  threshold is typically 4.0 in the widened format.
pub open spec fn has_escaped(z: ComplexFP, threshold: FixedPoint) -> bool {
    //  z has escaped if norm_sq is NOT less-or-equal to threshold
    !z.norm_sq().le_spec(threshold)
}

///  Escape time: iterate z = z² + c until |z|² > threshold or max_iter reached.
///  Returns the number of iterations completed.
pub open spec fn escape_time(
    z: ComplexFP, c_wide: ComplexFP,
    threshold: FixedPoint,
    remaining: nat, count: nat,
) -> nat
    decreases remaining,
{
    if remaining == 0 {
        count
    } else if has_escaped(z, threshold) {
        count
    } else {
        escape_time(
            mandelbrot_orbit_step(z, c_wide), c_wide,
            threshold,
            (remaining - 1) as nat, count + 1,
        )
    }
}

//  ══════════════════════════════════════════════════════════════
//  Properties
//  ══════════════════════════════════════════════════════════════

///  Escape time is bounded by max_iter.
pub proof fn lemma_escape_time_bounded(
    z: ComplexFP, c_wide: ComplexFP,
    threshold: FixedPoint,
    max_iter: nat,
)
    ensures escape_time(z, c_wide, threshold, max_iter, 0) <= max_iter,
{
    lemma_escape_time_bounded_from(z, c_wide, threshold, max_iter, 0);
}

proof fn lemma_escape_time_bounded_from(
    z: ComplexFP, c_wide: ComplexFP,
    threshold: FixedPoint,
    remaining: nat, count: nat,
)
    ensures escape_time(z, c_wide, threshold, remaining, count) <= count + remaining,
    decreases remaining,
{
    if remaining == 0 {
    } else if has_escaped(z, threshold) {
    } else {
        lemma_escape_time_bounded_from(
            mandelbrot_orbit_step(z, c_wide), c_wide,
            threshold,
            (remaining - 1) as nat, count + 1,
        );
    }
}

///  If z has escaped, escape_time returns immediately.
pub proof fn lemma_escaped_returns_count(
    z: ComplexFP, c_wide: ComplexFP,
    threshold: FixedPoint,
    remaining: nat, count: nat,
)
    requires has_escaped(z, threshold), remaining > 0,
    ensures escape_time(z, c_wide, threshold, remaining, count) == count,
{}

///  Mandelbrot step preserves the algebraic identity: z' = z² + c.
pub proof fn lemma_step_is_square_plus_c(z: ComplexFP, c_wide: ComplexFP)
    ensures
        mandelbrot_orbit_step(z, c_wide).re
            == z.re.mul_spec(z.re).sub_spec(z.im.mul_spec(z.im)).add_spec(c_wide.re),
        mandelbrot_orbit_step(z, c_wide).im
            == z.re.mul_spec(z.im).add_spec(z.re.mul_spec(z.im)).add_spec(c_wide.im),
{}

} //  verus!
