use vstd::prelude::*;

use crate::complex::*;
use crate::perturbation::*;
use crate::viewport::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ordered_field::OrderedField;

verus! {

pub type EscapeResult = (escaped: bool, iteration: nat);

/// Check if a point has escaped the Mandelbrot set.
/// |z|² > 4 is the standard bailout criterion.
pub open spec fn check_escape<T: Ring>(z: Complex<T>) -> bool {
    let four = T::one().add(T::one()).add(T::one()).add(T::one());
    complex_abs_sq(z).0.ge(four) || complex_abs_sq(z).1.ge(four)
}

/// Iterate Mandelbrot until escape or max_iters.
/// Returns (escaped: bool, iteration: nat).
pub open spec fn iterate_mandelbrot<T: Ring>(
    c: Complex<T>,
    max_iters: nat,
) -> EscapeResult
    decreases max_iters,
{
    if max_iters == 0 {
        (false, 0 as nat)
    } else {
        let z = ref_orbit(c, (max_iters - 1) as nat);
        if check_escape(z) {
            (true, (max_iters - 1) as nat)
        } else {
            iterate_mandelbrot(c, (max_iters - 1) as nat)
        }
    }
}

/// Distance estimator for smooth coloring.
/// Approximates distance to the Mandelbrot boundary.
pub open spec fn distance_estimator<T: Field>(
    z: Complex<T>, c: Complex<T>, n: nat,
) -> T {
    if n == 0 {
        T::zero()
    } else {
        let two = T::one().add(T::one());
        let zn_abs = complex_abs_sq(z);
        let derivative = two.mul(z.0).mul(z.0).add(two.mul(z.1).mul(z.1));
        zn_abs.div(derivative)
    }
}

}

verus! {

/// Proof that iterate_mandelbrot returns correct escape iteration.
pub proof fn lemma_iterate_mandelbrot_correct<T: Ring>(
    c: Complex<T>, max_iters: nat,
)
    ensures
        iterate_mandelbrot(c, max_iters).0 ==>
            check_escape(ref_orbit(c, iterate_mandelbrot(c, max_iters).1)),
{
    if max_iters > 0 {
        lemma_iterate_mandelbrot_correct(c, (max_iters - 1) as nat);
    }
}

/// Proof: if iterate_mandelbrot returns escaped=false, the point did not escape.
pub proof fn lemma_not_escaped_means_bounded<T: Ring>(
    c: Complex<T>, max_iters: nat,
)
    requires
        iterate_mandelbrot(c, max_iters).0 == false,
    ensures
        forall|n: nat| n <= max_iters ==> check_escape(ref_orbit(c, n)) == false,
{
    if max_iters > 0 {
        let result = iterate_mandelbrot(c, max_iters);
        lemma_not_escaped_means_bounded(c, (max_iters - 1) as nat);
    }
}

}
