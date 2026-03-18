use vstd::prelude::*;

use crate::complex::*;
use crate::perturbation::*;
use verus_algebra::traits::field::OrderedField;

verus! {

pub open spec fn compute_ref_orbit_spec<T: OrderedField>(
    c: Complex<T>,
    max_iters: nat,
) -> (Seq<Complex<T>>, nat)
    decreases max_iters,
{
    if max_iters == 0 {
        (Seq::empty().push(complex_zero()), 0 as nat)
    } else {
        let (prev_orbit, prev_escaped) = compute_ref_orbit_spec(c, (max_iters - 1) as nat);
        let prev_z = prev_orbit[prev_orbit.len() - 1];
        let new_z = mandelbrot_step(prev_z, c);
        let new_abs_sq = complex_abs_sq(new_z);
        let four = T::one().add(T::one()).add(T::one()).add(T::one());
        let escaped = four.le(new_abs_sq);
        if escaped {
            (prev_orbit.push(new_z), prev_orbit.len() as nat)
        } else {
            (prev_orbit.push(new_z), prev_escaped)
        }
    }
}

}
