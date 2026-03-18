use vstd::prelude::*;

use crate::complex::*;
use crate::perturbation::*;
use verus_algebra::traits::field::{Field, OrderedField};
use verus_algebra::traits::ring::Ring;

verus! {

pub type EscapeResult = (bool, nat);

pub open spec fn check_escape<T: OrderedField>(z: Complex<T>) -> bool {
    let four = T::one().add(T::one()).add(T::one()).add(T::one());
    complex_abs_sq(z).ge(four)
}

pub open spec fn iterate_mandelbrot<T: OrderedField>(
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
