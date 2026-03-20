use vstd::prelude::*;

use crate::complex::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::traits::ring::Ring;

verus! {

pub open spec fn perturbation_step<T: Ring>(
    z_ref: Complex<T>,
    delta: Complex<T>,
    delta_c: Complex<T>,
) -> Complex<T> {
    let two = T::one().add(T::one());
    complex_add(
        complex_add(
            complex_scale(two, complex_mul(z_ref, delta)),
            complex_square(delta),
        ),
        delta_c,
    )
}

pub open spec fn mandelbrot_step<T: Ring>(z: Complex<T>, c: Complex<T>) -> Complex<T> {
    complex_add(complex_square(z), c)
}

pub open spec fn ref_orbit<T: Ring>(c: Complex<T>, n: nat) -> Complex<T>
    decreases n,
{
    if n == 0 {
        complex_zero()
    } else {
        mandelbrot_step(ref_orbit(c, (n - 1) as nat), c)
    }
}

pub open spec fn perturbation_orbit<T: Ring>(
    ref_c: Complex<T>,
    delta_c: Complex<T>,
    n: nat,
) -> Complex<T>
    decreases n,
{
    if n == 0 {
        complex_zero()
    } else {
        perturbation_step(
            ref_orbit(ref_c, (n - 1) as nat),
            perturbation_orbit(ref_c, delta_c, (n - 1) as nat),
            delta_c,
        )
    }
}

pub open spec fn actual_orbit<T: Ring>(
    ref_c: Complex<T>,
    delta_c: Complex<T>,
    n: nat,
) -> Complex<T> {
    complex_add(ref_orbit(ref_c, n), perturbation_orbit(ref_c, delta_c, n))
}

pub open spec fn glitch_indicator<T: Ring>(
    z_ref: Complex<T>, delta: Complex<T>,
) -> T {
    let four = T::one().add(T::one()).add(T::one()).add(T::one());
    four.mul(complex_abs_sq(z_ref)).mul(complex_abs_sq(delta))
}

}
