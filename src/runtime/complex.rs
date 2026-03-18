#[cfg(verus_keep_ghost)]
use crate::complex::*;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;
use vstd::prelude::*;

verus! {

pub type Real = f64;
pub type Complex = (f64, f64);

pub fn complex_zero() -> (out: Complex) {
    (0.0, 0.0)
}

pub fn complex_one() -> (out: Complex) {
    (1.0, 0.0)
}

pub fn complex_add(a: Complex, b: Complex) -> (out: Complex) {
    (a.0 + b.0, a.1 + b.1)
}

pub fn complex_sub(a: Complex, b: Complex) -> (out: Complex) {
    (a.0 - b.0, a.1 - b.1)
}

pub fn complex_neg(a: Complex) -> (out: Complex) {
    (-a.0, -a.1)
}

pub fn complex_mul(a: Complex, b: Complex) -> (out: Complex) {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}

pub fn complex_square(z: Complex) -> (out: Complex) {
    (z.0 * z.0 - z.1 * z.1, 2.0 * z.0 * z.1)
}

pub fn complex_conj(z: Complex) -> (out: Complex) {
    (z.0, -z.1)
}

pub fn complex_abs_sq(z: Complex) -> (out: f64) {
    z.0 * z.0 + z.1 * z.1
}

}
