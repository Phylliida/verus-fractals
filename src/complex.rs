use vstd::prelude::*;

use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;

verus! {

pub type Complex<T> = (T, T);

pub open spec fn complex_zero<T: Ring>() -> Complex<T> {
    (T::zero(), T::zero())
}

pub open spec fn complex_one<T: Ring>() -> Complex<T> {
    (T::one(), T::zero())
}

pub open spec fn complex_add<T: Ring>(a: Complex<T>, b: Complex<T>) -> Complex<T> {
    (a.0.add(b.0), a.1.add(b.1))
}

pub open spec fn complex_sub<T: Ring>(a: Complex<T>, b: Complex<T>) -> Complex<T> {
    (a.0.sub(b.0), a.1.sub(b.1))
}

pub open spec fn complex_neg<T: Ring>(a: Complex<T>) -> Complex<T> {
    (a.0.neg(), a.1.neg())
}

pub open spec fn complex_mul<T: Ring>(a: Complex<T>, b: Complex<T>) -> Complex<T> {
    (a.0.mul(b.0).sub(a.1.mul(b.1)), a.0.mul(b.1).add(a.1.mul(b.0)))
}

pub open spec fn complex_square<T: Ring>(z: Complex<T>) -> Complex<T> {
    (z.0.mul(z.0).sub(z.1.mul(z.1)), T::one().add(T::one()).mul(z.0.mul(z.1)))
}

pub open spec fn complex_conj<T: Ring>(z: Complex<T>) -> Complex<T> {
    (z.0, z.1.neg())
}

pub open spec fn complex_abs_sq<T: Ring>(z: Complex<T>) -> T {
    z.0.mul(z.0).add(z.1.mul(z.1))
}

pub open spec fn complex_eq<T: Ring>(a: Complex<T>, b: Complex<T>) -> bool {
    a.0.eqv(b.0) && a.1.eqv(b.1)
}

pub open spec fn complex_scale<T: Ring>(s: T, z: Complex<T>) -> Complex<T> {
    (s.mul(z.0), s.mul(z.1))
}

}
