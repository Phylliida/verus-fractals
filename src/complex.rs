use vstd::prelude::*;

use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::traits::additive_group::AdditiveGroup;
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

verus! {

pub proof fn lemma_complex_neg_involutive<T: Ring>(a: Complex<T>)
    ensures complex_neg(complex_neg(a)).0.eqv(a.0),
        complex_neg(complex_neg(a)).1.eqv(a.1),
{
    additive_group_lemmas::lemma_neg_involution::<T>(a.0);
    additive_group_lemmas::lemma_neg_involution::<T>(a.1);
}

pub proof fn lemma_complex_abs_sq_nneg<T: Ring>(z: Complex<T>)
    ensures z.0.mul(z.0).add(z.1.mul(z.1)).eqv(z.1.mul(z.1).add(z.0.mul(z.0))),
{
    T::axiom_add_commutative(z.0.mul(z.0), z.1.mul(z.1));
}

pub proof fn lemma_complex_conj_involutive<T: Ring>(z: Complex<T>)
    ensures complex_conj(complex_conj(z)).0.eqv(z.0),
        complex_conj(complex_conj(z)).1.eqv(z.1),
{
    T::axiom_eqv_reflexive(z.0);
    additive_group_lemmas::lemma_neg_involution::<T>(z.1);
}

}
