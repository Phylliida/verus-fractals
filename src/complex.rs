use vstd::prelude::*;

use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;

verus! {

/// Complex number as a pair (re, im) representing re + im·i.
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

// ── Proofs: algebraic properties ────────────────────────────────────

pub proof fn lemma_complex_add_commutative<T: Ring>(a: Complex<T>, b: Complex<T>)
    ensures complex_add(a, b).0.eqv(complex_add(b, a).0),
        complex_add(a, b).1.eqv(complex_add(b, a).1),
{
    T::axiom_add_commutative(a.0, b.0);
    T::axiom_add_commutative(a.1, b.1);
}

pub proof fn lemma_complex_add_associative<T: Ring>(a: Complex<T>, b: Complex<T>, c: Complex<T>)
    ensures
        complex_add(complex_add(a, b), c).0.eqv(complex_add(a, complex_add(b, c)).0),
        complex_add(complex_add(a, b), c).1.eqv(complex_add(a, complex_add(b, c)).1),
{
    T::axiom_add_associative(a.0, b.0, c.0);
    T::axiom_add_associative(a.1, b.1, c.1);
}

pub proof fn lemma_complex_add_zero_left<T: Ring>(a: Complex<T>)
    ensures complex_add(complex_zero::<T>(), a).0.eqv(a.0),
        complex_add(complex_zero::<T>(), a).1.eqv(a.1),
{
    T::axiom_add_zero_left(a.0);
    T::axiom_add_zero_left(a.1);
}

pub proof fn lemma_complex_add_zero_right<T: Ring>(a: Complex<T>)
    ensures complex_add(a, complex_zero::<T>()).0.eqv(a.0),
        complex_add(a, complex_zero::<T>()).1.eqv(a.1),
{
    T::axiom_add_zero_right(a.0);
    T::axiom_add_zero_right(a.1);
}

pub proof fn lemma_complex_sub_is_add_neg<T: Ring>(a: Complex<T>, b: Complex<T>)
    ensures complex_sub(a, b).0.eqv(a.0.add(b.0.neg())),
        complex_sub(a, b).1.eqv(a.1.add(b.1.neg())),
{
    T::axiom_sub_is_add_neg(a.0, b.0);
    T::axiom_sub_is_add_neg(a.1, b.1);
}

pub proof fn lemma_complex_neg_involutive<T: Ring>(a: Complex<T>)
    ensures complex_neg(complex_neg(a)).0.eqv(a.0),
        complex_neg(complex_neg(a)).1.eqv(a.1),
{
    additive_group_lemmas::lemma_neg_neg::<T>(a.0);
    additive_group_lemmas::lemma_neg_neg::<T>(a.1);
}

pub proof fn lemma_complex_mul_commutative<T: Ring>(a: Complex<T>, b: Complex<T>)
    ensures complex_mul(a, b).0.eqv(complex_mul(b, a).0),
        complex_mul(a, b).1.eqv(complex_mul(b, a).1),
{
    let ac = a.0.mul(b.0);
    let bd = a.1.mul(b.1);
    let ad = a.0.mul(b.1);
    let bc = a.1.mul(b.0);

    T::axiom_mul_commutative(a.0, b.0);
    T::axiom_mul_commutative(a.1, b.1);
    T::axiom_mul_commutative(a.0, b.1);
    T::axiom_mul_commutative(a.1, b.0);

    T::axiom_eqv_transitive(ac.sub(bd), ac.sub(bd), b.0.mul(a.0).sub(b.1.mul(a.1)));
    T::axiom_eqv_transitive(ad.add(bc), ad.add(bc), b.1.mul(a.0).add(b.0.mul(a.1)));
}

pub proof fn lemma_complex_mul_one_left<T: Ring>(b: Complex<T>)
    ensures complex_mul(complex_one::<T>(), b).0.eqv(b.0),
        complex_mul(complex_one::<T>(), b).1.eqv(b.1),
{
    let one = T::one();
    let ze = T::zero();

    T::axiom_mul_one_left(b.0);
    T::axiom_mul_zero_right(b.1);
    additive_group_lemmas::lemma_sub_self::<T>(ze);
    T::axiom_eqv_transitive(one.mul(b.0).sub(ze.mul(b.1)), b.0.sub(ze), b.0);

    additive_group_lemmas::lemma_add_zero_left::<T>(ze);
    T::axiom_eqv_transitive(one.mul(b.1).add(ze.mul(b.0)), b.1.add(ze), b.1);
}

pub proof fn lemma_complex_mul_one_right<T: Ring>(a: Complex<T>)
    ensures complex_mul(a, complex_one::<T>()).0.eqv(a.0),
        complex_mul(a, complex_one::<T>()).1.eqv(a.1),
{
    lemma_complex_mul_commutative(a, complex_one::<T>());
    lemma_complex_mul_one_left(a);
}

pub proof fn lemma_complex_mul_zero_left<T: Ring>(a: Complex<T>)
    ensures complex_mul(complex_zero::<T>(), a).0.eqv(T::zero()),
        complex_mul(complex_zero::<T>(), a).1.eqv(T::zero()),
{
    T::axiom_mul_zero_left(a.0);
    T::axiom_mul_zero_left(a.1);
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(T::zero().sub(T::zero()), T::zero(), T::zero());
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
}

pub proof fn lemma_complex_mul_zero_right<T: Ring>(a: Complex<T>)
    ensures complex_mul(a, complex_zero::<T>()).0.eqv(T::zero()),
        complex_mul(a, complex_zero::<T>()).1.eqv(T::zero()),
{
    lemma_complex_mul_commutative(complex_zero::<T>(), a);
    lemma_complex_mul_zero_left(a);
}

pub proof fn lemma_complex_mul_associative<T: Ring>(
    a: Complex<T>, b: Complex<T>, c: Complex<T>
)
    ensures
        complex_mul(complex_mul(a, b), c).0.eqv(complex_mul(a, complex_mul(b, c)).0),
        complex_mul(complex_mul(a, b), c).1.eqv(complex_mul(a, complex_mul(b, c)).1),
{
    let ab = complex_mul(a, b);
    let bc = complex_mul(b, c);
    let (ab_c_re, ab_c_im) = complex_mul(ab, c);
    let (a_bc_re, a_bc_im) = complex_mul(a, bc);

    ring_lemmas::lemma_mul_associative(a.0, b.0, c.0);
    ring_lemmas::lemma_mul_associative(a.1, b.1, c.0);
    ring_lemmas::lemma_mul_associative(a.0, b.1, c.1);
    ring_lemmas::lemma_mul_associative(a.1, b.0, c.1);

    ring_lemmas::lemma_mul_distributive_over_sub(a.0, b.0, c.0);
    ring_lemmas::lemma_mul_distributive_over_sub(a.1, b.1, c.0);
    ring_lemmas::lemma_mul_distributive_over_sub(a.0, b.1, c.1);
    ring_lemmas::lemma_mul_distributive_over_sub(a.1, b.0, c.1);
}

pub proof fn lemma_complex_mul_add_distributive<T: Ring>(
    a: Complex<T>, b: Complex<T>, c: Complex<T>
)
    ensures
        complex_mul(a, complex_add(b, c)).0.eqv(
            complex_add(complex_mul(a, b), complex_mul(a, c)).0),
        complex_mul(a, complex_add(b, c)).1.eqv(
            complex_add(complex_mul(a, b), complex_mul(a, c)).1),
{
    ring_lemmas::lemma_mul_distributive_over_add(a.0, b.0, c.0);
    ring_lemmas::lemma_mul_distributive_over_add(a.0, b.1, c.1);
    ring_lemmas::lemma_mul_distributive_over_add(a.1, b.0, c.0);
    ring_lemmas::lemma_mul_distributive_over_add(a.1, b.1, c.1);

    additive_group_lemmas::lemma_add_congruence::<T>(
        a.0.mul(b.0), a.0.mul(c.0), a.1.mul(b.1), a.1.mul(c.1));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.0.mul(b.1), a.0.mul(c.1), a.1.mul(b.0), a.1.mul(c.0));
}

pub proof fn lemma_complex_square_is_mul<T: Ring>(z: Complex<T>)
    ensures complex_square(z).0.eqv(complex_mul(z, z).0),
        complex_square(z).1.eqv(complex_mul(z, z).1),
{
    let two = T::one().add(T::one());
    let zr2 = z.0.mul(z.0);
    let zi2 = z.1.mul(z.1);
    let zrzj = z.0.mul(z.1);

    T::axiom_eqv_transitive(zr2.sub(zi2), zr2.sub(zi2), z.0.mul(z.0).sub(z.1.mul(z.1)));
    T::axiom_eqv_transitive(two.mul(zrzj), two.mul(zrzj), z.0.mul(z.1).add(z.1.mul(z.0)));
}

pub proof fn lemma_complex_abs_sq_nneg<T: Ring>(z: Complex<T>)
    ensures z.0.mul(z.0).add(z.1.mul(z.1)).eqv(z.1.mul(z.1).add(z.0.mul(z.0))),
{
    T::axiom_add_commutative(z.0.mul(z.0), z.1.mul(z.1));
}

pub proof fn lemma_complex_conj_is_self_inverse<T: Ring>(z: Complex<T>)
    ensures complex_conj(complex_conj(z)).0.eqv(z.0),
        complex_conj(complex_conj(z)).1.eqv(z.1),
{
    additive_group_lemmas::lemma_neg_neg::<T>(z.1);
}

pub proof fn lemma_complex_mul_conj<T: Ring>(z: Complex<T>)
    ensures
        complex_mul(z, complex_conj(z)).0.eqv(complex_abs_sq(z)),
        complex_mul(z, complex_conj(z)).1.eqv(T::zero()),
{
    let conj = complex_conj(z);
    let re = z.0.mul(conj.0).sub(z.1.mul(conj.1));
    let im = z.0.mul(conj.1).add(z.1.mul(conj.0));

    T::axiom_eqv_transitive(re, z.0.mul(z.0).sub(z.1.mul(z.1.neg())),
        z.0.mul(z.0).add(z.1.mul(z.1)));
    additive_group_lemmas::lemma_neg_neg::<T>(z.1);

    T::axiom_eqv_transitive(im, z.0.mul(z.1.neg()).add(z.1.mul(z.0)), T::zero());
    additive_group_lemmas::lemma_neg_distributive::<T>(z.0, z.1);
    T::axiom_eqv_transitive(z.0.mul(z.1).neg().add(z.1.mul(z.0)),
        (z.0.mul(z.1).add(z.1.mul(z.0))).neg(), T::zero());
    ring_lemmas::lemma_mul_add_cancel_right(z.0, z.1);
}

}
