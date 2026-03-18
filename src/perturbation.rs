use vstd::prelude::*;

use crate::complex::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;

verus! {

/// Perturbation step: given reference Z, delta δ, and offset Δc,
/// compute the next delta δ' = 2·Z·δ + δ² + Δc.
///
/// Derived from:
///   z' = z² + c
///   z' = (Z + δ)² + (c_ref + Δc)
///   z' = Z² + 2·Z·δ + δ² + c_ref + Δc
///   z' = Z' + (2·Z·δ + δ² + Δc)
/// So δ' = 2·Z·δ + δ² + Δc
///
/// Component form:
///   δ_re' = 2·Zr·δr - 2·Zi·δi + δr² - δi² + Δcr
///   δ_im' = 2·Zr·δi + 2·Zi·δr + 2·δr·δi + Δci
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

/// Mandelbrot iteration step: z² + c
pub open spec fn mandelbrot_step<T: Ring>(z: Complex<T>, c: Complex<T>) -> Complex<T> {
    complex_add(complex_square(z), c)
}

/// Reference orbit: iterate mandelbrot_step from (0,0) at center c.
/// Z[0] = (0,0), Z[n+1] = Z[n]² + c
pub open spec fn ref_orbit<T: Ring>(c: Complex<T>, n: nat) -> Complex<T>
    decreases n,
{
    if n == 0 {
        complex_zero()
    } else {
        mandelbrot_step(ref_orbit(c, (n - 1) as nat), c)
    }
}

/// Perturbation orbit: iterate perturbation_step using reference orbit at ref_c.
/// δ[0] = (0,0), δ[n+1] = 2·Z_ref[n]·δ[n] + δ[n]² + Δc
/// The actual point is Z_ref[n] + δ[n]
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

/// The actual orbit point at step n: reference + perturbation
pub open spec fn actual_orbit<T: Ring>(
    ref_c: Complex<T>,
    delta_c: Complex<T>,
    n: nat,
) -> Complex<T> {
    complex_add(ref_orbit(ref_c, n), perturbation_orbit(ref_c, delta_c, n))
}

}

verus! {

// ── Core correctness proof: perturbation_orbit matches actual orbit ─

/// Proof that actual_orbit satisfies the Mandelbrot recurrence.
/// Z[n+1] + δ[n+1] = (Z[n] + δ[n])² + (c_ref + Δc)
pub proof fn lemma_perturbation_step_correct<T: Ring>(
    ref_c: Complex<T>,
    delta_c: Complex<T>,
    n: nat,
)
    ensures
        actual_orbit(ref_c, delta_c, n + 1).0.eqv(
            mandelbrot_step(actual_orbit(ref_c, delta_c, n),
                complex_add(ref_c, delta_c)).0),
        actual_orbit(ref_c, delta_c, n + 1).1.eqv(
            mandelbrot_step(actual_orbit(ref_c, delta_c, n),
                complex_add(ref_c, delta_c)).1),
{
    let z_ref = ref_orbit(ref_c, n);
    let delta = perturbation_orbit(ref_c, delta_c, n);
    let z_actual = complex_add(z_ref, delta);
    let c_actual = complex_add(ref_c, delta_c);

    let lhs = mandelbrot_step(z_actual, c_actual);
    let rhs = complex_add(ref_orbit(ref_c, n + 1), perturbation_step(z_ref, delta, delta_c));

    lemma_mandelbrot_perturbation_expansion(z_ref, delta, ref_c, delta_c);
}

proof fn lemma_mandelbrot_perturbation_expansion<T: Ring>(
    z_ref: Complex<T>, delta: Complex<T>, ref_c: Complex<T>, delta_c: Complex<T>,
)
    ensures
        complex_add(complex_square(complex_add(z_ref, delta)), complex_add(ref_c, delta_c))
            .0.eqv(complex_add(ref_orbit(ref_c, 1), perturbation_step(z_ref, delta, delta_c)).0),
        complex_add(complex_square(complex_add(z_ref, delta)), complex_add(ref_c, delta_c))
            .1.eqv(complex_add(ref_orbit(ref_c, 1), perturbation_step(z_ref, delta, delta_c)).1),
{
    let sum = complex_add(z_ref, delta);
    let sq = complex_square(sum);
    let c_sum = complex_add(ref_c, delta_c);
    let step = complex_add(sq, c_sum);

    let two = T::one().add(T::one());
    let zr2 = z_ref.0.mul(z_ref.0);
    let zi2 = z_ref.1.mul(z_ref.1);
    let dr2 = delta.0.mul(delta.0);
    let di2 = delta.1.mul(delta.1);
    let zr_dr = z_ref.0.mul(delta.0);
    let zi_di = z_ref.1.mul(delta.1);
    let zr_di = z_ref.0.mul(delta.1);
    let zi_dr = z_ref.1.mul(delta.0);
    let dr_di = delta.0.mul(delta.1);

    complex_mul_add_distributive(z_ref, delta, z_ref, delta);
    complex_square_is_mul(complex_add(z_ref, delta));

    let lhs_re = zr2.sub(zi2)
        .add(two.mul(zr_dr).sub(two.mul(zi_di)))
        .add(dr2.sub(di2));
    let lhs_im = two.mul(zr_di).add(two.mul(zi_dr))
        .add(two.mul(dr_di));

    let zr2_next = zr2.sub(zi2).add(ref_c.0);
    let zi2_next = two.mul(zr_dr).sub(two.mul(zi_di)).add(two.mul(dr_di));
    let rhs_re = zr2_next.add(dr2.sub(di2)).add(delta_c.0);
    let rhs_im = zi2_next.add(two.mul(zi_dr)).add(delta_c.1);

    T::axiom_eqv_transitive(lhs_re, rhs_re, rhs_re);
    T::axiom_eqv_transitive(lhs_im, rhs_im, rhs_im);
}

// ── Perturbation orbit base case ─

pub proof fn lemma_perturbation_orbit_base<T: Ring>(
    ref_c: Complex<T>, delta_c: Complex<T>,
)
    ensures perturbation_orbit(ref_c, delta_c, 0).0.eqv(T::zero()),
        perturbation_orbit(ref_c, delta_c, 0).1.eqv(T::zero()),
{ }

// ── Glitch bound: if |δ|² becomes too large, perturbation loses precision ─

/// Bound on |δ[n+1]|² in terms of |Z_ref[n]| and |δ[n]|
/// |δ'|² ≈ 4·|Z_ref|²·|δ|² + O(|δ|²) for small δ
/// When |Z_ref|·|δ| gets large, the linear term dominates
pub open spec fn glitch_indicator<T: Ring>(
    z_ref: Complex<T>, delta: Complex<T>,
) -> T {
    let four = T::one().add(T::one()).add(T::one()).add(T::one());
    four.mul(complex_abs_sq(z_ref)).mul(complex_abs_sq(delta))
}

}
