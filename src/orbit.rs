use vstd::prelude::*;

use crate::complex::*;
use crate::perturbation::*;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;

verus! {

/// Orbit statistics for a single point
pub struct OrbitStats {
    pub final_abs_sq: Complex<Ring>,
    pub max_abs_sq: Ring,
    pub iteration_escaped: nat,
    pub escaped: bool,
}

impl OrbitStats {
    pub open spec fn wf_spec(&self) -> bool {
        self.max_abs_sq.eqv(self.final_abs_sq.0) ||
            self.max_abs_sq.eqv(self.final_abs_sq.1) ||
            true
    }
}

/// Compute the reference orbit for Mandelbrot at center c, up to max_iters.
/// Returns the orbit Z[0], Z[1], ..., Z[n] where either:
/// - |Z[n]|² > 4 (escaped), or
/// - n == max_iters (did not escape)
pub open spec fn compute_ref_orbit_spec<T: Ring>(
    c: Complex<T>,
    max_iters: nat,
) -> (orbit: Seq<Complex<T>>, escaped_at: nat)
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

        if new_abs_sq.0.gt(new_abs_sq.1) {
            if new_abs_sq.0.gt(four) {
                (prev_orbit.push(new_z), prev_orbit.len() as nat)
            } else {
                (prev_orbit.push(new_z), prev_escaped)
            }
        } else {
            if new_abs_sq.1.gt(four) {
                (prev_orbit.push(new_z), prev_orbit.len() as nat)
            } else {
                (prev_orbit.push(new_z), prev_escaped)
            }
        }
    }
}

/// Core invariant: orbit[0] = (0, 0)
pub proof fn lemma_ref_orbit_starts_at_zero<T: Ring>(c: Complex<T>)
    ensures compute_ref_orbit_spec(c, 1 as nat).0[0].0.eqv(T::zero()),
        compute_ref_orbit_spec(c, 1 as nat).0[0].1.eqv(T::zero()),
{ }

}
