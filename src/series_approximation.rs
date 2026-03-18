use vstd::prelude::*;

use crate::complex::*;
use crate::perturbation::*;
use verus_algebra::traits::ring::Ring;

verus! {

/// Series Approximation (SA) coefficient at step n.
///
/// For deep zoom, instead of iterating δ[n+1] = 2·Z[n]·δ[n] + δ[n]² + Δc directly,
/// we approximate: z[n] ≈ A[n]·δ + Z_ref[n]
///
/// The SA coefficients A[n] satisfy:
///   A[0] = 0
///   A[n+1] = 2·Z[n]·A[n] + 1
///
/// This is derived from the perturbation equation by dropping the δ² term:
///   δ[n+1] ≈ 2·Z[n]·δ[n] + Δc
///   z[n+1] = Z[n+1] + δ[n+1]
///            = (Z[n]² + c_ref) + (2·Z[n]·δ[n] + δ[n]² + Δc)
///            ≈ Z[n+1] + (2·Z[n]·δ[n] + Δc)      [dropping δ²]
///            = Z[n+1] + A[n+1]·Δc                 [by definition of A[n+1]]
///
/// Component form:
///   A_re[n+1] = 2·Zr[n]·Ar[n] - 2·Zi[n]·Ai[n] + 1
///   A_im[n+1] = 2·Zr[n]·Ar[n] + 2·Zi[n]·Ar[n]

pub open spec fn sa_coeff<T: Ring>(c: Complex<T>, n: nat) -> Complex<T>
    decreases n,
{
    if n == 0 {
        complex_zero()
    } else {
        let z = ref_orbit(c, (n - 1) as nat);
        let a = sa_coeff(c, (n - 1) as nat);
        let two = T::one().add(T::one());
        (
            two.mul(z.0.mul(a.0)).sub(two.mul(z.1.mul(a.1))).add(T::one()),
            two.mul(z.0.mul(a.1)).add(two.mul(z.1.mul(a.0))),
        )
    }
}

/// SA approximation of the actual orbit point:
///   z_approx[n] = Z_ref[n] + sa_coeff(c, n) · Δc
pub open spec fn sa_approx<T: Ring>(
    ref_c: Complex<T>,
    delta_c: Complex<T>,
    n: nat,
) -> Complex<T> {
    complex_add(
        ref_orbit(ref_c, n),
        complex_mul(sa_coeff(ref_c, n), delta_c),
    )
}

/// SA error: the difference between actual and approximated orbit.
///   error[n] = (Z_ref[n] + δ[n]) - (Z_ref[n] + A[n]·Δc) = δ[n] - A[n]·Δc
pub open spec fn sa_error<T: Ring>(
    ref_c: Complex<T>,
    delta_c: Complex<T>,
    n: nat,
) -> Complex<T> {
    complex_sub(
        actual_orbit(ref_c, delta_c, n),
        sa_approx(ref_c, delta_c, n),
    )
}

/// SA error recurrence:
///   error[0] = 0
///   error[n+1] = 2·Z[n]·error[n] + δ[n]²
///
/// Proof sketch:
///   δ[n+1] - A[n+1]·Δc
///   = (2·Z[n]·δ[n] + δ[n]² + Δc) - (2·Z[n]·A[n] + 1)·Δc
///   = 2·Z[n]·(δ[n] - A[n]·Δc) + δ[n]²
///   = 2·Z[n]·error[n] + δ[n]²
pub open spec fn sa_error_step<T: Ring>(
    z_ref: Complex<T>,
    error: Complex<T>,
    delta: Complex<T>,
) -> Complex<T> {
    let two = T::one().add(T::one());
    complex_add(
        complex_scale(two, complex_mul(z_ref, error)),
        complex_square(delta),
    )
}

/// The error accumulates based on the reference orbit and previous error.
/// This bounds how the error grows.

pub open spec fn sa_error_bound_term<T: Ring>(
    z_ref_norm: T,
    prev_error_norm: T,
    delta_norm_sq: T,
) -> T {
    let two = T::one().add(T::one());
    let two_z_ref_norm = two.mul(z_ref_norm);
    two_z_ref_norm.mul(prev_error_norm).add(delta_norm_sq)
}

}
