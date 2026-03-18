use vstd::prelude::*;

use crate::complex::*;
use crate::orbit::*;
use crate::perturbation::*;
use crate::series_approximation::*;
use verus_algebra::embedding::from_int;
use verus_algebra::traits::field::OrderedField;

verus! {

pub struct DeepZoomParams<F: OrderedField> {
    pub ref_c: Complex<F>,
    pub delta_c: Complex<F>,
    pub max_iters: nat,
    pub escape_threshold_sq: F,
}

impl<F: OrderedField> DeepZoomParams<F> {
    pub open spec fn wf_spec(&self) -> bool {
        self.max_iters > 0
    }
}

pub open spec fn compute_deep_zoom_orbit<F: OrderedField>(
    params: DeepZoomParams<F>,
) -> DeepZoomResult<F>
{
    let ref_orbit_result = compute_ref_orbit_spec(params.ref_c, params.max_iters);
    let (_, escaped_at) = ref_orbit_result;
    if escaped_at > 0 {
        DeepZoomResult::Escaped {
            pixel_c: complex_add(params.ref_c, params.delta_c),
            ref_iters: escaped_at,
            pixel_iters: escaped_at,
        }
    } else {
        let ref_orbit = compute_ref_orbit_spec(params.ref_c, params.max_iters).0;
        let period = find_period_in_orbit::<F>(ref_orbit, params.max_iters).0;
        DeepZoomResult::Periodic {
            pixel_c: complex_add(params.ref_c, params.delta_c),
            period,
        }
    }
}

pub enum DeepZoomResult<F: OrderedField> {
    Escaped {
        pixel_c: Complex<F>,
        ref_iters: nat,
        pixel_iters: nat,
    },
    Periodic {
        pixel_c: Complex<F>,
        period: nat,
    },
}

pub open spec fn deep_zoom_iteration_with_sa<F: OrderedField>(
    ref_c: Complex<F>,
    delta_c: Complex<F>,
    n: nat,
) -> Complex<F> {
    let z_ref = ref_orbit(ref_c, n);
    let delta = perturbation_orbit(ref_c, delta_c, n);
    let sa_coeff = sa_coeff(ref_c, n);
    let sa_approx = complex_add(z_ref, complex_mul(sa_coeff, delta_c));
    let error = sa_error(ref_c, delta_c, n);
    complex_add(sa_approx, error)
}

pub open spec fn check_escape_with_threshold<F: OrderedField>(
    z: Complex<F>,
    threshold_sq: F,
) -> bool {
    complex_abs_sq(z).ge(threshold_sq)
}

}
