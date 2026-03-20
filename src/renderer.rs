use vstd::prelude::*;

use crate::coloring::*;
use crate::complex::*;
use crate::deep_zoom::*;
use crate::orbit::*;
use crate::perturbation::*;
use crate::viewport::*;
use verus_algebra::embedding::from_int;
use verus_algebra::traits::field::OrderedField;

verus! {

pub struct FractalRenderer<F: OrderedField> {
    pub viewport: Viewport<F>,
    pub max_iters: nat,
    pub escape_threshold_sq: F,
}

impl<F: OrderedField> FractalRenderer<F> {
    pub open spec fn wf_spec(&self) -> bool {
        self.viewport.wf_spec()
        && self.max_iters > 0
    }

    pub open spec fn render_pixel(&self, px: nat, py: nat) -> RenderResult<F> {
        let c = self.viewport.pixel_to_point(px, py);
        self.compute_mandelbrot(c)
    }

    pub open spec fn compute_mandelbrot(&self, c: Complex<F>) -> RenderResult<F> {
        let (orbit, escaped_at) = compute_ref_orbit_spec(c, self.max_iters);
        if escaped_at > 0 {
            RenderResult::Escaped {
                iters: escaped_at,
                final_z: orbit[escaped_at as int],
            }
        } else {
            let (period, found) = find_period_in_orbit::<F>(orbit, self.max_iters);
            if found {
                RenderResult::Periodic {
                    period,
                    z: orbit[self.max_iters as int - 1],
                }
            } else {
                RenderResult::Unknown {
                    max_iters: self.max_iters,
                }
            }
        }
    }
}

pub enum RenderResult<F: OrderedField> {
    Escaped {
        iters: nat,
        final_z: Complex<F>,
    },
    Periodic {
        period: nat,
        z: Complex<F>,
    },
    Unknown {
        max_iters: nat,
    },
}

pub open spec fn compute_ref_point_for_deep_zoom<F: OrderedField>(
    c: Complex<F>,
    period: nat,
) -> Complex<F> {
    if period == 0 {
        c
    } else {
        ref_orbit(c, period)
    }
}

pub open spec fn pixel_delta<F: OrderedField>(
    viewport: Viewport<F>,
    pixel: (nat, nat),
    ref_point: Complex<F>,
) -> Complex<F> {
    let pixel_point = viewport.pixel_to_point(pixel.0, pixel.1);
    (pixel_point.0.sub(ref_point.0), pixel_point.1.sub(ref_point.1))
}

}
