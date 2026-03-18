use vstd::prelude::*;

use crate::complex::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::ordered_field::OrderedField;

verus! {

/// A viewport maps screen coordinates (pixels) to complex coordinates.
///
/// The complex plane maps as:
///   c_re = center_re + (pixel_x - width/2) * scale
///   c_im = center_im + (pixel_y - height/2) * scale
/// where scale is the pixel size in complex units.

pub struct Viewport<F: OrderedField> {
    pub center_re: F,
    pub center_im: F,
    pub scale: F,
    pub width: nat,
    pub height: nat,
}

impl<F: OrderedField> Viewport<F> {
    pub open spec fn wf_spec(&self) -> bool {
        self.width > 0 && self.height > 0 && self.scale.gt(F::zero())
    }

    pub open spec fn pixel_to_complex_spec(self, px: nat, py: nat) -> Complex<F> {
        let two = F::one().add(F::one());
        let half_w = F::from_nat(self.width).div(two);
        let half_h = F::from_nat(self.height).div(two);
        let dx = F::from_nat(px).sub(half_w).mul(self.scale);
        let dy = F::from_nat(py).sub(half_h).mul(self.scale);
        (self.center_re.add(dx), self.center_im.add(dy))
    }

    pub open spec fn complex_to_pixel_re_spec(self, c_re: F) -> F {
        c_re.sub(self.center_re).div(self.scale).add(F::from_nat(self.width).div(F::from_nat(2)))
    }

    pub open spec fn complex_to_pixel_im_spec(self, c_im: F) -> F {
        c_im.sub(self.center_im).div(self.scale).add(F::from_nat(self.height).div(F::from_nat(2)))
    }
}

pub open spec fn complex_to_viewport<F: OrderedField>(
    viewport: Viewport<F>,
    c: Complex<F>,
) -> Complex<F> {
    (
        complex_to_pixel_re_spec(viewport, c.0),
        complex_to_pixel_im_spec(viewport, c.1),
    )
}

}

verus! {

pub proof fn lemma_pixel_round_trip<F: OrderedField>(
    viewport: Viewport<F>, px: nat, py: nat,
)
    requires viewport.wf_spec(),
    ensures
        viewport.complex_to_pixel_re_spec(
            viewport.pixel_to_complex_spec(px, py).0).eqv(F::from_nat(px)),
        viewport.complex_to_pixel_im_spec(
            viewport.pixel_to_complex_spec(px, py).1).eqv(F::from_nat(py)),
{
    let two = F::one().add(F::one());
    let half_w = F::from_nat(viewport.width).div(two);
    let half_h = F::from_nat(viewport.height).div(two);
    let dx = F::from_nat(px).sub(half_w).mul(viewport.scale);
    let dy = F::from_nat(py).sub(half_h).mul(viewport.scale);

    let c = (viewport.center_re.add(dx), viewport.center_im.add(dy));

    let px_back = c.0.sub(viewport.center_re).div(viewport.scale).add(
        F::from_nat(viewport.width).div(two));
    let py_back = c.1.sub(viewport.center_im).div(viewport.scale).add(
        F::from_nat(viewport.height).div(two));

    F::axiom_sub_cancel_right(px_back, F::from_nat(px));
    F::axiom_div_mul_inverse(c.0.sub(viewport.center_re), viewport.scale);
    F::axiom_sub_cancel_right(py_back, F::from_nat(py));
    F::axiom_div_mul_inverse(c.1.sub(viewport.center_im), viewport.scale);
}

}
