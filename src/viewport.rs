use vstd::prelude::*;

use crate::complex::*;
use verus_algebra::embedding::from_int;
use verus_algebra::traits::field::OrderedField;

verus! {

pub struct Viewport<F: OrderedField> {
    pub center_re: F,
    pub center_im: F,
    pub scale: F,
    pub width: nat,
    pub height: nat,
}

impl<F: OrderedField> Viewport<F> {
    pub open spec fn wf_spec(&self) -> bool {
        self.width > 0 && self.height > 0
    }

    pub open spec fn pixel_to_point(&self, px: nat, py: nat) -> Complex<F> {
        let half_h = from_int::<F>(self.height as int / 2);
        let half_w = from_int::<F>(self.width as int / 2);
        let px_centered = from_int::<F>(px as int).sub(half_w);
        let py_centered = from_int::<F>(py as int).sub(half_h);
        let re = self.center_re.add(self.scale.mul(px_centered));
        let im = self.center_im.add(self.scale.mul(py_centered));
        (re, im)
    }
}

}
