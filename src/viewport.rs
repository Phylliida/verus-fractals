use vstd::prelude::*;

use crate::complex::*;
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
}

}
