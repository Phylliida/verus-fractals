use vstd::prelude::*;

use crate::complex::*;
use crate::fractal::*;
use verus_algebra::embedding::from_int;
use verus_algebra::traits::field::OrderedField;

verus! {

pub struct ColoringParams<F: OrderedField> {
    pub max_iters: nat,
    pub escape_threshold_sq: F,
}

impl<F: OrderedField> ColoringParams<F> {
    pub open spec fn wf_spec(&self) -> bool {
        self.max_iters > 0
    }
}

pub open spec fn iteration_to_color<F: OrderedField>(
    iters: nat,
    max_iters: nat,
) -> F {
    if iters >= max_iters {
        F::zero()
    } else {
        from_int::<F>(iters as int)
    }
}

pub open spec fn period_to_color<F: OrderedField>(
    period: nat,
) -> F {
    from_int::<F>(period as int)
}

}
