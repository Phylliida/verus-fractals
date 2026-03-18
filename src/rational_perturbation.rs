use vstd::prelude::*;

use verus_interval_arithmetic::Interval;
use verus_rational::Rational;

verus! {

pub type RationalComplex = (Rational, Rational);

pub struct ComplexInterval {
    pub re: Interval,
    pub im: Interval,
}

impl ComplexInterval {
    pub open spec fn wf_spec(&self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }

    pub open spec fn contains_spec(&self, z: RationalComplex) -> bool {
        self.re.contains_spec(z.0) && self.im.contains_spec(z.1)
    }

    pub open spec fn from_point(re: Rational, im: Rational) -> ComplexInterval {
        ComplexInterval {
            re: Interval::from_point_spec(re),
            im: Interval::from_point_spec(im),
        }
    }

    pub open spec fn add(self, rhs: ComplexInterval) -> ComplexInterval {
        ComplexInterval {
            re: self.re.add_spec(rhs.re),
            im: self.im.add_spec(rhs.im),
        }
    }

    pub open spec fn square(self) -> ComplexInterval {
        ComplexInterval {
            re: self.re.square_spec().sub_spec(self.im.square_spec()),
            im: Interval::from_point_spec(Rational::from_int_spec(2))
                .mul_spec(self.re.mul_spec(self.im)),
        }
    }

    pub open spec fn magnitude_squared(self) -> Interval {
        self.re.square_spec().add_spec(self.im.square_spec())
    }
}

}
