use vstd::prelude::*;

use crate::complex::*;
use crate::perturbation::*;
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

    pub open spec fn contains_interval(self, other: ComplexInterval) -> bool {
        self.re.contains_interval_spec(other.re) && self.im.contains_interval_spec(other.im)
    }
}

}

verus! {

pub struct IntervalDelta {
    pub re: Interval,
    pub im: Interval,
}

impl IntervalDelta {
    pub open spec fn wf_spec(&self) -> bool {
        self.re.wf_spec() && self.im.wf_spec()
    }

    pub open spec fn from_point(re: Rational, im: Rational) -> IntervalDelta {
        IntervalDelta {
            re: Interval::from_point_spec(re),
            im: Interval::from_point_spec(im),
        }
    }

    pub open spec fn zero() -> IntervalDelta {
        IntervalDelta {
            re: Interval::from_point_spec(Rational::from_int_spec(0)),
            im: Interval::from_point_spec(Rational::from_int_spec(0)),
        }
    }

    pub open spec fn add(self, rhs: IntervalDelta) -> IntervalDelta {
        IntervalDelta {
            re: self.re.add_spec(rhs.re),
            im: self.im.add_spec(rhs.im),
        }
    }

    pub open spec fn scale(s: Rational, delta: IntervalDelta) -> IntervalDelta {
        IntervalDelta {
            re: Interval::from_point_spec(s).mul_spec(delta.re),
            im: Interval::from_point_spec(s).mul_spec(delta.im),
        }
    }

    pub open spec fn square(self) -> IntervalDelta {
        let re2 = self.re.square_spec();
        let im2 = self.im.square_spec();
        let two_re_im = Interval::from_point_spec(Rational::from_int_spec(2))
            .mul_spec(self.re.mul_spec(self.im));
        IntervalDelta {
            re: re2.sub_spec(im2),
            im: two_re_im,
        }
    }

    pub open spec fn width(self) -> Rational {
        self.re.width_spec().add_spec(self.im.width_spec())
    }

    pub open spec fn contains_point(&self, re: Rational, im: Rational) -> bool {
        self.re.contains_spec(re) && self.im.contains_spec(im)
    }

    pub open spec fn midpoint(&self) -> RationalComplex {
        (self.re.midpoint_spec(), self.im.midpoint_spec())
    }
}

}

verus! {

/// Reference orbit with rational (exact computation).
pub open spec fn rational_ref_orbit(c: RationalComplex, n: nat) -> RationalComplex
    decreases n,
{
    if n == 0 {
        (Rational::from_int_spec(0), Rational::from_int_spec(0))
    } else {
        let prev = rational_ref_orbit(c, (n - 1) as nat);
        let re_sq = prev.0.mul_spec(prev.0);
        let im_sq = prev.1.mul_spec(prev.1);
        let two_re_im = prev.0.mul_spec(prev.1).add_spec(prev.0.mul_spec(prev.1));
        let new_re = re_sq.sub_spec(im_sq).add_spec(c.0);
        let new_im = two_re_im.add_spec(c.1);
        (new_re, new_im)
    }
}

/// Perturbation step with interval arithmetic:
/// δ' = 2·Z_ref·δ + δ² + Δc
pub open spec fn interval_perturbation_step(
    z_ref: RationalComplex,
    delta: IntervalDelta,
    delta_c: IntervalDelta,
) -> IntervalDelta {
    let two = Rational::from_int_spec(2);
    let two_zr = Interval::from_point_spec(two.mul_spec(z_ref.0));
    let two_zi = Interval::from_point_spec(two.mul_spec(z_ref.1));
    let two_zr_delta = IntervalDelta {
        re: two_zr.mul_spec(delta.re),
        im: two_zi.mul_spec(delta.im),
    };
    let delta_sq = delta.square();
    let linear_plus_delta = two_zr_delta.add(delta_sq);
    linear_plus_delta.add(delta_c)
}

/// The actual orbit point as an interval: Z_ref[n] + δ[n]
pub open spec fn actual_orbit_interval(
    z_ref: RationalComplex,
    delta: IntervalDelta,
) -> ComplexInterval {
    ComplexInterval {
        re: Interval::from_point_spec(z_ref.0).add_spec(delta.re),
        im: Interval::from_point_spec(z_ref.1).add_spec(delta.im),
    }
}

/// Distance to the boundary (for glitch detection).
/// If |Z|² > 4, we've escaped. The distance to boundary is 4 - |Z|².
pub open spec fn distance_to_boundary_sq(z: RationalComplex) -> Rational {
    let abs_sq = z.0.mul_spec(z.0).add_spec(z.1.mul_spec(z.1));
    let four = Rational::from_int_spec(4);
    if four.lt_spec(abs_sq) {
        Rational::from_int_spec(0)
    } else {
        four.sub_spec(abs_sq)
    }
}

/// Check if glitch condition is met.
/// A glitch occurs when the delta interval width is too large relative to
/// the distance from the reference point to the boundary.
pub open spec fn detect_glitch(
    z_ref: RationalComplex,
    delta: IntervalDelta,
    glitch_threshold: Rational,
) -> bool {
    let delta_width = delta.width();
    let dist = distance_to_boundary_sq(z_ref);
    if dist.lt_spec(Rational::from_int_spec(1)) {
        delta_width.lt_spec(Rational::from_int_spec(1)) == false
    } else {
        glitch_threshold.mul_spec(dist).lt_spec(delta_width)
    }
}

/// Re-reference: compute a new delta_c based on a different reference point.
///
/// If we had been using ref_c_old with delta_c_old, and we want to switch to
/// ref_c_new, the new delta is:
///   Δc_new = (ref_c_new - ref_c_old) + Δc_old
///
/// Because:
///   z = Z_old + δ_old
///   z = Z_new + δ_new
///   δ_new = z - Z_new = (Z_old + δ_old) - Z_new = (Z_old - Z_new) + δ_old
pub open spec fn compute_new_delta_c(
    old_ref_c: RationalComplex,
    new_ref_c: RationalComplex,
    old_delta_c: IntervalDelta,
) -> IntervalDelta {
    let ref_shift = IntervalDelta {
        re: Interval::from_point_spec(new_ref_c.0.sub_spec(old_ref_c.0)),
        im: Interval::from_point_spec(new_ref_c.1.sub_spec(old_ref_c.1)),
    };
    old_delta_c.add(ref_shift)
}

/// Find a glitch-free depth in the reference orbit.
/// Starting from start_depth, find the first index where glitch condition
/// is NOT triggered (or reach max_depth).
pub open spec fn find_glitch_free_depth(
    ref_c: RationalComplex,
    delta_c: IntervalDelta,
    glitch_threshold: Rational,
    start_depth: nat,
    max_iters: nat,
) -> (nat, bool)
    decreases max_iters,
{
    if max_iters == 0 {
        (start_depth, true)
    } else {
        let z_ref = rational_ref_orbit(ref_c, start_depth);
        if detect_glitch(z_ref, delta_c, glitch_threshold) {
            if start_depth + 1 >= max_iters {
                (start_depth, false)
            } else {
                find_glitch_free_depth(ref_c, delta_c, glitch_threshold, (start_depth + 1) as nat, (max_iters - 1) as nat)
            }
        } else {
            (start_depth, true)
        }
    }
}

/// Escape check: is the interval definitely outside the set?
/// If |z|².lo > 4, then all points in the interval have escaped.
pub open spec fn certainly_escaped(c: ComplexInterval) -> bool {
    c.magnitude_squared().hi.lt_spec(Rational::from_int_spec(4)) == false
}

/// Possibly bounded: could the interval still be in the set?
/// If |z|².lo <= 4, some points might not have escaped yet.
pub open spec fn possibly_bounded(c: ComplexInterval) -> bool {
    c.magnitude_squared().lo.le_spec(Rational::from_int_spec(4))
}

}
