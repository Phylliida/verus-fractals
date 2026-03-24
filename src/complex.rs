use vstd::prelude::*;
use verus_fixed_point::fixed_point::FixedPoint;

verus! {

// ══════════════════════════════════════════════════════════════
// Complex fixed-point number: z = re + im·i
// ══════════════════════════════════════════════════════════════

/// Complex number backed by fixed-point components.
/// Both re and im share the same format (n limbs, frac fractional bits).
pub struct ComplexFP {
    pub re: FixedPoint,
    pub im: FixedPoint,
}

impl ComplexFP {
    /// Well-formedness: both components well-formed, same format.
    pub open spec fn wf(&self) -> bool {
        self.re.wf_spec()
        && self.im.wf_spec()
        && self.re.same_format(self.im)
    }

    pub open spec fn n(&self) -> nat { self.re.n }
    pub open spec fn frac(&self) -> nat { self.re.frac }

    /// Addition: (a+bi) + (c+di) = (a+c) + (b+d)i.
    pub open spec fn add(self, rhs: ComplexFP) -> ComplexFP {
        ComplexFP {
            re: self.re.add_spec(rhs.re),
            im: self.im.add_spec(rhs.im),
        }
    }

    /// Negation: -(a+bi) = (-a) + (-b)i.
    pub open spec fn neg(self) -> ComplexFP {
        ComplexFP {
            re: self.re.neg_spec(),
            im: self.im.neg_spec(),
        }
    }

    /// Subtraction: z - w = z + (-w).
    pub open spec fn sub(self, rhs: ComplexFP) -> ComplexFP {
        ComplexFP {
            re: self.re.sub_spec(rhs.re),
            im: self.im.sub_spec(rhs.im),
        }
    }

    /// Norm squared: |z|² = re² + im².
    /// Result is widened (2n limbs, 2*frac bits) since mul widens.
    pub open spec fn norm_sq(self) -> FixedPoint {
        self.re.mul_spec(self.re).add_spec(self.im.mul_spec(self.im))
    }

    /// Complex square: z² = (re² - im²) + (2·re·im)i.
    /// Result is widened (2n limbs, 2*frac bits).
    pub open spec fn square(self) -> ComplexFP {
        let re_sq = self.re.mul_spec(self.re);
        let im_sq = self.im.mul_spec(self.im);
        let cross = self.re.mul_spec(self.im);
        ComplexFP {
            re: re_sq.sub_spec(im_sq),      // re² - im²
            im: cross.add_spec(cross),       // 2·re·im = cross + cross
        }
    }

    /// Promote both components to wider format.
    pub open spec fn promote_to(self, new_n: nat, new_frac: nat) -> ComplexFP {
        ComplexFP {
            re: self.re.promote_spec(new_n, new_frac),
            im: self.im.promote_spec(new_n, new_frac),
        }
    }

    /// Reduce both components to narrower format (toward -∞).
    pub open spec fn reduce_down(self, target_n: nat, target_frac: nat) -> ComplexFP {
        ComplexFP {
            re: self.re.reduce_down_spec(target_n, target_frac),
            im: self.im.reduce_down_spec(target_n, target_frac),
        }
    }

    /// Mandelbrot step: z' = z² + c.
    /// z is in working format (n, frac). c must be promoted to match z² format (2n, 2*frac).
    pub open spec fn mandelbrot_step(self, c_wide: ComplexFP) -> ComplexFP {
        self.square().add(c_wide)
    }
}

// ══════════════════════════════════════════════════════════════
// Properties
// ══════════════════════════════════════════════════════════════

/// Negation preserves well-formedness.
pub proof fn lemma_neg_wf(z: ComplexFP)
    requires z.wf(),
    ensures z.neg().wf(),
{
    FixedPoint::lemma_neg_wf(z.re);
    FixedPoint::lemma_neg_wf(z.im);
    FixedPoint::lemma_neg_same_format(z.re);
    FixedPoint::lemma_neg_same_format(z.im);
}

/// z.square().re == re² - im².
pub proof fn lemma_square_re(z: ComplexFP)
    ensures z.square().re == z.re.mul_spec(z.re).sub_spec(z.im.mul_spec(z.im)),
{}

/// z.square().im == 2·re·im (= cross + cross).
pub proof fn lemma_square_im(z: ComplexFP)
    ensures z.square().im == z.re.mul_spec(z.im).add_spec(z.re.mul_spec(z.im)),
{}

} // verus!
