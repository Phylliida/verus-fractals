use vstd::prelude::*;
use verus_fixed_point::fixed_point::FixedPoint;

verus! {

/// Complex number backed by fixed-point: z = re + im·i.
/// Both components share the same format (n limbs, frac fractional bits).
pub struct ComplexFP {
    pub re: FixedPoint,
    pub im: FixedPoint,
}

impl ComplexFP {
    /// Well-formedness: both components are well-formed and same format.
    pub open spec fn wf(&self) -> bool {
        self.re.wf_spec()
        && self.im.wf_spec()
        && self.re.n == self.im.n
        && self.re.frac == self.im.frac
    }

    /// Number of limbs.
    pub open spec fn n(&self) -> nat {
        self.re.n
    }

    /// Fractional bits.
    pub open spec fn frac(&self) -> nat {
        self.re.frac
    }

    /// Complex zero.
    pub open spec fn zero(n: nat, frac: nat) -> ComplexFP {
        ComplexFP {
            re: FixedPoint::zero(n, frac),
            im: FixedPoint::zero(n, frac),
        }
    }

    /// Complex addition: (a + bi) + (c + di) = (a+c) + (b+d)i.
    pub open spec fn add(self, rhs: ComplexFP) -> ComplexFP {
        ComplexFP {
            re: self.re.add_spec(rhs.re),
            im: self.im.add_spec(rhs.im),
        }
    }

    /// Complex subtraction: (a + bi) - (c + di) = (a-c) + (b-d)i.
    pub open spec fn sub(self, rhs: ComplexFP) -> ComplexFP {
        ComplexFP {
            re: self.re.sub_spec(rhs.re),
            im: self.im.sub_spec(rhs.im),
        }
    }

    /// Complex negation: -(a + bi) = (-a) + (-b)i.
    pub open spec fn neg(self) -> ComplexFP {
        ComplexFP {
            re: self.re.neg_spec(),
            im: self.im.neg_spec(),
        }
    }

    /// Norm squared: |z|² = re² + im².
    /// Result is in widened format (2n limbs, 2*frac bits) since mul widens.
    pub open spec fn norm_sq(self) -> FixedPoint {
        self.re.mul_spec(self.re).add_spec(self.im.mul_spec(self.im))
    }

    /// Complex square: z² = (re² - im²) + (2·re·im)i.
    /// Result is in widened format (2n limbs, 2*frac bits).
    pub open spec fn square(self) -> ComplexFP {
        let re_sq = self.re.mul_spec(self.re);  // 2n limbs, 2*frac
        let im_sq = self.im.mul_spec(self.im);  // 2n limbs, 2*frac
        let cross = self.re.mul_spec(self.im);  // 2n limbs, 2*frac
        ComplexFP {
            re: re_sq.sub_spec(im_sq),           // re² - im²
            im: cross.add_spec(cross),            // 2·re·im
        }
    }

    /// Mandelbrot step: z' = z² + c.
    /// Result is in widened format (2n limbs, 2*frac bits).
    pub open spec fn mandelbrot_step(self, c: ComplexFP) -> ComplexFP {
        self.square().add(c.promote_to(2 * self.n(), 2 * self.frac()))
    }

    /// Promote to larger format (more limbs, more frac bits) without changing value.
    pub open spec fn promote_to(self, new_n: nat, new_frac: nat) -> ComplexFP {
        ComplexFP {
            re: self.re.promote_spec(new_n, new_frac),
            im: self.im.promote_spec(new_n, new_frac),
        }
    }

    /// Reduce to smaller format (fewer limbs, fewer frac bits).
    /// Uses reduce_down for both components (toward -∞ for lo-bound).
    pub open spec fn reduce_down(self, target_n: nat, target_frac: nat) -> ComplexFP {
        ComplexFP {
            re: self.re.reduce_down_spec(target_n, target_frac),
            im: self.im.reduce_down_spec(target_n, target_frac),
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Basic properties
// ══════════════════════════════════════════════════════════════

/// Complex zero is well-formed.
pub proof fn lemma_zero_wf(n: nat, frac: nat)
    requires n > 0, frac <= n * 32,
    ensures ComplexFP::zero(n, frac).wf(),
{
    FixedPoint::lemma_zero_wf(n, frac);
}

/// Complex addition preserves format (same n, same frac).
pub proof fn lemma_add_wf(a: ComplexFP, b: ComplexFP)
    requires
        a.wf(), b.wf(),
        a.n() == b.n(), a.frac() == b.frac(),
        FixedPoint::add_no_overflow(a.re, b.re),
        FixedPoint::add_no_overflow(a.im, b.im),
    ensures
        a.add(b).re.wf_spec(),
        a.add(b).im.wf_spec(),
        a.add(b).re.n == a.n(),
        a.add(b).re.frac == a.frac(),
{
    FixedPoint::lemma_add_wf(a.re, b.re);
    FixedPoint::lemma_add_wf(a.im, b.im);
}

/// Complex negation preserves well-formedness.
pub proof fn lemma_neg_wf(z: ComplexFP)
    requires z.wf(),
    ensures z.neg().wf(),
{
    FixedPoint::lemma_neg_wf(z.re);
    FixedPoint::lemma_neg_wf(z.im);
}

/// Norm squared is non-negative (both re² and im² are non-negative).
/// (This is a property of the rational view, not the fixed-point representation.)

/// Complex square re component = re² - im².
pub proof fn lemma_square_re(z: ComplexFP)
    requires z.wf(),
    ensures z.square().re == z.re.mul_spec(z.re).sub_spec(z.im.mul_spec(z.im)),
{}

/// Complex square im component = 2·re·im.
pub proof fn lemma_square_im(z: ComplexFP)
    requires z.wf(),
    ensures z.square().im == z.re.mul_spec(z.im).add_spec(z.re.mul_spec(z.im)),
{}

} // verus!
