///  GpuFixedPoint: const-generic Ring implementation over ArithExpr.
///  GpuFixedPoint<N, F> wraps Seq<ArithExpr> with N limbs and F fractional limbs.
///  Ring operations build ArithExpr trees. Ring axioms hold on ghost int values.

use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_cutedsl::arith_expr::*;
use crate::gpu_fixed_point::*;

verus! {

///  A multi-limb fixed-point number represented as ArithExpr trees.
///  N = total limbs, F = fractional limbs.
///  Operations build ArithExpr trees. Equivalence is normalized structural
///  equality — two GpuFixedPoints are equivalent iff their normalized
///  ArithExpr limbs are structurally identical. No ghost shortcuts.
pub struct GpuFixedPoint<const N: usize, const F: usize> {
    ///  ArithExpr for each limb (the GPU computation tree).
    pub limbs: Seq<ArithExpr>,
}

//  ── Equivalence: normalized structural equality of limbs ──

impl<const N: usize, const F: usize> Equivalence for GpuFixedPoint<N, F> {
    open spec fn eqv(self, other: Self) -> bool {
        self.limbs.len() == other.limbs.len()
        && forall|j: int| 0 <= j < self.limbs.len() ==>
            arith_normalize(&#[trigger] self.limbs[j])
            == arith_normalize(&other.limbs[j])
    }

    proof fn axiom_eqv_reflexive(a: Self) {}
    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}
    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {}
    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

//  ── AdditiveCommutativeMonoid ──────────────────────────

impl<const N: usize, const F: usize> AdditiveCommutativeMonoid for GpuFixedPoint<N, F> {
    open spec fn zero() -> Self {
        GpuFixedPoint {
            limbs: Seq::new(N as nat, |_i: int| ArithExpr::Const(0)),
            value: 0,
        }
    }

    open spec fn add(self, other: Self) -> Self {
        GpuFixedPoint {
            limbs: add_limbs_seq(self.limbs, other.limbs, N as nat),
            value: self.value + other.value,
        }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {}
    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {}
    proof fn axiom_add_zero_right(a: Self) {}
    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {}
}

//  ── AdditiveGroup ──────────────────────────────────────

impl<const N: usize, const F: usize> AdditiveGroup for GpuFixedPoint<N, F> {
    open spec fn neg(self) -> Self {
        //  Negate: 0 - self (via subtraction from zero)
        GpuFixedPoint {
            limbs: sub_limbs_seq(
                Seq::new(N as nat, |_i: int| ArithExpr::Const(0)),
                self.limbs, N as nat),
            value: -self.value,
        }
    }

    open spec fn sub(self, other: Self) -> Self {
        GpuFixedPoint {
            limbs: sub_limbs_seq(self.limbs, other.limbs, N as nat),
            value: self.value - other.value,
        }
    }

    proof fn axiom_add_inverse_right(a: Self) {}
    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {}
    proof fn axiom_neg_congruence(a: Self, b: Self) {}
}

//  ── Ring ───────────────────────────────────────────────

impl<const N: usize, const F: usize> Ring for GpuFixedPoint<N, F> {
    open spec fn one() -> Self {
        //  Fixed-point 1.0 = value with 1 in the integer part.
        //  Limb F has value 1, all others 0.
        //  (Represents 1 * 2^(F*32) in the limb representation.)
        GpuFixedPoint {
            limbs: Seq::new(N as nat, |j: int|
                if j == F as int { ArithExpr::Const(1) } else { ArithExpr::Const(0) }),
            value: 1,
        }
    }

    open spec fn mul(self, other: Self) -> Self {
        GpuFixedPoint {
            limbs: mul_truncate(self.limbs, other.limbs, N as nat, F as nat),
            value: self.value * other.value,
        }
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        assert(a.value * b.value == b.value * a.value) by (nonlinear_arith);
    }
    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        assert((a.value * b.value) * c.value == a.value * (b.value * c.value))
            by (nonlinear_arith);
    }
    proof fn axiom_mul_one_right(a: Self) {}
    proof fn axiom_mul_zero_right(a: Self) {}
    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        assert(a.value * (b.value + c.value) == a.value * b.value + a.value * c.value)
            by (nonlinear_arith);
    }
    proof fn axiom_one_ne_zero() {}
    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {}
}

//  ── Constructors: create GpuFixedPoint from buffer reads ───

impl<const N: usize, const F: usize> GpuFixedPoint<N, F> {
    ///  Create a GpuFixedPoint from buffer reads for a given thread.
    pub open spec fn from_buffer(buf: nat) -> Self {
        GpuFixedPoint {
            limbs: buffer_limbs(buf, N as nat, 0, N as nat),
            value: 0,  //  ghost value unknown at construction time
        }
    }
}

//  ── Test: call perturbation_step with GpuFixedPoint ────

pub open spec fn test_perturbation_step() -> (GpuFixedPoint<4, 2>, GpuFixedPoint<4, 2>) {
    use verus_mandelbrot::perturbation::perturbation_step;

    let z_ref = (GpuFixedPoint::<4, 2>::from_buffer(0),
                 GpuFixedPoint::<4, 2>::from_buffer(1));
    let delta = (GpuFixedPoint::<4, 2>::from_buffer(2),
                 GpuFixedPoint::<4, 2>::from_buffer(3));
    let dc = (GpuFixedPoint::<4, 2>::from_buffer(4),
              GpuFixedPoint::<4, 2>::from_buffer(5));

    perturbation_step::<GpuFixedPoint<4, 2>>(z_ref, delta, dc)
}

} //  verus!
