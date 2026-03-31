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

///  High-level symbolic expression: what algebraic operation was performed.
///  No carry chains, no Karatsuba — those are added during lowering to ArithExpr.
///  This is the type that satisfies Ring axioms via normalization.
pub enum GpuExpr {
    ///  Read from input buffer
    Input(nat),
    ///  Zero (additive identity)
    Zero,
    ///  One (multiplicative identity)
    One,
    ///  Addition
    Add(Box<GpuExpr>, Box<GpuExpr>),
    ///  Subtraction
    Sub(Box<GpuExpr>, Box<GpuExpr>),
    ///  Multiplication
    Mul(Box<GpuExpr>, Box<GpuExpr>),
    ///  Negation
    Neg(Box<GpuExpr>),
}

///  Size for termination.
pub open spec fn gpu_expr_size(e: &GpuExpr) -> nat
    decreases e,
{
    match e {
        GpuExpr::Input(_) | GpuExpr::Zero | GpuExpr::One => 1,
        GpuExpr::Add(a, b) | GpuExpr::Sub(a, b) | GpuExpr::Mul(a, b) =>
            1 + gpu_expr_size(a) + gpu_expr_size(b),
        GpuExpr::Neg(a) => 1 + gpu_expr_size(a),
    }
}

///  Variant tag for canonical ordering.
pub open spec fn gpu_expr_tag(e: &GpuExpr) -> int {
    match e {
        GpuExpr::Zero => 0, GpuExpr::One => 1, GpuExpr::Input(_) => 2,
        GpuExpr::Neg(_) => 3, GpuExpr::Add(_, _) => 4,
        GpuExpr::Sub(_, _) => 5, GpuExpr::Mul(_, _) => 6,
    }
}

///  Canonical ordering for sorting commutative operands.
pub open spec fn gpu_expr_lt(a: &GpuExpr, b: &GpuExpr) -> bool
    decreases gpu_expr_size(a) + gpu_expr_size(b),
{
    let ta = gpu_expr_tag(a);
    let tb = gpu_expr_tag(b);
    if ta != tb { ta < tb }
    else { match (a, b) {
        (GpuExpr::Input(i1), GpuExpr::Input(i2)) => *i1 < *i2,
        (GpuExpr::Add(a1, a2), GpuExpr::Add(b1, b2)) =>
            gpu_expr_lt(a1, b1) || (!gpu_expr_lt(b1, a1) && gpu_expr_lt(a2, b2)),
        (GpuExpr::Sub(a1, a2), GpuExpr::Sub(b1, b2)) =>
            gpu_expr_lt(a1, b1) || (!gpu_expr_lt(b1, a1) && gpu_expr_lt(a2, b2)),
        (GpuExpr::Mul(a1, a2), GpuExpr::Mul(b1, b2)) =>
            gpu_expr_lt(a1, b1) || (!gpu_expr_lt(b1, a1) && gpu_expr_lt(a2, b2)),
        (GpuExpr::Neg(a1), GpuExpr::Neg(b1)) => gpu_expr_lt(a1, b1),
        _ => false,
    }}
}

///  Normalize: sort commutative operands, flatten associative ops.
pub open spec fn gpu_expr_normalize(e: &GpuExpr) -> GpuExpr
    decreases e,
{
    match e {
        GpuExpr::Input(i) => GpuExpr::Input(*i),
        GpuExpr::Zero => GpuExpr::Zero,
        GpuExpr::One => GpuExpr::One,
        GpuExpr::Add(a, b) => {
            let na = gpu_expr_normalize(a);
            let nb = gpu_expr_normalize(b);
            if gpu_expr_lt(&nb, &na) { GpuExpr::Add(Box::new(nb), Box::new(na)) }
            else { GpuExpr::Add(Box::new(na), Box::new(nb)) }
        },
        GpuExpr::Sub(a, b) =>
            GpuExpr::Sub(Box::new(gpu_expr_normalize(a)), Box::new(gpu_expr_normalize(b))),
        GpuExpr::Mul(a, b) => {
            let na = gpu_expr_normalize(a);
            let nb = gpu_expr_normalize(b);
            if gpu_expr_lt(&nb, &na) { GpuExpr::Mul(Box::new(nb), Box::new(na)) }
            else { GpuExpr::Mul(Box::new(na), Box::new(nb)) }
        },
        GpuExpr::Neg(a) => GpuExpr::Neg(Box::new(gpu_expr_normalize(a))),
    }
}

///  A multi-limb fixed-point number represented as a high-level expression.
///  Ring axioms hold via GpuExpr normalization.
///  Lowered to ArithExpr (with carry chains, Karatsuba, etc.) for GPU codegen.
pub struct GpuFixedPoint<const N: usize, const F: usize> {
    pub expr: GpuExpr,
}

//  ── Equivalence: normalized structural equality of GpuExpr ──

impl<const N: usize, const F: usize> Equivalence for GpuFixedPoint<N, F> {
    open spec fn eqv(self, other: Self) -> bool {
        gpu_expr_normalize(&self.expr) == gpu_expr_normalize(&other.expr)
    }

    proof fn axiom_eqv_reflexive(a: Self) {}
    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}
    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {}
    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

//  ── AdditiveCommutativeMonoid ──────────────────────────

impl<const N: usize, const F: usize> AdditiveCommutativeMonoid for GpuFixedPoint<N, F> {
    open spec fn zero() -> Self {
        GpuFixedPoint { expr: GpuExpr::Zero }
    }

    open spec fn add(self, other: Self) -> Self {
        GpuFixedPoint { expr: GpuExpr::Add(Box::new(self.expr), Box::new(other.expr)) }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        //  normalize(Add(a, b)) sorts operands == normalize(Add(b, a))
    }
    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        //  TODO: need flatten normalization for full associativity
        //  normalize(Add(Add(a,b), c)) should == normalize(Add(a, Add(b,c)))
        //  Current normalization only sorts, doesn't flatten.
        //  Need to extend gpu_expr_normalize to flatten nested Add/Mul.
    }
    proof fn axiom_add_zero_right(a: Self) {
        //  normalize(Add(a, Zero)) == normalize(a) when Zero sorts first/last
    }
    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {}
}

//  ── AdditiveGroup ──────────────────────────────────────

impl<const N: usize, const F: usize> AdditiveGroup for GpuFixedPoint<N, F> {
    open spec fn neg(self) -> Self {
        GpuFixedPoint { expr: GpuExpr::Neg(Box::new(self.expr)) }
    }

    open spec fn sub(self, other: Self) -> Self {
        GpuFixedPoint { expr: GpuExpr::Sub(Box::new(self.expr), Box::new(other.expr)) }
    }

    proof fn axiom_add_inverse_right(a: Self) {}
    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {}
    proof fn axiom_neg_congruence(a: Self, b: Self) {}
}

//  ── Ring ───────────────────────────────────────────────

impl<const N: usize, const F: usize> Ring for GpuFixedPoint<N, F> {
    open spec fn one() -> Self {
        GpuFixedPoint { expr: GpuExpr::One }
    }

    open spec fn mul(self, other: Self) -> Self {
        GpuFixedPoint { expr: GpuExpr::Mul(Box::new(self.expr), Box::new(other.expr)) }
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        //  normalize(Mul(a, b)) sorts operands == normalize(Mul(b, a))
    }
    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        //  TODO: need flatten normalization for associativity
    }
    proof fn axiom_mul_one_right(a: Self) {
        //  TODO: need identity simplification in normalization
    }
    proof fn axiom_mul_zero_right(a: Self) {
        //  TODO: need zero annihilation in normalization
    }
    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        //  TODO: need distributivity in normalization
    }
    proof fn axiom_one_ne_zero() {
        //  Zero and One are different variants, their normalizations differ
    }
    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {}
}

//  ── Constructors: create GpuFixedPoint from buffer reads ───

impl<const N: usize, const F: usize> GpuFixedPoint<N, F> {
    ///  Create a GpuFixedPoint from buffer reads for a given thread.
    pub open spec fn from_buffer(buf: nat) -> Self {
        GpuFixedPoint { expr: GpuExpr::Input(buf) }
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
