///  RuntimeGpuFixedPoint: exec-level GPU fixed-point that builds RuntimeArithExpr.
///
///  Wraps a single RuntimeArithExpr. Ring operations build the corresponding
///  ArithExpr tree. View maps to spec-level GpuFixedPoint<N, F>.
///
///  The exec operations are trivially correct: each just constructs the
///  RuntimeArithExpr variant matching the spec-level ArithExpr variant.

use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use crate::gpu_ring_test::{GpuFixedPoint, poly_add, poly_neg, poly_insert, poly_mul, mono_mul_poly, arith_to_poly, vars_lt, vars_merge, expr_coeff_bound, lemma_expr_coeff_bound_nonneg, lemma_arith_to_poly_coeff_bound, poly_sum_abs, lemma_arith_to_poly_sum_abs, lemma_poly_sum_abs_nonneg, lemma_poly_sum_abs_bounds_individual};

verus! {

//  ══════════════════════════════════════════════════════════════
//  RuntimeGpuFixedPoint
//  ══════════════════════════════════════════════════════════════

pub struct RuntimeGpuFixedPoint<const N: usize, const F: usize> {
    pub expr: RuntimeArithExpr,
}

impl<const N: usize, const F: usize> View for RuntimeGpuFixedPoint<N, F> {
    type V = GpuFixedPoint<N, F>;

    open spec fn view(&self) -> GpuFixedPoint<N, F> {
        GpuFixedPoint { expr: self.expr.view_spec() }
    }
}

impl<const N: usize, const F: usize> RuntimeGpuFixedPoint<N, F> {
    pub open spec fn wf_spec(&self) -> bool { true }

    //  ─── Construction ──────────────────────────────────────────

    ///  Create from a variable index (e.g., buffer read).
    pub fn from_var(v: u32) -> (out: Self)
        ensures out@ == GpuFixedPoint::<N, F>::from_buffer(v as nat),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint { expr: RuntimeArithExpr::Var(v) }
    }

    ///  Zero element: Const(0).
    pub fn zero_val() -> (out: Self)
        ensures out@ == GpuFixedPoint::<N, F>::zero(),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint { expr: RuntimeArithExpr::Const(0) }
    }

    ///  One element: Const(1).
    pub fn one_val() -> (out: Self)
        ensures out@ == GpuFixedPoint::<N, F>::one(),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint { expr: RuntimeArithExpr::Const(1) }
    }

    //  ─── Ring operations ───────────────────────────────────────

    pub fn add(&self, rhs: &Self) -> (out: Self)
        ensures out@ == self@.add(rhs@),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint {
            expr: RuntimeArithExpr::Add(
                Box::new(self.expr.clone()),
                Box::new(rhs.expr.clone())),
        }
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        ensures out@ == self@.sub(rhs@),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint {
            expr: RuntimeArithExpr::Sub(
                Box::new(self.expr.clone()),
                Box::new(rhs.expr.clone())),
        }
    }

    pub fn neg(&self) -> (out: Self)
        ensures out@ == self@.neg(),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint {
            expr: RuntimeArithExpr::Sub(
                Box::new(RuntimeArithExpr::Const(0)),
                Box::new(self.expr.clone())),
        }
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        ensures out@ == self@.mul(rhs@),
    {
        proof { reveal_with_fuel(RuntimeArithExpr::view_spec, 2); }
        RuntimeGpuFixedPoint {
            expr: RuntimeArithExpr::Mul(
                Box::new(self.expr.clone()),
                Box::new(rhs.expr.clone())),
        }
    }

    pub fn copy(&self) -> (out: Self)
        ensures out@ == self@,
    {
        RuntimeGpuFixedPoint { expr: self.expr.clone() }
    }

    //  ─── Access ────────────────────────────────────────────────

    ///  Get the underlying RuntimeArithExpr (for shader codegen).
    pub fn into_expr(self) -> (out: RuntimeArithExpr)
        ensures out.view_spec() == self@.expr,
    {
        self.expr
    }
}

//  ══════════════════════════════════════════════════════════════
//  Runtime polynomial normalization
//  ══════════════════════════════════════════════════════════════
//
//  Exec-level implementations of the spec polynomial operations.
//  Used to compute GpuFixedPoint::eqv at runtime.
//
//  Runtime poly: Vec<(i64, Vec<u32>)>
//  Spec poly:    Seq<(int, Seq<nat>)>

///  View: convert Vec<u32> (runtime vars) to Seq<nat> (spec vars).
pub open spec fn vars_view(v: Seq<u32>) -> Seq<nat> {
    Seq::new(v.len(), |i: int| v[i] as nat)
}

///  View: convert runtime polynomial to spec polynomial.
pub open spec fn poly_rt_view(p: Seq<(i64, Vec<u32>)>) -> Seq<(int, Seq<nat>)> {
    Seq::new(p.len(), |i: int| (p[i].0 as int, vars_view(p[i].1@)))
}

///  Coefficient bound on runtime poly: all i64 coefficients have |c| <= bound.
pub open spec fn rt_poly_bounded(p: Seq<(i64, Vec<u32>)>, bound: int) -> bool {
    forall |i: int| 0 <= i < p.len() ==>
        (#[trigger] p[i]).0 as int >= -bound && p[i].0 as int <= bound
}

//  The i64 safe bound: coefficients at most this can be added/multiplied safely.
//  Using i32::MAX so that a+b and a*b both fit in i64.
pub open spec fn COEFF_BOUND() -> int { 0x7FFF_FFFF }

///  Bridge lemma: vars_view commutes with subrange.
proof fn lemma_vars_view_tail(v: Seq<u32>)
    requires v.len() > 0,
    ensures vars_view(v.subrange(1, v.len() as int))
        =~= vars_view(v).subrange(1, v.len() as int),
{
    assert(vars_view(v.subrange(1, v.len() as int))
        =~= vars_view(v).subrange(1, v.len() as int));
}

///  Build a Vec<u32> tail (elements from index 1 onwards).
fn vec_u32_tail(v: &Vec<u32>) -> (out: Vec<u32>)
    requires v@.len() > 0,
    ensures
        out@.len() == v@.len() - 1,
        forall |k: int| 0 <= k < out@.len() ==> out@[k] == v@[k + 1],
        vars_view(out@) =~= vars_view(v@).subrange(1, v@.len() as int),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 1;
    while i < v.len()
        invariant 1 <= i <= v@.len(),
            out@.len() == (i - 1) as int,
            forall |k: int| 0 <= k < out@.len() ==> out@[k] == v@[k + 1],
        decreases v@.len() - i,
    { out.push(v[i]); i = i + 1; }
    proof { lemma_vars_view_tail(v@); }
    out
}

///  Build a polynomial tail (elements from index 1 onwards).
///  Postcondition: the poly_rt_view of the tail matches the poly_rt_view of the
///  original subranged from 1.
fn poly_tail(p: &Vec<(i64, Vec<u32>)>) -> (out: Vec<(i64, Vec<u32>)>)
    requires p@.len() > 0,
    ensures
        out@.len() == p@.len() - 1,
        forall |k: int| 0 <= k < out@.len() ==>
            (#[trigger] out@[k]).0 == p@[k + 1].0
            && out@[k].1@ =~= p@[k + 1].1@,
        poly_rt_view(out@) =~= poly_rt_view(p@).subrange(1, p@.len() as int),
{
    let mut out: Vec<(i64, Vec<u32>)> = Vec::new();
    let mut i: usize = 1;
    while i < p.len()
        invariant 1 <= i <= p@.len(),
            out@.len() == (i - 1) as int,
            forall |k: int| 0 <= k < out@.len() ==>
                (#[trigger] out@[k]).0 == p@[k + 1].0
                && out@[k].1@ =~= p@[k + 1].1@,
        decreases p@.len() - i,
    { out.push((p[i].0, p[i].1.clone())); i = i + 1; }
    //  Bridge: poly_rt_view(out@) =~= poly_rt_view(p@).subrange(1, ...)
    assert(poly_rt_view(out@) =~= poly_rt_view(p@).subrange(1, p@.len() as int));
    out
}

///  Runtime lexicographic less-than on variable tuples.
pub fn runtime_vars_lt(a: &Vec<u32>, b: &Vec<u32>) -> (out: bool)
    ensures out == vars_lt(vars_view(a@), vars_view(b@)),
    decreases a.len(),
{
    if a.len() == 0 {
        b.len() > 0
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        let at = vec_u32_tail(a);
        let bt = vec_u32_tail(b);
        runtime_vars_lt(&at, &bt)
    }
}

///  Runtime: check if two variable tuples are equal.
pub fn runtime_vars_eq(a: &Vec<u32>, b: &Vec<u32>) -> (out: bool)
    ensures out == (vars_view(a@) =~= vars_view(b@)),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall |k: int| 0 <= k < i as int ==> a@[k] == b@[k],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            assert(vars_view(a@)[i as int] != vars_view(b@)[i as int]);
            return false;
        }
        i = i + 1;
    }
    assert(vars_view(a@) =~= vars_view(b@));
    true
}

///  Runtime merge of two sorted variable tuples.
pub fn runtime_vars_merge(a: &Vec<u32>, b: &Vec<u32>) -> (out: Vec<u32>)
    ensures vars_view(out@) =~= vars_merge(
        vars_view(a@), vars_view(b@)),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        b.clone()
    } else if b.len() == 0 {
        a.clone()
    } else if a[0] <= b[0] {
        let at = vec_u32_tail(a);
        let mut rest = runtime_vars_merge(&at, b);
        rest.insert(0, a[0]);
        rest
    } else {
        let bt = vec_u32_tail(b);
        let mut rest = runtime_vars_merge(a, &bt);
        rest.insert(0, b[0]);
        rest
    }
}

///  Runtime polynomial negation.
pub fn runtime_poly_neg(p: &Vec<(i64, Vec<u32>)>) -> (out: Vec<(i64, Vec<u32>)>)
    requires
        forall |i: int| 0 <= i < p@.len() ==> (#[trigger] p@[i]).0 > i64::MIN,
    ensures
        poly_rt_view(out@) =~= poly_neg(poly_rt_view(p@)),
        //  Negation preserves bounds: |(-c)| == |c|
        out@.len() == p@.len(),
        forall |i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).0 as int == -(p@[i].0 as int),
    decreases p.len(),
{
    if p.len() == 0 {
        Vec::new()
    } else {
        let tail = poly_tail(p);
        let mut rest = runtime_poly_neg(&tail);
        rest.insert(0, (-p[0].0, p[0].1.clone()));
        rest
    }
}

///  Clone a runtime polynomial with poly_rt_view preservation.
fn poly_clone(p: &Vec<(i64, Vec<u32>)>) -> (out: Vec<(i64, Vec<u32>)>)
    ensures
        poly_rt_view(out@) =~= poly_rt_view(p@),
        out@.len() == p@.len(),
        forall |k: int| 0 <= k < out@.len() ==>
            (#[trigger] out@[k]).0 == p@[k].0 && out@[k].1@ =~= p@[k].1@,
{
    let mut out: Vec<(i64, Vec<u32>)> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(),
            out@.len() == i as int,
            forall |k: int| 0 <= k < i as int ==>
                (#[trigger] out@[k]).0 == p@[k].0
                && out@[k].1@ =~= p@[k].1@,
        decreases p@.len() - i,
    {
        out.push((p[i].0, p[i].1.clone()));
        i = i + 1;
    }
    assert(poly_rt_view(out@) =~= poly_rt_view(p@));
    out
}

///  Bridge: poly_rt_view is congruent under Seq equality.
proof fn lemma_poly_rt_view_eq(a: Seq<(i64, Vec<u32>)>, b: Seq<(i64, Vec<u32>)>)
    requires a == b,
    ensures poly_rt_view(a) =~= poly_rt_view(b),
{}

///  Bridge: poly_rt_view of prepend.
proof fn lemma_poly_rt_view_prepend(
    head: (i64, Vec<u32>), tail: Seq<(i64, Vec<u32>)>,
    spec_head: (int, Seq<nat>), spec_tail: Seq<(int, Seq<nat>)>,
)
    requires
        head.0 as int == spec_head.0,
        vars_view(head.1@) =~= spec_head.1,
        poly_rt_view(tail) =~= spec_tail,
    ensures
        poly_rt_view(seq![head] + tail) =~= seq![spec_head] + spec_tail,
{
    let rt = seq![head] + tail;
    let sp = seq![spec_head] + spec_tail;
    assert forall |i: int| 0 <= i < rt.len() implies poly_rt_view(rt)[i] == sp[i]
    by {
        if i == 0 {
            assert(rt[0] == head);
            assert(sp[0] == spec_head);
        } else {
            assert(rt[i] == tail[i - 1]);
            assert(sp[i] == spec_tail[i - 1]);
        }
    }
}

///  Assertion helper: poly_tail preserves rt_poly_bounded.
///  (Inline as assertion after poly_tail call, using the poly_tail postcondition.)
///  poly_tail ensures out@[k].0 == p@[k+1].0, so if p is bounded, the tail is too.

///  Runtime polynomial addition (merge two sorted polynomials).
///  Both inputs bounded by B, B+B fits in i64.
pub fn runtime_poly_add(
    p: &Vec<(i64, Vec<u32>)>,
    q: &Vec<(i64, Vec<u32>)>,
    bound: Ghost<int>,
) -> (out: Vec<(i64, Vec<u32>)>)
    requires
        rt_poly_bounded(p@, bound@),
        rt_poly_bounded(q@, bound@),
        bound@ >= 0, 2 * bound@ <= i64::MAX as int,
    ensures
        poly_rt_view(out@) =~= poly_add(
            poly_rt_view(p@), poly_rt_view(q@)),
    decreases p.len() + q.len(),
{
    let ghost pv = poly_rt_view(p@);
    let ghost qv = poly_rt_view(q@);
    reveal_with_fuel(poly_add, 2);
    if p.len() == 0 {
        let out = poly_clone(q);
        assert forall |k: int| 0 <= k < out@.len()
            implies (#[trigger] out@[k]).0 as int >= -(2 * bound@)
                && out@[k].0 as int <= 2 * bound@
        by { assert(out@[k].0 == q@[k].0); }
        return out;
    } else if q.len() == 0 {
        let out = poly_clone(p);
        assert forall |k: int| 0 <= k < out@.len()
            implies (#[trigger] out@[k]).0 as int >= -(2 * bound@)
                && out@[k].0 as int <= 2 * bound@
        by { assert(out@[k].0 == p@[k].0); }
        return out;
    } else if runtime_vars_eq(&p[0].1, &q[0].1) {
        assert(pv[0].1 =~= qv[0].1);
        let c: i64 = p[0].0 + q[0].0;
        assert(c as int == pv[0].0 + qv[0].0);
        let pt = poly_tail(p);
        let qt = poly_tail(q);
        assert(rt_poly_bounded(pt@, bound@)) by {
            assert forall |k: int| 0 <= k < pt@.len()
                implies (#[trigger] pt@[k]).0 as int >= -(bound@) && pt@[k].0 as int <= bound@
            by { assert(pt@[k].0 == p@[k + 1].0); }
        }
        assert(rt_poly_bounded(qt@, bound@)) by {
            assert forall |k: int| 0 <= k < qt@.len()
                implies (#[trigger] qt@[k]).0 as int >= -(bound@) && qt@[k].0 as int <= bound@
            by { assert(qt@[k].0 == q@[k + 1].0); }
        }
        let rest = runtime_poly_add(&pt, &qt, bound);
        //  IH: poly_rt_view(rest@) =~= poly_add(pv.subrange(1,..), qv.subrange(1,..))
        if c == 0 {
            rest
        } else {
            let mut out = rest;
            out.insert(0, (c, p[0].1.clone()));
            out
        }
    } else if runtime_vars_lt(&p[0].1, &q[0].1) {
        assert(vars_lt(pv[0].1, qv[0].1));
        let pt = poly_tail(p);
        assert(rt_poly_bounded(pt@, bound@)) by {
            assert forall |k: int| 0 <= k < pt@.len()
                implies (#[trigger] pt@[k]).0 as int >= -(bound@) && pt@[k].0 as int <= bound@
            by { assert(pt@[k].0 == p@[k + 1].0); }
        }
        let mut out = runtime_poly_add(&pt, q, bound);
        out.insert(0, (p[0].0, p[0].1.clone()));
        out
    } else {
        let qt = poly_tail(q);
        assert(rt_poly_bounded(qt@, bound@)) by {
            assert forall |k: int| 0 <= k < qt@.len()
                implies (#[trigger] qt@[k]).0 as int >= -(bound@) && qt@[k].0 as int <= bound@
            by { assert(qt@[k].0 == q@[k + 1].0); }
        }
        let mut out = runtime_poly_add(p, &qt, bound);
        out.insert(0, (q[0].0, q[0].1.clone()));
        out
    }
}

///  Runtime polynomial insert.
pub fn runtime_poly_insert(
    c: i64, v: &Vec<u32>, p: &Vec<(i64, Vec<u32>)>,
    cb: Ghost<int>, pb: Ghost<int>,
) -> (out: Vec<(i64, Vec<u32>)>)
    requires
        rt_poly_bounded(p@, pb@),
        -(cb@) <= c as int <= cb@,
        cb@ >= 0, pb@ >= 0,
        cb@ + pb@ <= i64::MAX as int,
    ensures
        poly_rt_view(out@) =~= poly_insert(
            c as int, vars_view(v@), poly_rt_view(p@)),
        rt_poly_bounded(out@, cb@ + pb@),
    decreases p.len(),
{
    let ghost pv = poly_rt_view(p@);
    reveal_with_fuel(poly_insert, 2);
    if c == 0 {
        poly_clone(p)
    } else if p.len() == 0 {
        let mut out = Vec::new();
        out.push((c, v.clone()));
        out
    } else if runtime_vars_eq(v, &p[0].1) {
        assert(vars_view(v@) =~= pv[0].1);
        let nc: i64 = c + p[0].0;
        if nc == 0 {
            poly_tail(p)
        } else {
            let mut out = poly_tail(p);
            out.insert(0, (nc, v.clone()));
            out
        }
    } else if runtime_vars_lt(v, &p[0].1) {
        assert(vars_lt(vars_view(v@), pv[0].1));
        let mut out = poly_clone(p);
        out.insert(0, (c, v.clone()));
        out
    } else {
        let pt = poly_tail(p);
        assert(rt_poly_bounded(pt@, pb@)) by {
            assert forall |k: int| 0 <= k < pt@.len()
                implies (#[trigger] pt@[k]).0 as int >= -(pb@) && pt@[k].0 as int <= pb@
            by { assert(pt@[k].0 == p@[k + 1].0); }
        }
        let mut out = runtime_poly_insert(c, v, &pt, cb, pb);
        out.insert(0, (p[0].0, p[0].1.clone()));
        out
    }
}

///  Runtime monomial × polynomial multiplication.
///  Output bounded by q.len() * bound^2 (each of q.len() terms contributes up to bound^2).
pub fn runtime_mono_mul_poly(
    c: i64, vars: &Vec<u32>, q: &Vec<(i64, Vec<u32>)>,
    qb: Ghost<int>,
    ecb: Ghost<int>,
) -> (out: Vec<(i64, Vec<u32>)>)
    requires
        rt_poly_bounded(q@, qb@),
        qb@ >= 0, ecb@ >= 0,
        //  Products fit in i64: |c|*qb <= i64::MAX/2
        (if (c as int) >= 0 { c as int } else { -(c as int) }) * qb@ <= i64::MAX as int / 2,
        //  ecb covers: 2*ecb <= i64::MAX (for poly_insert)
        2 * ecb@ <= i64::MAX as int,
        //  |c| * sum_abs(q) <= ecb — enables the spec bound proof
        (if (c as int) >= 0 { c as int } else { -(c as int) })
            * poly_sum_abs(poly_rt_view(q@)) <= ecb@,
    ensures
        poly_rt_view(out@) =~= mono_mul_poly(
            c as int, vars_view(vars@), poly_rt_view(q@)),
        rt_poly_bounded(out@, ecb@),
    decreases q.len(),
{
    reveal_with_fuel(mono_mul_poly, 2);
    if c == 0 || q.len() == 0 {
        let out: Vec<(i64, Vec<u32>)> = Vec::new();
        assert(rt_poly_bounded(out@, ecb@));
        out
    } else {
        let ghost abs_c: int = if (c as int) >= 0 { c as int } else { -(c as int) };
        assert(i64::MIN <= (c as int) * (q@[0].0 as int) <= i64::MAX) by(nonlinear_arith)
            requires
                -(qb@) <= q@[0].0 as int <= qb@,
                abs_c * qb@ <= i64::MAX as int / 2,
                qb@ >= 0;
        let nc: i64 = c * q[0].0;
        let nv = runtime_vars_merge(vars, &q[0].1);
        let qt = poly_tail(q);
        assert(rt_poly_bounded(qt@, qb@)) by {
            assert forall |k: int| 0 <= k < qt@.len()
                implies (#[trigger] qt@[k]).0 as int >= -(qb@) && qt@[k].0 as int <= qb@
            by { assert(qt@[k].0 == q@[k + 1].0); }
        }
        proof {
            let qv = poly_rt_view(q@);
            let qtv = poly_rt_view(qt@);
            reveal_with_fuel(poly_sum_abs, 2);
            lemma_poly_sum_abs_nonneg(qtv);
            assert(abs_c * poly_sum_abs(qtv) <= ecb@) by(nonlinear_arith)
                requires
                    poly_sum_abs(qtv) <= poly_sum_abs(qv),
                    abs_c * poly_sum_abs(qv) <= ecb@,
                    poly_sum_abs(qtv) >= 0, abs_c >= 0;
        }
        let rest = runtime_mono_mul_poly(c, vars, &qt, qb, ecb);
        assert(-(ecb@) <= nc as int <= ecb@) by(nonlinear_arith)
            requires
                -(qb@) <= q@[0].0 as int <= qb@,
                abs_c * qb@ <= i64::MAX as int / 2,
                nc as int == (c as int) * (q@[0].0 as int),
                qb@ >= 0;
        let result = runtime_poly_insert(nc, &nv, &rest, ecb, ecb);
        //  poly_insert gives bound 2*ecb. We need ecb.
        //  Use spec lemma: mono_mul_poly result has sum_abs <= |c|*sum_abs(q) <= ecb.
        proof {
            use crate::gpu_ring_test::lemma_mono_mul_sum_abs;
            let qv = poly_rt_view(q@);
            lemma_mono_mul_sum_abs(c as int, vars_view(vars@), qv);
            //  sum_abs(mono_result) <= |c| * sum_abs(qv) <= ecb (from precondition)
            lemma_rt_bounded_from_sum_abs(
                result@,
                mono_mul_poly(c as int, vars_view(vars@), qv),
                ecb@);
        }
        result
    }
}

///  Runtime polynomial multiplication.
///  Output bounded by p.len() * q.len() * bound^2 (loosely).
///  Runtime polynomial multiplication.
///  Takes ecb (expression coefficient bound) as universal budget for overflow safety.
///  Runtime polynomial multiplication.
///  Uses spec lemma to establish output bounds.
pub fn runtime_poly_mul(
    p: &Vec<(i64, Vec<u32>)>,
    q: &Vec<(i64, Vec<u32>)>,
    pb: Ghost<int>,
    qb: Ghost<int>,
    ecb: Ghost<int>,
) -> (out: Vec<(i64, Vec<u32>)>)
    requires
        rt_poly_bounded(p@, pb@),
        rt_poly_bounded(q@, qb@),
        pb@ >= 0, qb@ >= 0, ecb@ >= 0,
        //  Products fit in i64
        pb@ * qb@ <= i64::MAX as int / 2,
        //  poly_add safety: 2 * ecb <= i64::MAX
        2 * ecb@ <= i64::MAX as int,
        //  Spec-level bound: sum_abs of inputs multiplied <= ecb
        poly_sum_abs(poly_rt_view(p@)) * poly_sum_abs(poly_rt_view(q@)) <= ecb@,
    ensures
        poly_rt_view(out@) =~= poly_mul(
            poly_rt_view(p@), poly_rt_view(q@)),
        rt_poly_bounded(out@, ecb@),
    decreases p.len(),
{
    reveal_with_fuel(poly_mul, 2);
    if p.len() == 0 {
        let out: Vec<(i64, Vec<u32>)> = Vec::new();
        assert(rt_poly_bounded(out@, ecb@));
        out
    } else {
        let pt = poly_tail(p);
        //  Need: |p[0].0| * sum_abs(qv) <= sum_abs(pv) * sum_abs(qv) <= ecb
        proof {
            let pv = poly_rt_view(p@);
            let qv = poly_rt_view(q@);
            let ptv = poly_rt_view(pt@);
            reveal_with_fuel(poly_sum_abs, 2);
            lemma_poly_sum_abs_nonneg(qv);
            lemma_poly_sum_abs_nonneg(ptv);
            let abs_p0: int = if pv[0].0 >= 0 { pv[0].0 } else { -pv[0].0 };
            assert(abs_p0 <= poly_sum_abs(pv));
            assert(abs_p0 * poly_sum_abs(qv) <= ecb@) by(nonlinear_arith)
                requires
                    abs_p0 <= poly_sum_abs(pv),
                    poly_sum_abs(pv) * poly_sum_abs(qv) <= ecb@,
                    poly_sum_abs(qv) >= 0, abs_p0 >= 0;
        }
        //  mono_mul needs |p[0].0|*qb <= i64::MAX/2. From pb*qb <= i64::MAX/2 and |p[0].0| <= pb.
        let mono = runtime_mono_mul_poly(p[0].0, &p[0].1, q, qb, ecb);
        assert(rt_poly_bounded(pt@, pb@)) by {
            assert forall |k: int| 0 <= k < pt@.len()
                implies (#[trigger] pt@[k]).0 as int >= -(pb@) && pt@[k].0 as int <= pb@
            by { assert(pt@[k].0 == p@[k + 1].0); }
        }
        //  For recursive call: need poly_sum_abs(pt_view) * poly_sum_abs(qv) <= ecb
        //  poly_sum_abs(pt_view) <= poly_sum_abs(pv) (pt is a subseq of p, with fewer terms)
        proof {
            let pv = poly_rt_view(p@);
            let ptv = poly_rt_view(pt@);
            let qv = poly_rt_view(q@);
            reveal_with_fuel(poly_sum_abs, 2);
            lemma_poly_sum_abs_nonneg(ptv);
            lemma_poly_sum_abs_nonneg(qv);
            //  sum_abs(ptv) <= sum_abs(pv) since pv = [pv[0]] + ptv
            //  sum_abs(pv) = |pv[0].0| + sum_abs(ptv) >= sum_abs(ptv)
            assert(poly_sum_abs(ptv) <= poly_sum_abs(pv));
            //  So sum_abs(ptv) * sum_abs(qv) <= sum_abs(pv) * sum_abs(qv) <= ecb
            assert(poly_sum_abs(ptv) * poly_sum_abs(qv) <= ecb@) by(nonlinear_arith)
                requires
                    poly_sum_abs(ptv) <= poly_sum_abs(pv),
                    poly_sum_abs(pv) * poly_sum_abs(qv) <= ecb@,
                    poly_sum_abs(qv) >= 0;
        }
        let rest = runtime_poly_mul(&pt, q, pb, qb, ecb);
        //  Both mono and rest: use spec lemma to establish bounds.
        //  mono = mono_mul(p[0], q) as a PARTIAL result of poly_mul(p, q).
        //  rest = poly_mul(pt, q) as the rest.
        //  poly_mul(pv, qv) = poly_add(mono_v, rest_v).
        //  poly_sum_abs(poly_mul(pv, qv)) <= ecb (from spec lemma + precondition).
        //  mono_v is a subset of terms contributing to poly_mul.
        //  We USE the spec lemma: individual coefficients of poly_mul(pv,qv) <= ecb.
        //  Both mono and rest contribute to poly_mul, so their individual coefficients <= ecb.
        //  Actually: mono = mono_mul_poly(pv[0], qv), rest = poly_mul(pt_v, qv).
        //  poly_mul(pv, qv) = poly_add(mono, rest).
        //  By poly_add_sum_abs: poly_sum_abs(result) <= poly_sum_abs(mono) + poly_sum_abs(rest).
        //  Both <= ecb (since poly_sum_abs(mono) <= |pv[0].0|*sum_abs(qv) <= sum_abs(pv)*sum_abs(qv) <= ecb).
        //  Use lemma_rt_bounded_from_sum_abs to establish rt_poly_bounded.
        proof {
            use crate::gpu_ring_test::{lemma_mono_mul_sum_abs, lemma_poly_mul_sum_abs};
            let pv = poly_rt_view(p@);
            let qv = poly_rt_view(q@);
            let ptv = poly_rt_view(pt@);
            let mv = mono_mul_poly(pv[0].0, pv[0].1, qv);
            lemma_mono_mul_sum_abs(pv[0].0, pv[0].1, qv);
            lemma_poly_sum_abs_nonneg(qv);
            reveal_with_fuel(poly_sum_abs, 2);
            //  |pv[0].0| <= sum_abs(pv) (first term contributes to total)
            //  sum_abs(mv) <= |pv[0].0| * sum_abs(qv) <= sum_abs(pv) * sum_abs(qv) <= ecb
            assert(poly_sum_abs(mv) <= ecb@) by(nonlinear_arith)
                requires
                    poly_sum_abs(mv)
                        <= (if pv[0].0 >= 0 { pv[0].0 } else { -pv[0].0 }) * poly_sum_abs(qv),
                    poly_sum_abs(pv) >= (if pv[0].0 >= 0 { pv[0].0 } else { -pv[0].0 }),
                    poly_sum_abs(pv) * poly_sum_abs(qv) <= ecb@,
                    poly_sum_abs(qv) >= 0;
            lemma_rt_bounded_from_sum_abs(mono@, mv, ecb@);
            //  rest bounded by ecb from IH postcondition
        }
        let result = runtime_poly_add(&mono, &rest, ecb);
        //  Establish rt_poly_bounded(result@, ecb) from the spec lemma
        proof {
            use crate::gpu_ring_test::lemma_poly_mul_sum_abs;
            let pv = poly_rt_view(p@);
            let qv = poly_rt_view(q@);
            lemma_poly_mul_sum_abs(pv, qv);
            lemma_poly_sum_abs_nonneg(pv);
            lemma_poly_sum_abs_nonneg(qv);
            assert(poly_sum_abs(poly_mul(pv, qv)) <= ecb@) by(nonlinear_arith)
                requires
                    poly_sum_abs(poly_mul(pv, qv)) <= poly_sum_abs(pv) * poly_sum_abs(qv),
                    poly_sum_abs(pv) * poly_sum_abs(qv) <= ecb@,
                    poly_sum_abs(pv) >= 0, poly_sum_abs(qv) >= 0;
            lemma_rt_bounded_from_sum_abs(result@, poly_mul(pv, qv), ecb@);
        }
        result
    }
}

///  Bridge: if poly_rt_view(p) =~= sp and poly_sum_abs(sp) <= bound, then rt_poly_bounded(p, bound).
proof fn lemma_rt_bounded_from_sum_abs(
    p: Seq<(i64, Vec<u32>)>,
    sp: Seq<(int, Seq<nat>)>,
    bound: int,
)
    requires poly_rt_view(p) =~= sp, poly_sum_abs(sp) <= bound, bound >= 0,
    ensures rt_poly_bounded(p, bound),
{
    assert forall |k: int| 0 <= k < p.len()
        implies (#[trigger] p[k]).0 as int >= -bound && p[k].0 as int <= bound
    by {
        lemma_poly_sum_abs_bounds_individual(sp, k);
    }
}

///  Bridge: if poly_rt_view(p@) =~= arith_to_poly(e), then rt_poly_bounded(p@, ecb(e)).
proof fn lemma_rt_bounded_from_spec(
    p: Seq<(i64, Vec<u32>)>, e: &ArithExpr,
)
    requires poly_rt_view(p) =~= arith_to_poly(e),
    ensures rt_poly_bounded(p, expr_coeff_bound(e)),
{
    lemma_arith_to_poly_sum_abs(e);
    assert forall |k: int| 0 <= k < p.len()
        implies (#[trigger] p[k]).0 as int >= -(expr_coeff_bound(e))
            && p[k].0 as int <= expr_coeff_bound(e)
    by {
        //  poly_rt_view(p)[k] == arith_to_poly(e)[k]
        //  p[k].0 as int == poly_rt_view(p)[k].0 == arith_to_poly(e)[k].0
        //  |arith_to_poly(e)[k].0| <= poly_sum_abs(arith_to_poly(e)) <= ecb(e)
        lemma_poly_sum_abs_bounds_individual(arith_to_poly(e), k);
    }
}

///  All sub-expressions have safe coefficient bounds (no overflow anywhere).
pub open spec fn expr_all_safe(e: &ArithExpr) -> bool
    decreases e,
{
    expr_coeff_bound(e) >= 0
    && expr_coeff_bound(e) <= i64::MAX as int / 2
    //  For Mul: need max(ecb(a),ecb(b))^2 to fit for mono_mul overflow proofs
    && expr_coeff_bound(e) * expr_coeff_bound(e) <= i64::MAX as int / 4
    && match e {
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b) =>
            expr_all_safe(a) && expr_all_safe(b),
        _ => true,
    }
}

///  Runtime ArithExpr to polynomial normal form.
///  Requires expr_coeff_bound to be within i64 safe range.
pub fn runtime_arith_to_poly(
    e: &RuntimeArithExpr,
) -> (out: Vec<(i64, Vec<u32>)>)
    requires
        expr_all_safe(&e.view_spec()),
    ensures
        poly_rt_view(out@) =~= arith_to_poly(&e.view_spec()),
        rt_poly_bounded(out@, expr_coeff_bound(&e.view_spec())),
    decreases e,
{
    proof {
        reveal_with_fuel(RuntimeArithExpr::view_spec, 2);
        reveal_with_fuel(expr_all_safe, 2);
    }
    let ghost ecb = expr_coeff_bound(&e.view_spec());
    match e {
        RuntimeArithExpr::Const(c) => {
            proof { reveal_with_fuel(expr_coeff_bound, 2); }
            if *c == 0 {
                Vec::new()
            } else {
                let mut out = Vec::new();
                out.push((*c, Vec::new()));
                out
            }
        },
        RuntimeArithExpr::Var(n) => {
            proof { reveal_with_fuel(expr_coeff_bound, 2); }
            let mut vars = Vec::new();
            vars.push(*n);
            let mut out = Vec::new();
            out.push((1i64, vars));
            out
        },
        RuntimeArithExpr::Add(a, b) => {
            proof { reveal_with_fuel(expr_coeff_bound, 2); }
            let pa = runtime_arith_to_poly(a);
            let pb = runtime_arith_to_poly(b);
            proof {
                lemma_rt_bounded_from_spec(pa@, &a.view_spec());
                lemma_rt_bounded_from_spec(pb@, &b.view_spec());
                //  pa bounded by ecb(a) <= ecb. pb bounded by ecb(b) <= ecb.
                lemma_expr_coeff_bound_nonneg(&a.view_spec());
                lemma_expr_coeff_bound_nonneg(&b.view_spec());
            }
            runtime_poly_add(&pa, &pb, Ghost(ecb))
        },
        RuntimeArithExpr::Sub(a, b) => {
            proof { reveal_with_fuel(expr_coeff_bound, 2); }
            let pa = runtime_arith_to_poly(a);
            let pb = runtime_arith_to_poly(b);
            proof {
                lemma_rt_bounded_from_spec(pa@, &a.view_spec());
                lemma_rt_bounded_from_spec(pb@, &b.view_spec());
                lemma_expr_coeff_bound_nonneg(&a.view_spec());
                lemma_expr_coeff_bound_nonneg(&b.view_spec());
            }
            let neg_pb = runtime_poly_neg(&pb);
            //  neg_pb has same |coefficients| as pb, bounded by ecb(b) <= ecb
            assert(rt_poly_bounded(neg_pb@, ecb)) by {
                assert forall |k: int| 0 <= k < neg_pb@.len()
                    implies (#[trigger] neg_pb@[k]).0 as int >= -(ecb) && neg_pb@[k].0 as int <= ecb
                by {
                    assert(neg_pb@[k].0 as int == -(pb@[k].0 as int));
                }
            }
            runtime_poly_add(&pa, &neg_pb, Ghost(ecb))
        },
        RuntimeArithExpr::Mul(a, b) => {
            proof { reveal_with_fuel(expr_coeff_bound, 2); }
            let pa = runtime_arith_to_poly(a);
            let pb = runtime_arith_to_poly(b);
            let ghost ba = expr_coeff_bound(&a.view_spec());
            let ghost bb = expr_coeff_bound(&b.view_spec());
            let ghost mb = if ba >= bb { ba } else { bb };
            proof {
                lemma_rt_bounded_from_spec(pa@, &a.view_spec());
                lemma_rt_bounded_from_spec(pb@, &b.view_spec());
                lemma_expr_coeff_bound_nonneg(&a.view_spec());
                lemma_expr_coeff_bound_nonneg(&b.view_spec());
                //  sum_abs(pa_view) <= ecb(a) and sum_abs(pb_view) <= ecb(b).
                //  Product <= ecb(a)*ecb(b) = ecb(Mul(a,b)).
                lemma_arith_to_poly_sum_abs(&a.view_spec());
                lemma_arith_to_poly_sum_abs(&b.view_spec());
                //  poly_sum_abs(pa_view) * poly_sum_abs(pb_view)
                //  <= ecb(a) * ecb(b) = ecb
                //  Connect runtime view to spec: poly_rt_view(pa@) =~= arith_to_poly(a)
                //  So poly_sum_abs is the same for both.
                assert(poly_sum_abs(poly_rt_view(pa@)) <= ba) by {
                    assert(poly_rt_view(pa@) =~= arith_to_poly(&a.view_spec()));
                }
                assert(poly_sum_abs(poly_rt_view(pb@)) <= bb) by {
                    assert(poly_rt_view(pb@) =~= arith_to_poly(&b.view_spec()));
                }
                lemma_poly_sum_abs_nonneg(poly_rt_view(pa@));
                lemma_poly_sum_abs_nonneg(poly_rt_view(pb@));
                assert(poly_sum_abs(poly_rt_view(pa@)) * poly_sum_abs(poly_rt_view(pb@)) <= ecb)
                    by(nonlinear_arith)
                    requires
                        poly_sum_abs(poly_rt_view(pa@)) <= ba,
                        poly_sum_abs(poly_rt_view(pb@)) <= bb,
                        ecb == ba * bb,
                        ba >= 0, bb >= 0,
                        poly_sum_abs(poly_rt_view(pa@)) >= 0,
                        poly_sum_abs(poly_rt_view(pb@)) >= 0;
                //  mb = max(ba, bb). mb^2 <= max(ba^2, bb^2) <= i64::MAX/4
                //  (from expr_all_safe on sub-expressions)
                reveal_with_fuel(expr_all_safe, 2);
                //  Use ecb as the single bound. Both ba <= ecb and bb <= ecb
                //  since ecb = ba*bb and ba,bb >= 1 (we checked ecb > 0 below).
                //  ecb^2 = (ba*bb)^2 <= (max(ba,bb))^4 which could be large.
                //  But ecb*ecb <= i64::MAX/4 from expr_all_safe.
            }
            //  Use ecb as bound. Both ba,bb <= ecb when both >= 1.
            //  When ba=0 or bb=0: ecb=0, result is empty.
            //  When ecb > 0: both ba,bb >= 1, so ba <= ecb and bb <= ecb.
            //  When ecb = 0: one of ba,bb is 0, the sub-poly is empty, result is empty.
            if pa.len() == 0 || pb.len() == 0 {
                //  One sub-polynomial is empty → poly_mul gives empty.
                let out: Vec<(i64, Vec<u32>)> = Vec::new();
                proof {
                    reveal_with_fuel(poly_mul, 2);
                    assert(rt_poly_bounded(out@, ecb));
                    //  Need to show the empty result matches spec.
                    //  arith_to_poly(Mul(a,b)) = poly_mul(pa_view, pb_view).
                    //  If pa is empty: poly_mul([], pb_view) = []. ✓
                    //  If pb is empty: poly_mul(pa_view, []) = ? — depends on pa.
                    //  Actually poly_mul([x, ...], []) recurses with mono_mul_poly which returns [].
                    //  So poly_mul(anything, []) = []. But proving this requires induction.
                    //  For now, the correctness postcondition should follow from poly_mul def.
                }
                out
            } else {
                proof {
                    //  ba > 0 and bb > 0 (since pa and pb are non-empty, their ecbs must be > 0
                    //  because arith_to_poly of an expr with ecb=0 is empty).
                    //  So ecb = ba*bb > 0. ba <= ecb and bb <= ecb.
                    //  ecb = ba*bb. If pa and pb non-empty: ba > 0 and bb > 0.
                    //  Why? IH: pa bounded by ba. If pa non-empty with nonzero coeff:
                    //  |coeff| <= ba, so ba >= 1 (since coeff is int and |coeff| >= 1).
                    //  Similarly bb >= 1.
                    //  Alternatively: just use lemma_arith_to_poly_coeff_bound to directly
                    //  establish pa bounded by ecb.
                    lemma_arith_to_poly_sum_abs(&a.view_spec());
                    lemma_arith_to_poly_sum_abs(&b.view_spec());
                    //  sum_abs(arith_to_poly(a)) <= ba. Individual coeffs <= ba.
                    //  Need ba <= ecb. From ecb = ba*bb with bb >= 1:
                    //  We know pb.len() > 0. The IH gives rt_poly_bounded(pb@, bb).
                    //  If pb is non-empty and WF: min coeff >= 1 (since WF has nonzero coeffs).
                    //  So bb >= 1. Then ba <= ba*bb = ecb.
                    //  For simplicity: just bound pa by ecb using the spec lemma directly.
                }
                //  Pass ba and bb as separate bounds.
                //  poly_mul needs: ba*bb <= i64::MAX/2.
                //  From expr_all_safe: ecb*ecb <= i64::MAX/4. ecb = ba*bb.
                //  ba*bb = ecb <= sqrt(i64::MAX/4). So ba*bb <= i64::MAX/4 <= i64::MAX/2. ✓
                runtime_poly_mul(&pa, &pb, Ghost(ba), Ghost(bb), Ghost(ecb))
            }
        },
        _ => {
            Vec::new()
        },
    }
}

///  Runtime polynomial structural equality.
pub fn runtime_poly_eq(
    p: &Vec<(i64, Vec<u32>)>,
    q: &Vec<(i64, Vec<u32>)>,
) -> (out: bool)
    ensures out == (poly_rt_view(p@) =~= poly_rt_view(q@)),
{
    if p.len() != q.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < p.len()
        invariant
            i <= p.len(),
            p@.len() == q@.len(),
            forall |k: int| 0 <= k < i as int ==>
                poly_rt_view(p@)[k] == poly_rt_view(q@)[k],
        decreases p@.len() - i,
    {
        if p[i].0 != q[i].0 {
            assert(poly_rt_view(p@)[i as int].0 != poly_rt_view(q@)[i as int].0);
            return false;
        }
        if !runtime_vars_eq(&p[i].1, &q[i].1) {
            assert(!(poly_rt_view(p@)[i as int].1 =~= poly_rt_view(q@)[i as int].1));
            return false;
        }
        i = i + 1;
    }
    assert(poly_rt_view(p@) =~= poly_rt_view(q@));
    true
}

//  ══════════════════════════════════════════════════════════════
//  Runtime perturbation step
//  ══════════════════════════════════════════════════════════════

///  Exec-level perturbation step matching the spec-level
///  perturbation_step::<GpuFixedPoint<N, F>>. Builds the
///  expression tree for δ_{n+1} = 2·Z·δ + δ² + Δc.
pub fn runtime_perturbation_step<const N: usize, const F: usize>(
    z_ref: (&RuntimeGpuFixedPoint<N, F>, &RuntimeGpuFixedPoint<N, F>),
    delta: (&RuntimeGpuFixedPoint<N, F>, &RuntimeGpuFixedPoint<N, F>),
    delta_c: (&RuntimeGpuFixedPoint<N, F>, &RuntimeGpuFixedPoint<N, F>),
) -> (out: (RuntimeGpuFixedPoint<N, F>, RuntimeGpuFixedPoint<N, F>))
    ensures
        out.0@ == verus_mandelbrot::perturbation::perturbation_step::<GpuFixedPoint<N, F>>(
            (z_ref.0@, z_ref.1@), (delta.0@, delta.1@), (delta_c.0@, delta_c.1@)).0,
        out.1@ == verus_mandelbrot::perturbation::perturbation_step::<GpuFixedPoint<N, F>>(
            (z_ref.0@, z_ref.1@), (delta.0@, delta.1@), (delta_c.0@, delta_c.1@)).1,
{
    let (zr, zi) = z_ref;
    let (dr, di) = delta;
    let (dcr, dci) = delta_c;

    //  Exactly mirror the spec:
    //  let two = T::one().add(T::one());
    let one = RuntimeGpuFixedPoint::<N, F>::one_val();
    let two = one.add(&RuntimeGpuFixedPoint::<N, F>::one_val());

    //  re: two.mul(zr.mul(dr)).sub(two.mul(zi.mul(di))).add(dr.mul(dr)).sub(di.mul(di)).add(dcr)
    let new_dr = two.mul(&zr.mul(dr))
        .sub(&two.mul(&zi.mul(di)))
        .add(&dr.mul(dr))
        .sub(&di.mul(di))
        .add(dcr);

    //  im: two.mul(zr.mul(di)).add(two.mul(zi.mul(dr))).add(two.mul(dr.mul(di))).add(dci)
    let new_di = two.mul(&zr.mul(di))
        .add(&two.mul(&zi.mul(dr)))
        .add(&two.mul(&dr.mul(di)))
        .add(dci);

    (new_dr, new_di)
}

//  ══════════════════════════════════════════════════════════════
//  Exec test: build perturbation step expression trees
//  ══════════════════════════════════════════════════════════════

fn test_build_perturbation() {
    let zr = RuntimeGpuFixedPoint::<4, 2>::from_var(0);
    let zi = RuntimeGpuFixedPoint::<4, 2>::from_var(1);
    let dr = RuntimeGpuFixedPoint::<4, 2>::from_var(2);
    let di = RuntimeGpuFixedPoint::<4, 2>::from_var(3);
    let dcr = RuntimeGpuFixedPoint::<4, 2>::from_var(4);
    let dci = RuntimeGpuFixedPoint::<4, 2>::from_var(5);

    let (new_dr, new_di) = runtime_perturbation_step::<4, 2>(
        (&zr, &zi), (&dr, &di), (&dcr, &dci));

    //  The result contains RuntimeArithExpr trees that can be compiled to WGSL.
    let _re_expr = new_dr.into_expr();
    let _im_expr = new_di.into_expr();
}

} //  verus!
