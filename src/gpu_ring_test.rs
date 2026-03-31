///  GpuFixedPoint: Ring over ArithExpr via polynomial normal form.
///
///  GpuFixedPoint<N, F> wraps an ArithExpr. Equivalence is defined by
///  converting to a canonical polynomial representation: a sorted list
///  of (coefficient, sorted-variable-tuple) pairs. Ring axioms follow
///  from properties of polynomial addition and multiplication.

use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_cutedsl::arith_expr::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  Polynomial normal form
//  ══════════════════════════════════════════════════════════════
//
//  A term is (coeff: int, vars: Seq<nat>) where vars is sorted.
//  E.g., 3·x₁·x₂² = (3, [1, 2, 2]).
//
//  A polynomial is Seq<(int, Seq<nat>)>:
//    • sorted by vars (lexicographic via vars_lt)
//    • no duplicate var-tuples
//    • no zero coefficients
//  The empty seq is the zero polynomial.

///  Lexicographic less-than on sorted variable tuples.
pub open spec fn vars_lt(a: Seq<nat>, b: Seq<nat>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        b.len() > 0
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        vars_lt(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

///  vars_lt is asymmetric: a < b implies !(b < a).
proof fn lemma_vars_lt_asymm(a: Seq<nat>, b: Seq<nat>)
    requires vars_lt(a, b),
    ensures !vars_lt(b, a),
    decreases a.len(),
{
    if a.len() == 0 {
        // a empty, b non-empty → vars_lt(b, a) = false (b non-empty, a empty)
    } else {
        // Both non-empty (b must be non-empty since vars_lt(a, b) = false when b empty)
        if a[0] != b[0] {
            // a[0] < b[0], so b[0] > a[0] → vars_lt(b, a) checks b[0] < a[0] → false
        } else {
            // a[0] == b[0], recurse
            lemma_vars_lt_asymm(
                a.subrange(1, a.len() as int),
                b.subrange(1, b.len() as int),
            );
        }
    }
}

///  vars_lt trichotomy: exactly one of a < b, a =~= b, b < a.
///  If a and b are not extensionally equal and a is not less than b, then b < a.
proof fn lemma_vars_lt_trichotomy(a: Seq<nat>, b: Seq<nat>)
    requires !(a =~= b), !vars_lt(a, b),
    ensures vars_lt(b, a),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        // vars_lt(a, b) = (b.len() > 0). Since !vars_lt(a, b): b.len() == 0.
        // But then a =~= b (both empty). Contradiction with !(a =~= b).
        assert(b.len() == 0);
        assert(a =~= b);  // contradiction
    } else if b.len() == 0 {
        // vars_lt(b, a) = (a.len() > 0) = true. ✓
    } else {
        // Both non-empty
        if a[0] != b[0] {
            // !vars_lt(a, b) and a[0] != b[0] means !(a[0] < b[0]) i.e., a[0] > b[0]
            // So b[0] < a[0] → vars_lt(b, a) = true ✓
        } else {
            // a[0] == b[0]
            // vars_lt(a, b) = vars_lt(a_tail, b_tail). !vars_lt(a, b) → !vars_lt(a_tail, b_tail).
            // !(a =~= b): since a[0] == b[0], a =~= b iff a_tail =~= b_tail.
            // So !(a_tail =~= b_tail).
            let at = a.subrange(1, a.len() as int);
            let bt = b.subrange(1, b.len() as int);
            assert(a =~= seq![a[0]] + at);
            assert(b =~= seq![b[0]] + bt);
            // Need: !(at =~= bt)
            // If at =~= bt, then a =~= b (since a[0] == b[0]). Contradiction.
            if at =~= bt {
                assert(a =~= b);  // contradiction
            }
            lemma_vars_lt_trichotomy(at, bt);
        }
    }
}

///  vars_lt is transitive.
proof fn lemma_vars_lt_trans(a: Seq<nat>, b: Seq<nat>, c: Seq<nat>)
    requires vars_lt(a, b), vars_lt(b, c),
    ensures vars_lt(a, c),
    decreases a.len(),
{
    if a.len() == 0 {
        // a is empty, c must be non-empty (since b non-empty and b < c)
        // Actually, a empty → vars_lt(a, b) = b.len() > 0. And vars_lt(b, c).
        // Need: vars_lt(a, c) = c.len() > 0.
        // Since b.len() > 0 and vars_lt(b, c): if b.len() > 0 and c.len() == 0, vars_lt(b,c) = false.
        // So c.len() > 0. ✓
    } else {
        // a non-empty, b non-empty (since vars_lt(a,b) with a non-empty requires b non-empty)
        // c non-empty (since vars_lt(b,c) with b non-empty requires c non-empty)
        if a[0] < b[0] {
            if b[0] < c[0] {
                // a[0] < b[0] < c[0] → a[0] < c[0] ✓
            } else if b[0] == c[0] {
                // a[0] < b[0] == c[0] → a[0] < c[0] ✓
            } else {
                // b[0] > c[0] but vars_lt(b,c) requires b[0] <= c[0]. Contradiction.
                // vars_lt(b, c) with b[0] != c[0] means b[0] < c[0]. Contradiction with b[0] > c[0].
            }
        } else {
            // a[0] == b[0] (since a[0] != b[0] → a[0] < b[0] by vars_lt definition)
            assert(a[0] == b[0]);
            if b[0] < c[0] {
                // a[0] == b[0] < c[0] → a[0] < c[0] ✓
            } else {
                assert(b[0] == c[0]);
                lemma_vars_lt_trans(
                    a.subrange(1, a.len() as int),
                    b.subrange(1, b.len() as int),
                    c.subrange(1, c.len() as int),
                );
            }
        }
    }
}

///  Merge two sorted variable tuples (for monomial multiplication).
pub open spec fn vars_merge(a: Seq<nat>, b: Seq<nat>) -> Seq<nat>
    decreases a.len() + b.len(),
{
    if a.len() == 0 { b }
    else if b.len() == 0 { a }
    else if a[0] <= b[0] {
        seq![a[0]] + vars_merge(a.subrange(1, a.len() as int), b)
    } else {
        seq![b[0]] + vars_merge(a, b.subrange(1, b.len() as int))
    }
}

///  Negate a polynomial (negate all coefficients).
pub open spec fn poly_neg(p: Seq<(int, Seq<nat>)>) -> Seq<(int, Seq<nat>)>
    decreases p.len(),
{
    if p.len() == 0 { seq![] }
    else {
        seq![(-p[0].0, p[0].1)] + poly_neg(p.subrange(1, p.len() as int))
    }
}

///  Add two sorted polynomials: merge, combine like terms, drop zeros.
pub open spec fn poly_add(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>,
) -> Seq<(int, Seq<nat>)>
    decreases p.len() + q.len(),
{
    if p.len() == 0 { q }
    else if q.len() == 0 { p }
    else if p[0].1 =~= q[0].1 {
        let c = p[0].0 + q[0].0;
        let rest = poly_add(
            p.subrange(1, p.len() as int),
            q.subrange(1, q.len() as int),
        );
        if c == 0int { rest } else { seq![(c, p[0].1)] + rest }
    } else if vars_lt(p[0].1, q[0].1) {
        seq![p[0]] + poly_add(p.subrange(1, p.len() as int), q)
    } else {
        seq![q[0]] + poly_add(p, q.subrange(1, q.len() as int))
    }
}

///  Insert a term into a sorted polynomial.
pub open spec fn poly_insert(
    c: int, v: Seq<nat>, p: Seq<(int, Seq<nat>)>,
) -> Seq<(int, Seq<nat>)>
    decreases p.len(),
{
    if c == 0int { p }
    else if p.len() == 0 { seq![(c, v)] }
    else if v =~= p[0].1 {
        let nc = c + p[0].0;
        if nc == 0int { p.subrange(1, p.len() as int) }
        else { seq![(nc, v)] + p.subrange(1, p.len() as int) }
    } else if vars_lt(v, p[0].1) {
        seq![(c, v)] + p
    } else {
        seq![p[0]] + poly_insert(c, v, p.subrange(1, p.len() as int))
    }
}

///  Multiply a single monomial (c, vars) by a polynomial.
pub open spec fn mono_mul_poly(
    c: int, vars: Seq<nat>, q: Seq<(int, Seq<nat>)>,
) -> Seq<(int, Seq<nat>)>
    decreases q.len(),
{
    if c == 0int || q.len() == 0 { seq![] }
    else {
        let nc = c * q[0].0;
        let nv = vars_merge(vars, q[0].1);
        let rest = mono_mul_poly(c, vars, q.subrange(1, q.len() as int));
        poly_insert(nc, nv, rest)
    }
}

///  Multiply two polynomials.
pub open spec fn poly_mul(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>,
) -> Seq<(int, Seq<nat>)>
    decreases p.len(),
{
    if p.len() == 0 { seq![] }
    else {
        poly_add(
            mono_mul_poly(p[0].0, p[0].1, q),
            poly_mul(p.subrange(1, p.len() as int), q),
        )
    }
}

///  Convert ArithExpr to polynomial normal form.
///  Only handles Ring fragment (Const, Var, Add, Sub, Mul).
pub open spec fn arith_to_poly(e: &ArithExpr) -> Seq<(int, Seq<nat>)>
    decreases e,
{
    match e {
        ArithExpr::Const(c) => {
            if *c == 0int { seq![] }
            else { seq![(*c, Seq::<nat>::empty())] }
        },
        ArithExpr::Var(n) => seq![(1int, seq![*n])],
        ArithExpr::Add(a, b) => poly_add(arith_to_poly(a), arith_to_poly(b)),
        ArithExpr::Sub(a, b) => poly_add(arith_to_poly(a), poly_neg(arith_to_poly(b))),
        ArithExpr::Mul(a, b) => poly_mul(arith_to_poly(a), arith_to_poly(b)),
        _ => seq![],
    }
}

//  ══════════════════════════════════════════════════════════════
//  Polynomial lemmas — addition
//  ══════════════════════════════════════════════════════════════

proof fn lemma_poly_neg_len(p: Seq<(int, Seq<nat>)>)
    ensures poly_neg(p).len() == p.len(),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_poly_neg_len(p.subrange(1, p.len() as int));
    }
}

proof fn lemma_poly_neg_tail(p: Seq<(int, Seq<nat>)>)
    requires p.len() > 0,
    ensures
        poly_neg(p).subrange(1, poly_neg(p).len() as int)
            =~= poly_neg(p.subrange(1, p.len() as int)),
    decreases p.len(),
{
    lemma_poly_neg_len(p);
}

///  poly_add is commutative.
proof fn lemma_poly_add_comm(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>,
)
    ensures poly_add(p, q) =~= poly_add(q, p),
    decreases p.len() + q.len(),
{
    if p.len() == 0 {
    } else if q.len() == 0 {
    } else if p[0].1 =~= q[0].1 {
        lemma_poly_add_comm(
            p.subrange(1, p.len() as int),
            q.subrange(1, q.len() as int),
        );
    } else if vars_lt(p[0].1, q[0].1) {
        //  poly_add(q, p): q[0].1 != p[0].1, !vars_lt(q[0].1, p[0].1)
        //  → else branch: seq![p[0]] + poly_add(q, p_tail)
        lemma_vars_lt_asymm(p[0].1, q[0].1);
        lemma_poly_add_comm(p.subrange(1, p.len() as int), q);
    } else {
        //  !vars_lt(p[0].1, q[0].1) and !(p[0].1 =~= q[0].1)
        //  → vars_lt(q[0].1, p[0].1) by trichotomy
        lemma_vars_lt_trichotomy(p[0].1, q[0].1);
        lemma_poly_add_comm(p, q.subrange(1, q.len() as int));
    }
}

///  Well-formed polynomial: sorted by vars, no zero coefficients, no duplicate var-tuples.
pub open spec fn poly_wf(p: Seq<(int, Seq<nat>)>) -> bool {
    (forall |i: int| 0 <= i < p.len() ==> p[i].0 != 0int)
    && (forall |i: int, j: int| 0 <= i < j < p.len() ==> vars_lt(p[i].1, p[j].1))
}

///  All terms in p have vars strictly greater than v.
pub open spec fn poly_gt(p: Seq<(int, Seq<nat>)>, v: Seq<nat>) -> bool {
    forall |i: int| 0 <= i < p.len() ==> vars_lt(v, p[i].1)
}

///  poly_wf implies poly_gt for the tail.
proof fn lemma_wf_tail_gt(p: Seq<(int, Seq<nat>)>)
    requires p.len() > 0, poly_wf(p),
    ensures poly_gt(p.subrange(1, p.len() as int), p[0].1),
{
    let pt = p.subrange(1, p.len() as int);
    assert forall |i: int| 0 <= i < pt.len() implies vars_lt(p[0].1, pt[i].1) by {
        assert(pt[i] == p[i + 1]);
    }
}

///  poly_add preserves poly_gt.
proof fn lemma_poly_add_gt(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>, v: Seq<nat>,
)
    requires poly_gt(p, v), poly_gt(q, v),
    ensures poly_gt(poly_add(p, q), v),
    decreases p.len() + q.len(),
{
    if p.len() == 0 || q.len() == 0 { return; }
    if p[0].1 =~= q[0].1 {
        lemma_poly_add_gt(
            p.subrange(1, p.len() as int),
            q.subrange(1, q.len() as int),
            v,
        );
        let c = p[0].0 + q[0].0;
        if c != 0int {
            let result = seq![(c, p[0].1)] + poly_add(
                p.subrange(1, p.len() as int),
                q.subrange(1, q.len() as int),
            );
            assert(vars_lt(v, result[0].1));
        }
    } else if vars_lt(p[0].1, q[0].1) {
        lemma_poly_add_gt(p.subrange(1, p.len() as int), q, v);
    } else {
        lemma_poly_add_gt(p, q.subrange(1, q.len() as int), v);
    }
}

///  If poly_gt(X, v), then poly_add(X, [(r, v)] + rt) = [(r, v)] + poly_add(X, rt)
///  when r != 0 (the head at v comes first because X starts after v).
///  If poly_gt(y, v) and c != 0, poly_add([(c,v)] + rest, y) = [(c,v)] + poly_add(rest, y).
proof fn lemma_poly_add_head_lt_left(
    c: int, v: Seq<nat>, rest: Seq<(int, Seq<nat>)>,
    y: Seq<(int, Seq<nat>)>,
)
    requires c != 0int, poly_gt(y, v),
    ensures
        poly_add(seq![(c, v)] + rest, y)
            =~= seq![(c, v)] + poly_add(rest, y),
{
    let p = seq![(c, v)] + rest;
    assert(p[0] == (c, v));
    if y.len() == 0 { return; }
    assert(vars_lt(v, y[0].1));
    lemma_vars_lt_asymm(v, y[0].1);
    if v =~= y[0].1 {}  // contradicts vars_lt
    assert(!(p[0].1 =~= y[0].1));
    assert(vars_lt(p[0].1, y[0].1));
    assert(p.subrange(1, p.len() as int) =~= rest);
}

///  If all terms in X have vars > v, then adding [(r0, v)] + rt puts (r0, v) first.
proof fn lemma_poly_add_head_lt(
    x: Seq<(int, Seq<nat>)>, r0: int, v: Seq<nat>,
    rt: Seq<(int, Seq<nat>)>,
)
    requires poly_gt(x, v), r0 != 0int,
    ensures
        poly_add(x, seq![(r0, v)] + rt)
            =~= seq![(r0, v)] + poly_add(x, rt),
    decreases x.len(),
{
    let q = seq![(r0, v)] + rt;
    assert(q[0] == (r0, v));
    assert(q[0].1 =~= v);
    if x.len() == 0 { return; }
    //  x[0].1 > v → not equal, and not less than v
    assert(vars_lt(v, x[0].1));
    lemma_vars_lt_asymm(v, x[0].1);
    //  x[0].1 != v (irreflexivity from asymmetry of strict order)
    if x[0].1 =~= v {
        //  Would mean vars_lt(v, v) — impossible
    }
    assert(!(x[0].1 =~= v));
    assert(!vars_lt(x[0].1, v));
    //  poly_add(x, q): else branch → seq![q[0]] + poly_add(x, q.subrange(1, ...))
    assert(q.subrange(1, q.len() as int) =~= rt);
}

///  Unfold poly_add when heads match and don't cancel.
proof fn lemma_poly_add_unfold_combine(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    requires p.len() > 0, q.len() > 0, p[0].1 =~= q[0].1,
        p[0].0 + q[0].0 != 0int,
    ensures poly_add(p, q) =~=
        seq![(p[0].0 + q[0].0, p[0].1)] + poly_add(
            p.subrange(1, p.len() as int),
            q.subrange(1, q.len() as int),
        ),
{}

///  Unfold poly_add when heads match and DO cancel.
proof fn lemma_poly_add_unfold_cancel(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    requires p.len() > 0, q.len() > 0, p[0].1 =~= q[0].1,
        p[0].0 + q[0].0 == 0int,
    ensures poly_add(p, q) =~= poly_add(
        p.subrange(1, p.len() as int),
        q.subrange(1, q.len() as int),
    ),
{}

///  Helper: associativity when all three heads have the same vars.
proof fn lemma_poly_add_assoc_same(
    p0: int, q0: int, r0: int, v: Seq<nat>,
    pt: Seq<(int, Seq<nat>)>,
    qt: Seq<(int, Seq<nat>)>,
    rt: Seq<(int, Seq<nat>)>,
)
    requires
        p0 != 0int, q0 != 0int, r0 != 0int,
        poly_gt(pt, v), poly_gt(qt, v), poly_gt(rt, v),
        poly_add(poly_add(pt, qt), rt) =~= poly_add(pt, poly_add(qt, rt)),
    ensures ({
        let p = seq![(p0, v)] + pt;
        let q = seq![(q0, v)] + qt;
        let r = seq![(r0, v)] + rt;
        poly_add(poly_add(p, q), r) =~= poly_add(p, poly_add(q, r))
    }),
{
    let p = seq![(p0, v)] + pt;
    let q = seq![(q0, v)] + qt;
    let r = seq![(r0, v)] + rt;
    let c_pq = p0 + q0;
    let c_qr = q0 + r0;
    let c_all = p0 + q0 + r0;

    //  Unfold poly_add(p, q): both heads at v → combine
    assert(p[0] == (p0, v));
    assert(q[0] == (q0, v));
    assert(p[0].1 =~= q[0].1);
    assert(p.subrange(1, p.len() as int) =~= pt);
    assert(q.subrange(1, q.len() as int) =~= qt);

    //  Unfold poly_add(q, r): both heads at v → combine
    assert(r[0] == (r0, v));
    assert(q[0].1 =~= r[0].1);
    assert(r.subrange(1, r.len() as int) =~= rt);

    let pq_tail = poly_add(pt, qt);
    let qr_tail = poly_add(qt, rt);

    if c_pq != 0int && c_qr != 0int {
        //  poly_add(p,q) = [(c_pq, v)] + pq_tail
        //  poly_add(q,r) = [(c_qr, v)] + qr_tail
        let pq = seq![(c_pq, v)] + pq_tail;
        let qr = seq![(c_qr, v)] + qr_tail;
        //  LHS: poly_add(pq, r): (c_pq,v) vs (r0,v) → combine c_all
        assert(pq[0] == (c_pq, v));
        assert(pq[0].1 =~= r[0].1);
        assert(pq.subrange(1, pq.len() as int) =~= pq_tail);
        //  RHS: poly_add(p, qr): (p0,v) vs (c_qr,v) → combine c_all
        assert(p[0].1 =~= qr[0].1);
        assert(qr.subrange(1, qr.len() as int) =~= qr_tail);
    } else if c_pq == 0int && c_qr != 0int {
        //  poly_add(p,q) = pq_tail (cancelled)
        //  LHS: poly_add(pq_tail, r), pq_tail all > v → r[0] first
        lemma_poly_add_gt(pt, qt, v);
        lemma_poly_add_head_lt(pq_tail, r0, v, rt);
        //  poly_add(q,r) = [(c_qr, v)] + qr_tail
        let qr = seq![(c_qr, v)] + qr_tail;
        //  RHS: poly_add(p, qr): (p0,v) vs (c_qr,v) → combine p0+c_qr = c_all = r0
        assert(qr[0] == (c_qr, v));
        assert(p[0].1 =~= qr[0].1);
        assert(qr.subrange(1, qr.len() as int) =~= qr_tail);
        assert(c_all == r0);
    } else if c_pq != 0int && c_qr == 0int {
        //  poly_add(q,r) = qr_tail (cancelled)
        //  RHS: poly_add(p, qr_tail), qr_tail all > v → p[0] first
        lemma_poly_add_gt(qt, rt, v);
        lemma_poly_add_head_lt_left(p0, v, pt, qr_tail);
        //  poly_add(p,q) = [(c_pq, v)] + pq_tail
        let pq = seq![(c_pq, v)] + pq_tail;
        //  LHS: poly_add(pq, r): (c_pq,v) vs (r0,v) → combine c_pq+r0 = c_all = p0
        assert(pq[0] == (c_pq, v));
        assert(pq[0].1 =~= r[0].1);
        assert(pq.subrange(1, pq.len() as int) =~= pq_tail);
        assert(c_all == p0);
    } else {
        //  Both cancel: c_pq==0, c_qr==0, so p0=-q0, r0=-q0=p0, c_all=p0=r0 != 0
        assert(c_all == p0);
        assert(c_all == r0);
        //  LHS: poly_add(pq_tail, r), pq_tail all > v → r[0] first
        lemma_poly_add_gt(pt, qt, v);
        lemma_poly_add_head_lt(pq_tail, r0, v, rt);
        //  RHS: poly_add(p, qr_tail), qr_tail all > v → p[0] first
        lemma_poly_add_gt(qt, rt, v);
        lemma_poly_add_head_lt_left(p0, v, pt, qr_tail);
    }
}

///  Extract the coefficient at variable tuple v from a well-formed polynomial.
///  Returns 0 if v is not present, otherwise returns the unique coefficient.
pub open spec fn poly_coeff(p: Seq<(int, Seq<nat>)>, v: Seq<nat>) -> int
    decreases p.len(),
{
    if p.len() == 0 { 0int }
    else if p[0].1 =~= v { p[0].0 }
    else { poly_coeff(p.subrange(1, p.len() as int), v) }
}

///  poly_coeff distributes over poly_add (requires poly_wf).
proof fn lemma_poly_add_coeff_wf(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
    v: Seq<nat>,
)
    requires poly_wf(p), poly_wf(q),
    ensures poly_coeff(poly_add(p, q), v) == poly_coeff(p, v) + poly_coeff(q, v),
    decreases p.len() + q.len(),
{
    if p.len() == 0 {
        //  poly_add(p, q) = q, poly_coeff(p, v) = 0
        assert(poly_coeff(p, v) == 0int);
        assert(poly_add(p, q) =~= q);
    } else if q.len() == 0 {
        //  poly_add(p, q) = p, poly_coeff(q, v) = 0
        assert(poly_coeff(q, v) == 0int);
        assert(poly_add(p, q) =~= p);
    } else if p[0].1 =~= q[0].1 {
        let c = p[0].0 + q[0].0;
        let pt = p.subrange(1, p.len() as int);
        let qt = q.subrange(1, q.len() as int);
        assert(poly_wf(pt)) by {
            assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
            assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
                assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
            }
        }
        assert(poly_wf(qt)) by {
            assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by { assert(qt[i] == q[i+1]); }
            assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
                assert(qt[i] == q[i+1]); assert(qt[j] == q[j+1]);
            }
        }
        lemma_wf_tail_gt(p);
        lemma_wf_tail_gt(q);
        //  IH for tails
        lemma_poly_add_coeff_wf(pt, qt, v);
        //  poly_coeff(poly_add(pt,qt), v) == poly_coeff(pt, v) + poly_coeff(qt, v)  [IH]
        if p[0].1 =~= v {
            //  poly_coeff(p, v) = p[0].0, poly_coeff(q, v) = q[0].0
            assert(poly_coeff(p, v) == p[0].0);
            assert(poly_coeff(q, v) == q[0].0);
            //  pt and qt don't contain v (sorted after p[0].1 = v)
            assert(poly_coeff(pt, v) == 0int) by { lemma_poly_coeff_gt_zero(pt, v); }
            assert(poly_coeff(qt, v) == 0int) by { lemma_poly_coeff_gt_zero(qt, v); }
            //  poly_coeff(poly_add(pt,qt), v) == 0
            assert(poly_coeff(poly_add(pt, qt), v) == 0int);
            if c == 0int {
                //  poly_add(p,q) = poly_add(pt,qt), poly_coeff = 0 = p[0].0 + q[0].0 ✓
                assert(poly_add(p, q) =~= poly_add(pt, qt));
                assert(poly_coeff(poly_add(p, q), v) == 0int);
                assert(poly_coeff(p, v) + poly_coeff(q, v) == 0int);
            } else {
                //  poly_add(p,q) = seq![(c,v)] + poly_add(pt,qt)
                //  poly_coeff of that at v = c ✓
                let result = seq![(c, p[0].1)] + poly_add(pt, qt);
                assert(poly_add(p, q) =~= result);
                assert(result[0].1 =~= v);
                assert(poly_coeff(result, v) == c);
                assert(poly_coeff(p, v) + poly_coeff(q, v) == c);
            }
        } else {
            //  p[0].1 ≠ v: poly_coeff(p, v) = poly_coeff(pt, v), poly_coeff(q, v) = poly_coeff(qt, v)
            assert(poly_coeff(p, v) == poly_coeff(pt, v));
            assert(poly_coeff(q, v) == poly_coeff(qt, v));
            if c == 0int {
                //  poly_add(p,q) = poly_add(pt,qt)
                assert(poly_add(p, q) =~= poly_add(pt, qt));
                //  poly_coeff(poly_add(p,q), v) = poly_coeff(poly_add(pt,qt), v) = poly_coeff(pt,v) + poly_coeff(qt,v) ✓
            } else {
                //  poly_add(p,q) = seq![(c, p[0].1)] + poly_add(pt,qt), p[0].1 ≠ v
                let result = seq![(c, p[0].1)] + poly_add(pt, qt);
                assert(poly_add(p, q) =~= result);
                assert(!(result[0].1 =~= v));
                assert(result.subrange(1, result.len() as int) =~= poly_add(pt, qt));
            }
        }
    } else if vars_lt(p[0].1, q[0].1) {
        let pt = p.subrange(1, p.len() as int);
        assert(poly_wf(pt)) by {
            assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
            assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
                assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
            }
        }
        lemma_vars_lt_asymm(p[0].1, q[0].1);
        //  poly_add(p,q) = seq![p[0]] + poly_add(pt, q)
        let result = seq![p[0]] + poly_add(pt, q);
        assert(poly_add(p, q) =~= result);
        //  IH
        lemma_poly_add_coeff_wf(pt, q, v);
        if p[0].1 =~= v {
            //  head matches v: poly_coeff(result, v) = p[0].0
            assert(result[0].1 =~= v);
            assert(poly_coeff(result, v) == p[0].0);
            assert(poly_coeff(p, v) == p[0].0);
            //  poly_coeff(q, v) = 0 (q[0].1 > v, all q > v)
            assert(poly_coeff(q, v) == 0int) by {
                lemma_poly_gt_from_head(q, v);
                lemma_poly_coeff_gt_zero(q, v);
            }
            //  poly_coeff(pt, v) = 0 (pt has all vars > p[0].1 = v)
            assert(poly_coeff(pt, v) == 0int) by {
                lemma_wf_tail_gt(p);
                assert(poly_gt(pt, v)) by {
                    assert forall |i: int| 0 <= i < pt.len() implies vars_lt(v, pt[i].1) by {
                        assert(vars_lt(p[0].1, pt[i].1));
                    }
                }
                lemma_poly_coeff_gt_zero(pt, v);
            }
            //  poly_coeff(poly_add(pt,q), v) = 0 + 0 = 0
            assert(poly_coeff(poly_add(pt, q), v) == 0int);
            //  poly_coeff(p, v) + poly_coeff(q, v) = p[0].0 + 0 = p[0].0 ✓
        } else {
            //  head p[0].1 ≠ v
            assert(!(result[0].1 =~= v));
            assert(result.subrange(1, result.len() as int) =~= poly_add(pt, q));
            assert(poly_coeff(p, v) == poly_coeff(pt, v));
            //  poly_coeff(result, v) = poly_coeff(pt, v) + poly_coeff(q, v) = poly_coeff(p, v) + poly_coeff(q, v) ✓
        }
    } else {
        //  vars_lt(q[0].1, p[0].1)
        let qt = q.subrange(1, q.len() as int);
        assert(poly_wf(qt)) by {
            assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by { assert(qt[i] == q[i+1]); }
            assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
                assert(qt[i] == q[i+1]); assert(qt[j] == q[j+1]);
            }
        }
        lemma_vars_lt_trichotomy(p[0].1, q[0].1);
        lemma_vars_lt_asymm(q[0].1, p[0].1);
        //  poly_add(p,q) = seq![q[0]] + poly_add(p, qt)
        let result = seq![q[0]] + poly_add(p, qt);
        assert(poly_add(p, q) =~= result);
        //  IH
        lemma_poly_add_coeff_wf(p, qt, v);
        if q[0].1 =~= v {
            //  head matches v: poly_coeff(result, v) = q[0].0
            assert(result[0].1 =~= v);
            assert(poly_coeff(result, v) == q[0].0);
            assert(poly_coeff(q, v) == q[0].0);
            //  poly_coeff(p, v) = 0 (p[0].1 > v)
            assert(poly_coeff(p, v) == 0int) by {
                lemma_poly_gt_from_head(p, v);
                lemma_poly_coeff_gt_zero(p, v);
            }
            //  poly_coeff(qt, v) = 0 (qt has all vars > q[0].1 = v)
            assert(poly_coeff(qt, v) == 0int) by {
                lemma_wf_tail_gt(q);
                assert(poly_gt(qt, v)) by {
                    assert forall |i: int| 0 <= i < qt.len() implies vars_lt(v, qt[i].1) by {
                        assert(vars_lt(q[0].1, qt[i].1));
                    }
                }
                lemma_poly_coeff_gt_zero(qt, v);
            }
            //  poly_coeff(poly_add(p,qt), v) = 0 + 0 = 0
            assert(poly_coeff(poly_add(p, qt), v) == 0int);
            //  poly_coeff(p, v) + poly_coeff(q, v) = 0 + q[0].0 = q[0].0 ✓
        } else {
            //  head q[0].1 ≠ v
            assert(!(result[0].1 =~= v));
            assert(result.subrange(1, result.len() as int) =~= poly_add(p, qt));
            assert(poly_coeff(q, v) == poly_coeff(qt, v));
            //  poly_coeff(result, v) = poly_coeff(p, v) + poly_coeff(qt, v) = poly_coeff(p, v) + poly_coeff(q, v) ✓
        }
    }
}

///  In a wf polynomial with head > v, all entries are > v.
proof fn lemma_poly_gt_from_head(p: Seq<(int, Seq<nat>)>, v: Seq<nat>)
    requires p.len() > 0, poly_wf(p), vars_lt(v, p[0].1),
    ensures poly_gt(p, v),
{
    assert forall |i: int| 0 <= i < p.len() implies vars_lt(v, p[i].1) by {
        if i == 0 {
            // direct
        } else {
            // p[0].1 < p[i].1 by wf (sorted), and v < p[0].1, so v < p[i].1 by transitivity
            assert(vars_lt(p[0].1, p[i].1));
            lemma_vars_lt_trans(v, p[0].1, p[i].1);
        }
    }
}

///  If poly_gt(p, v) then poly_coeff(p, v) = 0.
proof fn lemma_poly_coeff_gt_zero(p: Seq<(int, Seq<nat>)>, v: Seq<nat>)
    requires poly_gt(p, v),
    ensures poly_coeff(p, v) == 0int,
    decreases p.len(),
{
    if p.len() == 0 {
        assert(poly_coeff(p, v) == 0int);
    } else {
        //  p[0].1 > v → p[0].1 ≠ v (since vars_lt is strict)
        assert(vars_lt(v, p[0].1));
        lemma_vars_lt_asymm(v, p[0].1);
        assert(!(p[0].1 =~= v)) by {
            //  If p[0].1 =~= v, then vars_lt(v, v) — impossible (asymm with self)
            if p[0].1 =~= v {
                // vars_lt(v, p[0].1) = vars_lt(v, v), which would require vars_lt(v,v)
                // But vars_lt is asymmetric: vars_lt(v,v) → !vars_lt(v,v). Contradiction.
                assert(vars_lt(v, v));
                lemma_vars_lt_asymm(v, v);
            }
        }
        //  poly_coeff(p, v) = poly_coeff(p.subrange(1,...), v)
        let pt = p.subrange(1, p.len() as int);
        assert forall |i: int| 0 <= i < pt.len() implies vars_lt(v, pt[i].1) by {
            assert(pt[i] == p[i + 1]);
        }
        lemma_poly_coeff_gt_zero(pt, v);
    }
}

///  poly_add preserves poly_wf.
proof fn lemma_poly_add_wf(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    requires poly_wf(p), poly_wf(q),
    ensures poly_wf(poly_add(p, q)),
    decreases p.len() + q.len(),
{
    if p.len() == 0 || q.len() == 0 { return; }

    let pt = p.subrange(1, p.len() as int);
    let qt = q.subrange(1, q.len() as int);

    //  Well-formedness of tails
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by {
            assert(pt[i] == p[i + 1]);
        }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i + 1]); assert(pt[j] == p[j + 1]);
        }
    }
    assert(poly_wf(qt)) by {
        assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by {
            assert(qt[i] == q[i + 1]);
        }
        assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
            assert(qt[i] == q[i + 1]); assert(qt[j] == q[j + 1]);
        }
    }

    lemma_wf_tail_gt(p);
    lemma_wf_tail_gt(q);

    if p[0].1 =~= q[0].1 {
        let c = p[0].0 + q[0].0;
        lemma_poly_add_wf(pt, qt);
        let tail_wf = poly_add(pt, qt);
        if c == 0int {
            //  result = poly_add(pt, qt), which is wf by IH ✓
        } else {
            //  result = [(c, p[0].1)] + poly_add(pt, qt)
            //  Need: c != 0 ✓
            //  Need: all terms in poly_add(pt,qt) have vars > p[0].1
            lemma_poly_add_gt(pt, qt, p[0].1);
            let result = poly_add(p, q);
            assert(result =~= seq![(c, p[0].1)] + poly_add(pt, qt));
            assert forall |i: int| 0 <= i < result.len() implies result[i].0 != 0int by {
                if i == 0 {
                    assert(result[0] == (c, p[0].1));
                } else {
                    let tail = poly_add(pt, qt);
                    assert(result[i] == tail[i - 1]);
                    assert(tail[i - 1].0 != 0int);
                }
            }
            assert forall |i: int, j: int| 0 <= i < j < result.len() implies vars_lt(result[i].1, result[j].1) by {
                if i == 0 {
                    let tail = poly_add(pt, qt);
                    assert(result[0].1 =~= p[0].1);
                    assert(result[j] == tail[j - 1]);
                    assert(vars_lt(p[0].1, tail[j - 1].1));
                } else {
                    let tail = poly_add(pt, qt);
                    assert(result[i] == tail[i - 1]);
                    assert(result[j] == tail[j - 1]);
                    assert(vars_lt(tail[i - 1].1, tail[j - 1].1));
                }
            }
        }
    } else if vars_lt(p[0].1, q[0].1) {
        lemma_vars_lt_asymm(p[0].1, q[0].1);
        lemma_poly_add_wf(pt, q);
        //  result = seq![p[0]] + poly_add(pt, q)
        let result = poly_add(p, q);
        assert(result =~= seq![p[0]] + poly_add(pt, q));
        //  poly_gt(pt, p[0].1) from wf_tail_gt
        //  poly_gt(q, p[0].1) because vars_lt(p[0].1, q[0].1) and q is wf
        lemma_poly_gt_from_head(q, p[0].1);
        lemma_poly_add_gt(pt, q, p[0].1);
        assert forall |i: int| 0 <= i < result.len() implies result[i].0 != 0int by {
            if i == 0 {
                assert(result[0] == p[0]);
                assert(p[0].0 != 0int);
            } else {
                let tail = poly_add(pt, q);
                assert(result[i] == tail[i - 1]);
            }
        }
        assert forall |i: int, j: int| 0 <= i < j < result.len() implies vars_lt(result[i].1, result[j].1) by {
            if i == 0 {
                let tail = poly_add(pt, q);
                assert(result[j] == tail[j - 1]);
                assert(vars_lt(p[0].1, tail[j - 1].1));
            } else {
                let tail = poly_add(pt, q);
                assert(result[i] == tail[i - 1]);
                assert(result[j] == tail[j - 1]);
            }
        }
    } else {
        //  vars_lt(q[0].1, p[0].1)
        lemma_vars_lt_trichotomy(p[0].1, q[0].1);
        lemma_vars_lt_asymm(q[0].1, p[0].1);
        lemma_poly_add_wf(p, qt);
        //  result = seq![q[0]] + poly_add(p, qt)
        let result = poly_add(p, q);
        assert(result =~= seq![q[0]] + poly_add(p, qt));
        //  poly_gt(p, q[0].1) because vars_lt(q[0].1, p[0].1) and p is wf
        lemma_poly_gt_from_head(p, q[0].1);
        //  poly_gt(qt, q[0].1) from wf_tail_gt
        lemma_poly_add_gt(p, qt, q[0].1);
        assert forall |i: int| 0 <= i < result.len() implies result[i].0 != 0int by {
            if i == 0 {
                assert(result[0] == q[0]);
                assert(q[0].0 != 0int);
            } else {
                let tail = poly_add(p, qt);
                assert(result[i] == tail[i - 1]);
            }
        }
        assert forall |i: int, j: int| 0 <= i < j < result.len() implies vars_lt(result[i].1, result[j].1) by {
            if i == 0 {
                let tail = poly_add(p, qt);
                assert(result[j] == tail[j - 1]);
                assert(vars_lt(q[0].1, tail[j - 1].1));
            } else {
                let tail = poly_add(p, qt);
                assert(result[i] == tail[i - 1]);
                assert(result[j] == tail[j - 1]);
            }
        }
    }
}

///  If p and q are both well-formed and have equal coefficients at every v, then p =~= q.
proof fn lemma_poly_wf_eq_from_coeff(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    requires
        poly_wf(p), poly_wf(q),
        forall |v: Seq<nat>| poly_coeff(p, v) == poly_coeff(q, v),
    ensures p =~= q,
    decreases p.len() + q.len(),
{
    if p.len() == 0 && q.len() == 0 {
        // Both empty ✓
    } else if p.len() == 0 {
        //  p is empty but q is non-empty.
        //  poly_coeff(q, q[0].1) = q[0].0 ≠ 0 (wf), but poly_coeff(p, q[0].1) = 0. Contradiction.
        assert(poly_coeff(q, q[0].1) == q[0].0);
        assert(poly_coeff(p, q[0].1) == 0int);
        //  By hypothesis: poly_coeff(p, q[0].1) == poly_coeff(q, q[0].1) → 0 == q[0].0
        assert(q[0].0 == 0int);
        //  But wf says q[0].0 != 0
        assert(q[0].0 != 0int);
        assert(false);
    } else if q.len() == 0 {
        assert(poly_coeff(p, p[0].1) == p[0].0);
        assert(poly_coeff(q, p[0].1) == 0int);
        assert(p[0].0 == 0int);
        assert(p[0].0 != 0int);
        assert(false);
    } else {
        //  Both non-empty.
        //  Claim: p[0].1 =~= q[0].1.
        //  Proof by contradiction: suppose p[0].1 ≠ q[0].1.
        //  Case p[0].1 < q[0].1: poly_coeff(q, p[0].1) = 0 (q is sorted, all terms ≥ q[0].1 > p[0].1)
        //    but poly_coeff(p, p[0].1) = p[0].0 ≠ 0. Contradiction.
        //  Case q[0].1 < p[0].1: symmetric.
        assert(p[0].1 =~= q[0].1) by {
            if !(p[0].1 =~= q[0].1) {
                if vars_lt(p[0].1, q[0].1) {
                    //  poly_coeff(q, p[0].1) = 0 (q[0].1 > p[0].1, all q entries ≥ q[0].1)
                    lemma_poly_coeff_lt_head(q, p[0].1);
                    //  poly_coeff(p, p[0].1) = p[0].0 ≠ 0 (by wf)
                    assert(poly_coeff(p, p[0].1) == p[0].0);
                    //  hypothesis: poly_coeff(p, p[0].1) == poly_coeff(q, p[0].1)
                    //  So p[0].0 == 0 — contradiction with wf
                    assert(p[0].0 != 0int);
                    assert(false);
                } else {
                    lemma_vars_lt_trichotomy(p[0].1, q[0].1);
                    //  vars_lt(q[0].1, p[0].1): poly_coeff(p, q[0].1) = 0
                    lemma_poly_coeff_lt_head(p, q[0].1);
                    assert(poly_coeff(q, q[0].1) == q[0].0);
                    assert(q[0].0 != 0int);
                    assert(false);
                }
            }
        }
        //  Now p[0].1 =~= q[0].1. So poly_coeff(p, p[0].1) = p[0].0, poly_coeff(q, q[0].1) = q[0].0.
        //  By hypothesis: p[0].0 == q[0].0.
        assert(poly_coeff(p, p[0].1) == p[0].0);
        assert(poly_coeff(q, p[0].1) == q[0].0);
        assert(p[0].0 == q[0].0);
        //  Now apply IH to tails.
        let pt = p.subrange(1, p.len() as int);
        let qt = q.subrange(1, q.len() as int);
        assert(poly_wf(pt)) by {
            assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by {
                assert(pt[i] == p[i + 1]);
            }
            assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
                assert(pt[i] == p[i + 1]); assert(pt[j] == p[j + 1]);
            }
        }
        assert(poly_wf(qt)) by {
            assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by {
                assert(qt[i] == q[i + 1]);
            }
            assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
                assert(qt[i] == q[i + 1]); assert(qt[j] == q[j + 1]);
            }
        }
        //  poly_coeff(pt, v) == poly_coeff(qt, v) for all v.
        assert forall |v: Seq<nat>| poly_coeff(pt, v) == poly_coeff(qt, v) by {
            //  For v = p[0].1: poly_coeff(pt, p[0].1) = 0 and poly_coeff(qt, q[0].1) = 0
            //    because pt has all vars > p[0].1 (by wf) and qt has all vars > q[0].1 = p[0].1.
            //  For v ≠ p[0].1: poly_coeff(p, v) = poly_coeff(pt, v) and poly_coeff(q, v) = poly_coeff(qt, v).
            lemma_wf_tail_gt(p);
            lemma_wf_tail_gt(q);
            if v =~= p[0].1 {
                assert(poly_coeff(pt, v) == 0int) by { lemma_poly_coeff_gt_zero(pt, v); }
                assert(poly_coeff(qt, v) == 0int) by { lemma_poly_coeff_gt_zero(qt, v); }
            } else {
                //  poly_coeff(p, v): p[0].1 ≠ v → = poly_coeff(pt, v)
                //  poly_coeff(q, v): q[0].1 = p[0].1 ≠ v → = poly_coeff(qt, v)
                assert(poly_coeff(p, v) == poly_coeff(pt, v));
                assert(poly_coeff(q, v) == poly_coeff(qt, v));
            }
        }
        lemma_poly_wf_eq_from_coeff(pt, qt);
        assert(pt =~= qt);
        assert(p[0].0 == q[0].0);
        assert(p[0].1 =~= q[0].1);
        assert(p[0] == q[0]);
        //  p = seq![p[0]] + pt =~= seq![q[0]] + qt = q
        assert(p =~= seq![p[0]] + pt);
        assert(q =~= seq![q[0]] + qt);
        assert(seq![p[0]] + pt =~= seq![q[0]] + qt);
    }
}

///  Helper: if v is strictly less than the head of a wf polynomial p, then poly_coeff(p, v) = 0.
proof fn lemma_poly_coeff_lt_head(p: Seq<(int, Seq<nat>)>, v: Seq<nat>)
    requires p.len() > 0, poly_wf(p), vars_lt(v, p[0].1),
    ensures poly_coeff(p, v) == 0int,
    decreases p.len(),
{
    //  p[0].1 > v → p[0].1 ≠ v → head doesn't match
    lemma_vars_lt_asymm(v, p[0].1);
    assert(!(p[0].1 =~= v)) by {
        if p[0].1 =~= v {
            assert(vars_lt(v, v));
            lemma_vars_lt_asymm(v, v);
        }
    }
    //  poly_coeff(p, v) = poly_coeff(pt, v) where pt = p.subrange(1,...)
    //  Need: poly_coeff(pt, v) = 0
    //  pt has all vars > p[0].1 > v, so poly_gt(pt, v) → poly_coeff = 0
    lemma_wf_tail_gt(p);
    let pt = p.subrange(1, p.len() as int);
    //  poly_gt(pt, p[0].1) and vars_lt(v, p[0].1), so vars_lt(v, pt[i].1) for all i by transitivity
    assert(poly_gt(pt, v)) by {
        assert forall |i: int| 0 <= i < pt.len() implies vars_lt(v, pt[i].1) by {
            assert(vars_lt(p[0].1, pt[i].1));
            lemma_vars_lt_trans(v, p[0].1, pt[i].1);
        }
    }
    lemma_poly_coeff_gt_zero(pt, v);
}

///  poly_add is associative (for well-formed polynomials).
///  Proof: use coefficient extraction as bridge.
///  Both poly_add(poly_add(p,q),r) and poly_add(p,poly_add(q,r)) are wf,
///  and for every v their coefficient is poly_coeff(p,v) + poly_coeff(q,v) + poly_coeff(r,v).
proof fn lemma_poly_add_assoc(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
    r: Seq<(int, Seq<nat>)>,
)
    requires poly_wf(p), poly_wf(q), poly_wf(r),
    ensures poly_add(poly_add(p, q), r) =~= poly_add(p, poly_add(q, r)),
{
    let lhs = poly_add(poly_add(p, q), r);
    let rhs = poly_add(p, poly_add(q, r));

    //  Both sides are well-formed.
    lemma_poly_add_wf(p, q);
    lemma_poly_add_wf(poly_add(p, q), r);
    lemma_poly_add_wf(q, r);
    lemma_poly_add_wf(p, poly_add(q, r));

    //  For every v, both sides have the same coefficient.
    assert forall |v: Seq<nat>| poly_coeff(lhs, v) == poly_coeff(rhs, v) by {
        lemma_poly_add_coeff_wf(p, q, v);
        lemma_poly_add_coeff_wf(poly_add(p, q), r, v);
        lemma_poly_add_coeff_wf(q, r, v);
        lemma_poly_add_coeff_wf(p, poly_add(q, r), v);
        // poly_coeff(lhs, v) = poly_coeff(p,v) + poly_coeff(q,v) + poly_coeff(r,v)
        // poly_coeff(rhs, v) = poly_coeff(p,v) + poly_coeff(q,v) + poly_coeff(r,v)
        // They're equal by integer arithmetic associativity.
    };

    //  By lemma_poly_wf_eq_from_coeff: lhs =~= rhs.
    lemma_poly_wf_eq_from_coeff(lhs, rhs);
}

///  poly_add(p, poly_neg(p)) == []
proof fn lemma_poly_add_inverse(p: Seq<(int, Seq<nat>)>)
    ensures poly_add(p, poly_neg(p)) =~= seq![],
    decreases p.len(),
{
    if p.len() > 0 {
        assert(poly_neg(p)[0] == (-p[0].0, p[0].1));
        assert(p[0].1 =~= poly_neg(p)[0].1);
        assert(p[0].0 + poly_neg(p)[0].0 == 0int);
        lemma_poly_neg_len(p);
        lemma_poly_neg_tail(p);
        lemma_poly_add_inverse(p.subrange(1, p.len() as int));
    }
}

//  ══════════════════════════════════════════════════════════════
//  poly_insert / mono_mul_poly / poly_mul preserve well-formedness
//  ══════════════════════════════════════════════════════════════

///  poly_insert preserves poly_wf (when inserting into a poly where all vars > some bound,
///  and v is also > that bound, the result stays well-formed).
///  Simpler statement: poly_insert into a wf poly gives wf result.
proof fn lemma_poly_insert_wf(c: int, v: Seq<nat>, p: Seq<(int, Seq<nat>)>)
    requires poly_wf(p),
    ensures poly_wf(poly_insert(c, v, p)),
    decreases p.len(),
{
    if c == 0int { return; }
    if p.len() == 0 {
        let r = seq![(c, v)];
        assert forall |i: int| 0 <= i < r.len() implies r[i].0 != 0int by {}
        assert forall |i: int, j: int| 0 <= i < j < r.len()
            implies vars_lt(r[i].1, r[j].1) by {}
        return;
    }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
        }
    }
    if v =~= p[0].1 {
        let nc = c + p[0].0;
        if nc == 0int {
            //  Result is pt, which is wf
        } else {
            //  Result is [(nc, v)] + pt
            let r = seq![(nc, v)] + pt;
            lemma_wf_tail_gt(p);
            assert forall |i: int| 0 <= i < r.len() implies r[i].0 != 0int by {
                if i == 0 {} else { assert(r[i] == pt[i-1]); }
            }
            assert forall |i: int, j: int| 0 <= i < j < r.len()
                implies vars_lt(r[i].1, r[j].1) by {
                if i == 0 {
                    assert(r[0].1 =~= v);
                    assert(v =~= p[0].1);
                    assert(r[j] == pt[j-1]);
                    assert(vars_lt(p[0].1, pt[j-1].1));
                } else {
                    assert(r[i] == pt[i-1]);
                    assert(r[j] == pt[j-1]);
                }
            }
        }
    } else if vars_lt(v, p[0].1) {
        //  Result is [(c, v)] + p
        let r = seq![(c, v)] + p;
        assert forall |i: int| 0 <= i < r.len() implies r[i].0 != 0int by {
            if i == 0 {} else { assert(r[i] == p[i-1]); }
        }
        assert forall |i: int, j: int| 0 <= i < j < r.len()
            implies vars_lt(r[i].1, r[j].1) by {
            if i == 0 && j == 1 {
                assert(r[0].1 =~= v);
                assert(r[1] == p[0]);
            } else if i == 0 {
                assert(r[j] == p[j-1]);
                lemma_vars_lt_trans(v, p[0].1, p[j-1].1);
            } else {
                assert(r[i] == p[i-1]);
                assert(r[j] == p[j-1]);
            }
        }
    } else {
        //  Result is [p[0]] + poly_insert(c, v, pt)
        lemma_vars_lt_trichotomy(v, p[0].1);
        lemma_poly_insert_wf(c, v, pt);
        let ins = poly_insert(c, v, pt);
        let r = seq![p[0]] + ins;
        assert forall |i: int| 0 <= i < r.len() implies r[i].0 != 0int by {
            if i == 0 {} else { assert(r[i] == ins[i-1]); }
        }
        //  Need: p[0].1 < first element of ins (if ins non-empty)
        //  This requires knowing poly_insert preserves "all > p[0].1" property
        //  Since pt has all vars > p[0].1, and v > p[0].1, poly_insert(c, v, pt) also has all vars > p[0].1
        lemma_wf_tail_gt(p);
        lemma_poly_insert_gt(c, v, pt, p[0].1);
        assert forall |i: int, j: int| 0 <= i < j < r.len()
            implies vars_lt(r[i].1, r[j].1) by {
            if i == 0 {
                assert(r[j] == ins[j-1]);
            } else {
                assert(r[i] == ins[i-1]);
                assert(r[j] == ins[j-1]);
            }
        }
    }
}

///  poly_insert preserves poly_gt.
proof fn lemma_poly_insert_gt(c: int, v: Seq<nat>, p: Seq<(int, Seq<nat>)>, w: Seq<nat>)
    requires poly_gt(p, w), vars_lt(w, v),
    ensures poly_gt(poly_insert(c, v, p), w),
    decreases p.len(),
{
    if c == 0int { return; }
    if p.len() == 0 { return; }
    if v =~= p[0].1 {
        let nc = c + p[0].0;
        if nc == 0int {
            //  Result is p_tail, which has poly_gt(_, w)
            let pt = p.subrange(1, p.len() as int);
            assert forall |i: int| 0 <= i < pt.len() implies vars_lt(w, pt[i].1) by {
                assert(pt[i] == p[i+1]);
            }
        } else {
            let pt = p.subrange(1, p.len() as int);
            let r = seq![(nc, v)] + pt;
            assert(vars_lt(w, r[0].1));
            assert forall |i: int| 0 <= i < r.len() implies vars_lt(w, r[i].1) by {
                if i == 0 {} else { assert(r[i] == pt[i-1]); assert(pt[i-1] == p[i]); }
            }
        }
    } else if vars_lt(v, p[0].1) {
        let r = seq![(c, v)] + p;
        assert forall |i: int| 0 <= i < r.len() implies vars_lt(w, r[i].1) by {
            if i == 0 {} else { assert(r[i] == p[i-1]); }
        }
    } else {
        let pt = p.subrange(1, p.len() as int);
        assert(poly_gt(pt, w)) by {
            assert forall |i: int| 0 <= i < pt.len() implies vars_lt(w, pt[i].1) by {
                assert(pt[i] == p[i+1]);
            }
        }
        lemma_poly_insert_gt(c, v, pt, w);
        let ins = poly_insert(c, v, pt);
        let r = seq![p[0]] + ins;
        assert forall |i: int| 0 <= i < r.len() implies vars_lt(w, r[i].1) by {
            if i == 0 {} else { assert(r[i] == ins[i-1]); }
        }
    }
}

///  mono_mul_poly preserves poly_wf.
proof fn lemma_mono_mul_poly_wf(c: int, vars: Seq<nat>, q: Seq<(int, Seq<nat>)>)
    requires poly_wf(q), c != 0int,
    ensures poly_wf(mono_mul_poly(c, vars, q)),
    decreases q.len(),
{
    if q.len() == 0 { return; }
    let qt = q.subrange(1, q.len() as int);
    assert(poly_wf(qt)) by {
        assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by { assert(qt[i] == q[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
            assert(qt[i] == q[i+1]); assert(qt[j] == q[j+1]);
        }
    }
    lemma_mono_mul_poly_wf(c, vars, qt);
    let nc = c * q[0].0;
    //  c != 0 and q[0].0 != 0 → c * q[0].0 != 0 (integers: zero product property)
    if nc == 0int {
        assert(c * q[0].0 == 0int);
        //  For integers: a*b == 0 implies a == 0 or b == 0
        assert(c == 0int || q[0].0 == 0int) by(nonlinear_arith)
            requires c * q[0].0 == 0int;
    }
    let nv = vars_merge(vars, q[0].1);
    let rest = mono_mul_poly(c, vars, qt);
    lemma_poly_insert_wf(nc, nv, rest);
}

///  poly_mul preserves poly_wf.
proof fn lemma_poly_mul_wf(p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>)
    requires poly_wf(p), poly_wf(q),
    ensures poly_wf(poly_mul(p, q)),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
        }
    }
    lemma_mono_mul_poly_wf(p[0].0, p[0].1, q);
    lemma_poly_mul_wf(pt, q);
    lemma_poly_add_wf(mono_mul_poly(p[0].0, p[0].1, q), poly_mul(pt, q));
}

//  ══════════════════════════════════════════════════════════════
//  arith_to_poly produces well-formed output
//  ══════════════════════════════════════════════════════════════

proof fn lemma_arith_to_poly_wf(e: &ArithExpr)
    ensures poly_wf(arith_to_poly(e)),
    decreases e,
{
    match e {
        ArithExpr::Const(c) => {
            if *c == 0int {
                assert(arith_to_poly(e) =~= seq![]);
            } else {
                let p = seq![(*c, Seq::<nat>::empty())];
                assert(arith_to_poly(e) =~= p);
                assert forall |i: int| 0 <= i < p.len() implies p[i].0 != 0int by {}
                assert forall |i: int, j: int| 0 <= i < j < p.len()
                    implies vars_lt(p[i].1, p[j].1) by {}
            }
        },
        ArithExpr::Var(n) => {
            let p = seq![(1int, seq![*n])];
            assert(arith_to_poly(e) =~= p);
            assert forall |i: int| 0 <= i < p.len() implies p[i].0 != 0int by {}
            assert forall |i: int, j: int| 0 <= i < j < p.len()
                implies vars_lt(p[i].1, p[j].1) by {}
        },
        ArithExpr::Add(a, b) => {
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_poly_add_wf(arith_to_poly(a), arith_to_poly(b));
        },
        ArithExpr::Sub(a, b) => {
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_poly_neg_wf(arith_to_poly(b));
            lemma_poly_add_wf(arith_to_poly(a), poly_neg(arith_to_poly(b)));
        },
        ArithExpr::Mul(a, b) => {
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_poly_mul_wf(arith_to_poly(a), arith_to_poly(b));
        },
        _ => {
            //  Non-ring variants → empty poly, trivially wf
        },
    }
}

//  ══════════════════════════════════════════════════════════════
//  GpuFixedPoint Ring implementation
//  ══════════════════════════════════════════════════════════════

pub struct GpuFixedPoint<const N: usize, const F: usize> {
    pub expr: ArithExpr,
}

impl<const N: usize, const F: usize> Equivalence for GpuFixedPoint<N, F> {
    open spec fn eqv(self, other: Self) -> bool {
        arith_to_poly(&self.expr) =~= arith_to_poly(&other.expr)
    }

    proof fn axiom_eqv_reflexive(a: Self) {}
    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}
    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {}
    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

impl<const N: usize, const F: usize> AdditiveCommutativeMonoid for GpuFixedPoint<N, F> {
    open spec fn zero() -> Self {
        GpuFixedPoint { expr: ArithExpr::Const(0) }
    }

    open spec fn add(self, other: Self) -> Self {
        GpuFixedPoint { expr: ArithExpr::Add(Box::new(self.expr), Box::new(other.expr)) }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        let pa = arith_to_poly(&a.expr);
        let pb = arith_to_poly(&b.expr);
        lemma_poly_add_comm(pa, pb);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        reveal_with_fuel(arith_to_poly, 2);
        lemma_arith_to_poly_wf(&a.expr);
        lemma_arith_to_poly_wf(&b.expr);
        lemma_arith_to_poly_wf(&c.expr);
        let pa = arith_to_poly(&a.expr);
        let pb = arith_to_poly(&b.expr);
        let pc = arith_to_poly(&c.expr);
        lemma_poly_add_wf(pa, pb);
        lemma_poly_add_assoc(pa, pb, pc);
    }

    proof fn axiom_add_zero_right(a: Self) {
        reveal_with_fuel(arith_to_poly, 2);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {}
}

impl<const N: usize, const F: usize> AdditiveGroup for GpuFixedPoint<N, F> {
    open spec fn neg(self) -> Self {
        GpuFixedPoint {
            expr: ArithExpr::Sub(Box::new(ArithExpr::Const(0)), Box::new(self.expr)),
        }
    }

    open spec fn sub(self, other: Self) -> Self {
        GpuFixedPoint {
            expr: ArithExpr::Sub(Box::new(self.expr), Box::new(other.expr)),
        }
    }

    proof fn axiom_add_inverse_right(a: Self) {
        reveal_with_fuel(arith_to_poly, 3);
        let pa = arith_to_poly(&a.expr);
        lemma_poly_add_inverse(pa);
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        reveal_with_fuel(arith_to_poly, 3);
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {}
}

impl<const N: usize, const F: usize> GpuFixedPoint<N, F> {
    pub open spec fn from_buffer(buf: nat) -> Self {
        GpuFixedPoint { expr: ArithExpr::Var(buf) }
    }
}

//  ══════════════════════════════════════════════════════════════
//  Well-formedness preservation: neg, insert, mono_mul, mul
//  ══════════════════════════════════════════════════════════════

///  poly_neg preserves elements: poly_neg(p)[i] == (-p[i].0, p[i].1).
proof fn lemma_poly_neg_index(p: Seq<(int, Seq<nat>)>, i: int)
    requires 0 <= i < p.len(),
    ensures poly_neg(p)[i] == (-p[i].0, p[i].1),
    decreases p.len(),
{
    lemma_poly_neg_len(p);
    if i == 0 {
    } else {
        let pt = p.subrange(1, p.len() as int);
        lemma_poly_neg_index(pt, i - 1);
        assert(pt[i - 1] == p[i]);
        let np = poly_neg(p);
        let npt = poly_neg(pt);
        assert(np =~= seq![(-p[0].0, p[0].1)] + npt);
        assert(np[i] == npt[i - 1]);
    }
}

proof fn lemma_poly_neg_wf(p: Seq<(int, Seq<nat>)>)
    requires poly_wf(p),
    ensures poly_wf(poly_neg(p)),
{
    lemma_poly_neg_len(p);
    let np = poly_neg(p);
    assert forall |i: int| 0 <= i < np.len() implies np[i].0 != 0int by {
        lemma_poly_neg_index(p, i);
    }
    assert forall |i: int, j: int| 0 <= i < j < np.len()
        implies vars_lt(np[i].1, np[j].1) by {
        lemma_poly_neg_index(p, i);
        lemma_poly_neg_index(p, j);
        assert(np[i].1 =~= p[i].1);
        assert(np[j].1 =~= p[j].1);
    }
}

//  ══════════════════════════════════════════════════════════════
//  Evaluation bridge: poly_eval connects polynomials to integers
//  ══════════════════════════════════════════════════════════════

///  Evaluate a monomial: product of env[vars[i]] for each variable.
pub open spec fn mono_eval(vars: Seq<nat>, env: Seq<int>) -> int
    decreases vars.len(),
{
    if vars.len() == 0 { 1int }
    else {
        let v = if (vars[0] as int) < env.len() { env[vars[0] as int] } else { 0int };
        v * mono_eval(vars.subrange(1, vars.len() as int), env)
    }
}

///  Evaluate a polynomial: sum of coeff * mono_eval(vars, env).
pub open spec fn poly_eval(p: Seq<(int, Seq<nat>)>, env: Seq<int>) -> int
    decreases p.len(),
{
    if p.len() == 0 { 0int }
    else { p[0].0 * mono_eval(p[0].1, env) + poly_eval(p.subrange(1, p.len() as int), env) }
}

///  Standalone test: does the base case of mono_eval_merge work?
proof fn test_mono_merge_base(a: Seq<nat>, b: Seq<nat>, env: Seq<int>)
    requires a.len() == 0,
    ensures mono_eval(vars_merge(a, b), env) == mono_eval(a, env) * mono_eval(b, env),
{}

///  mono_eval(merge(a,b), env) == mono_eval(a, env) * mono_eval(b, env).
proof fn lemma_mono_eval_merge(a: Seq<nat>, b: Seq<nat>, env: Seq<int>)
    ensures mono_eval(vars_merge(a, b), env) == mono_eval(a, env) * mono_eval(b, env),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        test_mono_merge_base(a, b, env);
    } else if b.len() == 0 {
        // vars_merge(a, []) = a (second branch), mono_eval([], env) = 1
        assert(vars_merge(a, b) =~= a) by { reveal_with_fuel(vars_merge, 2); }
        assert(mono_eval(b, env) == 1int) by { reveal_with_fuel(mono_eval, 2); }
    } else if a[0] <= b[0] {
        let at = a.subrange(1, a.len() as int);
        lemma_mono_eval_merge(at, b, env);
        let va = if (a[0] as int) < env.len() { env[a[0] as int] } else { 0int };
        let m = vars_merge(a, b);
        assert(m =~= seq![a[0]] + vars_merge(at, b));
        assert(m.subrange(1, m.len() as int) =~= vars_merge(at, b));
        //  Explicitly tell Z3 what mono_eval of the merge is
        assert(mono_eval(m, env) == va * mono_eval(vars_merge(at, b), env));
        assert(mono_eval(a, env) == va * mono_eval(at, env));
        assert(mono_eval(vars_merge(at, b), env) == mono_eval(at, env) * mono_eval(b, env));
        assert(va * mono_eval(at, env) * mono_eval(b, env)
            == va * (mono_eval(at, env) * mono_eval(b, env))) by(nonlinear_arith);
    } else {
        let bt = b.subrange(1, b.len() as int);
        lemma_mono_eval_merge(a, bt, env);
        let vb = if (b[0] as int) < env.len() { env[b[0] as int] } else { 0int };
        let m = vars_merge(a, b);
        assert(m =~= seq![b[0]] + vars_merge(a, bt));
        assert(m.subrange(1, m.len() as int) =~= vars_merge(a, bt));
        //  Explicitly tell Z3 what mono_eval of the merge is
        assert(mono_eval(m, env) == vb * mono_eval(vars_merge(a, bt), env));
        assert(mono_eval(b, env) == vb * mono_eval(bt, env));
        assert(mono_eval(vars_merge(a, bt), env) == mono_eval(a, env) * mono_eval(bt, env));
        assert(vb * (mono_eval(a, env) * mono_eval(bt, env))
            == mono_eval(a, env) * (vb * mono_eval(bt, env))) by(nonlinear_arith);
    }
}

///  poly_eval(poly_insert(c, v, p), env) == c * mono_eval(v, env) + poly_eval(p, env)
///  for well-formed p.
proof fn lemma_poly_eval_insert(c: int, v: Seq<nat>, p: Seq<(int, Seq<nat>)>, env: Seq<int>)
    requires poly_wf(p),
    ensures poly_eval(poly_insert(c, v, p), env) == c * mono_eval(v, env) + poly_eval(p, env),
    decreases p.len(),
{
    if c == 0int {
        //  poly_insert = p, c * mono_eval = 0
        return;
    }
    if p.len() == 0 {
        //  poly_insert(c, v, []) = [(c, v)]
        //  poly_insert(c, v, []) = [(c, v)] since c != 0
        //  poly_eval([(c,v)], env) = c * mono_eval(v, env) + 0 = c * mono_eval(v, env)
        //  poly_eval([], env) = 0
        //  So postcondition: c * mono_eval(v, env) + 0 == c * mono_eval(v, env) + 0 ✓
        reveal_with_fuel(poly_eval, 2);
        return;
    }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
        }
    }
    if v =~= p[0].1 {
        let nc = c + p[0].0;
        if nc == 0int {
            //  poly_insert = pt
            //  poly_eval(pt) = poly_eval(p) - p[0].0 * mono_eval(p[0].1, env)
            //  c * mono_eval(v) + poly_eval(p) = c * mono_eval(v) + p[0].0 * mono_eval(v) + poly_eval(pt)
            //  = (c + p[0].0) * mono_eval(v) + poly_eval(pt) = 0 + poly_eval(pt) ✓
            assert(c * mono_eval(v, env) + poly_eval(p, env)
                == (c + p[0].0) * mono_eval(v, env) + poly_eval(pt, env))
                by(nonlinear_arith)
                requires poly_eval(p, env) == p[0].0 * mono_eval(p[0].1, env) + poly_eval(pt, env),
                    v =~= p[0].1;
        } else {
            //  poly_insert = [(nc, v)] + pt
            let r = seq![(nc, v)] + pt;
            assert(r.subrange(1, r.len() as int) =~= pt);
            assert(poly_eval(r, env) == nc * mono_eval(v, env) + poly_eval(pt, env));
            assert(nc * mono_eval(v, env) == (c + p[0].0) * mono_eval(v, env))
                by(nonlinear_arith) requires nc == c + p[0].0;
            assert((c + p[0].0) * mono_eval(v, env) + poly_eval(pt, env)
                == c * mono_eval(v, env) + p[0].0 * mono_eval(v, env) + poly_eval(pt, env))
                by(nonlinear_arith);
        }
    } else if vars_lt(v, p[0].1) {
        //  poly_insert = [(c, v)] + p
        let r = seq![(c, v)] + p;
        assert(r.subrange(1, r.len() as int) =~= p);
    } else {
        //  poly_insert = [p[0]] + poly_insert(c, v, pt)
        lemma_poly_eval_insert(c, v, pt, env);
        let ins = poly_insert(c, v, pt);
        let r = seq![p[0]] + ins;
        assert(r.subrange(1, r.len() as int) =~= ins);
        assert(poly_eval(r, env) == p[0].0 * mono_eval(p[0].1, env) + poly_eval(ins, env));
        assert(poly_eval(ins, env) == c * mono_eval(v, env) + poly_eval(pt, env));
    }
}

///  poly_eval(mono_mul_poly(c, vars, q), env) == c * mono_eval(vars, env) * poly_eval(q, env).
proof fn lemma_poly_eval_mono_mul(
    c: int, vars: Seq<nat>, q: Seq<(int, Seq<nat>)>, env: Seq<int>,
)
    requires poly_wf(q), c != 0int,
    ensures poly_eval(mono_mul_poly(c, vars, q), env) == c * mono_eval(vars, env) * poly_eval(q, env),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(poly_eval(seq![], env) == 0int);
        assert(poly_eval(q, env) == 0int);
        assert(c * mono_eval(vars, env) * 0int == 0int) by(nonlinear_arith);
        return;
    }
    let qt = q.subrange(1, q.len() as int);
    assert(poly_wf(qt)) by {
        assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by { assert(qt[i] == q[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
            assert(qt[i] == q[i+1]); assert(qt[j] == q[j+1]);
        }
    }
    let nc = c * q[0].0;
    let nv = vars_merge(vars, q[0].1);
    let rest = mono_mul_poly(c, vars, qt);

    lemma_poly_eval_mono_mul(c, vars, qt, env);
    lemma_mono_mul_poly_wf(c, vars, qt);
    lemma_poly_eval_insert(nc, nv, rest, env);
    lemma_mono_eval_merge(vars, q[0].1, env);

    //  poly_eval(poly_insert(nc, nv, rest), env) = nc * mono_eval(nv, env) + poly_eval(rest, env)
    //  = c * q[0].0 * mono_eval(vars, env) * mono_eval(q[0].1, env)
    //    + c * mono_eval(vars, env) * poly_eval(qt, env)
    //  = c * mono_eval(vars, env) * (q[0].0 * mono_eval(q[0].1, env) + poly_eval(qt, env))
    //  = c * mono_eval(vars, env) * poly_eval(q, env)

    //  Chain the algebra: poly_eval(result) = nc*mono(nv) + poly_eval(rest)
    //  = c*q0*mono(vars)*mono(q0_vars) + c*mono(vars)*poly_eval(qt)
    //  = c*mono(vars) * (q0*mono(q0_vars) + poly_eval(qt))
    //  = c*mono(vars) * poly_eval(q)
    assert(nc * mono_eval(nv, env) == c * q[0].0 * mono_eval(vars, env) * mono_eval(q[0].1, env))
        by(nonlinear_arith)
        requires nc == c * q[0].0,
            mono_eval(nv, env) == mono_eval(vars, env) * mono_eval(q[0].1, env);
    assert(c * q[0].0 * mono_eval(vars, env) * mono_eval(q[0].1, env)
        + c * mono_eval(vars, env) * poly_eval(qt, env)
        == c * mono_eval(vars, env) * (q[0].0 * mono_eval(q[0].1, env) + poly_eval(qt, env)))
        by(nonlinear_arith);
    assert(c * mono_eval(vars, env) * poly_eval(q, env)
        == c * mono_eval(vars, env) * (q[0].0 * mono_eval(q[0].1, env) + poly_eval(qt, env)))
        by(nonlinear_arith)
        requires poly_eval(q, env) == q[0].0 * mono_eval(q[0].1, env) + poly_eval(qt, env);
    assert(c * mono_eval(vars, env) * (q[0].0 * mono_eval(q[0].1, env) + poly_eval(qt, env))
        == c * q[0].0 * mono_eval(vars, env) * mono_eval(q[0].1, env) + c * mono_eval(vars, env) * poly_eval(qt, env))
        by(nonlinear_arith);
}

///  poly_eval(poly_mul(p, q), env) == poly_eval(p, env) * poly_eval(q, env).
proof fn lemma_poly_eval_mul(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>, env: Seq<int>,
)
    requires poly_wf(p), poly_wf(q),
    ensures poly_eval(poly_mul(p, q), env) == poly_eval(p, env) * poly_eval(q, env),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(poly_eval(p, env) == 0int);
        return;
    }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
        }
    }
    lemma_poly_eval_mono_mul(p[0].0, p[0].1, q, env);
    lemma_poly_eval_mul(pt, q, env);
    lemma_mono_mul_poly_wf(p[0].0, p[0].1, q);
    lemma_poly_mul_wf(pt, q);

    let mmp = mono_mul_poly(p[0].0, p[0].1, q);
    let pmul = poly_mul(pt, q);

    //  poly_mul(p, q) = poly_add(mmp, pmul)
    //  Need: poly_eval(poly_add(mmp, pmul), env) = poly_eval(mmp, env) + poly_eval(pmul, env)
    lemma_poly_eval_add(mmp, pmul, env);

    //  poly_eval(mmp, env) = p[0].0 * mono_eval(p[0].1, env) * poly_eval(q, env)
    //  poly_eval(pmul, env) = poly_eval(pt, env) * poly_eval(q, env)
    //  Sum = (p[0].0 * mono_eval(p[0].1, env) + poly_eval(pt, env)) * poly_eval(q, env)
    //      = poly_eval(p, env) * poly_eval(q, env)
    assert((p[0].0 * mono_eval(p[0].1, env) + poly_eval(pt, env)) * poly_eval(q, env)
        == p[0].0 * mono_eval(p[0].1, env) * poly_eval(q, env) + poly_eval(pt, env) * poly_eval(q, env))
        by(nonlinear_arith);
}

///  poly_eval(poly_add(p, q), env) == poly_eval(p, env) + poly_eval(q, env).
proof fn lemma_poly_eval_add(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>, env: Seq<int>,
)
    requires poly_wf(p), poly_wf(q),
    ensures poly_eval(poly_add(p, q), env) == poly_eval(p, env) + poly_eval(q, env),
    decreases p.len() + q.len(),
{
    if p.len() == 0 { return; }
    if q.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    let qt = q.subrange(1, q.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
        }
    }
    assert(poly_wf(qt)) by {
        assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int by { assert(qt[i] == q[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < qt.len() implies vars_lt(qt[i].1, qt[j].1) by {
            assert(qt[i] == q[i+1]); assert(qt[j] == q[j+1]);
        }
    }
    if p[0].1 =~= q[0].1 {
        lemma_poly_eval_add(pt, qt, env);
        let c = p[0].0 + q[0].0;
        if c == 0int {
            //  poly_add(p, q) = poly_add(pt, qt)
            assert((p[0].0 + q[0].0) * mono_eval(p[0].1, env) == 0int) by(nonlinear_arith)
                requires p[0].0 + q[0].0 == 0int;
            //  poly_eval(p) = p0*m + eval(pt), poly_eval(q) = q0*m' + eval(qt)
            //  where m = m' since p[0].1 =~= q[0].1
            //  sum = (p0+q0)*m + eval(pt) + eval(qt) = eval(pt) + eval(qt)
            //  poly_eval(poly_add(pt,qt)) = eval(pt) + eval(qt) [IH]
            assert(poly_eval(p, env) == p[0].0 * mono_eval(p[0].1, env) + poly_eval(pt, env));
            assert(poly_eval(q, env) == q[0].0 * mono_eval(q[0].1, env) + poly_eval(qt, env));
            //  Since p[0].1 =~= q[0].1, mono_eval gives same value
            assert(mono_eval(q[0].1, env) == mono_eval(p[0].1, env));
            //  So: sum = (p0+q0)*m + eval(pt) + eval(qt) = 0 + eval(pt) + eval(qt)
            assert(p[0].0 * mono_eval(p[0].1, env) + q[0].0 * mono_eval(p[0].1, env) == 0int)
                by(nonlinear_arith)
                requires p[0].0 + q[0].0 == 0int;
        } else {
            //  poly_add(p, q) = [(c, v)] + poly_add(pt, qt)
            let r = seq![(c, p[0].1)] + poly_add(pt, qt);
            assert(poly_add(p, q) =~= r);
            assert(r.subrange(1, r.len() as int) =~= poly_add(pt, qt));
            assert(c * mono_eval(p[0].1, env) == (p[0].0 + q[0].0) * mono_eval(p[0].1, env))
                by(nonlinear_arith) requires c == p[0].0 + q[0].0;
            assert((p[0].0 + q[0].0) * mono_eval(p[0].1, env) == p[0].0 * mono_eval(p[0].1, env) + q[0].0 * mono_eval(p[0].1, env))
                by(nonlinear_arith);
        }
    } else if vars_lt(p[0].1, q[0].1) {
        lemma_poly_eval_add(pt, q, env);
        lemma_vars_lt_asymm(p[0].1, q[0].1);
        let r = seq![p[0]] + poly_add(pt, q);
        assert(r.subrange(1, r.len() as int) =~= poly_add(pt, q));
    } else {
        lemma_vars_lt_trichotomy(p[0].1, q[0].1);
        lemma_poly_eval_add(p, qt, env);
        let r = seq![q[0]] + poly_add(p, qt);
        assert(r.subrange(1, r.len() as int) =~= poly_add(p, qt));
    }
}

///  poly_eval(arith_to_poly(e), env) == arith_eval(e, env).
///  An ArithExpr is a "ring expression" if it only uses Const/Var/Add/Sub/Mul.
pub open spec fn is_ring_expr(e: &ArithExpr) -> bool
    decreases e,
{
    match e {
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b) =>
            is_ring_expr(a) && is_ring_expr(b),
        _ => false,
    }
}

proof fn lemma_poly_eval_var(n: nat, env: Seq<int>)
    ensures poly_eval(seq![(1int, seq![n])], env) ==
        (if (n as int) < env.len() { env[n as int] } else { 0int }),
{
    let p = seq![(1int, seq![n])];
    assert(p[0] == (1int, seq![n]));
    assert(p[0].0 == 1int);
    assert(p[0].1 =~= seq![n]);
    assert(p.subrange(1, p.len() as int) =~= seq![]);
    //  mono_eval(seq![n], env)
    let vars = seq![n];
    assert(vars[0] == n);
    assert(vars.subrange(1, vars.len() as int) =~= Seq::<nat>::empty());
    let v = if (n as int) < env.len() { env[n as int] } else { 0int };
    assert(mono_eval(Seq::<nat>::empty(), env) == 1int) by {
        reveal_with_fuel(mono_eval, 1);
    };
    assert(mono_eval(vars, env) == v * 1int) by {
        reveal_with_fuel(mono_eval, 2);
    };
    assert(v * 1int == v) by(nonlinear_arith);
    assert(poly_eval(seq![], env) == 0int) by { reveal_with_fuel(poly_eval, 1); };
    assert(poly_eval(p, env) == 1int * mono_eval(vars, env) + poly_eval(seq![], env)) by {
        reveal_with_fuel(poly_eval, 2);
    };
    assert(1int * mono_eval(vars, env) == mono_eval(vars, env)) by(nonlinear_arith);
}

proof fn lemma_poly_eval_arith(e: &ArithExpr, env: Seq<int>)
    requires is_ring_expr(e),
    ensures poly_eval(arith_to_poly(e), env) == arith_eval(e, env),
    decreases e,
{
    reveal_with_fuel(arith_eval, 2);
    reveal_with_fuel(poly_eval, 2);
    reveal_with_fuel(mono_eval, 2);
    match e {
        ArithExpr::Const(c) => {
            //  arith_eval(Const(c), env) = c
            //  arith_to_poly(Const(c)) = if c==0 { [] } else { [(c, [])] }
            //  poly_eval([], env) = 0; poly_eval([(c,[])], env) = c * mono_eval([], env) + 0 = c * 1 = c
            assert(poly_eval(arith_to_poly(e), env) == arith_eval(e, env));
        },
        ArithExpr::Var(n) => {
            lemma_poly_eval_var(*n, env);
        },
        ArithExpr::Add(a, b) => {
            lemma_poly_eval_arith(a, env);
            lemma_poly_eval_arith(b, env);
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_poly_eval_add(arith_to_poly(a), arith_to_poly(b), env);
        },
        ArithExpr::Sub(a, b) => {
            lemma_poly_eval_arith(a, env);
            lemma_poly_eval_arith(b, env);
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_poly_neg_wf(arith_to_poly(b));
            lemma_poly_eval_neg(arith_to_poly(b), env);
            lemma_poly_eval_add(arith_to_poly(a), poly_neg(arith_to_poly(b)), env);
        },
        ArithExpr::Mul(a, b) => {
            lemma_poly_eval_arith(a, env);
            lemma_poly_eval_arith(b, env);
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_poly_eval_mul(arith_to_poly(a), arith_to_poly(b), env);
        },
        _ => {
            //  Unreachable by is_ring_expr precondition
            assert(!is_ring_expr(e));
        },
    }
}

///  poly_eval(poly_neg(p), env) == -poly_eval(p, env).
proof fn lemma_poly_eval_neg(p: Seq<(int, Seq<nat>)>, env: Seq<int>)
    ensures poly_eval(poly_neg(p), env) == -poly_eval(p, env),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_poly_eval_neg(pt, env);
    lemma_poly_neg_len(p);
    let np = poly_neg(p);
    let npt = poly_neg(pt);
    assert(np =~= seq![(-p[0].0, p[0].1)] + npt);
    assert(np.subrange(1, np.len() as int) =~= npt);
    assert((-p[0].0) * mono_eval(p[0].1, env) == -(p[0].0 * mono_eval(p[0].1, env)))
        by(nonlinear_arith);
}

    let pt = p.subrange(1, p.len() as int);
    lemma_poly_neg_index(p, 0);
    let np = poly_neg(p);
    if p[0].1 =~= v {
        assert(np[0].1 =~= v);
        assert(poly_coeff(np, v) == np[0].0);
        assert(np[0].0 == -p[0].0);
    } else {
        lemma_poly_neg_tail(p);
        lemma_poly_neg_coeff(pt, v);
        assert(!(np[0].1 =~= v));
        assert(np.subrange(1, np.len() as int) =~= poly_neg(pt));
    }
}

///  mono_eval with empty env: non-empty vars → 0.
proof fn lemma_mono_eval_empty(vars: Seq<nat>)
    requires vars.len() > 0,
    ensures mono_eval(vars, Seq::<int>::empty()) == 0int,
{
    reveal_with_fuel(mono_eval, 2);
}

///  mono_eval with all-ones env of sufficient length: result is 1.
proof fn lemma_mono_eval_ones(vars: Seq<nat>, env: Seq<int>)
    requires
        forall |i: int| 0 <= i < env.len() ==> env[i] == 1int,
        forall |i: int| 0 <= i < vars.len() ==> (vars[i] as int) < env.len(),
    ensures mono_eval(vars, env) == 1int,
    decreases vars.len(),
{
    if vars.len() == 0 { return; }
    lemma_mono_eval_ones(vars.subrange(1, vars.len() as int), env);
}

///  poly_eval at empty env: only constant terms (vars=[]) contribute.
proof fn lemma_poly_eval_at_empty(p: Seq<(int, Seq<nat>)>)
    requires poly_wf(p),
    ensures
        p.len() > 0 && p[0].1.len() == 0 ==> poly_eval(p, Seq::<int>::empty()) == p[0].0,
        (p.len() == 0 || p[0].1.len() > 0) ==> poly_eval(p, Seq::<int>::empty()) == 0int,
    decreases p.len(),
{
    let env = Seq::<int>::empty();
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len() implies vars_lt(pt[i].1, pt[j].1) by {
            assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]);
        }
    }
    if p[0].1.len() == 0 {
        reveal_with_fuel(mono_eval, 1);
        if pt.len() > 0 {
            lemma_wf_tail_gt(p);
            assert(pt[0].1.len() > 0) by { assert(vars_lt(p[0].1, pt[0].1)); }
            lemma_poly_eval_at_empty(pt);
        }
    } else {
        lemma_mono_eval_empty(p[0].1);
        assert(p[0].0 * mono_eval(p[0].1, env) == 0int) by(nonlinear_arith)
            requires mono_eval(p[0].1, env) == 0int;
        if pt.len() > 0 {
            lemma_wf_tail_gt(p);
            assert(pt[0].1.len() > 0) by { assert(vars_lt(p[0].1, pt[0].1)); }
            lemma_poly_eval_at_empty(pt);
        }
    }
}

///  A non-empty well-formed polynomial has a non-zero evaluation somewhere.
proof fn lemma_wf_poly_nonzero_eval(p: Seq<(int, Seq<nat>)>)
    requires poly_wf(p), p.len() > 0,
    ensures exists |env: Seq<int>| poly_eval(p, env) != 0int,
    decreases p.len(),
{
    //  Case 1: constant term (p[0].1 is empty)
    if p[0].1.len() == 0 {
        let env = Seq::<int>::empty();
        lemma_poly_eval_at_empty(p);
        assert(poly_eval(p, env) == p[0].0);
        return;
    }

    //  Case 2: single non-constant term
    if p.len() == 1 {
        let max_idx = p[0].1[p[0].1.len() as int - 1];
        let env = Seq::new((max_idx + 1) as nat, |_i: int| 1int);
        assert forall |i: int| 0 <= i < p[0].1.len()
            implies (p[0].1[i] as int) < env.len() by {}
        lemma_mono_eval_ones(p[0].1, env);
        reveal_with_fuel(poly_eval, 2);
        assert(poly_eval(p, env) == p[0].0);
        return;
    }

    //  Case 3: multi-term, no constant term
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int
            by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len()
            implies vars_lt(pt[i].1, pt[j].1)
            by { assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]); }
    }
    lemma_wf_poly_nonzero_eval(pt);
    let env_ih: Seq<int> = choose |env: Seq<int>| poly_eval(pt, env) != 0int;
    assert(poly_eval(p, env_ih) != 0int);
}

proof fn lemma_poly_identity(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    requires
        poly_wf(p), poly_wf(q),
        forall |env: Seq<int>| poly_eval(p, env) == poly_eval(q, env),
    ensures p =~= q,
{
    lemma_poly_neg_wf(q);
    let nq = poly_neg(q);
    lemma_poly_add_wf(p, nq);
    let d = poly_add(p, nq);

    //  poly_eval(d, env) == 0 for all env
    assert forall |env: Seq<int>| poly_eval(d, env) == 0int by {
        lemma_poly_eval_add(p, nq, env);
        lemma_poly_eval_neg(q, env);
    };

    //  d must be empty
    if d.len() > 0 {
        lemma_wf_poly_nonzero_eval(d);
        let env_witness: Seq<int> = choose |env: Seq<int>| poly_eval(d, env) != 0int;
        assert(poly_eval(d, env_witness) == 0int);
        assert(false);
    }

    //  d =~= [], so poly_coeff(p, v) == poly_coeff(q, v) for all v
    assert forall |v: Seq<nat>| poly_coeff(p, v) == poly_coeff(q, v) by {
        lemma_poly_add_coeff_wf(p, nq, v);
        lemma_poly_neg_coeff(q, v);
        //  poly_coeff(d, v) == poly_coeff(p, v) + poly_coeff(nq, v)
        //  = poly_coeff(p, v) - poly_coeff(q, v) == 0
    };
    lemma_poly_wf_eq_from_coeff(p, q);
}

} //  verus!
