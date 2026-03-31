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

///  arith_to_poly produces poly_vars_sorted output.
proof fn lemma_arith_to_poly_vars_sorted(e: &ArithExpr)
    ensures poly_vars_sorted(arith_to_poly(e)),
    decreases e,
{
    match e {
        ArithExpr::Const(c) => {
            //  [] or [(c, [])]. Both trivially sorted.
        },
        ArithExpr::Var(n) => {
            //  [(1, [n])]. Single element in vars → trivially sorted.
            let p = seq![(1int, seq![*n])];
            assert(arith_to_poly(e) =~= p);
        },
        ArithExpr::Add(a, b) => {
            lemma_arith_to_poly_vars_sorted(a);
            lemma_arith_to_poly_vars_sorted(b);
            lemma_vars_sorted_add(arith_to_poly(a), arith_to_poly(b));
        },
        ArithExpr::Sub(a, b) => {
            lemma_arith_to_poly_vars_sorted(a);
            lemma_arith_to_poly_vars_sorted(b);
            lemma_vars_sorted_neg(arith_to_poly(b));
            lemma_vars_sorted_add(arith_to_poly(a), poly_neg(arith_to_poly(b)));
        },
        ArithExpr::Mul(a, b) => {
            lemma_arith_to_poly_vars_sorted(a);
            lemma_arith_to_poly_vars_sorted(b);
            lemma_arith_to_poly_wf(a);
            lemma_arith_to_poly_wf(b);
            lemma_vars_sorted_mul(arith_to_poly(a), arith_to_poly(b));
        },
        _ => {},
    }
}

///  poly_mul preserves poly_vars_sorted.
proof fn lemma_vars_sorted_mul(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>,
)
    requires poly_vars_sorted(p), poly_vars_sorted(q), poly_wf(p), poly_wf(q),
    ensures poly_vars_sorted(poly_mul(p, q)),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_vars_sorted_tail(p);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int
            by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len()
            implies vars_lt(pt[i].1, pt[j].1)
            by { assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]); }
    }
    lemma_vars_sorted_mul(pt, q);
    lemma_vars_sorted_mono_mul(p[0].0, p[0].1, q);
    lemma_mono_mul_poly_wf(p[0].0, p[0].1, q);
    lemma_poly_mul_wf(pt, q);
    lemma_vars_sorted_add(mono_mul_poly(p[0].0, p[0].1, q), poly_mul(pt, q));
}

///  mono_mul_poly preserves poly_vars_sorted.
proof fn lemma_vars_sorted_mono_mul(c: int, vars: Seq<nat>, q: Seq<(int, Seq<nat>)>)
    requires poly_vars_sorted(q), poly_wf(q), c != 0int,
        forall |j: int| #![trigger vars[j]] 0 < j < vars.len() ==> vars[j-1] <= vars[j],
    ensures poly_vars_sorted(mono_mul_poly(c, vars, q)),
    decreases q.len(),
{
    if q.len() == 0 { return; }
    let qt = q.subrange(1, q.len() as int);
    assert(poly_wf(qt)) by {
        assert forall |i: int| 0 <= i < qt.len() implies qt[i].0 != 0int
            by { assert(qt[i] == q[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < qt.len()
            implies vars_lt(qt[i].1, qt[j].1)
            by { assert(qt[i] == q[i+1]); assert(qt[j] == q[j+1]); }
    }
    lemma_vars_sorted_tail(q);
    lemma_vars_sorted_mono_mul(c, vars, qt);
    lemma_mono_mul_poly_wf(c, vars, qt);
    //  mono_mul_poly(c, vars, q) = poly_insert(nc, nv, rest)
    //  vars_merge produces sorted output → nv is sorted.
    //  poly_insert preserves poly_vars_sorted (it inserts a sorted-vars term).
    lemma_vars_merge_sorted(vars, q[0].1);
    lemma_vars_sorted_insert(c * q[0].0, vars_merge(vars, q[0].1), mono_mul_poly(c, vars, qt));
}

///  poly_insert preserves poly_vars_sorted when the inserted term has sorted vars.
proof fn lemma_vars_sorted_insert(c: int, v: Seq<nat>, p: Seq<(int, Seq<nat>)>)
    requires poly_vars_sorted(p),
        forall |j: int| #![trigger v[j]] 0 < j < v.len() ==> v[j-1] <= v[j],
    ensures poly_vars_sorted(poly_insert(c, v, p)),
    decreases p.len(),
{
    if c == 0int || p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_vars_sorted_tail(p);
    if v =~= p[0].1 {
        //  Combined or cancelled — vars don't change for remaining terms.
    } else if vars_lt(v, p[0].1) {
        //  Prepend (c, v) to p. Both have sorted vars.
        let r = seq![(c, v)] + p;
        assert forall |i: int, j: int| #![trigger r[i].1[j]] 0 <= i < r.len() && 0 < j < r[i].1.len()
            implies r[i].1[j-1] <= r[i].1[j] by {
            if i == 0 {} else { assert(r[i] == p[i-1]); }
        }
    } else {
        lemma_vars_sorted_insert(c, v, pt);
        let ins = poly_insert(c, v, pt);
        let r = seq![p[0]] + ins;
        assert forall |i: int, j: int| #![trigger r[i].1[j]] 0 <= i < r.len() && 0 < j < r[i].1.len()
            implies r[i].1[j-1] <= r[i].1[j] by {
            if i == 0 {} else { assert(r[i] == ins[i-1]); }
        }
    }
}

///  vars_merge produces sorted output from sorted inputs.
proof fn lemma_vars_merge_sorted(a: Seq<nat>, b: Seq<nat>)
    requires
        forall |j: int| #![trigger a[j]] 0 < j < a.len() ==> a[j-1] <= a[j],
        forall |j: int| #![trigger b[j]] 0 < j < b.len() ==> b[j-1] <= b[j],
    ensures ({
        let m = vars_merge(a, b);
        forall |j: int| #![trigger m[j]] 0 < j < m.len() ==> m[j-1] <= m[j]
    }),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 { return; }
    if a[0] <= b[0] {
        let at = a.subrange(1, a.len() as int);
        assert forall |j: int| #![trigger at[j]] 0 < j < at.len() implies at[j-1] <= at[j] by {
            assert(at[j] == a[j+1]);
            if j > 0 { assert(at[j-1] == a[j]); }
        }
        lemma_vars_merge_sorted(at, b);
        let m = vars_merge(a, b);
        let mt = vars_merge(at, b);
        assert(m =~= seq![a[0]] + mt);
    } else {
        let bt = b.subrange(1, b.len() as int);
        assert forall |j: int| #![trigger bt[j]] 0 < j < bt.len() implies bt[j-1] <= bt[j] by {
            assert(bt[j] == b[j+1]);
            if j > 0 { assert(bt[j-1] == b[j]); }
        }
        lemma_vars_merge_sorted(a, bt);
        let m = vars_merge(a, b);
        let mt = vars_merge(a, bt);
        assert(m =~= seq![b[0]] + mt);
    }
}

///  Shortcut: poly_vars_sorted for poly_mul of arith_to_poly outputs.
proof fn lemma_mul_vars_sorted(a: &ArithExpr, b: &ArithExpr)
    ensures
        poly_vars_sorted(poly_mul(arith_to_poly(a), arith_to_poly(b))),
        poly_vars_sorted(arith_to_poly(a)),
        poly_vars_sorted(arith_to_poly(b)),
{
    lemma_arith_to_poly_vars_sorted(a);
    lemma_arith_to_poly_vars_sorted(b);
    lemma_arith_to_poly_wf(a);
    lemma_arith_to_poly_wf(b);
    lemma_vars_sorted_mul(arith_to_poly(a), arith_to_poly(b));
}

///  Shortcut: poly_vars_sorted for poly_add of arith_to_poly outputs.
proof fn lemma_add_vars_sorted(a: &ArithExpr, b: &ArithExpr)
    ensures
        poly_vars_sorted(poly_add(arith_to_poly(a), arith_to_poly(b))),
        poly_vars_sorted(arith_to_poly(a)),
        poly_vars_sorted(arith_to_poly(b)),
{
    lemma_arith_to_poly_vars_sorted(a);
    lemma_arith_to_poly_vars_sorted(b);
    lemma_vars_sorted_add(arith_to_poly(a), arith_to_poly(b));
}

///  Helper for mul_associative: eval part.
proof fn lemma_mul_assoc_eval(a: &ArithExpr, b: &ArithExpr, c: &ArithExpr)
    ensures forall |env: Seq<int>|
        poly_eval(poly_mul(poly_mul(arith_to_poly(a), arith_to_poly(b)), arith_to_poly(c)), env)
        == poly_eval(poly_mul(arith_to_poly(a), poly_mul(arith_to_poly(b), arith_to_poly(c))), env),
{
    let pa = arith_to_poly(a);
    let pb = arith_to_poly(b);
    let pc = arith_to_poly(c);
    lemma_arith_to_poly_wf(a);
    lemma_arith_to_poly_wf(b);
    lemma_arith_to_poly_wf(c);
    lemma_poly_mul_wf(pa, pb);
    lemma_poly_mul_wf(pb, pc);
    assert forall |env: Seq<int>|
        poly_eval(poly_mul(poly_mul(pa, pb), pc), env)
            == poly_eval(poly_mul(pa, poly_mul(pb, pc)), env) by {
        lemma_poly_eval_mul(pa, pb, env);
        lemma_poly_eval_mul(poly_mul(pa, pb), pc, env);
        lemma_poly_eval_mul(pb, pc, env);
        lemma_poly_eval_mul(pa, poly_mul(pb, pc), env);
        let ea = poly_eval(pa, env);
        let eb = poly_eval(pb, env);
        let ec = poly_eval(pc, env);
        assert((ea * eb) * ec == ea * (eb * ec)) by(nonlinear_arith);
    }
}

///  Helper for mul_associative: sorted + identity.
proof fn lemma_mul_assoc_helper(a: &ArithExpr, b: &ArithExpr, c: &ArithExpr)
    ensures poly_mul(poly_mul(arith_to_poly(a), arith_to_poly(b)), arith_to_poly(c))
        =~= poly_mul(arith_to_poly(a), poly_mul(arith_to_poly(b), arith_to_poly(c))),
{
    let pa = arith_to_poly(a);
    let pb = arith_to_poly(b);
    let pc = arith_to_poly(c);
    lemma_arith_to_poly_wf(a);
    lemma_arith_to_poly_wf(b);
    lemma_arith_to_poly_wf(c);
    lemma_poly_mul_wf(pa, pb);
    lemma_poly_mul_wf(pb, pc);
    lemma_poly_mul_wf(poly_mul(pa, pb), pc);
    lemma_poly_mul_wf(pa, poly_mul(pb, pc));
    lemma_mul_assoc_eval(a, b, c);
    lemma_mul_vars_sorted(a, b);
    lemma_mul_vars_sorted(b, c);
    lemma_vars_sorted_mul(poly_mul(pa, pb), pc);
    lemma_vars_sorted_mul(pa, poly_mul(pb, pc));
    lemma_same_eval_same_poly(poly_mul(poly_mul(pa, pb), pc), poly_mul(pa, poly_mul(pb, pc)));
}

///  Helper for mul_distributes_left: eval part.
proof fn lemma_mul_distrib_eval(a: &ArithExpr, b: &ArithExpr, c: &ArithExpr)
    ensures forall |env: Seq<int>|
        poly_eval(poly_mul(arith_to_poly(a), poly_add(arith_to_poly(b), arith_to_poly(c))), env)
        == poly_eval(poly_add(poly_mul(arith_to_poly(a), arith_to_poly(b)), poly_mul(arith_to_poly(a), arith_to_poly(c))), env),
{
    let pa = arith_to_poly(a);
    let pb = arith_to_poly(b);
    let pc = arith_to_poly(c);
    lemma_arith_to_poly_wf(a);
    lemma_arith_to_poly_wf(b);
    lemma_arith_to_poly_wf(c);
    lemma_poly_add_wf(pb, pc);
    lemma_poly_mul_wf(pa, pb);
    lemma_poly_mul_wf(pa, pc);
    assert forall |env: Seq<int>|
        poly_eval(poly_mul(pa, poly_add(pb, pc)), env)
            == poly_eval(poly_add(poly_mul(pa, pb), poly_mul(pa, pc)), env) by {
        lemma_poly_eval_add(pb, pc, env);
        lemma_poly_eval_mul(pa, poly_add(pb, pc), env);
        lemma_poly_eval_mul(pa, pb, env);
        lemma_poly_eval_mul(pa, pc, env);
        lemma_poly_eval_add(poly_mul(pa, pb), poly_mul(pa, pc), env);
        let ea = poly_eval(pa, env);
        let eb = poly_eval(pb, env);
        let ec = poly_eval(pc, env);
        assert(ea * (eb + ec) == ea * eb + ea * ec) by(nonlinear_arith);
    }
}

///  Helper for mul_distributes_left: sorted + identity.
proof fn lemma_mul_distrib_helper(a: &ArithExpr, b: &ArithExpr, c: &ArithExpr)
    ensures poly_mul(arith_to_poly(a), poly_add(arith_to_poly(b), arith_to_poly(c)))
        =~= poly_add(poly_mul(arith_to_poly(a), arith_to_poly(b)), poly_mul(arith_to_poly(a), arith_to_poly(c))),
{
    let pa = arith_to_poly(a);
    let pb = arith_to_poly(b);
    let pc = arith_to_poly(c);
    lemma_arith_to_poly_wf(a);
    lemma_arith_to_poly_wf(b);
    lemma_arith_to_poly_wf(c);
    lemma_poly_add_wf(pb, pc);
    lemma_poly_mul_wf(pa, poly_add(pb, pc));
    lemma_poly_mul_wf(pa, pb);
    lemma_poly_mul_wf(pa, pc);
    lemma_poly_add_wf(poly_mul(pa, pb), poly_mul(pa, pc));
    lemma_mul_distrib_eval(a, b, c);
    lemma_arith_to_poly_vars_sorted(a);
    lemma_arith_to_poly_vars_sorted(b);
    lemma_arith_to_poly_vars_sorted(c);
    lemma_vars_sorted_add(pb, pc);
    lemma_vars_sorted_mul(pa, poly_add(pb, pc));
    lemma_vars_sorted_mul(pa, pb);
    lemma_vars_sorted_mul(pa, pc);
    lemma_vars_sorted_add(poly_mul(pa, pb), poly_mul(pa, pc));
    lemma_same_eval_same_poly(
        poly_mul(pa, poly_add(pb, pc)),
        poly_add(poly_mul(pa, pb), poly_mul(pa, pc)),
    );
}

///  Helper: two polynomials with same poly_eval have same normal form.
proof fn lemma_same_eval_same_poly(
    pa: Seq<(int, Seq<nat>)>,
    pb: Seq<(int, Seq<nat>)>,
)
    requires
        poly_wf(pa), poly_wf(pb),
        poly_vars_sorted(pa), poly_vars_sorted(pb),
        forall |env: Seq<int>| poly_eval(pa, env) == poly_eval(pb, env),
    ensures pa =~= pb,
{
    lemma_poly_identity(pa, pb);
}

impl<const N: usize, const F: usize> Ring for GpuFixedPoint<N, F> {
    open spec fn one() -> Self {
        GpuFixedPoint { expr: ArithExpr::Const(1) }
    }

    open spec fn mul(self, other: Self) -> Self {
        GpuFixedPoint { expr: ArithExpr::Mul(Box::new(self.expr), Box::new(other.expr)) }
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        let pa = arith_to_poly(&a.expr);
        let pb = arith_to_poly(&b.expr);
        lemma_arith_to_poly_wf(&a.expr);
        lemma_arith_to_poly_wf(&b.expr);
        //  arith_to_poly(Mul(a,b)) = poly_mul(pa, pb)
        //  arith_to_poly(Mul(b,a)) = poly_mul(pb, pa)
        //  poly_eval(poly_mul(pa,pb), env) = poly_eval(pa)*poly_eval(pb) = poly_eval(pb)*poly_eval(pa)
        //  = poly_eval(poly_mul(pb,pa), env)
        lemma_poly_mul_wf(pa, pb);
        lemma_poly_mul_wf(pb, pa);
        assert forall |env: Seq<int>|
            poly_eval(poly_mul(pa, pb), env) == poly_eval(poly_mul(pb, pa), env) by {
            lemma_poly_eval_mul(pa, pb, env);
            lemma_poly_eval_mul(pb, pa, env);
            assert(poly_eval(pa, env) * poly_eval(pb, env)
                == poly_eval(pb, env) * poly_eval(pa, env)) by(nonlinear_arith);
        }
        lemma_mul_vars_sorted(&a.expr, &b.expr);
        lemma_mul_vars_sorted(&b.expr, &a.expr);
        lemma_same_eval_same_poly(poly_mul(pa, pb), poly_mul(pb, pa));
        reveal_with_fuel(arith_to_poly, 2);
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        lemma_mul_assoc_helper(&a.expr, &b.expr, &c.expr);
        reveal_with_fuel(arith_to_poly, 3);
    }

    proof fn axiom_mul_one_right(a: Self) {
        let pa = arith_to_poly(&a.expr);
        let one_poly = arith_to_poly(&ArithExpr::Const(1));
        lemma_arith_to_poly_wf(&a.expr);
        lemma_arith_to_poly_wf(&ArithExpr::Const(1));
        lemma_poly_mul_wf(pa, one_poly);
        assert forall |env: Seq<int>|
            poly_eval(poly_mul(pa, one_poly), env) == poly_eval(pa, env) by {
            lemma_poly_eval_mul(pa, one_poly, env);
            //  poly_eval(one_poly, env) = 1 (by computation)
            reveal_with_fuel(poly_eval, 2);
            reveal_with_fuel(mono_eval, 1);
            assert(poly_eval(pa, env) * 1int == poly_eval(pa, env)) by(nonlinear_arith);
        }
        lemma_arith_to_poly_vars_sorted(&a.expr);
        lemma_arith_to_poly_vars_sorted(&ArithExpr::Const(1));
        lemma_vars_sorted_mul(pa, one_poly);
        lemma_same_eval_same_poly(poly_mul(pa, one_poly), pa);
        reveal_with_fuel(arith_to_poly, 2);
    }

    proof fn axiom_mul_zero_right(a: Self) {
        let pa = arith_to_poly(&a.expr);
        lemma_arith_to_poly_wf(&a.expr);
        lemma_poly_mul_wf(pa, seq![]);
        assert forall |env: Seq<int>|
            poly_eval(poly_mul(pa, seq![]), env) == poly_eval(seq![], env) by {
            lemma_poly_eval_mul(pa, seq![], env);
            assert(poly_eval(pa, env) * 0int == 0int) by(nonlinear_arith);
        }
        lemma_arith_to_poly_vars_sorted(&a.expr);
        lemma_vars_sorted_mul(pa, seq![]);
        lemma_same_eval_same_poly(poly_mul(pa, seq![]), seq![]);
        reveal_with_fuel(arith_to_poly, 2);
    }

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        lemma_mul_distrib_helper(&a.expr, &b.expr, &c.expr);
        reveal_with_fuel(arith_to_poly, 3);
    }

    proof fn axiom_one_ne_zero() {
        assert(arith_to_poly(&ArithExpr::Const(1)).len() == 1);
        assert(arith_to_poly(&ArithExpr::Const(0)).len() == 0);
    }

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        reveal_with_fuel(arith_to_poly, 2);
    }
}

//  ── Constructors ───────────────────────────────────────────

impl<const N: usize, const F: usize> GpuFixedPoint<N, F> {
    pub open spec fn from_buffer(buf: nat) -> Self {
        GpuFixedPoint { expr: ArithExpr::Var(buf) }
    }
}

//  ── Test ───────────────────────────────────────────────────

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


///  poly_coeff(poly_neg(p), v) == -poly_coeff(p, v).
proof fn lemma_poly_neg_coeff(p: Seq<(int, Seq<nat>)>, v: Seq<nat>)
    ensures poly_coeff(poly_neg(p), v) == -poly_coeff(p, v),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    lemma_poly_neg_len(p);
    let pt = p.subrange(1, p.len() as int);
    lemma_poly_neg_index(p, 0);
    let np = poly_neg(p);
    if p[0].1 =~= v {
        assert(np[0].1 =~= v);
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

///  Maximum element in a Seq<nat>.
pub open spec fn seq_max_nat(s: Seq<nat>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else {
        let rest_max = seq_max_nat(s.subrange(1, s.len() as int));
        if s[0] > rest_max { s[0] } else { rest_max }
    }
}

proof fn lemma_seq_max_nat_bound(s: Seq<nat>)
    ensures forall |i: int| 0 <= i < s.len() ==> s[i] <= seq_max_nat(s),
    decreases s.len(),
{
    if s.len() > 0 {
        let st = s.subrange(1, s.len() as int);
        lemma_seq_max_nat_bound(st);
        assert forall |i: int| 0 <= i < s.len() implies s[i] <= seq_max_nat(s) by {
            if i == 0 {
            } else {
                assert(s[i] == st[i - 1]);
                assert(st[i - 1] <= seq_max_nat(st));
            }
        }
    }
}

///  Total degree: sum of all term variable-count.
pub open spec fn poly_total_degree(p: Seq<(int, Seq<nat>)>) -> nat
    decreases p.len(),
{
    if p.len() == 0 { 0 }
    else { (p[0].1.len() + poly_total_degree(p.subrange(1, p.len() as int))) as nat }
}

///  Remove first var from each term (divide by env[v0]).
///  Only applied when all terms start with v0.
pub open spec fn poly_factor_out_first_var(p: Seq<(int, Seq<nat>)>) -> Seq<(int, Seq<nat>)>
    decreases p.len(),
{
    if p.len() == 0 { seq![] }
    else {
        seq![(p[0].0, p[0].1.subrange(1, p[0].1.len() as int))]
            + poly_factor_out_first_var(p.subrange(1, p.len() as int))
    }
}

///  Filter: keep only terms whose first var == v0.
pub open spec fn poly_filter_first_var(p: Seq<(int, Seq<nat>)>, v0: nat) -> Seq<(int, Seq<nat>)>
    decreases p.len(),
{
    if p.len() == 0 { seq![] }
    else if p[0].1.len() > 0 && p[0].1[0] == v0 {
        seq![p[0]] + poly_filter_first_var(p.subrange(1, p.len() as int), v0)
    } else {
        poly_filter_first_var(p.subrange(1, p.len() as int), v0)
    }
}

///  poly_filter_first_var preserves wf.
proof fn lemma_poly_filter_wf(p: Seq<(int, Seq<nat>)>, v0: nat)
    requires poly_wf(p),
    ensures poly_wf(poly_filter_first_var(p, v0)),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int
            by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len()
            implies vars_lt(pt[i].1, pt[j].1)
            by { assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]); }
    }
    lemma_poly_filter_wf(pt, v0);
    if p[0].1.len() > 0 && p[0].1[0] == v0 {
        let filtered_tail = poly_filter_first_var(pt, v0);
        let result = seq![p[0]] + filtered_tail;
        //  Need: result is wf. p[0].0 != 0 ✓. filtered_tail is wf ✓.
        //  Need: p[0].1 < all of filtered_tail's var tuples.
        //  filtered_tail contains terms from pt that start with v0.
        //  All such terms have vars > p[0].1 (from wf ordering in p).
        assert forall |i: int| 0 <= i < result.len() implies result[i].0 != 0int by {
            if i == 0 {} else { assert(result[i] == filtered_tail[i-1]); }
        }
        //  sorted: need to show. Z3 has wf(filtered_tail) so filtered_tail is sorted.
        //  Need: p[0].1 < filtered_tail[0].1 (if filtered_tail non-empty).
        //  filtered_tail elements come from pt. pt elements come from p[1:].
        //  All p[k] for k >= 1 have vars_lt(p[0].1, p[k].1).
        //  filtered_tail is a subsequence of pt preserving order.
        //  So filtered_tail[0].1 = pt[j].1 for some j >= 0.
        //  vars_lt(p[0].1, pt[j].1) = vars_lt(p[0].1, p[j+1].1). ✓
        //  But we need to formally connect filtered_tail[0] to some pt[j].
        //  This requires a "filter is subsequence" lemma.
        //  For now, use the fact that wf(filtered_tail) gives internal sorting,
        //  and we need p[0] < filtered_tail[0] specifically.
        assert forall |i: int, j: int| 0 <= i < j < result.len()
            implies vars_lt(result[i].1, result[j].1) by {
            if i > 0 {
                assert(result[i] == filtered_tail[i-1]);
                assert(result[j] == filtered_tail[j-1]);
            } else {
                //  i == 0: result[0] = p[0]. result[j] = filtered_tail[j-1].
                //  Need: vars_lt(p[0].1, filtered_tail[j-1].1).
                //  filtered_tail[j-1] comes from pt, which is a subseq of p[1:].
                //  All elements of filtered_tail are elements of pt.
                //  By wf(p): p[0] < all pt elements, so p[0] < filtered_tail[j-1].
                assert(result[j] == filtered_tail[j-1]);
                //  filtered_tail is a subsequence of pt. Each element of filtered_tail
                //  is an element of pt at some index. Since pt = p[1:], each is some p[k] with k >= 1.
                //  vars_lt(p[0].1, p[k].1) by wf.
                //  But we can't easily get the index k. Use a helper.
                lemma_poly_filter_subseq(pt, v0, j - 1);
                //  This gives: filtered_tail[j-1] == pt[some_k] for some k.
                //  And vars_lt(p[0].1, pt[some_k].1) since pt[some_k] = p[some_k+1].
            }
        }
    }
}

///  poly_filter_first_var has all terms starting with v0.
proof fn lemma_poly_filter_all_start(p: Seq<(int, Seq<nat>)>, v0: nat)
    ensures forall |i: int| 0 <= i < poly_filter_first_var(p, v0).len()
        ==> (#[trigger] poly_filter_first_var(p, v0)[i]).1.len() > 0
            && poly_filter_first_var(p, v0)[i].1[0] == v0,
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_poly_filter_all_start(pt, v0);
    if p[0].1.len() > 0 && p[0].1[0] == v0 {
        let filtered_tail = poly_filter_first_var(pt, v0);
        let result = seq![p[0]] + filtered_tail;
        assert forall |i: int| 0 <= i < result.len()
            implies (#[trigger] result[i]).1.len() > 0 && result[i].1[0] == v0 by {
            if i == 0 {} else { assert(result[i] == filtered_tail[i-1]); }
        }
    }
}

///  poly_filter_first_var has fewer or equal terms.
proof fn lemma_poly_filter_len(p: Seq<(int, Seq<nat>)>, v0: nat)
    ensures poly_filter_first_var(p, v0).len() <= p.len(),
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_poly_filter_len(p.subrange(1, p.len() as int), v0);
    }
}

///  poly_eval of filtered v0-terms: equals v0-contribution of original poly.
///  At env with env[v0] = 0: non-v0 terms eval same, v0-terms eval 0.
///  So poly_eval(p, env) = poly_eval(filter(p, v0), env) + poly_eval(non_v0, env).
///  And poly_eval(filter, env_with_v0=0) = 0.

///  filter is a subsequence: each element of filter(p, v0) is an element of p.
proof fn lemma_poly_filter_subseq(p: Seq<(int, Seq<nat>)>, v0: nat, i: int)
    requires 0 <= i < poly_filter_first_var(p, v0).len(),
    ensures exists |k: int| 0 <= k < p.len() && poly_filter_first_var(p, v0)[i] == p[k],
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    if p[0].1.len() > 0 && p[0].1[0] == v0 {
        if i == 0 {
            //  filter(p)[0] = p[0]. Witness k = 0.
            assert(poly_filter_first_var(p, v0)[0] == p[0]);
        } else {
            //  filter(p)[i] = filter(pt)[i-1]. By IH: filter(pt)[i-1] == pt[k'] for some k'.
            //  pt[k'] = p[k'+1]. So filter(p)[i] = p[k'+1]. Witness k = k'+1.
            lemma_poly_filter_subseq(pt, v0, i - 1);
            let filtered_tail = poly_filter_first_var(pt, v0);
            let result = seq![p[0]] + filtered_tail;
            assert(result[i] == filtered_tail[i - 1]);
            let k_prime: int = choose |k: int| 0 <= k < pt.len() && filtered_tail[i-1] == pt[k];
            assert(pt[k_prime] == p[k_prime + 1]);
        }
    } else {
        //  filter(p) = filter(pt). By IH: filter(pt)[i] == pt[k'] for some k'.
        //  pt[k'] = p[k'+1].
        lemma_poly_filter_subseq(pt, v0, i);
        let k_prime: int = choose |k: int| 0 <= k < pt.len() && poly_filter_first_var(pt, v0)[i] == pt[k];
        assert(pt[k_prime] == p[k_prime + 1]);
    }
}

///  poly_filter_first_var total_degree <= original.
proof fn lemma_poly_filter_total_degree(p: Seq<(int, Seq<nat>)>, v0: nat)
    ensures poly_total_degree(poly_filter_first_var(p, v0)) <= poly_total_degree(p),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_poly_filter_total_degree(pt, v0);
    //  If p[0] is included: filter(p) = [p[0]] + filter(pt).
    //    poly_total_degree = p[0].1.len() + poly_total_degree(filter(pt))
    //                     <= p[0].1.len() + poly_total_degree(pt) = poly_total_degree(p).
    //  If p[0] is excluded: filter(p) = filter(pt).
    //    poly_total_degree = poly_total_degree(filter(pt)) <= poly_total_degree(pt) <= poly_total_degree(p).
    if p[0].1.len() > 0 && p[0].1[0] == v0 {
        //  filter(p) = [p[0]] + filter(pt), total_degree = p[0].1.len() + td(filter(pt))
        //  <= p[0].1.len() + td(pt) = td(p).
        let ft = poly_filter_first_var(pt, v0);
        assert(poly_filter_first_var(p, v0) =~= seq![p[0]] + ft);
        let fp = poly_filter_first_var(p, v0);
        assert(fp =~= seq![p[0]] + ft);
        assert(fp.subrange(1, fp.len() as int) =~= ft);
        reveal_with_fuel(poly_total_degree, 2);
    } else {
        //  filter(p) = filter(pt), total_degree <= td(pt) <= td(p).
    }
}

///  poly_factor_out_first_var preserves len.
proof fn lemma_poly_factor_len(p: Seq<(int, Seq<nat>)>)
    ensures poly_factor_out_first_var(p).len() == p.len(),
    decreases p.len(),
{
    if p.len() > 0 { lemma_poly_factor_len(p.subrange(1, p.len() as int)); }
}

///  Element-wise characterization of poly_factor_out_first_var.
proof fn lemma_poly_factor_index(p: Seq<(int, Seq<nat>)>, i: int)
    requires 0 <= i < p.len(), p[i].1.len() > 0,
    ensures ({
        let pf = poly_factor_out_first_var(p);
        pf[i] == (p[i].0, p[i].1.subrange(1, p[i].1.len() as int))
    }),
    decreases p.len(),
{
    lemma_poly_factor_len(p);
    if i == 0 {
    } else {
        let pt = p.subrange(1, p.len() as int);
        assert(pt[i-1] == p[i]);
        assert(pt[i-1].1.len() > 0);
        lemma_poly_factor_index(pt, i - 1);
        let pf = poly_factor_out_first_var(p);
        let pft = poly_factor_out_first_var(pt);
        assert(pf =~= seq![(p[0].0, p[0].1.subrange(1, p[0].1.len() as int))] + pft);
        assert(pf[i] == pft[i-1]);
    }
}

///  poly_factor_out_first_var preserves wf when all terms share the same first var.
proof fn lemma_poly_factor_wf(p: Seq<(int, Seq<nat>)>, v0: nat)
    requires
        poly_wf(p), p.len() > 0,
        forall |i: int| 0 <= i < p.len() ==> p[i].1.len() > 0 && p[i].1[0] == v0,
    ensures poly_wf(poly_factor_out_first_var(p)),
    decreases p.len(),
{
    if p.len() <= 1 {
        lemma_poly_factor_len(p);
        return;
    }
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int
            by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len()
            implies vars_lt(pt[i].1, pt[j].1)
            by { assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]); }
    }
    assert forall |i: int| 0 <= i < pt.len()
        implies pt[i].1.len() > 0 && pt[i].1[0] == v0
        by { assert(pt[i] == p[i+1]); }
    lemma_poly_factor_wf(pt, v0);
    let pf = poly_factor_out_first_var(p);
    let pft = poly_factor_out_first_var(pt);
    lemma_poly_factor_len(p);
    lemma_poly_factor_len(pt);
    assert(pf =~= seq![(p[0].0, p[0].1.subrange(1, p[0].1.len() as int))] + pft);
    assert forall |i: int| 0 <= i < pf.len() implies pf[i].0 != 0int by {
        if i == 0 {} else { assert(pf[i] == pft[i-1]); }
    }
    assert forall |i: int, j: int| 0 <= i < j < pf.len()
        implies vars_lt(pf[i].1, pf[j].1) by {
        if i > 0 {
            assert(pf[i] == pft[i-1]);
            assert(pf[j] == pft[j-1]);
        } else {
            assert(pf[j] == pft[j-1]);
            assert(vars_lt(p[0].1, p[j].1));
            assert(p[0].1[0] == v0 && p[j].1[0] == v0);
            //  vars_lt([v0, a...], [v0, b...]) with equal first → vars_lt(a, b)
            assert(p[0].1.subrange(1, p[0].1.len() as int) =~= pf[0].1);
            assert(p[j].1.subrange(1, p[j].1.len() as int) =~= pf[j].1) by {
                lemma_poly_factor_index(p, j);
            }
        }
    }
}

///  Total degree decreases by at least 1 after factoring when all terms have non-empty vars.
proof fn lemma_poly_factor_total_degree(p: Seq<(int, Seq<nat>)>)
    requires p.len() > 0,
        forall |i: int| 0 <= i < p.len() ==> p[i].1.len() > 0,
    ensures poly_total_degree(poly_factor_out_first_var(p)) < poly_total_degree(p),
    decreases p.len(),
{
    //  poly_total_degree(p) = Σ p[i].1.len() >= p.len() (each term has len >= 1)
    //  poly_total_degree(factored) = Σ (p[i].1.len() - 1) = poly_total_degree(p) - p.len()
    //  Since p.len() >= 1: poly_total_degree(factored) < poly_total_degree(p).
    //
    //  Prove by induction: each step removes 1 from the first term's contribution.
    let pf = poly_factor_out_first_var(p);
    lemma_poly_factor_len(p);
    if p.len() == 1 {
        //  poly_total_degree(p) = p[0].1.len() >= 1
        //  factored has 1 term with vars len = p[0].1.len() - 1
        lemma_poly_factor_index(p, 0);
        reveal_with_fuel(poly_total_degree, 2);
    } else {
        let pt = p.subrange(1, p.len() as int);
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].1.len() > 0
            by { assert(pt[i] == p[i+1]); }
        lemma_poly_factor_total_degree(pt);
        //  IH: poly_total_degree(factored_tail) < poly_total_degree(tail)
        //  poly_total_degree(p) = p[0].1.len() + poly_total_degree(tail)
        //  poly_total_degree(pf) = (p[0].1.len()-1) + poly_total_degree(factored_tail)
        //  < p[0].1.len() + poly_total_degree(tail) = poly_total_degree(p)
        lemma_poly_factor_index(p, 0);
        lemma_poly_factor_len(pt);
        let pft = poly_factor_out_first_var(pt);
        assert(pf =~= seq![(p[0].0, p[0].1.subrange(1, p[0].1.len() as int))] + pft);
        assert(pf.subrange(1, pf.len() as int) =~= pft);
    }
}

///  Factoring relation: poly_eval(p, env) = env[v0] * poly_eval(factored, env)
///  when all terms start with v0.
proof fn lemma_poly_eval_factor(p: Seq<(int, Seq<nat>)>, env: Seq<int>, v0: nat)
    requires forall |i: int| 0 <= i < p.len() ==> p[i].1.len() > 0 && p[i].1[0] == v0,
    ensures poly_eval(p, env) == ({
        let ev0 = if (v0 as int) < env.len() { env[v0 as int] } else { 0int };
        ev0 * poly_eval(poly_factor_out_first_var(p), env)
    }),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    assert forall |i: int| 0 <= i < pt.len() implies pt[i].1.len() > 0 && pt[i].1[0] == v0
        by { assert(pt[i] == p[i+1]); }
    lemma_poly_eval_factor(pt, env, v0);
    reveal_with_fuel(mono_eval, 2);
    let ev0 = if (v0 as int) < env.len() { env[v0 as int] } else { 0int };
    let pf = poly_factor_out_first_var(p);
    let pft = poly_factor_out_first_var(pt);
    //  poly_eval(p, env) = p[0].0 * mono_eval(p[0].1, env) + poly_eval(pt, env)
    //  mono_eval([v0, rest], env) = ev0 * mono_eval(rest, env)
    //  poly_eval(pt, env) = ev0 * poly_eval(pft, env) [IH]
    //  = p[0].0 * ev0 * mono_eval(rest, env) + ev0 * poly_eval(pft, env)
    //  = ev0 * (p[0].0 * mono_eval(rest, env) + poly_eval(pft, env))
    //  = ev0 * poly_eval(pf, env)
    assert(p[0].1[0] == v0);
    let rest = p[0].1.subrange(1, p[0].1.len() as int);
    assert(pf =~= seq![(p[0].0, rest)] + pft);
    assert(pf.subrange(1, pf.len() as int) =~= pft) by { lemma_poly_factor_len(p); lemma_poly_factor_len(pt); }
    assert(p[0].0 * (ev0 * mono_eval(rest, env)) + ev0 * poly_eval(pft, env)
        == ev0 * (p[0].0 * mono_eval(rest, env) + poly_eval(pft, env)))
        by(nonlinear_arith);
}

///  If vars contains v and env[v] = 0 (or v out of range), mono_eval = 0.
proof fn lemma_mono_eval_zero_var(vars: Seq<nat>, env: Seq<int>, v: nat)
    requires
        vars.len() > 0, vars[0] == v,
        (v as int) >= env.len() || env[v as int] == 0int,
    ensures mono_eval(vars, env) == 0int,
{
    reveal_with_fuel(mono_eval, 2);
    //  mono_eval(vars, env) = (if v < env.len() { env[v] } else { 0 }) * mono_eval(rest, env)
    //  The first factor is 0 (by precondition). 0 * anything = 0.
    let first = if (v as int) < env.len() { env[v as int] } else { 0int };
    assert(first == 0int);
    assert(0int * mono_eval(vars.subrange(1, vars.len() as int), env) == 0int)
        by(nonlinear_arith);
}

///  mono_eval doesn't depend on env[v0] when no var equals v0.
proof fn lemma_mono_eval_v0_indep(
    vars: Seq<nat>, env1: Seq<int>, env2: Seq<int>, v0: nat,
)
    requires
        env1.len() == env2.len(),
        forall |i: int| 0 <= i < env1.len() && i != v0 as int ==> env1[i] == env2[i],
        forall |i: int| 0 <= i < vars.len() ==> vars[i] != v0,
    ensures mono_eval(vars, env1) == mono_eval(vars, env2),
    decreases vars.len(),
{
    if vars.len() == 0 { return; }
    lemma_mono_eval_v0_indep(vars.subrange(1, vars.len() as int), env1, env2, v0);
    reveal_with_fuel(mono_eval, 2);
}

///  In a wf polynomial, if term p[i] has p[i].1[0] > v0 and vars are sorted,
///  then no element of p[i].1 equals v0. We encode this by requiring that the
///  polynomial's vars tuples are sorted (non-decreasing), which holds for all
///  polynomials produced by arith_to_poly (vars_merge always produces sorted output).
pub open spec fn poly_vars_sorted(p: Seq<(int, Seq<nat>)>) -> bool {
    forall |i: int, j: int| #![trigger p[i].1[j]]
        0 <= i < p.len() && 0 < j < p[i].1.len()
        ==> p[i].1[j - 1] <= p[i].1[j]
}

///  The non-v0 part of poly_eval is v0-independent:
///  poly_eval(p, env1) - poly_eval(filter(p,v0), env1)
///  == poly_eval(p, env2) - poly_eval(filter(p,v0), env2)
///  when env1 and env2 differ only at v0 and poly_vars_sorted(p).
proof fn lemma_non_v0_eval_independent(
    p: Seq<(int, Seq<nat>)>, env1: Seq<int>, env2: Seq<int>, v0: nat,
)
    requires
        poly_vars_sorted(p),
        env1.len() == env2.len(),
        forall |i: int| 0 <= i < env1.len() && i != v0 as int ==> env1[i] == env2[i],
        //  all terms have first var >= v0 (non-v0 terms have first var > v0)
        forall |i: int| 0 <= i < p.len() && p[i].1.len() > 0 ==> p[i].1[0] >= v0,
    ensures
        poly_eval(p, env1) - poly_eval(poly_filter_first_var(p, v0), env1)
        == poly_eval(p, env2) - poly_eval(poly_filter_first_var(p, v0), env2),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_vars_sorted_tail(p);
    assert forall |i: int| 0 <= i < pt.len() && pt[i].1.len() > 0
        implies pt[i].1[0] >= v0 by { assert(pt[i] == p[i+1]); }
    lemma_non_v0_eval_independent(pt, env1, env2, v0);
    if p[0].1.len() > 0 && p[0].1[0] == v0 {
        //  p[0] is a v0-term. It's in the filter. Non-v0 part doesn't include it.
        //  filter(p) = [p[0]] + filter(pt). Differences cancel p[0] term.
        let fp = poly_filter_first_var(p, v0);
        let fpt = poly_filter_first_var(pt, v0);
        assert(fp =~= seq![p[0]] + fpt);
        assert(fp.subrange(1, fp.len() as int) =~= fpt) by { lemma_poly_filter_len(pt, v0); }
    } else {
        //  p[0] is NOT a v0-term. It's NOT in the filter. Non-v0 part includes it.
        //  poly_eval(p) = p[0] eval + poly_eval(pt)
        //  poly_eval(filter(p)) = poly_eval(filter(pt))
        //  Difference = p[0] eval + (poly_eval(pt) - poly_eval(filter(pt)))
        //  Need: p[0] eval is same at env1 and env2.
        //  p[0] is not a v0-term. If p[0].1 is empty: mono_eval = 1, same at both. ✓
        //  If p[0].1 non-empty: p[0].1[0] > v0 (not starting with v0 and non-empty).
        //  Actually p[0].1[0] might equal v0 if the filter condition failed for another reason.
        //  Filter checks: p[0].1.len() > 0 && p[0].1[0] == v0. If this is false:
        //  either p[0].1.len() == 0 (constant, v0-independent) or p[0].1[0] != v0.
        //  If p[0].1[0] != v0: by poly_vars_sorted, all vars >= p[0].1[0].
        //  If p[0].1[0] > v0: all vars > v0 ≥ v0, so no var equals v0.
        //  If p[0].1[0] < v0: vars could still contain v0 later.
        //  But v0 = p_outer[0].1[0] = smallest first var. p[0].1[0] can't be < v0
        //  because... actually it CAN be, since p might be a sub-polynomial.
        //
        //  Hmm, we need: if p[0].1[0] != v0 AND p[0].1 is sorted, then either:
        //  (a) p[0].1[0] > v0 → all vars > v0, none = v0 (by sorted)
        //  (b) p[0].1[0] < v0 → vars could contain v0 later
        //  Case (b) would break v0-independence!
        //
        //  In our specific use case: v0 = p_original[0].1[0] which is the SMALLEST
        //  first var in the original polynomial. After filtering, the non-v0 terms
        //  have first var > v0 (since v0 is the smallest and they don't equal v0).
        //  But this isn't captured by the lemma's preconditions.
        //
        //  FIX: add precondition that non-v0 terms have first var > v0.
        //  Or: add precondition that p's terms have first var >= v0.
        //  In our use case: all terms of p have first var >= v0.
        if p[0].1.len() == 0 {
            //  Constant term: mono_eval = 1, same at both envs.
        } else {
            //  p[0].1[0] != v0 (not a v0-term).
            //  By poly_vars_sorted: vars[j] >= vars[0] for all j.
            //  If vars[0] > v0: all vars > v0, none = v0.
            //  Need: mono_eval(p[0].1, env1) == mono_eval(p[0].1, env2).
            //  Requires: no var in p[0].1 equals v0.
            //  This holds when vars[0] > v0 (all vars >= vars[0] > v0).
            //  But we can't prove vars[0] > v0 in general.
            //  Add as precondition.
            //  p[0].1[0] >= v0 (precondition) and != v0 (not a v0-term) → > v0
            assert(p[0].1[0] > v0);
            lemma_sorted_vars_no_v0(p[0].1, v0);
            lemma_mono_eval_v0_indep(p[0].1, env1, env2, v0);
        }
    }
}

///  poly_neg preserves poly_vars_sorted (doesn't change vars tuples).
proof fn lemma_vars_sorted_neg(p: Seq<(int, Seq<nat>)>)
    requires poly_vars_sorted(p),
    ensures poly_vars_sorted(poly_neg(p)),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_vars_sorted_tail(p);
    lemma_vars_sorted_neg(pt);
    lemma_poly_neg_len(p);
    let np = poly_neg(p);
    assert forall |i: int, j: int| #![trigger np[i].1[j]] 0 <= i < np.len() && 0 < j < np[i].1.len()
        implies np[i].1[j-1] <= np[i].1[j] by {
        lemma_poly_neg_index(p, i);
        //  np[i] = (-p[i].0, p[i].1). So np[i].1 = p[i].1.
    }
}

///  poly_add preserves poly_vars_sorted (terms keep their vars).
proof fn lemma_vars_sorted_add(
    p: Seq<(int, Seq<nat>)>, q: Seq<(int, Seq<nat>)>,
)
    requires poly_vars_sorted(p), poly_vars_sorted(q),
    ensures poly_vars_sorted(poly_add(p, q)),
    decreases p.len() + q.len(),
{
    if p.len() == 0 || q.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    let qt = q.subrange(1, q.len() as int);
    lemma_vars_sorted_tail(p);
    lemma_vars_sorted_tail(q);
    if p[0].1 =~= q[0].1 {
        lemma_vars_sorted_add(pt, qt);
        let c = p[0].0 + q[0].0;
        if c != 0int {
            let r = seq![(c, p[0].1)] + poly_add(pt, qt);
            assert forall |i: int, j: int| #![trigger r[i].1[j]] 0 <= i < r.len() && 0 < j < r[i].1.len()
                implies r[i].1[j-1] <= r[i].1[j] by {
                if i == 0 {
                    //  r[0].1 = p[0].1 — sorted by poly_vars_sorted(p)
                } else {
                    assert(r[i] == poly_add(pt, qt)[i-1]);
                }
            }
        }
    } else if vars_lt(p[0].1, q[0].1) {
        lemma_vars_sorted_add(pt, q);
        let r = seq![p[0]] + poly_add(pt, q);
        assert forall |i: int, j: int| #![trigger r[i].1[j]] 0 <= i < r.len() && 0 < j < r[i].1.len()
            implies r[i].1[j-1] <= r[i].1[j] by {
            if i == 0 {} else { assert(r[i] == poly_add(pt, q)[i-1]); }
        }
    } else {
        lemma_vars_sorted_add(p, qt);
        let r = seq![q[0]] + poly_add(p, qt);
        assert forall |i: int, j: int| #![trigger r[i].1[j]] 0 <= i < r.len() && 0 < j < r[i].1.len()
            implies r[i].1[j-1] <= r[i].1[j] by {
            if i == 0 {} else { assert(r[i] == poly_add(p, qt)[i-1]); }
        }
    }
}

///  poly_vars_sorted for tail of p.
proof fn lemma_vars_sorted_tail(p: Seq<(int, Seq<nat>)>)
    requires poly_vars_sorted(p), p.len() > 0,
    ensures poly_vars_sorted(p.subrange(1, p.len() as int)),
{
    let pt = p.subrange(1, p.len() as int);
    assert forall |i: int, j: int| #![trigger pt[i].1[j]]
        0 <= i < pt.len() && 0 < j < pt[i].1.len()
        implies pt[i].1[j-1] <= pt[i].1[j] by {
        assert(pt[i] == p[i+1]);
    }
}

///  poly_vars_sorted for poly_filter_first_var.
proof fn lemma_vars_sorted_filter(p: Seq<(int, Seq<nat>)>, v0: nat)
    requires poly_vars_sorted(p),
    ensures poly_vars_sorted(poly_filter_first_var(p, v0)),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_vars_sorted_tail(p);
    lemma_vars_sorted_filter(pt, v0);
    if p[0].1.len() > 0 && p[0].1[0] == v0 {
        let ft = poly_filter_first_var(pt, v0);
        let result = seq![p[0]] + ft;
        assert forall |i: int, j: int| #![trigger result[i].1[j]] 0 <= i < result.len() && 0 < j < result[i].1.len()
            implies result[i].1[j-1] <= result[i].1[j] by {
            if i == 0 {} else { assert(result[i] == ft[i-1]); }
        }
    }
}

///  poly_vars_sorted for poly_factor_out_first_var.
proof fn lemma_vars_sorted_factor(p: Seq<(int, Seq<nat>)>)
    requires poly_vars_sorted(p),
        forall |i: int| 0 <= i < p.len() ==> p[i].1.len() > 0,
    ensures poly_vars_sorted(poly_factor_out_first_var(p)),
    decreases p.len(),
{
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_vars_sorted_tail(p);
    assert forall |i: int| 0 <= i < pt.len() implies pt[i].1.len() > 0
        by { assert(pt[i] == p[i+1]); }
    lemma_vars_sorted_factor(pt);
    let pf = poly_factor_out_first_var(p);
    let pft = poly_factor_out_first_var(pt);
    lemma_poly_factor_len(p);
    assert(pf =~= seq![(p[0].0, p[0].1.subrange(1, p[0].1.len() as int))] + pft);
    assert forall |i: int, j: int| #![trigger pf[i].1[j]] 0 <= i < pf.len() && 0 < j < pf[i].1.len()
        implies pf[i].1[j-1] <= pf[i].1[j] by {
        if i == 0 {
            //  pf[0].1 = p[0].1[1:]. If j > 0: pf[0].1[j-1] = p[0].1[j], pf[0].1[j] = p[0].1[j+1].
            //  By poly_vars_sorted(p): p[0].1[j] <= p[0].1[j+1]. ✓
            assert(pf[0].1[j] == p[0].1[j + 1]);
            if j > 0 { assert(pf[0].1[j - 1] == p[0].1[j]); }
        } else {
            assert(pf[i] == pft[i-1]);
        }
    }
}

///  In sorted vars with first element > v0, no element equals v0.
///  Helper: in a sorted sequence, all elements >= first element.
proof fn lemma_sorted_seq_ge_first(s: Seq<nat>, k: int)
    requires
        s.len() > 0, 0 <= k < s.len(),
        forall |j: int| #![trigger s[j]] 0 < j < s.len() ==> s[j-1] <= s[j],
    ensures s[k] >= s[0],
    decreases k,
{
    if k == 0 {} else {
        lemma_sorted_seq_ge_first(s, k - 1);
    }
}

proof fn lemma_sorted_vars_no_v0(vars: Seq<nat>, v0: nat)
    requires
        vars.len() > 0, vars[0] > v0,
        forall |j: int| #![trigger vars[j]] 0 < j < vars.len() ==> vars[j-1] <= vars[j],
    ensures forall |j: int| 0 <= j < vars.len() ==> vars[j] != v0,
{
    assert forall |j: int| 0 <= j < vars.len() implies vars[j] != v0 by {
        lemma_sorted_seq_ge_first(vars, j);
        //  vars[j] >= vars[0] > v0, so vars[j] > v0, so vars[j] != v0.
    }
}

//  Zero-padding: extending env with zeros doesn't change mono_eval.
proof fn lemma_mono_eval_zero_pad(
    vars: Seq<nat>,
    env: Seq<int>,
    new_len: nat,
)
    requires new_len >= env.len(),
    ensures
        mono_eval(vars, Seq::new(new_len, |i: int|
            if i < env.len() { env[i] } else { 0int }))
        == mono_eval(vars, env),
    decreases vars.len(),
{
    let env2 = Seq::new(new_len, |i: int|
        if i < env.len() { env[i] } else { 0int });
    if vars.len() == 0 {
    } else {
        let tail = vars.subrange(1, vars.len() as int);
        lemma_mono_eval_zero_pad(tail, env, new_len);
        //  For vars[0]: val in env2 == val in env.
        //  if vars[0] < env.len(): env2[vars[0]] = env[vars[0]]. Same.
        //  if env.len() <= vars[0] < new_len: env2[vars[0]] = 0, env out of range = 0. Same.
        //  if vars[0] >= new_len: both out of range = 0. Same.
    }
}

//  Zero-padding: extending env with zeros doesn't change poly_eval.
proof fn lemma_poly_eval_zero_pad(
    p: Seq<(int, Seq<nat>)>,
    env: Seq<int>,
    new_len: nat,
)
    requires new_len >= env.len(),
    ensures
        poly_eval(p, Seq::new(new_len, |i: int|
            if i < env.len() { env[i] } else { 0int }))
        == poly_eval(p, env),
    decreases p.len(),
{
    if p.len() == 0 {
    } else {
        let tail = p.subrange(1, p.len() as int);
        lemma_poly_eval_zero_pad(tail, env, new_len);
        lemma_mono_eval_zero_pad(p[0].1, env, new_len);
    }
}

//  Modular congruence: mono_eval(vars, env[v0:=r]) == mono_eval(vars, env) + r * m
//  when env[v0] = 0. Returns the quotient m.
proof fn lemma_mono_eval_mod_r(
    vars: Seq<nat>,
    env: Seq<int>,
    v0: nat,
    r: int,
) -> (m: int)
    requires
        (v0 as int) < env.len(),
        env[v0 as int] == 0int,
    ensures
        mono_eval(vars, env.update(v0 as int, r))
            == mono_eval(vars, env) + r * m,
    decreases vars.len(),
{
    let env2 = env.update(v0 as int, r);
    if vars.len() == 0 {
        0int
    } else {
        let w = vars[0];
        let tail = vars.subrange(1, vars.len() as int);
        let m_tail = lemma_mono_eval_mod_r(tail, env, v0, r);
        if w == v0 {
            assert(mono_eval(vars, env) == 0int) by(nonlinear_arith)
                requires mono_eval(vars, env) == 0int * mono_eval(tail, env);
            let m_out = mono_eval(tail, env2);
            assert(mono_eval(vars, env2) == mono_eval(vars, env) + r * m_out)
                by(nonlinear_arith)
                requires
                    mono_eval(vars, env2) == r * mono_eval(tail, env2),
                    mono_eval(vars, env) == 0int,
                    m_out == mono_eval(tail, env2);
            m_out
        } else {
            //  env2 = env.update(v0, r). For w != v0:
            //  if w < env.len(): env2[w] = env[w] (update at different index).
            //  if w >= env.len(): both out of range, mono_eval uses 0.
            let vw = if (w as int) < env.len() { env[w as int] } else { 0int };
            if (w as int) < env.len() {
                assert(env2[w as int] == env[w as int]);
            }
            let m_out = vw * m_tail;
            assert(mono_eval(vars, env2) == mono_eval(vars, env) + r * m_out)
                by(nonlinear_arith)
                requires
                    mono_eval(vars, env2) == vw * mono_eval(tail, env2),
                    mono_eval(vars, env) == vw * mono_eval(tail, env),
                    mono_eval(tail, env2) == mono_eval(tail, env) + r * m_tail,
                    m_out == vw * m_tail;
            m_out
        }
    }
}

//  Modular congruence: poly_eval(p, env[v0:=r]) == poly_eval(p, env) + r * q
//  when env[v0] = 0. Returns the quotient q.
proof fn lemma_poly_eval_mod_r(
    p: Seq<(int, Seq<nat>)>,
    env: Seq<int>,
    v0: nat,
    r: int,
) -> (q: int)
    requires
        (v0 as int) < env.len(),
        env[v0 as int] == 0int,
    ensures
        poly_eval(p, env.update(v0 as int, r))
            == poly_eval(p, env) + r * q,
    decreases p.len(),
{
    let env2 = env.update(v0 as int, r);
    if p.len() == 0 {
        0int
    } else {
        let tail = p.subrange(1, p.len() as int);
        let q_tail = lemma_poly_eval_mod_r(tail, env, v0, r);
        let m_mono = lemma_mono_eval_mod_r(p[0].1, env, v0, r);
        let q_out = p[0].0 * m_mono + q_tail;
        assert(poly_eval(p, env2) == poly_eval(p, env) + r * q_out)
            by(nonlinear_arith)
            requires
                poly_eval(p, env2) == p[0].0 * mono_eval(p[0].1, env2) + poly_eval(tail, env2),
                poly_eval(p, env) == p[0].0 * mono_eval(p[0].1, env) + poly_eval(tail, env),
                mono_eval(p[0].1, env2) == mono_eval(p[0].1, env) + r * m_mono,
                poly_eval(tail, env2) == poly_eval(tail, env) + r * q_tail,
                q_out == p[0].0 * m_mono + q_tail;
        q_out
    }
}

proof fn lemma_wf_poly_nonzero_eval(p: Seq<(int, Seq<nat>)>)
    requires poly_wf(p), p.len() > 0, poly_vars_sorted(p),
    ensures exists |env: Seq<int>| poly_eval(p, env) != 0int,
    decreases poly_total_degree(p), p.len(),
{
    //  Case 1: constant term (p[0].1 is empty)
    if p[0].1.len() == 0 {
        let env = Seq::<int>::empty();
        lemma_poly_eval_at_empty(p);
        assert(poly_eval(p, env) == p[0].0);
        return;
    }

    //  Case 2: single non-constant term
    //  p = [(c, vars)], c != 0, vars non-empty.
    //  Use env = [1, 1, ..., 1] large enough to cover all variable indices.
    //  Need: for all i in 0..vars.len(), vars[i] < env.len().
    //  Choose env.len() to be larger than any possible nat value in vars.
    //  Since vars elements are nat, we pick env large enough by using
    //  a bound on variable indices. Use a Seq with all 1s of arbitrary large size.
    if p.len() == 1 {
        //  Evaluate at env = [1; N] where N is large enough.
        //  For a single term, poly_eval = c * mono_eval(vars, env).
        //  If all indices in vars are < N, mono_eval = 1, so poly_eval = c != 0.
        //  We construct N as max(vars) + 1, but need to prove vars[i] <= max(vars).
        //  Since we don't track sortedness of individual vars tuples,
        //  use a helper: for any vars, there exists a large enough env.
        //  Actually, just use an env of length = sum of all indices + vars.len() (overkill but works).
        //  Simpler: use the fact that nat values in a finite Seq have a maximum.
        let vars = p[0].1;
        //  Use spec function to find max variable index
        let ghost max_v: nat = seq_max_nat(vars);
        lemma_seq_max_nat_bound(vars);
        let env = Seq::new((max_v + 1) as nat, |_i: int| 1int);
        assert forall |i: int| 0 <= i < vars.len()
            implies (vars[i] as int) < env.len() by {
        }
        lemma_mono_eval_ones(vars, env);
        reveal_with_fuel(poly_eval, 2);
        assert(poly_eval(p, env) == p[0].0);
        return;
    }

    //  Case 3: multi-term, no constant term.
    //  IH on tail, then try env with first var = 0 to zero out first term.
    let pt = p.subrange(1, p.len() as int);
    assert(poly_wf(pt)) by {
        assert forall |i: int| 0 <= i < pt.len() implies pt[i].0 != 0int
            by { assert(pt[i] == p[i+1]); }
        assert forall |i: int, j: int| 0 <= i < j < pt.len()
            implies vars_lt(pt[i].1, pt[j].1)
            by { assert(pt[i] == p[i+1]); assert(pt[j] == p[j+1]); }
    }
    lemma_vars_sorted_tail(p);
    lemma_wf_poly_nonzero_eval(pt);
    let env_ih: Seq<int> = choose |env: Seq<int>| poly_eval(pt, env) != 0int;
    let v0 = p[0].1[0];
    let env2 = if (v0 as int) < env_ih.len() {
        env_ih.update(v0 as int, 0int)
    } else {
        env_ih
    };
    //  Try env_ih directly
    if poly_eval(p, env_ih) != 0int {
        return;
    }

    //  Try env2 (v0 = 0): zeroes first term
    if poly_eval(p, env2) != 0int {
        return;
    }

    //  Both give 0. Key insight:
    //  At env2 (v0=0): poly_eval(p, env2) = poly_eval(pt, env2) = 0
    //    (first term zeroed since it starts with v0)
    //  At env_ih: poly_eval(pt, env_ih) != 0 but poly_eval(p, env_ih) = 0
    //
    //  ALL terms in p have non-empty vars (no constant term, case 1 excluded).
    //  p[0].1[0] = v0 (smallest first variable).
    //  All terms in p have first var >= v0.
    //
    //  At env2 (v0=0): every term whose vars contains v0 evaluates to 0
    //  (mono_eval includes a factor of env[v0] = 0).
    //  Terms that DON'T contain v0 at all: their first var > v0 (by sorted wf).
    //  These terms are unaffected by setting v0=0.
    //
    //  Since poly_eval(p, env2) = 0 and only non-v0 terms contribute at env2:
    //  The non-v0 terms sum to 0 at env2 = env_ih[v0:=0].
    //  But these non-v0 terms also sum to 0 at env_ih (same values for non-v0 vars).
    //
    //  Wait, the non-v0 terms evaluate the SAME at env_ih and env2 (they don't use v0).
    //  So non-v0 terms contribute the same amount S at both envs.
    //  At env2: S = 0 (poly_eval(p, env2) = 0 and v0-terms contribute 0).
    //  At env_ih: S + v0_terms_contribution = 0, so v0_terms_contribution = 0.
    //  But poly_eval(pt, env_ih) != 0 and pt includes the non-v0 terms (which sum to S=0)
    //  plus v0-terms (excluding p[0]).
    //  So v0-terms in pt at env_ih = poly_eval(pt, env_ih) - S = poly_eval(pt, env_ih) != 0.
    //  But we also said v0-terms contribution to p at env_ih = 0.
    //  v0-terms in p = p[0] + v0-terms in pt.
    //  So p[0] contribution + v0-terms-in-pt contribution = 0 at env_ih.
    //  And v0-terms-in-pt contribution at env_ih = poly_eval(pt, env_ih) != 0.
    //  So p[0] contribution = -poly_eval(pt, env_ih) != 0.
    //
    //  All v0-terms (including p[0]) have mono_eval that includes env[v0] as a factor.
    //  Factor out env[v0]:
    //  At env_ih: total v0-contribution = env_ih[v0] * (factored sum) = 0
    //  If env_ih[v0] = 0: then env2 = env_ih (nothing changed), contradicting
    //    poly_eval(pt, env_ih) != 0 and poly_eval(pt, env2) = 0.
    //  If env_ih[v0] != 0: factored sum = 0.
    //  The "factored sum" is poly_eval of p with v0 removed from each term
    //  = poly_eval(p_factored, env) where p_factored has lower total degree.
    //
    //  Hmm, p_factored needs to be wf. And factoring only works for terms with v0 at the START.
    //
    //  Since ALL terms have non-empty vars and p[0].1[0] = v0 (smallest):
    //  All terms with v0 in vars: their vars is [v0, ...]. Since v0 is the smallest var
    //  index and the vars are sorted, v0 appears at the START of each such term.
    //  Wait, not necessarily — a term could have vars [1, 3] where v0 = 0, and this term
    //  has first var = 1 > 0 = v0, so it does NOT contain v0.
    //
    //  So terms split into: those starting with v0, and those with first var > v0.
    //  Terms with first var > v0 DON'T contain v0 (since vars are sorted, all entries >= first var > v0).
    //  Terms starting with v0 have v0 as first entry.
    //
    //  We showed: terms NOT containing v0 sum to S = 0 at env2 = env_ih[v0:=0].
    //  And they sum to the SAME S = 0 at env_ih (they don't use v0).
    //
    //  Terms containing v0 (starting with v0): factor out env[v0].
    //  mono_eval([v0, rest...], env) = env[v0] * mono_eval(rest, env).
    //  So their contribution = env[v0] * Σ coeff_i * mono_eval(rest_i, env).
    //  = env[v0] * poly_eval(p_factored, env)
    //  where p_factored has each v0-term with its first v0 removed.
    //
    //  At env_ih: env[v0] * poly_eval(p_factored, env_ih) + S = 0
    //  → env[v0] * poly_eval(p_factored, env_ih) = -S = 0
    //  → env[v0] = 0 or poly_eval(p_factored, env_ih) = 0
    //
    //  If env[v0] = 0: env2 = env_ih, contradiction with pt being nonzero at env_ih but zero at env2.
    //  Hmm wait, if env_ih[v0] was already 0, then env2 = env_ih (the update is a no-op).
    //  Then poly_eval(pt, env2) = poly_eval(pt, env_ih) != 0, contradicting our else branch
    //  assumption that poly_eval(p, env2) = 0. Let's check: poly_eval(p, env2) includes p[0]
    //  which also has v0 with value 0, so p[0] contributes 0. And poly_eval(p, env2) =
    //  0 + poly_eval(pt, env2) = poly_eval(pt, env_ih) != 0. So poly_eval(p, env2) != 0.
    //  But we're in the branch where poly_eval(p, env2) == 0. Contradiction!
    //  So env_ih[v0] != 0 and the env2 case was actually handled above.
    //
    //  Wait, if v0 >= env_ih.len(), then env_ih[v0] is effectively 0 (mono_eval uses 0 for
    //  out-of-range indices). And env2 = env_ih (no update). Same argument applies.
    //
    //  So the contradiction is: if we reach this branch, env_ih[v0] effectively = 0,
    //  which means env2 = env_ih, which means poly_eval(p, env2) = poly_eval(p, env_ih) = 0.
    //  But poly_eval(p, env2) includes poly_eval(pt, env2) = poly_eval(pt, env_ih) != 0
    //  plus p[0]'s contribution (= 0 since v0 = 0).
    //  So poly_eval(p, env2) = poly_eval(pt, env_ih) != 0. CONTRADICTION!

    //  Formalize: if we're here, poly_eval(p, env2) == 0 and poly_eval(p, env_ih) == 0.
    //  Show: if env_ih[v0] effectively = 0, then env2 = env_ih (or equivalent),
    //  and poly_eval(pt, env2) = poly_eval(pt, env_ih) != 0, so poly_eval(p, env2) != 0.
    //  Contradiction with poly_eval(p, env2) == 0.
    //
    //  If env_ih[v0] effectively != 0, then factored sum = 0 gives recursion with lower
    //  total degree. But we'd need to construct p_factored.
    //
    //  For now, handle the case env_ih[v0] effectively = 0:
    if (v0 as int) >= env_ih.len() || env_ih[v0 as int] == 0int {
        //  env_ih[v0] is effectively 0 (out of range or explicitly 0).
        //  mono_eval(p[0].1, env_ih): p[0].1[0] = v0, and env_ih[v0] = 0.
        //  So the first factor in mono_eval is 0, making the whole product 0.
        //  poly_eval(p, env_ih) = p[0].0 * 0 + poly_eval(pt, env_ih) = poly_eval(pt, env_ih) != 0.
        //  But we assumed poly_eval(p, env_ih) == 0 above. Contradiction!
        //  So the first 'if' branch should have returned. We never reach here.
        //  Prove: mono_eval(p[0].1, env_ih) = 0.
        //  Contradiction: poly_eval(p, env_ih) should be 0 (from if-check above)
        //  but p[0] contributes 0 (v0=0) and pt contributes != 0 (from IH).
        //  So poly_eval(p, env_ih) = 0 + poly_eval(pt, env_ih) != 0. Contradiction!
        //  Use env_ih as our non-zero witness (the if-check above must have returned).
        assert(p[0].1[0] == v0);
        lemma_mono_eval_zero_var(p[0].1, env_ih, v0);
        assert(p[0].0 * mono_eval(p[0].1, env_ih) == 0int) by(nonlinear_arith)
            requires mono_eval(p[0].1, env_ih) == 0int;
        //  poly_eval(p, env_ih) = p[0].0*mono(p[0].1, env_ih) + poly_eval(pt, env_ih)
        //                       = 0 + poly_eval(pt, env_ih) = poly_eval(pt, env_ih) != 0
        //  So poly_eval(p, env_ih) != 0, which means the earlier if-check should have
        //  caught it and returned. Since we're here, Z3 sees false.
        assert(poly_eval(p, env_ih) != 0int);
    } else {
        //  env_ih[v0] != 0. Use filter + factor.
        //  p_v0 = v0-terms of p. p_fac = factor(p_v0). Lower total_degree.
        //  IH on p_fac → env_fac. poly_eval(p, env_fac) = env_fac[v0] * poly_eval(p_fac, env_fac) + S.
        //  S = non-v0 terms eval. We showed S = 0 at env_ih's non-v0 values.
        //  Use env_fac but override non-v0 vars to env_ih's values.
        //  At that combined env: S = 0, poly_eval(p) = env[v0] * poly_eval(p_fac, env).
        //  If env_fac[v0] != 0 and poly_eval(p_fac, combined_env) != 0: done.
        //  The combined env preserves p_fac's non-zero eval IF p_fac only depends on
        //  v0-related vars... which we can't guarantee.
        //
        //  Cleanest approach: build env with v0 = env_ih[v0] != 0 and everything else = env_ih values.
        //  At this env: S = 0 (same non-v0 as env_ih).
        //  poly_eval(p, env_ih) = env_ih[v0] * poly_eval(p_fac_at_env_ih_values) + 0 = 0.
        //  So poly_eval(p_fac_at_env_ih_values) = 0 / env_ih[v0] = 0.
        //  Not useful directly — p_fac is zero at env_ih.
        //
        //  But IH on p_fac gives SOME env_fac where p_fac != 0.
        //  At env_fac: poly_eval(p, env_fac) INCLUDES non-v0 terms which might not be 0.
        //  First 'if' above already checked poly_eval(p, env_fac) and it was 0 or non-zero.
        //  If non-zero: already returned. So poly_eval(p, env_fac) == 0.
        //
        //  We need: env where BOTH poly_eval(p_v0, env) != 0 AND non_v0_terms(env) == 0.
        //  non_v0_terms = 0 when non-v0 vars match env_ih's values.
        //  poly_eval(p_v0, env) != 0 when env[v0] != 0 AND poly_eval(p_fac, env) != 0.
        //  We need env where: (a) non-v0 vars = env_ih values, (b) v0 such that p_fac != 0.
        //  p_fac at env_ih's values with varying v0: a univariate polynomial in v0.
        //  It's zero at v0 = env_ih[v0] (shown above). It's the zero polynomial or has roots.
        //  If zero polynomial: poly_eval(p_v0, env) = env[v0] * 0 = 0 for all v0.
        //    Then poly_eval(p, env_ih) = 0 + S = 0 + 0 = 0. Consistent but useless.
        //    But poly_eval(pt, env_ih) != 0. And poly_eval(p, env_ih) = p[0]_eval + poly_eval(pt, env_ih) = 0.
        //    So p[0]_eval = -poly_eval(pt, env_ih) != 0. p[0] IS a v0-term.
        //    poly_eval(p_v0, env_ih) = p[0]_eval + other_v0_terms_eval.
        //    If poly_eval(p_v0, env_ih) == 0: other v0 terms cancel p[0] at env_ih.
        //    But poly_eval(p_fac, env_ih) = poly_eval(p_v0, env_ih) / env_ih[v0].
        //    If poly_eval(p_v0, env_ih) = env_ih[v0] * poly_eval(p_fac, env_ih) = 0:
        //    Then env_ih[v0] != 0 implies poly_eval(p_fac, env_ih) = 0. ✓ consistent.
        //
        //  p_fac is zero at env_ih (with all non-v0 vars fixed).
        //  p_fac is non-zero SOMEWHERE (IH). So it's not identically zero.
        //  Viewed as function of ALL vars: non-zero. Viewed as function of v0 only
        //  (non-v0 vars fixed to env_ih): might be identically zero if it depends on other vars.
        //
        //  If p_fac depends only on v0: it's a univariate polynomial, non-zero somewhere.
        //  At env_ih it's zero. So it has a root at env_ih[v0]. Try v0 = env_ih[v0] + 1.
        //  If non-zero: poly_eval(p, env with v0=env_ih[v0]+1, others=env_ih) != 0.
        //
        //  If p_fac depends on other vars too: it's zero at env_ih's full assignment.
        //  But non-zero at env_fac's assignment. Different non-v0 values → different eval.
        //  Can't use env_ih's non-v0 values for the S = 0 guarantee.
        //
        //  CLEANEST FIX: just try 4 more specific envs built from env_ih by varying v0.
        //  Use: env_ih (v0=original), env2 (v0=0), env3 (v0=env_ih[v0]+1), env4 (v0=env_ih[v0]*2).
        //  poly_eval(p, env3) uses S = 0 (non-v0 vars from env_ih) and new v0 value.
        //  = env3[v0] * poly_eval(p_fac, env3) where env3 has v0 = env_ih[v0]+1.
        //  env3[v0] = env_ih[v0]+1 != 0 (env_ih[v0] >= 0 as nat... wait, env values are int, could be negative).
        //  Actually env_ih[v0] is int, could be any value. env_ih[v0]+1 could be 0 if env_ih[v0] = -1.
        //  Use v0 = 1 instead: env_ih[v0:=1].
        //  poly_eval(p, env_ih[v0:=1]) = 1 * poly_eval(p_fac, env_ih[v0:=1]) + 0.
        //  If poly_eval(p_fac, env_ih[v0:=1]) != 0: done!
        //  If == 0: poly_eval(p_fac, env_ih[v0:=0]) = poly_eval(p_fac, env2) and
        //    poly_eval(p_fac, env_ih[v0:=1]) = 0, poly_eval(p_fac, env_ih) = 0.
        //    Three roots in v0 (0, 1, env_ih[v0]).
        //    Wait, env_ih[v0:=0] might not equal env2 if v0 was out of range.
        //    And env_ih[v0] might equal 0 or 1. Let me think more carefully.
        //
        //  We have env_ih[v0] != 0 (this else branch).
        //  env2 = env_ih[v0:=0]. poly_eval(p_fac, env_ih[v0:=0]) might be anything.
        //  poly_eval(p_fac, env_ih) is with env_ih[v0] as the v0 value.
        //  We showed: env_ih[v0] * poly_eval(p_fac, env_ih) = 0 and env_ih[v0] != 0.
        //  So poly_eval(p_fac, env_ih) = 0. One root of f(x) = poly_eval(p_fac, env_ih[v0:=x]) at x = env_ih[v0].
        //  Try x = 1: f(1). If != 0: done.
        //  f has total_degree(p_fac) which is < total_degree(p).
        //  f has at most total_degree(p)-1 roots. We tried 1 value (env_ih[v0]).
        //  If f(1) = 0: we have 2 roots. Need at most total_degree(p_fac) - 1 more tries.
        //  Try x = 2, 3, ... total_degree(p) values. One must work.
        //  But we can't iterate.
        //
        //  WE CAN RECURSE! poly_eval(p, env_ih[v0:=x]) = x * f(x).
        //  f has total_degree < total_degree(p). f(env_ih[v0]) = 0.
        //  By IH on total_degree: f is non-zero somewhere.
        //  Actually f might be identically zero in v0 if it depends on other vars.
        //  We need: exists env, f(env) != 0 AND env[v0] != 0.
        //  This is EXACTLY the constrained helper problem!
        //
        //  OK I'll write the constrained helper. It recurses on total_degree.
        //  Each level: factor out v0 from v0-terms, get lower total_degree.
        //  Base: total_degree = 0 → constant, non-zero, any v0 works.
        //
        //  But the helper needs all terms starting with v0. And after factoring,
        //  some terms might not start with v0 anymore.
        //
        //  DIFFERENT APPROACH: don't use the helper at all. Instead, observe:
        //  poly_eval(p_fac, env_fac) != 0 (from IH).
        //  poly_eval(p, env_fac) = env_fac[v0] * poly_eval(p_fac, env_fac) + S_at_env_fac.
        //  We checked: poly_eval(p, env_fac) == 0 (first if-else). So:
        //  env_fac[v0] * poly_eval(p_fac, env_fac) + S_at_env_fac = 0.
        //  S_at_env_fac = -env_fac[v0] * poly_eval(p_fac, env_fac).
        //
        //  If env_fac[v0] == 0: S_at_env_fac = 0. Try env_fac[v0:=1]:
        //    poly_eval(p, env_fac[v0:=1]) = 1 * poly_eval(p_fac, env_fac[v0:=1]) + S_at_env_fac_v0_1.
        //    S_at_env_fac_v0_1 = S_at_env_fac = 0 (non-v0 terms, v0-independent).
        //    Wait, are non-v0 terms v0-independent? They don't START with v0.
        //    But they might USE v0 in later positions (vars [w, v0, ...] where w > v0).
        //    Oh wait — these terms were NOT filtered out by poly_filter_first_var.
        //    They ARE in p but NOT in p_v0. Their mono_eval CAN depend on v0.
        //    So S IS v0-dependent for these terms!
        //
        //  HOWEVER: a term with vars [w, v0, ...] where w > v0 has first var w > v0.
        //  Since vars are sorted, w > v0 means w is the minimum element. All elements >= w > v0.
        //  But v0 < w. So v0 can't appear in the vars at all! vars[0] = w > v0, and
        //  vars is sorted, so all entries >= w > v0. No entry equals v0.
        //
        //  WAIT: this IS the key insight I missed! In a SORTED vars tuple, if the first
        //  element is w > v0, then ALL elements are >= w > v0. So v0 CANNOT appear.
        //  These non-v0 terms truly don't use v0!
        //
        //  So S IS v0-independent! Setting v0 to any value doesn't change S.
        //  S = S_at_env_fac = -env_fac[v0] * poly_eval(p_fac, env_fac) for the fixed non-v0 values.
        //
        //  If env_fac[v0] == 0: S = 0. poly_eval(p, env_fac[v0:=1]) = 1 * poly_eval(p_fac, env_fac[v0:=1]).
        //  If poly_eval(p_fac, env_fac[v0:=1]) != 0: done!
        //  If == 0: 2 roots (v0=0 non-zero, v0=1 zero, v0=env_ih[v0] zero)... root bound needed.
        //
        //  If env_fac[v0] != 0: S = -env_fac[v0] * nonzero != 0.
        //  poly_eval(p, env_fac[v0:=0]) = 0 * anything + S = S != 0. Done!
        //
        //  THIS WORKS! If env_fac[v0] != 0: use env_fac[v0:=0] to get S != 0.
        //  If env_fac[v0] == 0: S = 0. Use env_fac[v0:=1] to get 1 * poly_eval(p_fac, env_fac[v0:=1]).
        //  Need poly_eval(p_fac, env_fac[v0:=1]) != 0. p_fac has lower total_degree.
        //  If p_fac doesn't use v0: same eval, non-zero. Done.
        //  If p_fac uses v0: eval changed. Need root bound...
        //  But p_fac using v0 means some p_fac term has v0 in its vars.
        //  After factoring, p_fac terms come from p_v0 terms with first v0 removed.
        //  Original: [v0, v0, ...] → factored: [v0, ...]. So yes, v0 can appear.
        //
        //  For env_fac[v0] != 0 case: use env_fac[v0:=0]!
        let p_v0 = poly_filter_first_var(p, v0);
        lemma_poly_filter_wf(p, v0);
        lemma_poly_filter_all_start(p, v0);
        assert(p_v0.len() > 0) by { reveal_with_fuel(poly_filter_first_var, 2); }
        let p_fac = poly_factor_out_first_var(p_v0);
        lemma_poly_factor_wf(p_v0, v0);
        lemma_poly_factor_total_degree(p_v0);
        lemma_poly_filter_total_degree(p, v0);
        lemma_poly_factor_len(p_v0);
        assert(poly_total_degree(p_fac) < poly_total_degree(p));
        lemma_vars_sorted_filter(p, v0);
        lemma_vars_sorted_factor(p_v0);
        lemma_wf_poly_nonzero_eval(p_fac);
        let env_fac: Seq<int> = choose |env: Seq<int>| poly_eval(p_fac, env) != 0int;
        //  Try env_fac directly — it might already witness p != 0
        if poly_eval(p, env_fac) != 0int {
            return;
        }

        let ev0_fac = if (v0 as int) < env_fac.len() { env_fac[v0 as int] } else { 0int };

        if ev0_fac != 0int {
            //  env_fac[v0] != 0. poly_eval(p_v0, env_fac) = ev0_fac * poly_eval(p_fac, env_fac) != 0.
            //  poly_eval(p, env_fac) = poly_eval(p_v0, env_fac) + S_at_env_fac.
            //  We checked: if poly_eval(p, env_fac) != 0: first 'if' above returned.
            //  So poly_eval(p, env_fac) == 0. S_at_env_fac = -poly_eval(p_v0, env_fac) != 0.
            //  S is v0-independent (non-v0 terms don't use v0, since sorted vars with first > v0).
            //  At env_fac[v0:=0]: v0-terms contribute 0 (env[v0]=0). S unchanged.
            //  poly_eval(p, env_fac[v0:=0]) = 0 + S_at_env_fac != 0.
            let env_v0z = if (v0 as int) < env_fac.len() {
                env_fac.update(v0 as int, 0int)
            } else { env_fac };
            //  At env_v0z: v0 = 0, so all v0-terms (whose mono_eval includes factor env[v0]=0) give 0.
            //  Non-v0 terms: same as at env_fac (don't use v0).
            //  poly_eval(p, env_v0z) = S_at_env_fac != 0.
            //
            //  But we need Z3 to see this. The factoring relation:
            //  poly_eval(p_v0, env_v0z) = 0 * poly_eval(p_fac, env_v0z) = 0.
            lemma_poly_eval_factor(p_v0, env_fac, v0);
            lemma_poly_eval_factor(p_v0, env_v0z, v0);
            //  S = poly_eval(p) - poly_eval(p_v0) is v0-independent.
            //  At env_fac: S = 0 - ev0_fac * poly_eval(p_fac, env_fac) != 0.
            //  At env_v0z: poly_eval(p_v0, env_v0z) = 0 (v0=0).
            //  poly_eval(p, env_v0z) = 0 + S = S != 0.
            //  Need env_fac and env_v0z to have same length and differ only at v0.
            if (v0 as int) < env_fac.len() {
                assert(env_v0z.len() == env_fac.len());
                assert forall |i: int| 0 <= i < env_fac.len() && i != v0 as int
                    implies env_v0z[i] == env_fac[i] by {}
                //  All terms have first var >= v0 (v0 is the smallest first var in p).
                assert forall |i: int| 0 <= i < p.len() && p[i].1.len() > 0
                    implies p[i].1[0] >= v0 by {
                    if i > 0 {
                        assert(vars_lt(p[0].1, p[i].1));
                        if p[i].1[0] < v0 {
                            lemma_vars_lt_asymm(p[0].1, p[i].1);
                        }
                    }
                }
                lemma_non_v0_eval_independent(p, env_fac, env_v0z, v0);
                //  S at env_fac = S at env_v0z.
                //  poly_eval(p, env_v0z) - poly_eval(p_v0, env_v0z)
                //  == poly_eval(p, env_fac) - poly_eval(p_v0, env_fac)
                //  poly_eval(p_v0, env_v0z) = 0 (from factoring with v0=0).
                //  poly_eval(p, env_v0z) = 0 + (poly_eval(p, env_fac) - poly_eval(p_v0, env_fac))
                //  = 0 - ev0_fac * poly_eval(p_fac, env_fac) != 0.
                assert(poly_eval(p_v0, env_v0z) == 0int) by(nonlinear_arith)
                    requires poly_eval(p_v0, env_v0z) == 0int * poly_eval(p_fac, env_v0z);
                assert(poly_eval(p_v0, env_fac) == ev0_fac * poly_eval(p_fac, env_fac));
                assert(ev0_fac * poly_eval(p_fac, env_fac) != 0int) by(nonlinear_arith)
                    requires ev0_fac != 0int, poly_eval(p_fac, env_fac) != 0int;
                //  The v0-independence chain:
                //  poly_eval(p, env_fac) - poly_eval(p_v0, env_fac)
                //  == poly_eval(p, env_v0z) - poly_eval(p_v0, env_v0z)
                //  0 - (ev0_fac * p_fac_eval) == poly_eval(p, env_v0z) - 0
                //  poly_eval(p, env_v0z) == -(ev0_fac * p_fac_eval) != 0
                //  Connect p_v0 to poly_filter_first_var(p, v0)
                assert(p_v0 =~= poly_filter_first_var(p, v0));
                //  From v0-independence:
                //  poly_eval(p, env_fac) - poly_eval(p_v0, env_fac)
                //  == poly_eval(p, env_v0z) - poly_eval(p_v0, env_v0z)
                //  Substituting known values:
                //  0 - (ev0_fac * poly_eval(p_fac, env_fac))
                //  == poly_eval(p, env_v0z) - 0
                assert(poly_eval(p, env_fac) == 0int);
                assert(poly_eval(p, env_v0z) ==
                    poly_eval(p, env_fac) - poly_eval(p_v0, env_fac)
                    + poly_eval(p_v0, env_v0z));
                assert(poly_eval(p, env_v0z) != 0int);
            } else {
                //  v0 out of range: env_v0z = env_fac (no change).
                //  But then ev0_fac = 0 (out of range gives 0). Contradicts ev0_fac != 0.
                assert(false);  // unreachable
            }
        } else {
            //  env_fac[v0] == 0 (or v0 out of range). Use modular congruence.
            //  A = poly_eval(p_fac, env_fac) != 0.
            //  Pick r = |A| + 1 >= 2. r cannot divide A (since |r| > |A| > 0).
            //  By modular congruence: poly_eval(p_fac, env0[v0:=r]) = A + r * Q.
            //  If this were 0: A = -r*Q, so r | A. Contradiction.
            //  So poly_eval(p_fac, env_r) != 0. And r != 0.
            //  poly_eval(p, env_r) = r * poly_eval(p_fac, env_r) + S.
            //  S = 0 (v0-independent, was 0 at env0). So poly_eval(p, env_r) != 0.
            let a_val = poly_eval(p_fac, env_fac);
            let r_val: int = if a_val >= 0int { a_val + 1 } else { -a_val + 1 };

            //  Build env0: env_fac zero-padded so v0 is in range, with env0[v0] = 0.
            let new_len: nat = if (v0 as int) < env_fac.len() {
                env_fac.len()
            } else {
                (v0 + 1) as nat
            };
            let env0: Seq<int> = if (v0 as int) < env_fac.len() {
                env_fac
            } else {
                lemma_poly_eval_zero_pad(p_fac, env_fac, new_len);
                lemma_poly_eval_zero_pad(p, env_fac, new_len);
                Seq::new(new_len, |i: int|
                    if i < env_fac.len() { env_fac[i] } else { 0int })
            };
            assert((v0 as int) < env0.len());
            assert(env0[v0 as int] == 0int);
            assert(poly_eval(p_fac, env0) == a_val);
            assert(poly_eval(p, env0) == 0int);

            //  Apply modular congruence: poly_eval(p_fac, env0[v0:=r]) = A + r*Q.
            let q_mod = lemma_poly_eval_mod_r(p_fac, env0, v0, r_val);
            let env_r = env0.update(v0 as int, r_val);

            //  Contradiction if poly_eval(p_fac, env_r) == 0:
            //  A + r*Q == 0 → A = -r*Q.
            //  If Q == 0: A == 0. Contradiction with A != 0.
            //  If Q != 0: |A| = |r|*|Q| >= |r| = |A|+1 > |A|. Contradiction.
            assert(poly_eval(p_fac, env_r) != 0int) by(nonlinear_arith)
                requires
                    poly_eval(p_fac, env_r) == a_val + r_val * q_mod,
                    a_val != 0int,
                    r_val == (if a_val >= 0int { a_val + 1 } else { -a_val + 1 });

            //  r_val != 0 (r_val = |A| + 1 >= 2).
            assert(r_val != 0int) by(nonlinear_arith)
                requires a_val != 0int,
                    r_val == (if a_val >= 0int { a_val + 1 } else { -a_val + 1 });

            //  Factoring: poly_eval(p_v0, env_r) = r * poly_eval(p_fac, env_r) != 0.
            lemma_poly_eval_factor(p_v0, env_r, v0);
            assert(poly_eval(p_v0, env_r) != 0int) by(nonlinear_arith)
                requires
                    poly_eval(p_v0, env_r) == r_val * poly_eval(p_fac, env_r),
                    r_val != 0int,
                    poly_eval(p_fac, env_r) != 0int;

            //  v0-independence: S at env0 == S at env_r.
            //  At env0 (v0=0): poly_eval(p_v0, env0) = 0 * ... = 0.
            //  S_env0 = poly_eval(p, env0) - poly_eval(p_v0, env0) = 0 - 0 = 0.
            //  So S_env_r = 0, meaning poly_eval(p, env_r) = poly_eval(p_v0, env_r) != 0.
            lemma_poly_eval_factor(p_v0, env0, v0);
            assert(poly_eval(p_v0, env0) == 0int) by(nonlinear_arith)
                requires poly_eval(p_v0, env0) == 0int * poly_eval(p_fac, env0);

            assert(env_r.len() == env0.len());
            assert forall |i: int| 0 <= i < env0.len() && i != v0 as int
                implies env_r[i] == env0[i] by {}
            assert forall |i: int| 0 <= i < p.len() && p[i].1.len() > 0
                implies p[i].1[0] >= v0 by {
                if i > 0 {
                    assert(vars_lt(p[0].1, p[i].1));
                    if p[i].1[0] < v0 { lemma_vars_lt_asymm(p[0].1, p[i].1); }
                }
            }
            lemma_non_v0_eval_independent(p, env0, env_r, v0);
            //  poly_eval(p, env_r) - poly_eval(p_v0, env_r)
            //  == poly_eval(p, env0) - poly_eval(p_v0, env0) == 0 - 0 == 0
            assert(poly_eval(p, env_r) == poly_eval(p_v0, env_r));
            assert(poly_eval(p, env_r) != 0int);
        }
    }
}

proof fn lemma_poly_identity(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    requires
        poly_wf(p), poly_wf(q),
        poly_vars_sorted(p), poly_vars_sorted(q),
        forall |env: Seq<int>| poly_eval(p, env) == poly_eval(q, env),
    ensures p =~= q,
{
    lemma_poly_neg_wf(q);
    lemma_vars_sorted_neg(q);
    let nq = poly_neg(q);
    lemma_poly_add_wf(p, nq);
    lemma_vars_sorted_add(p, nq);
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

//  ══════════════════════════════════════════════════════════════
//  Coefficient bound infrastructure
//  ══════════════════════════════════════════════════════════════

///  Upper bound on max |coefficient| in arith_to_poly(e).
///  Always >= Σ|coefficients|, hence >= max|individual coefficient|.
pub open spec fn expr_coeff_bound(e: &ArithExpr) -> int
    decreases e,
{
    match e {
        ArithExpr::Const(c) => if *c >= 0 { *c } else { -*c },
        ArithExpr::Var(_) => 1,
        ArithExpr::Add(a, b) => expr_coeff_bound(a) + expr_coeff_bound(b),
        ArithExpr::Sub(a, b) => expr_coeff_bound(a) + expr_coeff_bound(b),
        ArithExpr::Mul(a, b) => expr_coeff_bound(a) * expr_coeff_bound(b),
        _ => 0,
    }
}

///  expr_coeff_bound is always >= 0.
pub proof fn lemma_expr_coeff_bound_nonneg(e: &ArithExpr)
    ensures expr_coeff_bound(e) >= 0,
    decreases e,
{
    reveal_with_fuel(expr_coeff_bound, 2);
    match e {
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) => {
            lemma_expr_coeff_bound_nonneg(a);
            lemma_expr_coeff_bound_nonneg(b);
        },
        ArithExpr::Mul(a, b) => {
            lemma_expr_coeff_bound_nonneg(a);
            lemma_expr_coeff_bound_nonneg(b);
        },
        _ => {},
    }
}

///  Sum of absolute values of polynomial coefficients.
pub open spec fn poly_sum_abs(p: Seq<(int, Seq<nat>)>) -> int
    decreases p.len(),
{
    if p.len() == 0 { 0int }
    else {
        (if p[0].0 >= 0 { p[0].0 } else { -p[0].0 })
        + poly_sum_abs(p.subrange(1, p.len() as int))
    }
}

///  poly_sum_abs is always >= 0.
pub proof fn lemma_poly_sum_abs_nonneg(p: Seq<(int, Seq<nat>)>)
    ensures poly_sum_abs(p) >= 0,
    decreases p.len(),
{
    if p.len() > 0 {
        lemma_poly_sum_abs_nonneg(p.subrange(1, p.len() as int));
    }
}

///  Each individual coefficient is bounded by poly_sum_abs.
pub proof fn lemma_poly_sum_abs_bounds_individual(p: Seq<(int, Seq<nat>)>, k: int)
    requires 0 <= k < p.len(),
    ensures p[k].0 >= -poly_sum_abs(p), p[k].0 <= poly_sum_abs(p),
    decreases p.len(),
{
    lemma_poly_sum_abs_nonneg(p);
    if k == 0 {
        lemma_poly_sum_abs_nonneg(p.subrange(1, p.len() as int));
    } else {
        lemma_poly_sum_abs_bounds_individual(p.subrange(1, p.len() as int), k - 1);
        assert(p.subrange(1, p.len() as int)[k-1] == p[k]);
    }
}

///  poly_sum_abs of a prepended element.
proof fn lemma_poly_sum_abs_prepend(head: (int, Seq<nat>), tail: Seq<(int, Seq<nat>)>)
    ensures poly_sum_abs(seq![head] + tail) ==
        (if head.0 >= 0 { head.0 } else { -head.0 }) + poly_sum_abs(tail),
{
    let s = seq![head] + tail;
    assert(s.len() > 0);
    assert(s[0] == head);
    assert(s.subrange(1, s.len() as int) =~= tail);
    reveal_with_fuel(poly_sum_abs, 2);
}

///  Triangle inequality for integers: |a + b| <= |a| + |b|.
proof fn lemma_abs_triangle(a: int, b: int)
    ensures
        (if a + b >= 0 { a + b } else { -(a + b) })
        <= (if a >= 0 { a } else { -a }) + (if b >= 0 { b } else { -b }),
{}

///  poly_neg preserves poly_sum_abs.
proof fn lemma_poly_neg_sum_abs(p: Seq<(int, Seq<nat>)>)
    ensures poly_sum_abs(poly_neg(p)) == poly_sum_abs(p),
    decreases p.len(),
{
    reveal_with_fuel(poly_sum_abs, 2);
    reveal_with_fuel(poly_neg, 2);
    if p.len() == 0 {
    } else {
        let pt = p.subrange(1, p.len() as int);
        lemma_poly_neg_sum_abs(pt);
        let np = poly_neg(p);
        let npt = poly_neg(pt);
        //  np = [(-p[0].0, p[0].1)] + npt
        //  poly_sum_abs unfolds on np: |np[0].0| + poly_sum_abs(np.subrange(1,...))
        //  np.subrange(1,...) =~= npt
        assert(np.subrange(1, np.len() as int) =~= npt);
        //  |(-x)| == |x|
        assert((if np[0].0 >= 0 { np[0].0 } else { -np[0].0 })
            == (if p[0].0 >= 0 { p[0].0 } else { -p[0].0 }));
    }
}

///  poly_add: sum_abs of result <= sum of inputs' sum_abs.
proof fn lemma_poly_add_sum_abs(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    ensures poly_sum_abs(poly_add(p, q)) <= poly_sum_abs(p) + poly_sum_abs(q),
    decreases p.len() + q.len(),
{
    reveal_with_fuel(poly_add, 2);
    reveal_with_fuel(poly_sum_abs, 2);
    lemma_poly_sum_abs_nonneg(p);
    lemma_poly_sum_abs_nonneg(q);
    if p.len() == 0 { return; }
    if q.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    let qt = q.subrange(1, q.len() as int);
    lemma_poly_sum_abs_nonneg(pt);
    lemma_poly_sum_abs_nonneg(qt);
    if p[0].1 =~= q[0].1 {
        let c = p[0].0 + q[0].0;
        lemma_poly_add_sum_abs(pt, qt);
        let rest = poly_add(pt, qt);
        if c == 0 {
            //  result = rest. rest <= sa(pt) + sa(qt) <= sa(p) + sa(q).
        } else {
            lemma_abs_triangle(p[0].0, q[0].0);
            lemma_poly_sum_abs_prepend((c, p[0].1), rest);
        }
    } else if vars_lt(p[0].1, q[0].1) {
        lemma_poly_add_sum_abs(pt, q);
        lemma_poly_sum_abs_prepend(p[0], poly_add(pt, q));
    } else {
        lemma_poly_add_sum_abs(p, qt);
        lemma_poly_sum_abs_prepend(q[0], poly_add(p, qt));
    }
}

///  poly_insert: sum_abs of result <= |c| + sum_abs(p).
proof fn lemma_poly_insert_sum_abs(
    c: int, v: Seq<nat>,
    p: Seq<(int, Seq<nat>)>,
)
    ensures poly_sum_abs(poly_insert(c, v, p))
        <= (if c >= 0 { c } else { -c }) + poly_sum_abs(p),
    decreases p.len(),
{
    reveal_with_fuel(poly_insert, 2);
    lemma_poly_sum_abs_nonneg(p);
    reveal_with_fuel(poly_sum_abs, 2);
    if c == 0 { return; }
    if p.len() == 0 { return; }
    let pt = p.subrange(1, p.len() as int);
    lemma_poly_sum_abs_nonneg(pt);
    if v =~= p[0].1 {
        let nc = c + p[0].0;
        if nc == 0 {
            //  result = pt <= |c| + sa(p) since sa(p) = |p[0].0| + sa(pt) >= sa(pt)
        } else {
            lemma_abs_triangle(c, p[0].0);
            lemma_poly_sum_abs_prepend((nc, v), pt);
        }
    } else if vars_lt(v, p[0].1) {
        lemma_poly_sum_abs_prepend((c, v), p);
    } else {
        lemma_poly_insert_sum_abs(c, v, pt);
        lemma_poly_sum_abs_prepend(p[0], poly_insert(c, v, pt));
    }
}

///  mono_mul_poly: sum_abs of result <= |c| * sum_abs(q).
proof fn lemma_mono_mul_sum_abs(
    c: int, vars: Seq<nat>,
    q: Seq<(int, Seq<nat>)>,
)
    ensures poly_sum_abs(mono_mul_poly(c, vars, q))
        <= (if c >= 0 { c } else { -c }) * poly_sum_abs(q),
    decreases q.len(),
{
    reveal_with_fuel(mono_mul_poly, 2);
    reveal_with_fuel(poly_sum_abs, 2);
    lemma_poly_sum_abs_nonneg(q);
    if c == 0 || q.len() == 0 {
    } else {
        let nc = c * q[0].0;
        let nv = vars_merge(vars, q[0].1);
        let qt = q.subrange(1, q.len() as int);
        let rest = mono_mul_poly(c, vars, qt);
        lemma_mono_mul_sum_abs(c, vars, qt);
        lemma_poly_insert_sum_abs(nc, nv, rest);
        lemma_poly_sum_abs_nonneg(qt);
        lemma_poly_sum_abs_nonneg(rest);
        assert(poly_sum_abs(mono_mul_poly(c, vars, q))
            <= (if c >= 0 { c } else { -c }) * poly_sum_abs(q))
            by(nonlinear_arith)
            requires
                poly_sum_abs(poly_insert(nc, nv, rest))
                    <= (if nc >= 0 { nc } else { -nc }) + poly_sum_abs(rest),
                poly_sum_abs(rest)
                    <= (if c >= 0 { c } else { -c }) * poly_sum_abs(qt),
                nc == c * q[0].0,
                poly_sum_abs(q) == (if q[0].0 >= 0 { q[0].0 } else { -q[0].0 })
                    + poly_sum_abs(qt),
                poly_sum_abs(qt) >= 0, poly_sum_abs(rest) >= 0,
                mono_mul_poly(c, vars, q) == poly_insert(nc, nv, rest);
    }
}

///  poly_mul: sum_abs of result <= sum_abs(p) * sum_abs(q).
proof fn lemma_poly_mul_sum_abs(
    p: Seq<(int, Seq<nat>)>,
    q: Seq<(int, Seq<nat>)>,
)
    ensures poly_sum_abs(poly_mul(p, q)) <= poly_sum_abs(p) * poly_sum_abs(q),
    decreases p.len(),
{
    reveal_with_fuel(poly_mul, 2);
    if p.len() == 0 {
    } else {
        let pt = p.subrange(1, p.len() as int);
        let mono = mono_mul_poly(p[0].0, p[0].1, q);
        let rest = poly_mul(pt, q);
        lemma_mono_mul_sum_abs(p[0].0, p[0].1, q);
        lemma_poly_mul_sum_abs(pt, q);
        lemma_poly_add_sum_abs(mono, rest);
        lemma_poly_sum_abs_nonneg(q);
        lemma_poly_sum_abs_nonneg(pt);
        lemma_poly_sum_abs_nonneg(mono);
        lemma_poly_sum_abs_nonneg(rest);
        assert(poly_sum_abs(poly_mul(p, q)) <= poly_sum_abs(p) * poly_sum_abs(q))
            by(nonlinear_arith)
            requires
                poly_sum_abs(poly_add(mono, rest))
                    <= poly_sum_abs(mono) + poly_sum_abs(rest),
                poly_sum_abs(mono)
                    <= (if p[0].0 >= 0 { p[0].0 } else { -p[0].0 }) * poly_sum_abs(q),
                poly_sum_abs(rest) <= poly_sum_abs(pt) * poly_sum_abs(q),
                poly_sum_abs(p) == (if p[0].0 >= 0 { p[0].0 } else { -p[0].0 })
                    + poly_sum_abs(pt),
                poly_sum_abs(q) >= 0, poly_sum_abs(pt) >= 0,
                poly_sum_abs(mono) >= 0, poly_sum_abs(rest) >= 0,
                poly_mul(p, q) == poly_add(mono, rest);
    }
}

///  arith_to_poly: sum_abs bounded by expr_coeff_bound.
pub proof fn lemma_arith_to_poly_sum_abs(e: &ArithExpr)
    ensures poly_sum_abs(arith_to_poly(e)) <= expr_coeff_bound(e),
    decreases e,
{
    reveal_with_fuel(expr_coeff_bound, 2);
    reveal_with_fuel(poly_sum_abs, 2);
    reveal_with_fuel(arith_to_poly, 2);
    match e {
        ArithExpr::Const(c) => {},
        ArithExpr::Var(n) => {},
        ArithExpr::Add(a, b) => {
            lemma_arith_to_poly_sum_abs(a);
            lemma_arith_to_poly_sum_abs(b);
            lemma_poly_add_sum_abs(arith_to_poly(a), arith_to_poly(b));
        },
        ArithExpr::Sub(a, b) => {
            lemma_arith_to_poly_sum_abs(a);
            lemma_arith_to_poly_sum_abs(b);
            lemma_poly_neg_sum_abs(arith_to_poly(b));
            lemma_poly_add_sum_abs(arith_to_poly(a), poly_neg(arith_to_poly(b)));
        },
        ArithExpr::Mul(a, b) => {
            lemma_arith_to_poly_sum_abs(a);
            lemma_arith_to_poly_sum_abs(b);
            let pa = arith_to_poly(a);
            let pb = arith_to_poly(b);
            lemma_poly_mul_sum_abs(pa, pb);
            lemma_expr_coeff_bound_nonneg(a);
            lemma_expr_coeff_bound_nonneg(b);
            lemma_poly_sum_abs_nonneg(pa);
            lemma_poly_sum_abs_nonneg(pb);
            //  Chain: sa(mul(pa,pb)) <= sa(pa)*sa(pb) <= ecb(a)*ecb(b) = ecb(Mul(a,b))
            assert(poly_sum_abs(poly_mul(pa, pb)) <= expr_coeff_bound(e))
                by(nonlinear_arith)
                requires
                    poly_sum_abs(poly_mul(pa, pb)) <= poly_sum_abs(pa) * poly_sum_abs(pb),
                    poly_sum_abs(pa) <= expr_coeff_bound(a),
                    poly_sum_abs(pb) <= expr_coeff_bound(b),
                    expr_coeff_bound(a) >= 0, expr_coeff_bound(b) >= 0,
                    poly_sum_abs(pa) >= 0, poly_sum_abs(pb) >= 0,
                    expr_coeff_bound(e) == expr_coeff_bound(a) * expr_coeff_bound(b);
        },
        _ => {},
    }
}

///  MAIN LEMMA: arith_to_poly(e) has all coefficients bounded by expr_coeff_bound(e).
pub proof fn lemma_arith_to_poly_coeff_bound(e: &ArithExpr, k: int)
    requires 0 <= k < arith_to_poly(e).len(),
    ensures
        arith_to_poly(e)[k].0 >= -expr_coeff_bound(e),
        arith_to_poly(e)[k].0 <= expr_coeff_bound(e),
{
    lemma_arith_to_poly_sum_abs(e);
    lemma_poly_sum_abs_bounds_individual(arith_to_poly(e), k);
    //  |arith_to_poly(e)[k].0| <= poly_sum_abs(arith_to_poly(e)) <= expr_coeff_bound(e)
}

} //  verus!
