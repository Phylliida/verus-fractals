///  GPU Fixed-Point ArithExpr Unrolling
///
///  Translates verus-fixed-point multi-limb algorithms into ArithExpr trees
///  that can be emitted as GPU shaders. Each GPU thread processes one
///  multi-limb number independently — the carry chain is unrolled into
///  nested ArithExpr subexpressions.
///
///  This is a second "exec backend" for FixedPoint: the CPU exec uses
///  Vec<u32> with sequential loops, the GPU exec uses ArithExpr with
///  unrolled carries. Both are proved against the same FixedPoint spec.

use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_cutedsl::kernel::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  Buffer layout helpers
//  ══════════════════════════════════════════════════════════════

///  The base-2^32 limb modulus.
pub open spec fn LIMB_BASE() -> int { 0x1_0000_0000 }

///  Read limb `limb_idx` of multi-limb number stored for thread `Var(0)`
///  in buffer `buf`. Layout: thread t's limbs are at positions t*n_limbs .. t*n_limbs + n_limbs - 1.
pub open spec fn limb_read(buf: nat, n_limbs: nat, limb_idx: nat) -> ArithExpr {
    ArithExpr::Index(buf, Box::new(
        ArithExpr::Add(
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Var(0)),
                Box::new(ArithExpr::Const(n_limbs as int)))),
            Box::new(ArithExpr::Const(limb_idx as int)))))
}

///  Scatter index for limb `limb_idx` of thread `Var(0)`.
pub open spec fn limb_scatter(n_limbs: nat, limb_idx: nat) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_limbs as int)))),
        Box::new(ArithExpr::Const(limb_idx as int)))
}

//  ══════════════════════════════════════════════════════════════
//  Multi-limb addition: carry chain unrolled into ArithExpr
//  ══════════════════════════════════════════════════════════════

///  The carry INTO limb position `limb` (0 for limb 0).
///  carry[i] = (a[i-1] + b[i-1] + carry[i-1]) / 2^32
///  The carry INTO limb position `limb` (0 for limb 0).
///  carry[i] = (a[i-1] + b[i-1] + carry[i-1]) / 2^32
///  Single recursion (no mutual recursion) for clean Z3 unfolding.
pub open spec fn add_carry_expr(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr
    decreases limb,
{
    if limb == 0 {
        ArithExpr::Const(0)
    } else {
        //  carry[limb] = (a[limb-1] + b[limb-1] + carry[limb-1]) / LIMB_BASE
        let prev = (limb - 1) as nat;
        ArithExpr::Div(
            Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Add(
                    Box::new(limb_read(a_buf, n_limbs, prev)),
                    Box::new(limb_read(b_buf, n_limbs, prev)))),
                Box::new(add_carry_expr(a_buf, b_buf, n_limbs, prev)))),
            Box::new(ArithExpr::Const(LIMB_BASE())))
    }
}

///  The full (unwrapped) sum at limb position `limb`: a[limb] + b[limb] + carry_in.
///  Non-recursive — just composes limb reads with carry.
pub open spec fn add_full_sum(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Add(
            Box::new(limb_read(a_buf, n_limbs, limb)),
            Box::new(limb_read(b_buf, n_limbs, limb)))),
        Box::new(add_carry_expr(a_buf, b_buf, n_limbs, limb)))
}

///  The result limb at position `limb`: (a[limb] + b[limb] + carry) mod 2^32.
pub open spec fn add_result_limb(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr {
    ArithExpr::Mod(
        Box::new(add_full_sum(a_buf, b_buf, n_limbs, limb)),
        Box::new(ArithExpr::Const(LIMB_BASE())))
}

///  Build a complete multi-limb add kernel: one OutputSpec per result limb.
pub open spec fn add_limbs_kernel(
    a_buf: nat, b_buf: nat, n_limbs: nat, n_threads: nat,
) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_threads as int))),
        outputs: Seq::new(n_limbs, |i: int|
            OutputSpec {
                scatter: limb_scatter(n_limbs, i as nat),
                compute: add_result_limb(a_buf, b_buf, n_limbs, i as nat),
            }),
    }
}

//  ══════════════════════════════════════════════════════════════
//  Mathematical carry chain (spec-level, for proof obligations)
//  ══════════════════════════════════════════════════════════════

///  Mathematical carry: the carry after adding limbs 0..limb.
pub open spec fn limb_carry(a_vals: Seq<int>, b_vals: Seq<int>, limb: nat) -> int
    decreases limb,
{
    if limb == 0 { 0 }
    else {
        (a_vals[(limb - 1) as int] + b_vals[(limb - 1) as int]
            + limb_carry(a_vals, b_vals, (limb - 1) as nat)) / LIMB_BASE()
    }
}

///  Mathematical result limb.
pub open spec fn limb_result(a_vals: Seq<int>, b_vals: Seq<int>, limb: nat) -> int {
    (a_vals[limb as int] + b_vals[limb as int]
        + limb_carry(a_vals, b_vals, limb)) % LIMB_BASE()
}

//  ══════════════════════════════════════════════════════════════
//  Helper: what limb_read evaluates to
//  ══════════════════════════════════════════════════════════════

///  limb_read(buf, n, i) evaluates to arrays[buf][tid * n + i].
pub proof fn lemma_limb_read_eval(
    buf: nat, n_limbs: nat, limb_idx: nat,
    env: Seq<int>, arrays: Seq<Seq<int>>, tid: int,
)
    requires
        env.len() > 0,
        env[0] == tid,
        (buf as int) < arrays.len(),
        tid >= 0,
        tid * (n_limbs as int) + (limb_idx as int) >= 0,
        tid * (n_limbs as int) + (limb_idx as int) < arrays[buf as int].len(),
    ensures
        arith_eval_with_arrays(&limb_read(buf, n_limbs, limb_idx), env, arrays)
            == arrays[buf as int][tid * (n_limbs as int) + (limb_idx as int)],
{
    //  Unfold step by step:
    //  Var(0) → env[0] = tid
    let var0 = ArithExpr::Var(0);
    assert(arith_eval_with_arrays(&var0, env, arrays) == tid);
    //  Const(n_limbs) → n_limbs
    let cn = ArithExpr::Const(n_limbs as int);
    assert(arith_eval_with_arrays(&cn, env, arrays) == n_limbs as int);
    //  Mul(Var(0), Const(n)) → tid * n_limbs
    let mul_expr = ArithExpr::Mul(Box::new(var0), Box::new(cn));
    assert(arith_eval_with_arrays(&mul_expr, env, arrays) == tid * (n_limbs as int));
    //  Const(limb_idx) → limb_idx
    let ci = ArithExpr::Const(limb_idx as int);
    assert(arith_eval_with_arrays(&ci, env, arrays) == limb_idx as int);
    //  Add(tid*n, limb_idx) → tid*n + limb_idx
    let add_expr = ArithExpr::Add(Box::new(mul_expr), Box::new(ci));
    assert(arith_eval_with_arrays(&add_expr, env, arrays) == tid * (n_limbs as int) + (limb_idx as int));
    //  Index(buf, tid*n+limb_idx) → arrays[buf][tid*n+limb_idx]
}

//  ══════════════════════════════════════════════════════════════
//  ArithExpr evaluation helpers — trivial by definition, but give
//  Z3 intermediate steps for deeply nested expressions.
//  ══════════════════════════════════════════════════════════════

pub proof fn lemma_eval_add(a: ArithExpr, b: ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>)
    ensures arith_eval_with_arrays(
        &ArithExpr::Add(Box::new(a), Box::new(b)), env, arrays)
        == arith_eval_with_arrays(&a, env, arrays) + arith_eval_with_arrays(&b, env, arrays),
{}

pub proof fn lemma_eval_div(num: ArithExpr, den: ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>)
    ensures arith_eval_with_arrays(
        &ArithExpr::Div(Box::new(num), Box::new(den)), env, arrays)
        == if arith_eval_with_arrays(&den, env, arrays) != 0 {
            arith_eval_with_arrays(&num, env, arrays) / arith_eval_with_arrays(&den, env, arrays)
        } else { 0 },
{}

pub proof fn lemma_eval_mod(num: ArithExpr, den: ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>)
    ensures arith_eval_with_arrays(
        &ArithExpr::Mod(Box::new(num), Box::new(den)), env, arrays)
        == if arith_eval_with_arrays(&den, env, arrays) != 0 {
            arith_eval_with_arrays(&num, env, arrays) % arith_eval_with_arrays(&den, env, arrays)
        } else { 0 },
{}

pub proof fn lemma_eval_const(c: int, env: Seq<int>, arrays: Seq<Seq<int>>)
    ensures arith_eval_with_arrays(&ArithExpr::Const(c), env, arrays) == c,
{}

//  ══════════════════════════════════════════════════════════════
//  Correctness: ArithExpr carry chain matches mathematical carry
//  ══════════════════════════════════════════════════════════════

///  The ArithExpr carry chain evaluates to the mathematical carry.
pub proof fn lemma_add_carry_correct(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
    env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires
        env.len() > 0,
        env[0] >= 0,
        (a_buf as int) < arrays.len(),
        (b_buf as int) < arrays.len(),
        n_limbs > 0,
        limb <= n_limbs,
        //  All limbs accessible and in [0, 2^32)
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[a_buf as int].len(),
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[b_buf as int].len(),
        forall|i: nat| i < n_limbs ==> (
            0 <= #[trigger] arrays[a_buf as int][env[0] * (n_limbs as int) + (i as int)]
            && arrays[a_buf as int][env[0] * (n_limbs as int) + (i as int)] < LIMB_BASE()
        ),
        forall|i: nat| i < n_limbs ==> (
            0 <= #[trigger] arrays[b_buf as int][env[0] * (n_limbs as int) + (i as int)]
            && arrays[b_buf as int][env[0] * (n_limbs as int) + (i as int)] < LIMB_BASE()
        ),
    ensures ({
        let tid = env[0];
        let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
        let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);
        arith_eval_with_arrays(&add_carry_expr(a_buf, b_buf, n_limbs, limb), env, arrays)
            == limb_carry(a_vals, b_vals, limb)
    }),
    decreases limb,
{
    let tid = env[0];
    let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
    let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);

    if limb == 0 {
        //  Both sides are 0
        assert(add_carry_expr(a_buf, b_buf, n_limbs, 0nat) == ArithExpr::Const(0));
        assert(arith_eval_with_arrays(&ArithExpr::Const(0), env, arrays) == 0);
        assert(limb_carry(a_vals, b_vals, 0nat) == 0);
    } else {
        let prev = (limb - 1) as nat;

        //  IH: carry at prev is correct
        lemma_add_carry_correct(a_buf, b_buf, n_limbs, prev, env, arrays);

        //  Limb reads evaluate to array values
        lemma_limb_read_eval(a_buf, n_limbs, prev, env, arrays, tid);
        lemma_limb_read_eval(b_buf, n_limbs, prev, env, arrays, tid);

        //  Build the ArithExpr pieces that add_carry_expr(limb) unfolds to:
        let a_read = limb_read(a_buf, n_limbs, prev);
        let b_read = limb_read(b_buf, n_limbs, prev);
        let carry_prev_expr = add_carry_expr(a_buf, b_buf, n_limbs, prev);
        let ab_sum = ArithExpr::Add(Box::new(a_read), Box::new(b_read));
        let full_sum = ArithExpr::Add(Box::new(ab_sum), Box::new(carry_prev_expr));
        let base_const = ArithExpr::Const(LIMB_BASE());

        //  Step-by-step evaluation using helpers
        lemma_eval_add(a_read, b_read, env, arrays);
        lemma_eval_add(ab_sum, carry_prev_expr, env, arrays);
        lemma_eval_const(LIMB_BASE(), env, arrays);
        lemma_eval_div(full_sum, base_const, env, arrays);

        //  Now Z3 knows:
        //  eval(ab_sum) == a_vals[prev] + b_vals[prev]
        //  eval(full_sum) == a_vals[prev] + b_vals[prev] + limb_carry(prev)
        //  eval(Div(full_sum, BASE)) == eval(full_sum) / LIMB_BASE

        //  Connect: add_carry_expr(limb) IS Div(full_sum, base_const)
        reveal_with_fuel(add_carry_expr, 2);
    }
}

///  Each result limb matches the mathematical result.
pub proof fn lemma_add_result_correct(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
    env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires
        env.len() > 0,
        env[0] >= 0,
        (a_buf as int) < arrays.len(),
        (b_buf as int) < arrays.len(),
        n_limbs > 0,
        limb < n_limbs,
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[a_buf as int].len(),
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[b_buf as int].len(),
        forall|i: nat| i < n_limbs ==> (
            0 <= #[trigger] arrays[a_buf as int][env[0] * (n_limbs as int) + (i as int)]
            && arrays[a_buf as int][env[0] * (n_limbs as int) + (i as int)] < LIMB_BASE()
        ),
        forall|i: nat| i < n_limbs ==> (
            0 <= #[trigger] arrays[b_buf as int][env[0] * (n_limbs as int) + (i as int)]
            && arrays[b_buf as int][env[0] * (n_limbs as int) + (i as int)] < LIMB_BASE()
        ),
    ensures ({
        let tid = env[0];
        let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
        let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);
        arith_eval_with_arrays(&add_result_limb(a_buf, b_buf, n_limbs, limb), env, arrays)
            == limb_result(a_vals, b_vals, limb)
    }),
{
    let tid = env[0];

    //  Carry is correct
    lemma_add_carry_correct(a_buf, b_buf, n_limbs, limb, env, arrays);

    //  Limb reads evaluate to array values
    lemma_limb_read_eval(a_buf, n_limbs, limb, env, arrays, tid);
    lemma_limb_read_eval(b_buf, n_limbs, limb, env, arrays, tid);

    //  Decompose add_result_limb = Mod(Add(Add(a_read, b_read), carry), BASE)
    let a_read = limb_read(a_buf, n_limbs, limb);
    let b_read = limb_read(b_buf, n_limbs, limb);
    let carry_expr = add_carry_expr(a_buf, b_buf, n_limbs, limb);
    let ab_sum = ArithExpr::Add(Box::new(a_read), Box::new(b_read));
    let full_sum = ArithExpr::Add(Box::new(ab_sum), Box::new(carry_expr));
    let base_const = ArithExpr::Const(LIMB_BASE());

    lemma_eval_add(a_read, b_read, env, arrays);
    lemma_eval_add(ab_sum, carry_expr, env, arrays);
    lemma_eval_const(LIMB_BASE(), env, arrays);
    lemma_eval_mod(full_sum, base_const, env, arrays);
}

//  ══════════════════════════════════════════════════════════════
//  Schoolbook multiply: base case for Karatsuba
//  ══════════════════════════════════════════════════════════════

///  Sum of partial products for result limb `k`:
///  Σ_{j=0}^{max_j} a[j] * b[k-j]  (only where both indices are valid)
pub open spec fn partial_products(
    a_buf: nat, b_buf: nat, n_limbs: nat, k: nat, max_j: nat,
) -> ArithExpr
    decreases max_j,
{
    //  Is this term valid? j < n and k-j < n
    let valid = max_j < n_limbs && k >= max_j && (k - max_j) < n_limbs;
    let term = if valid {
        ArithExpr::Mul(
            Box::new(limb_read(a_buf, n_limbs, max_j)),
            Box::new(limb_read(b_buf, n_limbs, (k - max_j) as nat)))
    } else {
        ArithExpr::Const(0)
    };
    if max_j == 0 {
        term
    } else {
        ArithExpr::Add(
            Box::new(partial_products(a_buf, b_buf, n_limbs, k, (max_j - 1) as nat)),
            Box::new(term))
    }
}

///  Carry into result limb `limb` of schoolbook multiply.
///  carry[0] = 0
///  carry[k] = (partial_products(k-1) + carry[k-1]) / BASE
pub open spec fn schoolbook_carry(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr
    decreases limb,
{
    if limb == 0 {
        ArithExpr::Const(0)
    } else {
        let prev = (limb - 1) as nat;
        ArithExpr::Div(
            Box::new(ArithExpr::Add(
                Box::new(partial_products(a_buf, b_buf, n_limbs, prev, (n_limbs - 1) as nat)),
                Box::new(schoolbook_carry(a_buf, b_buf, n_limbs, prev)))),
            Box::new(ArithExpr::Const(LIMB_BASE())))
    }
}

///  Result limb `limb` of schoolbook multiply: (acc + carry) % BASE.
pub open spec fn schoolbook_result_limb(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr {
    ArithExpr::Mod(
        Box::new(ArithExpr::Add(
            Box::new(partial_products(a_buf, b_buf, n_limbs, limb, (n_limbs - 1) as nat)),
            Box::new(schoolbook_carry(a_buf, b_buf, n_limbs, limb)))),
        Box::new(ArithExpr::Const(LIMB_BASE())))
}

///  Build a schoolbook multiply kernel: 2*n output limbs.
pub open spec fn schoolbook_mul_kernel(
    a_buf: nat, b_buf: nat, n_limbs: nat, n_threads: nat,
) -> KernelSpec
    recommends n_limbs > 0,
{
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_threads as int))),
        outputs: Seq::new(2 * n_limbs, |i: int|
            OutputSpec {
                scatter: limb_scatter(2 * n_limbs, i as nat),
                compute: schoolbook_result_limb(a_buf, b_buf, n_limbs, i as nat),
            }),
    }
}

//  ══════════════════════════════════════════════════════════════
//  Mathematical specs for schoolbook multiply (for proof)
//  ══════════════════════════════════════════════════════════════

///  Mathematical partial product accumulator for result limb k.
pub open spec fn math_partial_products(a_vals: Seq<int>, b_vals: Seq<int>, k: nat, max_j: nat) -> int
    decreases max_j,
{
    let valid = max_j < a_vals.len() && k >= max_j && (k - max_j) < b_vals.len();
    let term = if valid { a_vals[max_j as int] * b_vals[(k - max_j) as int] } else { 0 };
    if max_j == 0 { term }
    else { math_partial_products(a_vals, b_vals, k, (max_j - 1) as nat) + term }
}

///  Mathematical carry for schoolbook multiply.
pub open spec fn math_schoolbook_carry(a_vals: Seq<int>, b_vals: Seq<int>, n: nat, limb: nat) -> int
    decreases limb,
{
    if limb == 0 { 0 }
    else {
        let prev = (limb - 1) as nat;
        (math_partial_products(a_vals, b_vals, prev, (n - 1) as nat)
            + math_schoolbook_carry(a_vals, b_vals, n, prev)) / LIMB_BASE()
    }
}

///  Mathematical result limb for schoolbook multiply.
pub open spec fn math_schoolbook_result(a_vals: Seq<int>, b_vals: Seq<int>, n: nat, limb: nat) -> int {
    (math_partial_products(a_vals, b_vals, limb, (n - 1) as nat)
        + math_schoolbook_carry(a_vals, b_vals, n, limb)) % LIMB_BASE()
}

//  ══════════════════════════════════════════════════════════════
//  Schoolbook correctness proofs
//  ══════════════════════════════════════════════════════════════

///  Partial products ArithExpr evaluates to mathematical partial products.
pub proof fn lemma_partial_products_correct(
    a_buf: nat, b_buf: nat, n_limbs: nat, k: nat, max_j: nat,
    env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires
        env.len() > 0,
        env[0] >= 0,
        (a_buf as int) < arrays.len(),
        (b_buf as int) < arrays.len(),
        n_limbs > 0,
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[a_buf as int].len(),
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[b_buf as int].len(),
    ensures ({
        let tid = env[0];
        let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
        let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);
        arith_eval_with_arrays(
            &partial_products(a_buf, b_buf, n_limbs, k, max_j), env, arrays)
            == math_partial_products(a_vals, b_vals, k, max_j)
    }),
    decreases max_j,
{
    let tid = env[0];
    let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
    let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);

    let valid = max_j < n_limbs && k >= max_j && (k - max_j) < n_limbs;

    if valid {
        lemma_limb_read_eval(a_buf, n_limbs, max_j, env, arrays, tid);
        lemma_limb_read_eval(b_buf, n_limbs, (k - max_j) as nat, env, arrays, tid);
    }

    if max_j > 0 {
        lemma_partial_products_correct(a_buf, b_buf, n_limbs, k, (max_j - 1) as nat, env, arrays);
        //  Use eval helpers
        let prev_expr = partial_products(a_buf, b_buf, n_limbs, k, (max_j - 1) as nat);
        let term_expr = if valid {
            ArithExpr::Mul(
                Box::new(limb_read(a_buf, n_limbs, max_j)),
                Box::new(limb_read(b_buf, n_limbs, (k - max_j) as nat)))
        } else {
            ArithExpr::Const(0)
        };
        lemma_eval_add(prev_expr, term_expr, env, arrays);
    }
}

///  Schoolbook carry ArithExpr evaluates to mathematical carry.
pub proof fn lemma_schoolbook_carry_correct(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
    env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires
        env.len() > 0,
        env[0] >= 0,
        (a_buf as int) < arrays.len(),
        (b_buf as int) < arrays.len(),
        n_limbs > 0,
        limb <= 2 * n_limbs,
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[a_buf as int].len(),
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[b_buf as int].len(),
    ensures ({
        let tid = env[0];
        let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
        let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);
        arith_eval_with_arrays(
            &schoolbook_carry(a_buf, b_buf, n_limbs, limb), env, arrays)
            == math_schoolbook_carry(a_vals, b_vals, n_limbs, limb)
    }),
    decreases limb,
{
    let tid = env[0];
    let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
    let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);

    if limb == 0 {
        // Both sides are 0
    } else {
        let prev = (limb - 1) as nat;
        //  IH
        lemma_schoolbook_carry_correct(a_buf, b_buf, n_limbs, prev, env, arrays);
        //  Partial products correct
        lemma_partial_products_correct(a_buf, b_buf, n_limbs, prev, (n_limbs - 1) as nat, env, arrays);

        //  Structural decomposition using eval helpers
        let pp_expr = partial_products(a_buf, b_buf, n_limbs, prev, (n_limbs - 1) as nat);
        let carry_prev_expr = schoolbook_carry(a_buf, b_buf, n_limbs, prev);
        let sum_expr = ArithExpr::Add(Box::new(pp_expr), Box::new(carry_prev_expr));
        let base_expr = ArithExpr::Const(LIMB_BASE());

        lemma_eval_add(pp_expr, carry_prev_expr, env, arrays);
        lemma_eval_const(LIMB_BASE(), env, arrays);
        lemma_eval_div(sum_expr, base_expr, env, arrays);

        reveal_with_fuel(schoolbook_carry, 2);
    }
}

///  Schoolbook result limb ArithExpr evaluates to mathematical result.
pub proof fn lemma_schoolbook_result_correct(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
    env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires
        env.len() > 0,
        env[0] >= 0,
        (a_buf as int) < arrays.len(),
        (b_buf as int) < arrays.len(),
        n_limbs > 0,
        limb < 2 * n_limbs,
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[a_buf as int].len(),
        env[0] * (n_limbs as int) + (n_limbs as int) <= arrays[b_buf as int].len(),
    ensures ({
        let tid = env[0];
        let a_vals = Seq::new(n_limbs, |i: int| arrays[a_buf as int][tid * (n_limbs as int) + i]);
        let b_vals = Seq::new(n_limbs, |i: int| arrays[b_buf as int][tid * (n_limbs as int) + i]);
        arith_eval_with_arrays(
            &schoolbook_result_limb(a_buf, b_buf, n_limbs, limb), env, arrays)
            == math_schoolbook_result(a_vals, b_vals, n_limbs, limb)
    }),
{
    let tid = env[0];
    lemma_schoolbook_carry_correct(a_buf, b_buf, n_limbs, limb, env, arrays);
    lemma_partial_products_correct(a_buf, b_buf, n_limbs, limb, (n_limbs - 1) as nat, env, arrays);

    let pp_expr = partial_products(a_buf, b_buf, n_limbs, limb, (n_limbs - 1) as nat);
    let carry_expr = schoolbook_carry(a_buf, b_buf, n_limbs, limb);
    let sum_expr = ArithExpr::Add(Box::new(pp_expr), Box::new(carry_expr));
    let base_expr = ArithExpr::Const(LIMB_BASE());

    lemma_eval_add(pp_expr, carry_expr, env, arrays);
    lemma_eval_const(LIMB_BASE(), env, arrays);
    lemma_eval_mod(sum_expr, base_expr, env, arrays);
}

//  ══════════════════════════════════════════════════════════════
//  Karatsuba multiply: recursive splitting
//  ══════════════════════════════════════════════════════════════
//
//  a * b = z0 + z1 * B^half + z2 * B^(2*half)
//  where z0 = a_lo*b_lo, z2 = a_hi*b_hi,
//        z1 = (a_lo+a_hi)*(b_lo+b_hi) - z0 - z2
//
//  For ArithExpr: each z is itself an ArithExpr sub-tree (either
//  schoolbook for small n, or recursive Karatsuba for large n).
//  The combine step uses multi-limb add/sub ArithExprs.
//
//  TODO: implement karatsuba_result_limb(a_buf, b_buf, n, limb)
//  that recursively builds the ArithExpr tree, splitting at n/2
//  and using schoolbook for n <= 4.

} //  verus!
