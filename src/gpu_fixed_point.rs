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
//  Generalized multi-limb ops: take Seq<ArithExpr> as inputs
//  ══════════════════════════════════════════════════════════════
//
//  Karatsuba's intermediate values (z0, z1, a_sum) are computed
//  ArithExpr trees, not buffer reads. We generalize all multi-limb
//  ops to take Seq<ArithExpr> inputs — the buffer-read versions
//  become a special case.

///  Generalized partial products: sum of a[j]*b[k-j] where a,b are ArithExpr sequences.
pub open spec fn gen_partial_products(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, k: nat, max_j: nat,
) -> ArithExpr
    decreases max_j,
{
    let n_a = a.len();
    let n_b = b.len();
    let valid = (max_j as int) < n_a && k >= max_j && ((k - max_j) as int) < n_b;
    let term = if valid {
        ArithExpr::Mul(Box::new(a[max_j as int]), Box::new(b[(k - max_j) as int]))
    } else {
        ArithExpr::Const(0)
    };
    if max_j == 0 { term }
    else {
        ArithExpr::Add(
            Box::new(gen_partial_products(a, b, k, (max_j - 1) as nat)),
            Box::new(term))
    }
}

///  Generalized carry chain for multiplication.
pub open spec fn gen_mul_carry(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, max_j: nat, limb: nat,
) -> ArithExpr
    decreases limb,
{
    if limb == 0 { ArithExpr::Const(0) }
    else {
        let prev = (limb - 1) as nat;
        ArithExpr::Div(
            Box::new(ArithExpr::Add(
                Box::new(gen_partial_products(a, b, prev, max_j)),
                Box::new(gen_mul_carry(a, b, max_j, prev)))),
            Box::new(ArithExpr::Const(LIMB_BASE())))
    }
}

///  Generalized result limb for multiplication.
pub open spec fn gen_mul_result_limb(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, max_j: nat, limb: nat,
) -> ArithExpr {
    ArithExpr::Mod(
        Box::new(ArithExpr::Add(
            Box::new(gen_partial_products(a, b, limb, max_j)),
            Box::new(gen_mul_carry(a, b, max_j, limb)))),
        Box::new(ArithExpr::Const(LIMB_BASE())))
}

///  Generalized carry chain for addition of two ArithExpr sequences.
pub open spec fn gen_add_carry(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, limb: nat,
) -> ArithExpr
    decreases limb,
{
    if limb == 0 { ArithExpr::Const(0) }
    else {
        let prev = (limb - 1) as nat;
        ArithExpr::Div(
            Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Add(Box::new(a[prev as int]), Box::new(b[prev as int]))),
                Box::new(gen_add_carry(a, b, prev)))),
            Box::new(ArithExpr::Const(LIMB_BASE())))
    }
}

///  Generalized result limb for addition.
pub open spec fn gen_add_result_limb(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, limb: nat,
) -> ArithExpr {
    ArithExpr::Mod(
        Box::new(ArithExpr::Add(
            Box::new(ArithExpr::Add(Box::new(a[limb as int]), Box::new(b[limb as int]))),
            Box::new(gen_add_carry(a, b, limb)))),
        Box::new(ArithExpr::Const(LIMB_BASE())))
}

///  Generalized subtraction with borrow chain (for z1 = z1_full - z0 - z2).
pub open spec fn gen_sub_borrow(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, limb: nat,
) -> ArithExpr
    decreases limb,
{
    if limb == 0 { ArithExpr::Const(0) }
    else {
        let prev = (limb - 1) as nat;
        //  borrow = if (a[prev] - b[prev] - borrow_prev) < 0 then 1 else 0
        //  Equivalently: borrow = (a[prev] - b[prev] - borrow_prev + BASE) / BASE
        //  when result is in [-BASE, 2*BASE), quotient is 0 or 1.
        //  Actually: (BASE + a - b - borrow) / BASE gives 0 if a-b-borrow < 0, 1 if >= 0.
        //  So borrow = 1 - (BASE + a - b - borrow_prev) / BASE.
        //  Simpler: just use the div/mod pattern like add.
        //  diff = a[prev] - b[prev] + BASE - borrow_prev
        //  borrow = 1 - diff / BASE
        let diff = ArithExpr::Sub(
            Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Sub(Box::new(a[prev as int]), Box::new(b[prev as int]))),
                Box::new(ArithExpr::Const(LIMB_BASE())))),
            Box::new(gen_sub_borrow(a, b, prev)));
        ArithExpr::Sub(
            Box::new(ArithExpr::Const(1)),
            Box::new(ArithExpr::Div(Box::new(diff), Box::new(ArithExpr::Const(LIMB_BASE())))))
    }
}

///  Generalized result limb for subtraction.
pub open spec fn gen_sub_result_limb(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, limb: nat,
) -> ArithExpr {
    //  result = (a[limb] - b[limb] + BASE - borrow) % BASE
    ArithExpr::Mod(
        Box::new(ArithExpr::Sub(
            Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Sub(Box::new(a[limb as int]), Box::new(b[limb as int]))),
                Box::new(ArithExpr::Const(LIMB_BASE())))),
            Box::new(gen_sub_borrow(a, b, limb)))),
        Box::new(ArithExpr::Const(LIMB_BASE())))
}

//  ══════════════════════════════════════════════════════════════
//  Karatsuba multiply: recursive ArithExpr construction
//  ══════════════════════════════════════════════════════════════

///  Build ArithExpr inputs from buffer reads with offset.
pub open spec fn buffer_limbs(
    buf: nat, n_total: nat, offset: nat, count: nat,
) -> Seq<ArithExpr> {
    Seq::new(count, |j: int| limb_read(buf, n_total, (offset + j) as nat))
}

///  Result limbs of a multiply as a Seq<ArithExpr>.
///  For n ≤ 4: schoolbook. For n > 4: Karatsuba recursion.
pub open spec fn mul_result_limbs(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, n: nat,
) -> Seq<ArithExpr>
    recommends a.len() == n, b.len() == n, n > 0,
    decreases n, 1nat,
{
    if n <= 4 {
        //  Schoolbook base case: 2*n result limbs
        let result_len = (2 * n) as nat;
        let max_j = (n - 1) as nat;
        Seq::new(result_len, |k: int| gen_mul_result_limb(a, b, max_j, k as nat))
    } else {
        karatsuba_combine(a, b, n)
    }
}

///  Karatsuba recursive combine — separated for clarity.
///  a * b = z0 + z1 * B^half + z2 * B^(2*half)
pub open spec fn karatsuba_combine(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, n: nat,
) -> Seq<ArithExpr>
    recommends a.len() == n, b.len() == n, n > 4,
    decreases n, 0nat,
{
    if n <= 4 { Seq::empty() }  //  guard for termination (unreachable in practice)
    else {
    let half = n / 2;
    let upper = (n - half) as nat;

    //  Split inputs
    let a_lo = a.subrange(0, half as int);
    let a_hi = a.subrange(half as int, n as int);
    let b_lo = b.subrange(0, half as int);
    let b_hi = b.subrange(half as int, n as int);

    //  Pad lo halves to `upper` limbs if needed (odd n)
    let a_lo_p: Seq<ArithExpr> = if half < upper {
        a_lo.push(ArithExpr::Const(0))
    } else { a_lo };
    let b_lo_p: Seq<ArithExpr> = if half < upper {
        b_lo.push(ArithExpr::Const(0))
    } else { b_lo };

    //  z0 = a_lo * b_lo, z2 = a_hi * b_hi  (recursive, size ≤ ceil(n/2))
    let z0: Seq<ArithExpr> = mul_result_limbs(a_lo_p, b_lo_p, upper);
    let z2: Seq<ArithExpr> = mul_result_limbs(a_hi, b_hi, upper);

    //  a_sum = a_lo + a_hi (upper+1 limbs including carry)
    let sum_len = (upper + 1) as nat;
    let a_sum: Seq<ArithExpr> = Seq::new(sum_len, |j: int|
        if j < upper as int { gen_add_result_limb(a_lo_p, a_hi, j as nat) }
        else { gen_add_carry(a_lo_p, a_hi, upper) });
    let b_sum: Seq<ArithExpr> = Seq::new(sum_len, |j: int|
        if j < upper as int { gen_add_result_limb(b_lo_p, b_hi, j as nat) }
        else { gen_add_carry(b_lo_p, b_hi, upper) });

    //  z1_full = a_sum * b_sum (recursive, size upper+1)
    let z1_full: Seq<ArithExpr> = mul_result_limbs(a_sum, b_sum, sum_len);

    //  z1 = z1_full - z0 - z2 (pad z0, z2 to match z1_full length)
    let z1_len = (2 * sum_len) as nat;
    let z0_pad: Seq<ArithExpr> = Seq::new(z1_len, |j: int|
        if j < z0.len() { z0[j] } else { ArithExpr::Const(0) });
    let z2_pad: Seq<ArithExpr> = Seq::new(z1_len, |j: int|
        if j < z2.len() { z2[j] } else { ArithExpr::Const(0) });
    let z1_tmp: Seq<ArithExpr> = Seq::new(z1_len, |j: int|
        gen_sub_result_limb(z1_full, z0_pad, j as nat));
    let z1: Seq<ArithExpr> = Seq::new(z1_len, |j: int|
        gen_sub_result_limb(z1_tmp, z2_pad, j as nat));

    //  Combine: result = z0 + z1*B^half + z2*B^(2*half)
    let result_len = (2 * n) as nat;
    let z0_ext: Seq<ArithExpr> = Seq::new(result_len, |k: int|
        if k < z0.len() { z0[k] } else { ArithExpr::Const(0) });
    let z1_shift: Seq<ArithExpr> = Seq::new(result_len, |k: int|
        if k >= half as int && (k - half as int) < z1.len() {
            z1[k - half as int]
        } else { ArithExpr::Const(0) });
    let z2_shift: Seq<ArithExpr> = Seq::new(result_len, |k: int|
        if k >= (2 * half) as int && (k - (2 * half) as int) < z2.len() {
            z2[k - (2 * half) as int]
        } else { ArithExpr::Const(0) });

    //  Two-pass addition
    let temp: Seq<ArithExpr> = Seq::new(result_len, |k: int|
        gen_add_result_limb(z0_ext, z1_shift, k as nat));
    Seq::new(result_len, |k: int|
        gen_add_result_limb(temp, z2_shift, k as nat))
    }  //  else
}

///  Build a Karatsuba multiply kernel from buffer reads.
pub open spec fn karatsuba_mul_kernel(
    a_buf: nat, b_buf: nat, n_limbs: nat, n_threads: nat,
) -> KernelSpec
    recommends n_limbs > 0,
{
    let a = buffer_limbs(a_buf, n_limbs, 0, n_limbs);
    let b = buffer_limbs(b_buf, n_limbs, 0, n_limbs);
    let result = mul_result_limbs(a, b, n_limbs);
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_threads as int))),
        outputs: Seq::new(2 * n_limbs, |i: int|
            OutputSpec {
                scatter: limb_scatter(2 * n_limbs, i as nat),
                compute: result[i],
            }),
    }
}

//  ══════════════════════════════════════════════════════════════
//  Multi-limb sequence helpers
//  ══════════════════════════════════════════════════════════════

///  Add two n-limb ArithExpr sequences, producing n result limbs.
pub open spec fn add_limbs_seq(a: Seq<ArithExpr>, b: Seq<ArithExpr>, n: nat) -> Seq<ArithExpr> {
    Seq::new(n, |j: int| gen_add_result_limb(a, b, j as nat))
}

///  Subtract two n-limb ArithExpr sequences, producing n result limbs.
pub open spec fn sub_limbs_seq(a: Seq<ArithExpr>, b: Seq<ArithExpr>, n: nat) -> Seq<ArithExpr> {
    Seq::new(n, |j: int| gen_sub_result_limb(a, b, j as nat))
}

///  Multiply and truncate for fixed-point: (a * b) >> (frac_limbs * 32).
///  Keeps `n` result limbs starting at position `frac_limbs` of the 2n-limb product.
pub open spec fn mul_truncate(
    a: Seq<ArithExpr>, b: Seq<ArithExpr>, n: nat, frac_limbs: nat,
) -> Seq<ArithExpr>
    recommends frac_limbs + n <= 2 * n,
{
    let full = mul_result_limbs(a, b, n);
    full.subrange(frac_limbs as int, (frac_limbs + n) as int)
}

///  Pad or truncate a Seq<ArithExpr> to exactly `len` elements.
pub open spec fn pad_seq(s: Seq<ArithExpr>, len: nat) -> Seq<ArithExpr> {
    Seq::new(len, |j: int| if j < s.len() { s[j] } else { ArithExpr::Const(0) })
}

//  ══════════════════════════════════════════════════════════════
//  Complex arithmetic on multi-limb fixed-point ArithExpr
//  ══════════════════════════════════════════════════════════════

///  Complex addition: (a_re + b_re, a_im + b_im).
pub open spec fn complex_add(
    a_re: Seq<ArithExpr>, a_im: Seq<ArithExpr>,
    b_re: Seq<ArithExpr>, b_im: Seq<ArithExpr>,
    n: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>) {
    (add_limbs_seq(a_re, b_re, n), add_limbs_seq(a_im, b_im, n))
}

///  Complex subtraction: (a_re - b_re, a_im - b_im).
pub open spec fn complex_sub(
    a_re: Seq<ArithExpr>, a_im: Seq<ArithExpr>,
    b_re: Seq<ArithExpr>, b_im: Seq<ArithExpr>,
    n: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>) {
    (sub_limbs_seq(a_re, b_re, n), sub_limbs_seq(a_im, b_im, n))
}

///  Complex multiply with fixed-point truncation:
///  (a_re*b_re - a_im*b_im, a_re*b_im + a_im*b_re)
///  Each product is truncated from 2n limbs to n limbs.
pub open spec fn complex_mul(
    a_re: Seq<ArithExpr>, a_im: Seq<ArithExpr>,
    b_re: Seq<ArithExpr>, b_im: Seq<ArithExpr>,
    n: nat, frac_limbs: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>) {
    let rr = mul_truncate(a_re, b_re, n, frac_limbs);  //  a_re * b_re
    let ii = mul_truncate(a_im, b_im, n, frac_limbs);  //  a_im * b_im
    let ri = mul_truncate(a_re, b_im, n, frac_limbs);  //  a_re * b_im
    let ir = mul_truncate(a_im, b_re, n, frac_limbs);  //  a_im * b_re

    let re = sub_limbs_seq(rr, ii, n);  //  a_re*b_re - a_im*b_im
    let im = add_limbs_seq(ri, ir, n);  //  a_re*b_im + a_im*b_re
    (re, im)
}

///  Complex square with fixed-point truncation:
///  (re² - im², 2*re*im)
pub open spec fn complex_square(
    re: Seq<ArithExpr>, im: Seq<ArithExpr>,
    n: nat, frac_limbs: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>) {
    let re_sq = mul_truncate(re, re, n, frac_limbs);
    let im_sq = mul_truncate(im, im, n, frac_limbs);
    let re_im = mul_truncate(re, im, n, frac_limbs);
    let two_re_im = add_limbs_seq(re_im, re_im, n);  //  2 * re * im

    let result_re = sub_limbs_seq(re_sq, im_sq, n);
    (result_re, two_re_im)
}

///  Scale a complex number by 2: (2*re, 2*im) = (re+re, im+im).
pub open spec fn complex_double(
    re: Seq<ArithExpr>, im: Seq<ArithExpr>, n: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>) {
    (add_limbs_seq(re, re, n), add_limbs_seq(im, im, n))
}

//  ══════════════════════════════════════════════════════════════
//  Mandelbrot perturbation step kernel
//  ══════════════════════════════════════════════════════════════
//
//  δ_{n+1} = 2·Z_n·δ + δ² + Δc
//
//  Input buffers (6 buffers, n limbs each per thread):
//    0: Z_re  (reference orbit real)
//    1: Z_im  (reference orbit imaginary)
//    2: δ_re  (current perturbation real)
//    3: δ_im  (current perturbation imaginary)
//    4: Δc_re (pixel offset real)
//    5: Δc_im (pixel offset imaginary)
//
//  Output: new δ_re, δ_im (2 buffers, n limbs each per thread)

///  Build the perturbation step as ArithExpr sequences.
///  Returns (new_delta_re, new_delta_im) as Seq<ArithExpr>.
pub open spec fn perturbation_step_exprs(
    n: nat, frac_limbs: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>)
    recommends n > 0, frac_limbs < n,
{
    //  Read inputs from buffers
    let z_re = buffer_limbs(0, n, 0, n);
    let z_im = buffer_limbs(1, n, 0, n);
    let d_re = buffer_limbs(2, n, 0, n);
    let d_im = buffer_limbs(3, n, 0, n);
    let dc_re = buffer_limbs(4, n, 0, n);
    let dc_im = buffer_limbs(5, n, 0, n);

    //  2·Z_n·δ  (complex multiply of 2*Z with δ)
    let (two_z_re, two_z_im) = complex_double(z_re, z_im, n);
    let (two_z_d_re, two_z_d_im) = complex_mul(two_z_re, two_z_im, d_re, d_im, n, frac_limbs);

    //  δ²  (complex square of δ)
    let (d_sq_re, d_sq_im) = complex_square(d_re, d_im, n, frac_limbs);

    //  δ_{n+1} = 2·Z·δ + δ² + Δc
    let (sum1_re, sum1_im) = complex_add(two_z_d_re, two_z_d_im, d_sq_re, d_sq_im, n);
    complex_add(sum1_re, sum1_im, dc_re, dc_im, n)
}

///  Build the complete perturbation step kernel.
///  Each thread processes one pixel's perturbation iteration.
pub open spec fn perturbation_kernel(
    n_limbs: nat, frac_limbs: nat, n_threads: nat,
) -> KernelSpec
    recommends n_limbs > 0, frac_limbs < n_limbs,
{
    let (new_d_re, new_d_im) = perturbation_step_exprs(n_limbs, frac_limbs);
    let out_stride = (2 * n_limbs) as nat;  //  2 complex components in output

    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_threads as int))),
        outputs: {
            //  First n_limbs outputs: new δ_re
            let re_outputs = Seq::new(n_limbs, |i: int| OutputSpec {
                scatter: limb_scatter(out_stride, i as nat),
                compute: new_d_re[i],
            });
            //  Next n_limbs outputs: new δ_im
            let im_outputs = Seq::new(n_limbs, |i: int| OutputSpec {
                scatter: limb_scatter(out_stride, (n_limbs + i) as nat),
                compute: new_d_im[i],
            });
            re_outputs + im_outputs
        },
    }
}

//  ══════════════════════════════════════════════════════════════
//  Multi-limb comparison and magnitude
//  ══════════════════════════════════════════════════════════════

///  Multi-limb greater-than: returns 1 if a > b, 0 otherwise.
///  Compares from MSB to LSB using cascading Cmp nodes.
pub open spec fn multi_limb_gt(a: Seq<ArithExpr>, b: Seq<ArithExpr>, limb: nat) -> ArithExpr
    decreases limb,
{
    //  At limb: if a[limb] > b[limb] → 1
    //           if a[limb] == b[limb] → recurse to lower limbs
    //           if a[limb] < b[limb] → 0
    let gt_here = ArithExpr::Cmp(CmpOp::Gt, Box::new(a[limb as int]), Box::new(b[limb as int]));
    if limb == 0 { gt_here }
    else {
        let eq_here = ArithExpr::Cmp(CmpOp::Eq, Box::new(a[limb as int]), Box::new(b[limb as int]));
        let lower = multi_limb_gt(a, b, (limb - 1) as nat);
        //  gt_here + eq_here * lower  (disjoint cases, so Add works as OR)
        ArithExpr::Add(
            Box::new(gt_here),
            Box::new(ArithExpr::Mul(Box::new(eq_here), Box::new(lower))))
    }
}

///  Magnitude squared: re² + im² (truncated to n limbs).
pub open spec fn magnitude_sq(
    re: Seq<ArithExpr>, im: Seq<ArithExpr>, n: nat, frac_limbs: nat,
) -> Seq<ArithExpr> {
    let re_sq = mul_truncate(re, re, n, frac_limbs);
    let im_sq = mul_truncate(im, im, n, frac_limbs);
    add_limbs_seq(re_sq, im_sq, n)
}

///  Escape check: |Z + δ|² > threshold (e.g., 4 in fixed-point).
///  Returns ArithExpr that evaluates to 1 if escaped, 0 if not.
pub open spec fn escape_check(
    z_re: Seq<ArithExpr>, z_im: Seq<ArithExpr>,
    d_re: Seq<ArithExpr>, d_im: Seq<ArithExpr>,
    threshold: Seq<ArithExpr>,
    n: nat, frac_limbs: nat,
) -> ArithExpr
    recommends n > 0,
{
    let total_re = add_limbs_seq(z_re, d_re, n);
    let total_im = add_limbs_seq(z_im, d_im, n);
    let mag_sq = magnitude_sq(total_re, total_im, n, frac_limbs);
    multi_limb_gt(mag_sq, threshold, (n - 1) as nat)
}

///  Glitch check: |δ|² > |Z|².
///  Returns ArithExpr that evaluates to 1 if glitched, 0 if not.
pub open spec fn glitch_check(
    z_re: Seq<ArithExpr>, z_im: Seq<ArithExpr>,
    d_re: Seq<ArithExpr>, d_im: Seq<ArithExpr>,
    n: nat, frac_limbs: nat,
) -> ArithExpr
    recommends n > 0,
{
    let z_mag_sq = magnitude_sq(z_re, z_im, n, frac_limbs);
    let d_mag_sq = magnitude_sq(d_re, d_im, n, frac_limbs);
    multi_limb_gt(d_mag_sq, z_mag_sq, (n - 1) as nat)
}

//  ══════════════════════════════════════════════════════════════
//  Orbit computation kernel: Z_{n+1} = Z_n² + c
//  ══════════════════════════════════════════════════════════════

///  Single orbit step: Z' = Z² + c. Returns (new_Z_re, new_Z_im).
pub open spec fn orbit_step_exprs(
    z_re: Seq<ArithExpr>, z_im: Seq<ArithExpr>,
    c_re: Seq<ArithExpr>, c_im: Seq<ArithExpr>,
    n: nat, frac_limbs: nat,
) -> (Seq<ArithExpr>, Seq<ArithExpr>) {
    let (sq_re, sq_im) = complex_square(z_re, z_im, n, frac_limbs);
    complex_add(sq_re, sq_im, c_re, c_im, n)
}

///  Orbit computation kernel.
///  Each thread computes one reference orbit.
///  Reads c from input, iteratively computes Z = Z² + c,
///  writes each Z_n to a flat orbit buffer.
///
///  Buffer layout:
///    buf 0: c_re        [n_orbits × n_limbs]   — reference point real
///    buf 1: c_im        [n_orbits × n_limbs]   — reference point imag
///    buf 2: Z_re_cur    [n_orbits × n_limbs]   — current Z real (updated in-place)
///    buf 3: Z_im_cur    [n_orbits × n_limbs]   — current Z imag (updated in-place)
///    buf 4: orbit_re    [n_orbits × max_iter × n_limbs] — output: all Z_re history
///    buf 5: orbit_im    [n_orbits × max_iter × n_limbs] — output: all Z_im history
///    buf 6: iter_count  [n_orbits]              — current iteration counter
pub open spec fn orbit_kernel(n_limbs: nat, frac_limbs: nat, n_orbits: nat) -> KernelSpec
    recommends n_limbs > 0, frac_limbs < n_limbs,
{
    let n = n_limbs;
    let c_re = buffer_limbs(0, n, 0, n);
    let c_im = buffer_limbs(1, n, 0, n);
    let z_re = buffer_limbs(2, n, 0, n);
    let z_im = buffer_limbs(3, n, 0, n);

    //  Compute Z' = Z² + c
    let (new_z_re, new_z_im) = orbit_step_exprs(z_re, z_im, c_re, c_im, n, frac_limbs);

    //  Current iteration index (for writing to orbit history)
    let iter_idx = ArithExpr::Index(6, Box::new(ArithExpr::Var(0)));

    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_orbits as int))),
        outputs: {
            //  Update Z_re_cur in-place (buf 2)
            let z_re_out = Seq::new(n, |j: int| OutputSpec {
                scatter: limb_scatter(n, j as nat),
                compute: new_z_re[j],
            });
            //  Update Z_im_cur in-place (buf 3)
            let z_im_out = Seq::new(n, |j: int| OutputSpec {
                scatter: limb_scatter(n, j as nat),
                compute: new_z_im[j],
            });
            //  Increment iteration counter (buf 6)
            let iter_out = seq![OutputSpec {
                scatter: ArithExpr::Var(0),
                compute: ArithExpr::Add(Box::new(iter_idx), Box::new(ArithExpr::Const(1))),
            }];
            z_re_out + z_im_out + iter_out
        },
    }
}

//  ══════════════════════════════════════════════════════════════
//  Full perturbation kernel with escape + glitch detection
//  ══════════════════════════════════════════════════════════════

///  Select expression: if cond == 1 then a else b.
///  cond must be 0 or 1. Computes: cond * a + (1 - cond) * b.
pub open spec fn select_expr(cond: ArithExpr, a: ArithExpr, b: ArithExpr) -> ArithExpr {
    //  cond * a + (1 - cond) * b, where cond is 0 or 1
    ArithExpr::Add(
        Box::new(ArithExpr::Mul(Box::new(cond), Box::new(a))),
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Sub(
                Box::new(ArithExpr::Const(1)),
                Box::new(cond))),
            Box::new(b))))
}

///  Select between two multi-limb sequences based on a condition.
pub open spec fn select_limbs(
    cond: ArithExpr, a: Seq<ArithExpr>, b: Seq<ArithExpr>, n: nat,
) -> Seq<ArithExpr> {
    Seq::new(n, |j: int| select_expr(cond, a[j], b[j]))
}

///  Perturbation step with escape detection and glitch flagging.
///
///  Buffer layout:
///    buf 0: orbit_re     [max_iter × n_limbs]   — reference orbit (shared, read-only)
///    buf 1: orbit_im     [max_iter × n_limbs]   — reference orbit (shared, read-only)
///    buf 2: δ_re         [n_pixels × n_limbs]   — perturbation real (updated)
///    buf 3: δ_im         [n_pixels × n_limbs]   — perturbation imag (updated)
///    buf 4: Δc_re        [n_pixels × n_limbs]   — pixel offset (constant)
///    buf 5: Δc_im        [n_pixels × n_limbs]   — pixel offset (constant)
///    buf 6: iter_count   [n_pixels]              — iteration counter (incremented)
///    buf 7: escaped      [n_pixels]              — escape flag (0→1 when escaped)
///    buf 8: glitched     [n_pixels]              — glitch flag (0→1 when |δ|>|Z|)
///    buf 9: threshold    [n_limbs]               — escape radius² in fixed-point (shared)
pub open spec fn perturbation_kernel_full(
    n_limbs: nat, frac_limbs: nat, n_pixels: nat,
) -> KernelSpec
    recommends n_limbs > 0, frac_limbs < n_limbs,
{
    let n = n_limbs;

    //  Read current iteration to index into orbit buffer
    let iter_idx = ArithExpr::Index(6, Box::new(ArithExpr::Var(0)));
    let escaped_flag = ArithExpr::Index(7, Box::new(ArithExpr::Var(0)));

    //  not_escaped = 1 - escaped (0 or 1)
    let not_escaped = ArithExpr::Sub(
        Box::new(ArithExpr::Const(1)), Box::new(escaped_flag));

    //  Read Z_n from orbit buffer at position iter * n_limbs + j
    let z_re = Seq::new(n, |j: int| ArithExpr::Index(0, Box::new(
        ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(iter_idx), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Const(j))))));
    let z_im = Seq::new(n, |j: int| ArithExpr::Index(1, Box::new(
        ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(iter_idx), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Const(j))))));

    //  Read current δ, Δc
    let d_re = buffer_limbs(2, n, 0, n);
    let d_im = buffer_limbs(3, n, 0, n);
    let dc_re = buffer_limbs(4, n, 0, n);
    let dc_im = buffer_limbs(5, n, 0, n);
    let threshold = Seq::new(n, |j: int| ArithExpr::Index(9, Box::new(ArithExpr::Const(j))));

    //  Compute perturbation step: δ' = 2Zδ + δ² + Δc
    let (two_z_re, two_z_im) = complex_double(z_re, z_im, n);
    let (two_z_d_re, two_z_d_im) = complex_mul(two_z_re, two_z_im, d_re, d_im, n, frac_limbs);
    let (d_sq_re, d_sq_im) = complex_square(d_re, d_im, n, frac_limbs);
    let (sum1_re, sum1_im) = complex_add(two_z_d_re, two_z_d_im, d_sq_re, d_sq_im, n);
    let (new_d_re, new_d_im) = complex_add(sum1_re, sum1_im, dc_re, dc_im, n);

    //  Escape check: |Z + δ'|² > threshold
    let esc = escape_check(z_re, z_im, new_d_re, new_d_im, threshold, n, frac_limbs);

    //  Glitch check: |δ'|² > |Z|²
    let glitch = glitch_check(z_re, z_im, new_d_re, new_d_im, n, frac_limbs);

    //  Masked updates: only update if not already escaped
    //  δ_out = not_escaped ? new_δ : old_δ
    let masked_d_re = select_limbs(not_escaped, new_d_re, d_re, n);
    let masked_d_im = select_limbs(not_escaped, new_d_im, d_im, n);
    //  iter_out = iter + not_escaped  (increment only if still active)
    let new_iter = ArithExpr::Add(Box::new(iter_idx), Box::new(not_escaped));
    //  escaped_out = escaped OR esc  (once escaped, stays escaped)
    //  = max(escaped, esc) = escaped + (1-escaped)*esc
    let new_escaped = ArithExpr::Add(
        Box::new(escaped_flag),
        Box::new(ArithExpr::Mul(Box::new(not_escaped), Box::new(esc))));
    //  glitched_out = glitched OR glitch
    let glitched_flag = ArithExpr::Index(8, Box::new(ArithExpr::Var(0)));
    let not_glitched = ArithExpr::Sub(
        Box::new(ArithExpr::Const(1)), Box::new(glitched_flag));
    let new_glitched = ArithExpr::Add(
        Box::new(glitched_flag),
        Box::new(ArithExpr::Mul(Box::new(not_glitched), Box::new(glitch))));

    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_pixels as int))),
        outputs: {
            let d_re_out = Seq::new(n, |j: int| OutputSpec {
                scatter: limb_scatter(n, j as nat),
                compute: masked_d_re[j],
            });
            let d_im_out = Seq::new(n, |j: int| OutputSpec {
                scatter: limb_scatter(n, j as nat),
                compute: masked_d_im[j],
            });
            let meta_out = seq![
                OutputSpec { scatter: ArithExpr::Var(0), compute: new_iter },
                OutputSpec { scatter: ArithExpr::Var(0), compute: new_escaped },
                OutputSpec { scatter: ArithExpr::Var(0), compute: new_glitched },
            ];
            d_re_out + d_im_out + meta_out
        },
    }
}

} //  verus!
