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
///  Mutual recursion: add_carry_expr calls add_full_sum with limb-1.
///  Termination: (limb, 0) for carry, (limb, 1) for full_sum. Lexicographic decrease.
pub open spec fn add_carry_expr(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr
    decreases limb, 0nat,
{
    if limb == 0 {
        ArithExpr::Const(0)
    } else {
        ArithExpr::Div(
            Box::new(add_full_sum(a_buf, b_buf, n_limbs, (limb - 1) as nat)),
            Box::new(ArithExpr::Const(LIMB_BASE())))
    }
}

///  The full (unwrapped) sum at limb position `limb`: a[limb] + b[limb] + carry_in.
pub open spec fn add_full_sum(
    a_buf: nat, b_buf: nat, n_limbs: nat, limb: nat,
) -> ArithExpr
    decreases limb, 1nat,
{
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
        let carry_prev = arith_eval_with_arrays(
            &add_carry_expr(a_buf, b_buf, n_limbs, prev), env, arrays);
        assert(carry_prev == limb_carry(a_vals, b_vals, prev));

        //  Limb reads evaluate to array values
        lemma_limb_read_eval(a_buf, n_limbs, prev, env, arrays, tid);
        lemma_limb_read_eval(b_buf, n_limbs, prev, env, arrays, tid);
        let a_prev = arith_eval_with_arrays(&limb_read(a_buf, n_limbs, prev), env, arrays);
        let b_prev = arith_eval_with_arrays(&limb_read(b_buf, n_limbs, prev), env, arrays);
        assert(a_prev == a_vals[prev as int]);
        assert(b_prev == b_vals[prev as int]);

        //  Full sum at prev = a[prev] + b[prev] + carry[prev]
        let full_sum_expr = add_full_sum(a_buf, b_buf, n_limbs, prev);
        let full_sum_val = arith_eval_with_arrays(&full_sum_expr, env, arrays);
        assert(full_sum_val == a_prev + b_prev + carry_prev);

        //  Carry at limb = full_sum / LIMB_BASE
        let carry_expr = add_carry_expr(a_buf, b_buf, n_limbs, limb);
        assert(full_sum_val >= 0) by (nonlinear_arith)
            requires a_prev >= 0, b_prev >= 0, carry_prev >= 0;
        assert(arith_eval_with_arrays(&carry_expr, env, arrays)
            == full_sum_val / LIMB_BASE());

        //  And limb_carry(limb) = (a[prev] + b[prev] + limb_carry(prev)) / LIMB_BASE
        assert(limb_carry(a_vals, b_vals, limb)
            == (a_vals[prev as int] + b_vals[prev as int] + limb_carry(a_vals, b_vals, prev))
               / LIMB_BASE());
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
    //  add_result_limb = Mod(add_full_sum, LIMB_BASE)
    //  add_full_sum = a[limb] + b[limb] + carry[limb]
    //  Result = (a[limb] + b[limb] + carry[limb]) % LIMB_BASE = limb_result(...)
    lemma_add_carry_correct(a_buf, b_buf, n_limbs, limb, env, arrays);
    lemma_limb_read_eval(a_buf, n_limbs, limb, env, arrays, tid);
    lemma_limb_read_eval(b_buf, n_limbs, limb, env, arrays, tid);
}

} //  verus!
