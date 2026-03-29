///  Verified Mandelbrot kernel as a Stage tree.
///
///  Proves end-to-end: staged_eval(mandelbrot_kernel, init_state) computes
///  the correct Mandelbrot orbit for each pixel.
///
///  Uses exact int arithmetic (no fixed-point truncation). The fixed-point
///  version is a refinement that adds Shr nodes to the ArithExpr.

use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_cutedsl::kernel::*;
use verus_cutedsl::stage::*;
use verus_cutedsl::proof::stage_lemmas::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  Buffer layout
//  ══════════════════════════════════════════════════════════════

pub open spec fn BUF_Z_RE() -> nat { 0 }
pub open spec fn BUF_Z_IM() -> nat { 1 }
pub open spec fn BUF_C_RE() -> nat { 2 }
pub open spec fn BUF_C_IM() -> nat { 3 }
pub open spec fn NUM_BUFS() -> nat { 4 }

///  Index(buf, Var(0)) — thread i reads buf[i].
pub open spec fn idx(buf: nat) -> ArithExpr {
    ArithExpr::Index(buf, Box::new(ArithExpr::Var(0)))
}

//  ══════════════════════════════════════════════════════════════
//  Mandelbrot step kernel: z' = z² + c
//  ══════════════════════════════════════════════════════════════

pub open spec fn mandelbrot_step_kernel(n_pixels: nat) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_pixels as int))),
        outputs: seq![
            OutputSpec {
                scatter: ArithExpr::Var(0),
                compute: ArithExpr::Add(
                    Box::new(ArithExpr::Sub(
                        Box::new(ArithExpr::Mul(Box::new(idx(0)), Box::new(idx(0)))),
                        Box::new(ArithExpr::Mul(Box::new(idx(1)), Box::new(idx(1)))))),
                    Box::new(idx(2))),
            },
            OutputSpec {
                scatter: ArithExpr::Var(0),
                compute: ArithExpr::Add(
                    Box::new(ArithExpr::Mul(
                        Box::new(ArithExpr::Const(2)),
                        Box::new(ArithExpr::Mul(Box::new(idx(0)), Box::new(idx(1)))))),
                    Box::new(idx(3))),
            },
        ],
    }
}

//  ══════════════════════════════════════════════════════════════
//  Mandelbrot orbit spec
//  ══════════════════════════════════════════════════════════════

pub open spec fn mandelbrot_orbit(c_re: int, c_im: int, n: nat) -> (int, int)
    decreases n,
{
    if n == 0 { (0, 0) }
    else {
        let (zr, zi) = mandelbrot_orbit(c_re, c_im, (n - 1) as nat);
        (zr * zr - zi * zi + c_re, 2 * zr * zi + c_im)
    }
}

pub open spec fn mandelbrot_step(zr: int, zi: int, cr: int, ci: int) -> (int, int) {
    (zr * zr - zi * zi + cr, 2 * zr * zi + ci)
}

pub proof fn lemma_orbit_step(c_re: int, c_im: int, n: nat)
    ensures ({
        let (zr, zi) = mandelbrot_orbit(c_re, c_im, n);
        mandelbrot_orbit(c_re, c_im, n + 1) == mandelbrot_step(zr, zi, c_re, c_im)
    }),
{}

//  ══════════════════════════════════════════════════════════════
//  Kernel correctness: ArithExpr computes mandelbrot_step
//  ══════════════════════════════════════════════════════════════

pub proof fn lemma_mandelbrot_step_kernel_correct(
    n_pixels: nat,
    z_re_buf: Seq<int>, z_im_buf: Seq<int>,
    c_re_buf: Seq<int>, c_im_buf: Seq<int>,
    px: nat,
)
    requires
        px < n_pixels,
        z_re_buf.len() >= n_pixels as int,
        z_im_buf.len() >= n_pixels as int,
        c_re_buf.len() >= n_pixels as int,
        c_im_buf.len() >= n_pixels as int,
    ensures ({
        let k = mandelbrot_step_kernel(n_pixels);
        let env = thread_env_1d(px);
        let inputs = seq![z_re_buf, z_im_buf, c_re_buf, c_im_buf];
        let (new_re, new_im) = mandelbrot_step(
            z_re_buf[px as int], z_im_buf[px as int],
            c_re_buf[px as int], c_im_buf[px as int]);
        arith_eval_with_arrays(&k.guard, env, inputs) != 0
        && arith_eval_with_arrays(&k.outputs[0].compute, env, inputs) == new_re
        && arith_eval_with_arrays(&k.outputs[1].compute, env, inputs) == new_im
        && arith_eval_with_arrays(&k.outputs[0].scatter, env, inputs) == px as int
        && arith_eval_with_arrays(&k.outputs[1].scatter, env, inputs) == px as int
    }),
{
    let k = mandelbrot_step_kernel(n_pixels);
    let env = thread_env_1d(px);
    let inputs = seq![z_re_buf, z_im_buf, c_re_buf, c_im_buf];
    let var0 = ArithExpr::Var(0);
    let idx0 = idx(0); let idx1 = idx(1); let idx2 = idx(2); let idx3 = idx(3);

    assert(arith_eval_with_arrays(&var0, env, inputs) == px as int);
    lemma_eval_with_arrays_index(0, &var0, env, inputs, px as int);
    lemma_eval_with_arrays_index(1, &var0, env, inputs, px as int);
    lemma_eval_with_arrays_index(2, &var0, env, inputs, px as int);
    lemma_eval_with_arrays_index(3, &var0, env, inputs, px as int);

    lemma_eval_with_arrays_cmp(&CmpOp::Lt, &var0,
        &ArithExpr::Const(n_pixels as int), env, inputs);

    //  Output 0: z_re² - z_im² + c_re
    lemma_eval_with_arrays_mul(&idx0, &idx0, env, inputs);
    lemma_eval_with_arrays_mul(&idx1, &idx1, env, inputs);
    let zr_sq = ArithExpr::Mul(Box::new(idx0), Box::new(idx0));
    let zi_sq = ArithExpr::Mul(Box::new(idx1), Box::new(idx1));
    lemma_eval_with_arrays_sub(&zr_sq, &zi_sq, env, inputs);
    let diff = ArithExpr::Sub(Box::new(zr_sq), Box::new(zi_sq));
    lemma_eval_with_arrays_add(&diff, &idx2, env, inputs);

    //  Output 1: 2 * z_re * z_im + c_im
    lemma_eval_with_arrays_mul(&idx0, &idx1, env, inputs);
    let cross = ArithExpr::Mul(Box::new(idx0), Box::new(idx1));
    lemma_eval_with_arrays_mul(&ArithExpr::Const(2), &cross, env, inputs);
    let two_cross = ArithExpr::Mul(Box::new(ArithExpr::Const(2)), Box::new(cross));
    lemma_eval_with_arrays_add(&two_cross, &idx3, env, inputs);

    assert(k.outputs[0].compute == ArithExpr::Add(
        Box::new(ArithExpr::Sub(
            Box::new(ArithExpr::Mul(Box::new(idx(0)), Box::new(idx(0)))),
            Box::new(ArithExpr::Mul(Box::new(idx(1)), Box::new(idx(1)))))),
        Box::new(idx(2))));
    assert(k.outputs[1].compute == ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Const(2)),
            Box::new(ArithExpr::Mul(Box::new(idx(0)), Box::new(idx(1)))))),
        Box::new(idx(3))));

    assert(2 * (z_re_buf[px as int] * z_im_buf[px as int])
        == 2 * z_re_buf[px as int] * z_im_buf[px as int]) by (nonlinear_arith);
}

//  ══════════════════════════════════════════════════════════════
//  Stage tree
//  ══════════════════════════════════════════════════════════════

pub open spec fn mandelbrot_body(n_pixels: nat) -> Stage {
    Stage::Map {
        spec: mandelbrot_step_kernel(n_pixels),
        input_bufs: seq![BUF_Z_RE(), BUF_Z_IM(), BUF_C_RE(), BUF_C_IM()],
        output_bufs: seq![BUF_Z_RE(), BUF_Z_IM()],
        thread_dim: ThreadDim::Dim1D,
    }
}

pub open spec fn mandelbrot_kernel(n_pixels: nat, max_iter: nat) -> Stage {
    Stage::Loop {
        bound: max_iter,
        body: Box::new(mandelbrot_body(n_pixels)),
        invariant: |_s: SharedState, _i: nat| true,
    }
}

pub open spec fn mandelbrot_init_state(
    n_pixels: nat, c_re_vals: Seq<int>, c_im_vals: Seq<int>,
) -> SharedState {
    SharedState {
        buffers: seq![
            Seq::new(n_pixels, |_i: int| 0int),
            Seq::new(n_pixels, |_i: int| 0int),
            c_re_vals,
            c_im_vals,
        ],
        workgroup_size: n_pixels,
    }
}

//  ══════════════════════════════════════════════════════════════
//  Loop invariant
//  ══════════════════════════════════════════════════════════════

pub open spec fn orbit_invariant(
    n_pixels: nat, c_re_vals: Seq<int>, c_im_vals: Seq<int>,
) -> spec_fn(SharedState, nat) -> bool {
    |state: SharedState, iter: nat|
        state.buffers.len() == NUM_BUFS()
        && state.buffers[BUF_Z_RE() as int].len() == n_pixels as int
        && state.buffers[BUF_Z_IM() as int].len() == n_pixels as int
        && state.buffers[BUF_C_RE() as int] == c_re_vals
        && state.buffers[BUF_C_IM() as int] == c_im_vals
        && state.workgroup_size == n_pixels
        && forall|px: int| 0 <= px < n_pixels as int ==>
            #[trigger] state.buffers[BUF_Z_RE() as int][px]
                == mandelbrot_orbit(c_re_vals[px], c_im_vals[px], iter).0
            && state.buffers[BUF_Z_IM() as int][px]
                == mandelbrot_orbit(c_re_vals[px], c_im_vals[px], iter).1
}

pub proof fn lemma_orbit_invariant_init(
    n_pixels: nat, c_re_vals: Seq<int>, c_im_vals: Seq<int>,
)
    requires
        c_re_vals.len() == n_pixels as int,
        c_im_vals.len() == n_pixels as int,
        n_pixels > 0,
    ensures
        orbit_invariant(n_pixels, c_re_vals, c_im_vals)(
            mandelbrot_init_state(n_pixels, c_re_vals, c_im_vals), 0),
{
    let state = mandelbrot_init_state(n_pixels, c_re_vals, c_im_vals);
    assert forall|px: int| 0 <= px < n_pixels as int implies
        #[trigger] state.buffers[BUF_Z_RE() as int][px]
            == mandelbrot_orbit(c_re_vals[px], c_im_vals[px], 0).0
        && state.buffers[BUF_Z_IM() as int][px]
            == mandelbrot_orbit(c_re_vals[px], c_im_vals[px], 0).1
    by {
        assert(mandelbrot_orbit(c_re_vals[px], c_im_vals[px], 0) == (0int, 0int));
    }
}

//  ══════════════════════════════════════════════════════════════
//  Preservation: one step advances the orbit
//
//  With the declarative eval_map, this is clean:
//  eval_map uses map_output_declarative which is a Seq::new.
//  Each pixel px gets compute(px, inputs) = mandelbrot_step(z[px], c[px]).
//  ══════════════════════════════════════════════════════════════

pub proof fn lemma_orbit_invariant_preserved(
    n_pixels: nat,
    c_re_vals: Seq<int>,
    c_im_vals: Seq<int>,
    state: SharedState,
    k: nat,
)
    requires
        n_pixels > 0,
        c_re_vals.len() == n_pixels as int,
        c_im_vals.len() == n_pixels as int,
        orbit_invariant(n_pixels, c_re_vals, c_im_vals)(state, k),
    ensures
        orbit_invariant(n_pixels, c_re_vals, c_im_vals)(
            staged_eval(&mandelbrot_body(n_pixels), state), k + 1),
{
    let body = mandelbrot_body(n_pixels);
    let spec = mandelbrot_step_kernel(n_pixels);
    let input_bufs = seq![BUF_Z_RE(), BUF_Z_IM(), BUF_C_RE(), BUF_C_IM()];
    let output_bufs = seq![BUF_Z_RE(), BUF_Z_IM()];
    let dim = ThreadDim::Dim1D;
    let old_zr = state.buffers[BUF_Z_RE() as int];
    let old_zi = state.buffers[BUF_Z_IM() as int];
    let inputs = seq![old_zr, old_zi, c_re_vals, c_im_vals];
    let ws = thread_count(&dim, state.workgroup_size);

    //  staged_eval(body) = eval_map(spec, input_bufs, output_bufs, state, &dim)
    let new_state = staged_eval(&body, state);
    //  Help Z3 see through the match in staged_eval
    assert(new_state == eval_map(&spec, input_bufs, output_bufs, state, &dim));

    //  Unfold eval_map into two set_buffer calls via map_output_declarative
    lemma_eval_map_two_outputs(&spec, input_bufs, output_bufs, state, &dim);

    let new_zr_buf = map_output_declarative(&spec, 0, inputs,
        old_zr, ws, &dim);
    let after_zr = state.set_buffer(BUF_Z_RE(), new_zr_buf);
    let new_zi_buf = map_output_declarative(&spec, 1, inputs,
        after_zr.buffers[BUF_Z_IM() as int], ws, &dim);
    let after_both = after_zr.set_buffer(BUF_Z_IM(), new_zi_buf);

    //  eval_map == after_both (from lemma_eval_map_two_outputs)
    assert(eval_map(&spec, input_bufs, output_bufs, state, &dim) == after_both);
    assert(new_state == after_both);

    //  c buffers unchanged: set_buffer on buf 0 doesn't affect bufs 2,3
    //  set_buffer on buf 1 doesn't affect bufs 2,3
    lemma_set_buffer_other(state, BUF_Z_RE(), new_zr_buf, BUF_C_RE());
    lemma_set_buffer_other(state, BUF_Z_RE(), new_zr_buf, BUF_C_IM());
    lemma_set_buffer_other(after_zr, BUF_Z_IM(), new_zi_buf, BUF_C_RE());
    lemma_set_buffer_other(after_zr, BUF_Z_IM(), new_zi_buf, BUF_C_IM());

    //  z_im unchanged after first set_buffer (buf 0 != buf 1)
    lemma_set_buffer_other(state, BUF_Z_RE(), new_zr_buf, BUF_Z_IM());
    //  So after_zr.buffers[BUF_Z_IM()] == old_zi
    assert(after_zr.buffers[BUF_Z_IM() as int] == old_zi);

    //  Structural properties of new_state
    assert(after_both.buffers.len() == NUM_BUFS());
    assert(after_both.workgroup_size == n_pixels);
    assert(after_both.buffers[BUF_C_RE() as int] == c_re_vals);
    assert(after_both.buffers[BUF_C_IM() as int] == c_im_vals);

    //  Bridge: thread_env_for_dim(Dim1D, t) == thread_env_1d(t)
    assert forall|t: nat| thread_env_for_dim(&dim, t) == thread_env_1d(t) by {}

    //  Per-pixel orbit correctness
    assert forall|px: int| 0 <= px < n_pixels as int implies
        #[trigger] after_both.buffers[BUF_Z_RE() as int][px]
            == mandelbrot_orbit(c_re_vals[px], c_im_vals[px], (k + 1) as nat).0
        && after_both.buffers[BUF_Z_IM() as int][px]
            == mandelbrot_orbit(c_re_vals[px], c_im_vals[px], (k + 1) as nat).1
    by {
        //  Old z values from invariant
        let (orbit_re, orbit_im) = mandelbrot_orbit(c_re_vals[px], c_im_vals[px], k);
        assert(old_zr[px] == orbit_re);
        assert(old_zi[px] == orbit_im);

        //  Kernel correctness
        lemma_mandelbrot_step_kernel_correct(
            n_pixels, old_zr, old_zi, c_re_vals, c_im_vals, px as nat);

        //  Orbit step
        lemma_orbit_step(c_re_vals[px], c_im_vals[px], k);

        //  map_output_declarative for output 0 (z_re): thread px writes compute_0
        //  Since scatter = Var(0) = px, thread px is the writer for position px
        assert(thread_env_for_dim(&dim, px as nat) == thread_env_1d(px as nat));
        assert(arith_eval_with_arrays(&spec.guard,
            thread_env_for_dim(&dim, px as nat), inputs) != 0);
        assert(arith_eval_with_arrays(&spec.outputs[0].scatter,
            thread_env_for_dim(&dim, px as nat), inputs) == px);

        //  new_zr_buf[px] = compute_0(px, inputs) = z_re² - z_im² + c_re
        //  new_zi_buf[px] = compute_1(px, inputs) = 2*z_re*z_im + c_im
        //  (These follow from the exists/choose in map_output_declarative
        //   since thread px satisfies the predicate)
    }

    //  Buffer lengths preserved
    assert(new_zr_buf.len() == old_zr.len());
    assert(after_both.buffers[BUF_Z_RE() as int].len() == n_pixels as int);
    assert(after_both.buffers[BUF_Z_IM() as int].len() == n_pixels as int);
}

//  ══════════════════════════════════════════════════════════════
//  End-to-end theorem
//  ══════════════════════════════════════════════════════════════

pub proof fn theorem_mandelbrot_orbit_correctness(
    n_pixels: nat,
    c_re_vals: Seq<int>,
    c_im_vals: Seq<int>,
    max_iter: nat,
)
    requires
        n_pixels > 0,
        c_re_vals.len() == n_pixels as int,
        c_im_vals.len() == n_pixels as int,
    ensures ({
        let final_state = staged_eval(
            &mandelbrot_kernel(n_pixels, max_iter),
            mandelbrot_init_state(n_pixels, c_re_vals, c_im_vals));
        forall|px: int| 0 <= px < n_pixels as int ==> {
            let (zr, zi) = mandelbrot_orbit(c_re_vals[px], c_im_vals[px], max_iter);
            &&& #[trigger] final_state.buffers[BUF_Z_RE() as int][px] == zr
            &&& final_state.buffers[BUF_Z_IM() as int][px] == zi
        }
    }),
{
    let init = mandelbrot_init_state(n_pixels, c_re_vals, c_im_vals);
    let body = mandelbrot_body(n_pixels);
    let inv = orbit_invariant(n_pixels, c_re_vals, c_im_vals);

    //  1. Invariant holds initially
    lemma_orbit_invariant_init(n_pixels, c_re_vals, c_im_vals);

    //  2. staged_eval(kernel) = eval_loop(body, init, max_iter, 0)
    let kernel = mandelbrot_kernel(n_pixels, max_iter);
    assert(staged_eval(&kernel, init) == eval_loop(&body, init, max_iter, 0));

    //  3. Invariant preserved by each step (in trigger form for lemma_loop_inv)
    assert forall|s: SharedState, k: nat|
        #[trigger] inv(staged_eval(&body, s), k + 1)
        || !(k < max_iter && inv(s, k))
    by {
        if k < max_iter && inv(s, k) {
            lemma_orbit_invariant_preserved(n_pixels, c_re_vals, c_im_vals, s, k);
        }
    }

    //  4. Apply loop invariant induction
    lemma_loop_inv(&body, init, max_iter, inv);

    //  5. Extract result from invariant at iteration max_iter
    let final_state = eval_loop(&body, init, max_iter, 0);
    assert(inv(final_state, max_iter));
}

} //  verus!
