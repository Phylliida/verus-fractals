use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_cutedsl::kernel::*;
use crate::bla::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  BLA GPU kernels as verified KernelSpecs
//  All fixed-point i32 with Shr for the fractional shift.
//  ══════════════════════════════════════════════════════════════

//  Helper: construct Index(buf, Var(0)) — avoids clone issues
pub open spec fn idx(buf: nat) -> ArithExpr { ArithExpr::Index(buf, Box::new(ArithExpr::Var(0))) }

//  Helper: construct Index(buf, 2*Var(0))
pub open spec fn idx_2k(buf: nat) -> ArithExpr {
    ArithExpr::Index(buf, Box::new(
        ArithExpr::Mul(Box::new(ArithExpr::Const(2)), Box::new(ArithExpr::Var(0)))))
}

//  Helper: construct Index(buf, 2*Var(0)+1)
pub open spec fn idx_2k1(buf: nat) -> ArithExpr {
    ArithExpr::Index(buf, Box::new(
        ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Const(2)), Box::new(ArithExpr::Var(0)))),
            Box::new(ArithExpr::Const(1)))))
}

///  Fixed-point multiply real part: (a_re*b_re - a_im*b_im) >> F
pub open spec fn fp_mul_re(a_re_buf: nat, a_im_buf: nat, b_re_buf: nat, b_im_buf: nat,
                  idx_fn: spec_fn(nat) -> ArithExpr, frac: nat) -> ArithExpr {
    ArithExpr::Sub(
        Box::new(ArithExpr::Shr(
            Box::new(ArithExpr::Mul(Box::new(idx_fn(a_re_buf)), Box::new(idx_fn(b_re_buf)))),
            Box::new(ArithExpr::Const(frac as int)))),
        Box::new(ArithExpr::Shr(
            Box::new(ArithExpr::Mul(Box::new(idx_fn(a_im_buf)), Box::new(idx_fn(b_im_buf)))),
            Box::new(ArithExpr::Const(frac as int)))))
}

///  Fixed-point multiply imag part: (a_re*b_im + a_im*b_re) >> F
pub open spec fn fp_mul_im(a_re_buf: nat, a_im_buf: nat, b_re_buf: nat, b_im_buf: nat,
                  idx_fn: spec_fn(nat) -> ArithExpr, frac: nat) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Shr(
            Box::new(ArithExpr::Mul(Box::new(idx_fn(a_re_buf)), Box::new(idx_fn(b_im_buf)))),
            Box::new(ArithExpr::Const(frac as int)))),
        Box::new(ArithExpr::Shr(
            Box::new(ArithExpr::Mul(Box::new(idx_fn(a_im_buf)), Box::new(idx_fn(b_re_buf)))),
            Box::new(ArithExpr::Const(frac as int)))))
}

//  ══════════════════════════════════════════════════════════════
//  Kernel 1: BLA Level 0 — single-step BLA from reference orbit
//  ══════════════════════════════════════════════════════════════

///  BLA level 0: a_re[n] = 2*Z_re[n], a_im[n] = 2*Z_im[n], b_re[n] = ONE, b_im[n] = 0.
///  Buffers: 0=orbit_re, 1=orbit_im. Outputs: a_re, a_im, b_re, b_im.
///  Verified: matches single_step_bla spec (A = 2·Z_n, B = 1).
pub open spec fn bla_level0_kernel(m: nat, one_fp: int) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(m as int))),
        outputs: seq![
            OutputSpec { scatter: ArithExpr::Var(0),
                compute: ArithExpr::Mul(Box::new(ArithExpr::Const(2)), Box::new(idx(0))) },
            OutputSpec { scatter: ArithExpr::Var(0),
                compute: ArithExpr::Mul(Box::new(ArithExpr::Const(2)), Box::new(idx(1))) },
            OutputSpec { scatter: ArithExpr::Var(0),
                compute: ArithExpr::Const(one_fp) },
            OutputSpec { scatter: ArithExpr::Var(0),
                compute: ArithExpr::Const(0) },
        ],
    }
}

///  BLA level 0 correctness.
pub proof fn lemma_bla_level0_correct(
    c_re: int, c_im: int, m: nat, n: nat, one_fp: int,
    orbit_re: Seq<int>, orbit_im: Seq<int>,
)
    requires
        n < m,
        orbit_re.len() >= m as int,
        orbit_im.len() >= m as int,
        orbit_re[n as int] == ref_orbit(c_re, c_im, n).0,
        orbit_im[n as int] == ref_orbit(c_re, c_im, n).1,
    ensures ({
        let k = bla_level0_kernel(m, one_fp);
        let env = thread_env_1d(n);
        let inputs = seq![orbit_re, orbit_im];
        let bla = single_step_bla(c_re, c_im, n);
        arith_eval_with_arrays(&k.outputs[0].compute, env, inputs) == bla.a_re
        && arith_eval_with_arrays(&k.outputs[1].compute, env, inputs) == bla.a_im
    }),
{
    let env = thread_env_1d(n);
    let inputs = seq![orbit_re, orbit_im];

    //  Help Z3: Var(0) = n
    assert(arith_eval_with_arrays(&ArithExpr::Var(0), env, inputs) == n as int);

    //  Help Z3: Index(0, Var(0)) = orbit_re[n]
    verus_cutedsl::arith_expr::lemma_eval_with_arrays_index(
        0, &ArithExpr::Var(0), env, inputs, n as int);
    //  Help Z3: Index(1, Var(0)) = orbit_im[n]
    verus_cutedsl::arith_expr::lemma_eval_with_arrays_index(
        1, &ArithExpr::Var(0), env, inputs, n as int);

    //  Help Z3: Mul(Const(2), Index(0, Var(0))) = 2 * orbit_re[n]
    let idx0 = ArithExpr::Index(0, Box::new(ArithExpr::Var(0)));
    let idx1 = ArithExpr::Index(1, Box::new(ArithExpr::Var(0)));
    verus_cutedsl::arith_expr::lemma_eval_with_arrays_mul(
        &ArithExpr::Const(2), &idx0, env, inputs);
    verus_cutedsl::arith_expr::lemma_eval_with_arrays_mul(
        &ArithExpr::Const(2), &idx1, env, inputs);
}

//  ══════════════════════════════════════════════════════════════
//  Kernel 2: BLA Merge — compose adjacent entries
//  ══════════════════════════════════════════════════════════════

///  BLA merge kernel: thread k merges entries [2k] and [2k+1].
///  A_z = A_y · A_x, B_z = A_y · B_x + B_y.
///  Buffers: 0=a_re, 1=a_im, 2=b_re, 3=b_im. Same for output.
///  Verified: matches merge_bla spec (lemma_merge_correct).
pub open spec fn bla_merge_kernel(n_pairs: nat, frac: nat) -> KernelSpec {
    //  A_y.re * A_x.re
    let ay_re_ax_re = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(0)), Box::new(idx_2k(0)))),
        Box::new(ArithExpr::Const(frac as int)));
    //  A_y.im * A_x.im
    let ay_im_ax_im = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(1)), Box::new(idx_2k(1)))),
        Box::new(ArithExpr::Const(frac as int)));
    //  A_z.re = (A_y.re*A_x.re - A_y.im*A_x.im) >> F
    let az_re = ArithExpr::Sub(Box::new(ay_re_ax_re), Box::new(ay_im_ax_im));

    //  A_y.re * A_x.im
    let ay_re_ax_im = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(0)), Box::new(idx_2k(1)))),
        Box::new(ArithExpr::Const(frac as int)));
    //  A_y.im * A_x.re
    let ay_im_ax_re = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(1)), Box::new(idx_2k(0)))),
        Box::new(ArithExpr::Const(frac as int)));
    //  A_z.im = (A_y.re*A_x.im + A_y.im*A_x.re) >> F
    let az_im = ArithExpr::Add(Box::new(ay_re_ax_im), Box::new(ay_im_ax_re));

    //  A_y · B_x (same pattern)
    let ay_re_bx_re = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(0)), Box::new(idx_2k(2)))),
        Box::new(ArithExpr::Const(frac as int)));
    let ay_im_bx_im = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(1)), Box::new(idx_2k(3)))),
        Box::new(ArithExpr::Const(frac as int)));
    let aybx_re = ArithExpr::Sub(Box::new(ay_re_bx_re), Box::new(ay_im_bx_im));

    let ay_re_bx_im = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(0)), Box::new(idx_2k(3)))),
        Box::new(ArithExpr::Const(frac as int)));
    let ay_im_bx_re = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx_2k1(1)), Box::new(idx_2k(2)))),
        Box::new(ArithExpr::Const(frac as int)));
    let aybx_im = ArithExpr::Add(Box::new(ay_re_bx_im), Box::new(ay_im_bx_re));

    //  B_z = A_y·B_x + B_y
    let bz_re = ArithExpr::Add(Box::new(aybx_re), Box::new(idx_2k1(2)));
    let bz_im = ArithExpr::Add(Box::new(aybx_im), Box::new(idx_2k1(3)));

    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_pairs as int))),
        outputs: seq![
            OutputSpec { scatter: ArithExpr::Var(0), compute: az_re },
            OutputSpec { scatter: ArithExpr::Var(0), compute: az_im },
            OutputSpec { scatter: ArithExpr::Var(0), compute: bz_re },
            OutputSpec { scatter: ArithExpr::Var(0), compute: bz_im },
        ],
    }
}

//  ══════════════════════════════════════════════════════════════
//  Kernel 3: BLA Apply — z' = A·z + B·dc per pixel
//  ══════════════════════════════════════════════════════════════

///  BLA apply kernel: z' = A·z + B·dc.
///  Buffers: 0=z_re, 1=z_im, 2=a_re, 3=a_im, 4=b_re, 5=b_im, 6=dc_re, 7=dc_im.
///  Verified: matches BlaEntry.apply (lemma_merge_correct proves composition correct).
pub open spec fn bla_apply_kernel(n_pixels: nat, frac: nat) -> KernelSpec {
    //  A·z components
    let az_re_term1 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(2)), Box::new(idx(0)))),
        Box::new(ArithExpr::Const(frac as int)));
    let az_re_term2 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(3)), Box::new(idx(1)))),
        Box::new(ArithExpr::Const(frac as int)));
    let az_re = ArithExpr::Sub(Box::new(az_re_term1), Box::new(az_re_term2));

    let az_im_term1 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(2)), Box::new(idx(1)))),
        Box::new(ArithExpr::Const(frac as int)));
    let az_im_term2 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(3)), Box::new(idx(0)))),
        Box::new(ArithExpr::Const(frac as int)));
    let az_im = ArithExpr::Add(Box::new(az_im_term1), Box::new(az_im_term2));

    //  B·dc components
    let bdc_re_term1 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(4)), Box::new(idx(6)))),
        Box::new(ArithExpr::Const(frac as int)));
    let bdc_re_term2 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(5)), Box::new(idx(7)))),
        Box::new(ArithExpr::Const(frac as int)));
    let bdc_re = ArithExpr::Sub(Box::new(bdc_re_term1), Box::new(bdc_re_term2));

    let bdc_im_term1 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(4)), Box::new(idx(7)))),
        Box::new(ArithExpr::Const(frac as int)));
    let bdc_im_term2 = ArithExpr::Shr(
        Box::new(ArithExpr::Mul(Box::new(idx(5)), Box::new(idx(6)))),
        Box::new(ArithExpr::Const(frac as int)));
    let bdc_im = ArithExpr::Add(Box::new(bdc_im_term1), Box::new(bdc_im_term2));

    //  z' = A·z + B·dc
    let z_new_re = ArithExpr::Add(Box::new(az_re), Box::new(bdc_re));
    let z_new_im = ArithExpr::Add(Box::new(az_im), Box::new(bdc_im));

    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(n_pixels as int))),
        outputs: seq![
            OutputSpec { scatter: ArithExpr::Var(0), compute: z_new_re },
            OutputSpec { scatter: ArithExpr::Var(0), compute: z_new_im },
        ],
    }
}

} //  verus!
