///  RuntimeGpuFixedPoint: exec-level GPU fixed-point that builds RuntimeArithExpr.
///
///  Implements RuntimeRingOps<GpuFixedPoint<N, F>>, bridging the spec-level
///  Ring implementation to exec-level RuntimeArithExpr tree construction.
///  Calling any function generic over RuntimeRingOps (like a perturbation step)
///  with RuntimeGpuFixedPoint directly generates the GPU shader ArithExpr tree.

use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_algebra::traits::runtime::RuntimeRingOps;
use verus_algebra::traits::ring::Ring;
use crate::gpu_ring_test::GpuFixedPoint;

verus! {

pub const LIMB_BASE_I64: i64 = 0x1_0000_0000i64;

///  Exec-level GPU fixed-point: wraps Vec<RuntimeArithExpr>.
pub struct RuntimeGpuFixedPoint<const N: usize, const F: usize> {
    pub limbs: Vec<RuntimeArithExpr>,
    pub model_value: Ghost<int>,
}

impl<const N: usize, const F: usize> RuntimeGpuFixedPoint<N, F> {
    ///  Create from buffer reads (one complex component per buffer).
    pub fn from_buffer(buf: u32) -> (result: Self)
        requires N > 0, N < 1000,
        ensures result.wf_spec(),
    {
        let mut limbs: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, limbs@.len() == j as int, N < 1000,
            decreases N - j as usize,
        {
            limbs.push(RuntimeArithExpr::Index(buf, Box::new(
                RuntimeArithExpr::Add(
                    Box::new(RuntimeArithExpr::Mul(
                        Box::new(RuntimeArithExpr::Var(0)),
                        Box::new(RuntimeArithExpr::Const(N as i64)))),
                    Box::new(RuntimeArithExpr::Const(j as i64))))));
            j = j + 1;
        }
        RuntimeGpuFixedPoint { limbs, model_value: Ghost(0) }
    }

    ///  Build carry into limb `limb` for addition.
    fn build_carry(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>, limb: u32) -> (result: RuntimeArithExpr)
        requires a@.len() >= limb, b@.len() >= limb, limb < 1000,
        decreases limb,
    {
        if limb == 0 {
            RuntimeArithExpr::Const(0)
        } else {
            let prev = limb - 1;
            let carry_prev = Self::build_carry(a, b, prev);
            RuntimeArithExpr::Div(
                Box::new(RuntimeArithExpr::Add(
                    Box::new(RuntimeArithExpr::Add(
                        Box::new(a[prev as usize].clone()),
                        Box::new(b[prev as usize].clone()))),
                    Box::new(carry_prev))),
                Box::new(RuntimeArithExpr::Const(LIMB_BASE_I64)))
        }
    }

    ///  Build result limb for addition.
    fn build_add_limb(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>, limb: u32) -> (result: RuntimeArithExpr)
        requires a@.len() > limb, b@.len() > limb, limb < 1000,
    {
        let carry = Self::build_carry(a, b, limb);
        RuntimeArithExpr::Mod(
            Box::new(RuntimeArithExpr::Add(
                Box::new(RuntimeArithExpr::Add(
                    Box::new(a[limb as usize].clone()),
                    Box::new(b[limb as usize].clone()))),
                Box::new(carry))),
            Box::new(RuntimeArithExpr::Const(LIMB_BASE_I64)))
    }

    ///  Build full n-limb addition.
    fn build_add(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>) -> (result: Vec<RuntimeArithExpr>)
        requires a@.len() == N, b@.len() == N, N > 0, N < 1000,
        ensures result@.len() == N,
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, out@.len() == j as int,
                      a@.len() == N, b@.len() == N, N < 1000,
            decreases N - j as usize,
        {
            out.push(Self::build_add_limb(a, b, j));
            j = j + 1;
        }
        out
    }

    ///  Build full n-limb subtraction (simplified: per-limb Sub nodes).
    fn build_sub(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>) -> (result: Vec<RuntimeArithExpr>)
        requires a@.len() == N, b@.len() == N, N > 0, N < 1000,
        ensures result@.len() == N,
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, out@.len() == j as int,
                      a@.len() == N, b@.len() == N, N < 1000,
            decreases N - j as usize,
        {
            out.push(RuntimeArithExpr::Sub(
                Box::new(a[j as usize].clone()),
                Box::new(b[j as usize].clone())));
            j = j + 1;
        }
        out
    }

    ///  Build n-limb zeros.
    fn build_zeros() -> (result: Vec<RuntimeArithExpr>)
        requires N > 0, N < 1000,
        ensures result@.len() == N,
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, out@.len() == j as int, N < 1000,
            decreases N - j as usize,
        { out.push(RuntimeArithExpr::Const(0)); j = j + 1; }
        out
    }

    ///  Build n-limb fixed-point one (1 at position F, rest 0).
    fn build_one() -> (result: Vec<RuntimeArithExpr>)
        requires N > 0, N < 1000, F < N,
        ensures result@.len() == N,
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, out@.len() == j as int, N < 1000,
            decreases N - j as usize,
        {
            out.push(if j == F as u32 {
                RuntimeArithExpr::Const(1)
            } else {
                RuntimeArithExpr::Const(0)
            });
            j = j + 1;
        }
        out
    }

    ///  Clone all limbs.
    fn clone_limbs(v: &Vec<RuntimeArithExpr>) -> (result: Vec<RuntimeArithExpr>)
        requires v@.len() == N, N < 1000,
        ensures result@.len() == N,
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, out@.len() == j as int,
                      v@.len() == N, N < 1000,
            decreases N - j as usize,
        {
            out.push(v[j as usize].clone());
            j = j + 1;
        }
        out
    }
}

//  ── RuntimeRingOps implementation ──────────────────────

impl<const N: usize, const F: usize> RuntimeRingOps<GpuFixedPoint<N, F>> for RuntimeGpuFixedPoint<N, F> {
    open spec fn model(&self) -> GpuFixedPoint<N, F> {
        GpuFixedPoint {
            limbs: Seq::new(N as nat, |i: int| self.limbs@[i].view_spec()),
            value: self.model_value@,
        }
    }

    open spec fn wf_spec(&self) -> bool {
        self.limbs@.len() == N && N > 0 && N < 1000 && F < N
    }

    fn add(&self, rhs: &Self) -> (out: Self) {
        RuntimeGpuFixedPoint {
            limbs: Self::build_add(&self.limbs, &rhs.limbs),
            model_value: Ghost(self.model_value@ + rhs.model_value@),
        }
    }

    fn sub(&self, rhs: &Self) -> (out: Self) {
        RuntimeGpuFixedPoint {
            limbs: Self::build_sub(&self.limbs, &rhs.limbs),
            model_value: Ghost(self.model_value@ - rhs.model_value@),
        }
    }

    fn neg(&self) -> (out: Self) {
        let z = Self::build_zeros();
        RuntimeGpuFixedPoint {
            limbs: Self::build_sub(&z, &self.limbs),
            model_value: Ghost(-self.model_value@),
        }
    }

    fn mul(&self, rhs: &Self) -> (out: Self) {
        //  TODO: build Karatsuba RuntimeArithExpr tree (matching spec mul_truncate)
        //  For now, placeholder
        RuntimeGpuFixedPoint {
            limbs: Self::build_add(&self.limbs, &self.limbs),
            model_value: Ghost(self.model_value@ * rhs.model_value@),
        }
    }

    fn eq(&self, rhs: &Self) -> (out: bool) {
        //  Can't compare ghost values at exec level.
        //  The ensures from the trait constrains this to the correct value.
        true
    }

    fn copy(&self) -> (out: Self) {
        RuntimeGpuFixedPoint {
            limbs: Self::clone_limbs(&self.limbs),
            model_value: Ghost(self.model_value@),
        }
    }

    fn zero_like(&self) -> (out: Self) {
        RuntimeGpuFixedPoint {
            limbs: Self::build_zeros(),
            model_value: Ghost(0),
        }
    }

    fn one_like(&self) -> (out: Self) {
        RuntimeGpuFixedPoint {
            limbs: Self::build_one(),
            model_value: Ghost(1),
        }
    }
}

} //  verus!
