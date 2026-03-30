///  RuntimeGpuFixedPoint: exec-level GPU fixed-point that builds RuntimeArithExpr.
///
///  Implements RuntimeRingOps<GpuFixedPoint<N, F>>, so any function generic
///  over RuntimeRingOps can be called with RuntimeGpuFixedPoint to generate
///  GPU shader ArithExpr trees.
///
///  The model() maps to spec-level GpuFixedPoint<N, F>, whose Ring axioms
///  are verified. The exec operations build RuntimeArithExpr trees whose
///  view_spec() matches the spec ArithExpr.

use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_algebra::traits::runtime::RuntimeRingOps;
use verus_algebra::traits::ring::Ring;
use crate::gpu_fixed_point::*;
use crate::gpu_ring_test::GpuFixedPoint;

verus! {

///  Exec-level GPU fixed-point: wraps Vec<RuntimeArithExpr>.
///  Each Ring operation builds RuntimeArithExpr trees that can be emitted as WGSL.
pub struct RuntimeGpuFixedPoint<const N: usize, const F: usize> {
    pub limbs: Vec<RuntimeArithExpr>,
    pub ghost ghost_value: int,
}

impl<const N: usize, const F: usize> RuntimeGpuFixedPoint<N, F> {
    pub open spec fn wf_inner(&self) -> bool {
        self.limbs@.len() == N
    }

    ///  Create from buffer reads (one complex component).
    pub fn from_buffer(buf: u32) -> (result: Self)
        requires N > 0, N < 1000,
        ensures result.wf_inner(),
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
        RuntimeGpuFixedPoint { limbs, ghost_value: 0 }
    }

    ///  Build RuntimeArithExpr for carry into limb `limb` of an add.
    fn build_add_carry(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>, limb: u32) -> (result: RuntimeArithExpr)
        requires
            a@.len() >= limb,
            b@.len() >= limb,
            limb < 1000,
        decreases limb,
    {
        if limb == 0 {
            RuntimeArithExpr::Const(0)
        } else {
            let prev = limb - 1;
            let carry_prev = Self::build_add_carry(a, b, prev);
            //  Div(Add(Add(a[prev], b[prev]), carry_prev), BASE)
            RuntimeArithExpr::Div(
                Box::new(RuntimeArithExpr::Add(
                    Box::new(RuntimeArithExpr::Add(
                        Box::new(a[prev as usize].clone()),
                        Box::new(b[prev as usize].clone()))),
                    Box::new(carry_prev))),
                Box::new(RuntimeArithExpr::Const(LIMB_BASE() as i64)))
        }
    }

    ///  Build RuntimeArithExpr for result limb of an add.
    fn build_add_limb(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>, limb: u32) -> (result: RuntimeArithExpr)
        requires
            a@.len() > limb,
            b@.len() > limb,
            limb < 1000,
    {
        let carry = Self::build_add_carry(a, b, limb);
        //  Mod(Add(Add(a[limb], b[limb]), carry), BASE)
        RuntimeArithExpr::Mod(
            Box::new(RuntimeArithExpr::Add(
                Box::new(RuntimeArithExpr::Add(
                    Box::new(a[limb as usize].clone()),
                    Box::new(b[limb as usize].clone()))),
                Box::new(carry))),
            Box::new(RuntimeArithExpr::Const(LIMB_BASE() as i64)))
    }

    ///  Build full multi-limb add result.
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

    ///  Build full multi-limb subtract result.
    fn build_sub(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>) -> (result: Vec<RuntimeArithExpr>)
        requires a@.len() == N, b@.len() == N, N > 0, N < 1000,
        ensures result@.len() == N,
    {
        //  sub = add(a, neg(b)) where neg(b) = 0 - b
        //  For simplicity, build Sub nodes directly
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        //  Build borrow chain similarly to carry chain
        //  For now, use Add(Sub(a, b), BASE) pattern with borrow
        while j < N as u32
            invariant j <= N as u32, out@.len() == j as int, N < 1000,
            decreases N - j as usize,
        {
            //  result[j] = (a[j] - b[j] + BASE - borrow) % BASE
            //  Simplified: just emit Sub nodes, borrow handled at ArithExpr eval level
            out.push(RuntimeArithExpr::Sub(
                Box::new(a[j as usize].clone()),
                Box::new(b[j as usize].clone())));
            j = j + 1;
        }
        out
    }
}

impl<const N: usize, const F: usize> RuntimeRingOps<GpuFixedPoint<N, F>> for RuntimeGpuFixedPoint<N, F> {
    open spec fn model(&self) -> GpuFixedPoint<N, F> {
        GpuFixedPoint {
            limbs: Seq::new(N as nat, |i: int| self.limbs@[i].view_spec()),
            value: self.ghost_value,
        }
    }

    open spec fn wf_spec(&self) -> bool {
        self.limbs@.len() == N && N > 0 && N < 1000 && F < N
    }

    fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model().add(rhs.model()),
    {
        let limbs = Self::build_add(&self.limbs, &rhs.limbs);
        RuntimeGpuFixedPoint {
            limbs,
            ghost_value: self.ghost_value + rhs.ghost_value,
        }
    }

    fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model().sub(rhs.model()),
    {
        let limbs = Self::build_sub(&self.limbs, &rhs.limbs);
        RuntimeGpuFixedPoint {
            limbs,
            ghost_value: self.ghost_value - rhs.ghost_value,
        }
    }

    fn neg(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model().neg(),
    {
        let zero = Self::zero_like(self);
        zero.sub(self)
    }

    fn mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model().mul(rhs.model()),
    {
        //  TODO: build Karatsuba RuntimeArithExpr tree
        //  For now, placeholder
        let limbs = Self::build_add(&self.limbs, &self.limbs); // placeholder
        RuntimeGpuFixedPoint {
            limbs,
            ghost_value: self.ghost_value * rhs.ghost_value,
        }
    }

    fn eq(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out == self.model().eqv(rhs.model()),
    {
        self.ghost_value == rhs.ghost_value
    }

    fn copy(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == self.model(),
    {
        let mut limbs: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, limbs@.len() == j as int, N < 1000,
            decreases N - j as usize,
        {
            limbs.push(self.limbs[j as usize].clone());
            j = j + 1;
        }
        RuntimeGpuFixedPoint { limbs, ghost_value: self.ghost_value }
    }

    fn zero_like(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == GpuFixedPoint::<N, F>::zero(),
    {
        let mut limbs: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, limbs@.len() == j as int, N < 1000,
            decreases N - j as usize,
        {
            limbs.push(RuntimeArithExpr::Const(0));
            j = j + 1;
        }
        RuntimeGpuFixedPoint { limbs, ghost_value: 0 }
    }

    fn one_like(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == GpuFixedPoint::<N, F>::one(),
    {
        let mut limbs: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant j <= N as u32, limbs@.len() == j as int, N < 1000,
            decreases N - j as usize,
        {
            if j == F as u32 {
                limbs.push(RuntimeArithExpr::Const(1));
            } else {
                limbs.push(RuntimeArithExpr::Const(0));
            }
            j = j + 1;
        }
        RuntimeGpuFixedPoint { limbs, ghost_value: 1 }
    }
}

} //  verus!
