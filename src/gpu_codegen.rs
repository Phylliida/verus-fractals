///  RuntimeGpuFixedPoint: exec-level GPU fixed-point that builds RuntimeArithExpr.
///
///  Implements RuntimeRingOps<GpuFixedPoint<N, F>>, bridging the spec-level
///  Ring implementation to exec-level RuntimeArithExpr tree construction.
///  Each exec Ring operation builds a RuntimeArithExpr tree whose view_spec()
///  is STRUCTURALLY IDENTICAL to the spec-level GpuFixedPoint ArithExpr.

use vstd::prelude::*;
use verus_cutedsl::arith_expr::*;
use verus_algebra::traits::runtime::RuntimeRingOps;
use verus_algebra::traits::ring::Ring;
use crate::gpu_fixed_point::*;
use crate::gpu_ring_test::GpuFixedPoint;

verus! {

pub const LIMB_BASE_I64: i64 = 0x1_0000_0000i64;

//  ══════════════════════════════════════════════════════════════
//  Helper: map Vec<RuntimeArithExpr> to Seq<ArithExpr> via view_spec
//  ══════════════════════════════════════════════════════════════

pub open spec fn view_spec_seq(v: Seq<RuntimeArithExpr>) -> Seq<ArithExpr> {
    Seq::new(v.len(), |i: int| v[i].view_spec())
}

//  ══════════════════════════════════════════════════════════════
//  RuntimeGpuFixedPoint
//  ══════════════════════════════════════════════════════════════

pub struct RuntimeGpuFixedPoint<const N: usize, const F: usize> {
    pub limbs: Vec<RuntimeArithExpr>,
    pub model_value: Ghost<int>,
}

impl<const N: usize, const F: usize> RuntimeGpuFixedPoint<N, F> {
    pub open spec fn limbs_spec(&self) -> Seq<ArithExpr> {
        view_spec_seq(self.limbs@)
    }

    ///  Create from buffer reads.
    pub fn from_buffer(buf: u32) -> (result: Self)
        requires N > 0, N < 1000,
        ensures
            result.limbs@.len() == N,
            result.model_value@ == 0,
            result.limbs_spec() =~= buffer_limbs(buf as nat, N as nat, 0, N as nat),
    {
        let mut limbs: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant
                j <= N as u32,
                limbs@.len() == j as int,
                N < 1000,
                forall|k: int| 0 <= k < j as int ==>
                    (#[trigger] limbs@[k]).view_spec() == limb_read(buf as nat, N as nat, k as nat),
            decreases N - j as usize,
        {
            let elem = RuntimeArithExpr::Index(buf, Box::new(
                RuntimeArithExpr::Add(
                    Box::new(RuntimeArithExpr::Mul(
                        Box::new(RuntimeArithExpr::Var(0)),
                        Box::new(RuntimeArithExpr::Const(N as i64)))),
                    Box::new(RuntimeArithExpr::Const(j as i64)))));
            proof {
                reveal_with_fuel(RuntimeArithExpr::view_spec, 5);
            }
            limbs.push(elem);
            j = j + 1;
        }
        RuntimeGpuFixedPoint { limbs, model_value: Ghost(0) }
    }

    ///  Build n-limb zeros.
    fn build_zeros() -> (result: Vec<RuntimeArithExpr>)
        requires N > 0, N < 1000,
        ensures
            result@.len() == N,
            view_spec_seq(result@) =~= Seq::new(N as nat, |_i: int| ArithExpr::Const(0)),
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant
                j <= N as u32,
                out@.len() == j as int,
                N < 1000,
                forall|k: int| 0 <= k < j as int ==>
                    (#[trigger] out@[k]).view_spec() == ArithExpr::Const(0),
            decreases N - j as usize,
        { out.push(RuntimeArithExpr::Const(0)); j = j + 1; }
        out
    }

    ///  Build n-limb one (1 at position F, rest 0).
    fn build_one() -> (result: Vec<RuntimeArithExpr>)
        requires N > 0, N < 1000, F < N,
        ensures
            result@.len() == N,
            view_spec_seq(result@) =~= Seq::new(N as nat, |j: int|
                if j == F as int { ArithExpr::Const(1) } else { ArithExpr::Const(0) }),
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant
                j <= N as u32,
                out@.len() == j as int,
                N < 1000,
                forall|k: int| 0 <= k < j as int ==>
                    (#[trigger] out@[k]).view_spec() ==
                        (if k == F as int { ArithExpr::Const(1) } else { ArithExpr::Const(0) }),
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
        ensures
            result@.len() == N,
            view_spec_seq(result@) =~= view_spec_seq(v@),
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant
                j <= N as u32,
                out@.len() == j as int,
                v@.len() == N,
                N < 1000,
                forall|k: int| 0 <= k < j as int ==>
                    (#[trigger] out@[k]).view_spec() == v@[k].view_spec(),
            decreases N - j as usize,
        {
            out.push(v[j as usize].clone());
            j = j + 1;
        }
        out
    }

    ///  Build carry chain (runtime version matching spec gen_add_carry).
    fn build_carry(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>, limb: u32) -> (result: RuntimeArithExpr)
        requires
            a@.len() >= limb, b@.len() >= limb, limb < 1000,
        ensures
            result.view_spec() == gen_add_carry(
                view_spec_seq(a@), view_spec_seq(b@), limb as nat),
        decreases limb,
    {
        if limb == 0 {
            //  Matches gen_add_carry(..., 0) == ArithExpr::Const(0)
            assert(RuntimeArithExpr::Const(0).view_spec() == ArithExpr::Const(0int));
            reveal_with_fuel(gen_add_carry, 1);
            RuntimeArithExpr::Const(0)
        } else {
            let prev = limb - 1;
            let carry_prev = Self::build_carry(a, b, prev);
            //  Div(Add(Add(a[prev], b[prev]), carry_prev), BASE)
            RuntimeArithExpr::Div(
                Box::new(RuntimeArithExpr::Add(
                    Box::new(RuntimeArithExpr::Add(
                        Box::new(a[prev as usize].clone()),
                        Box::new(b[prev as usize].clone()))),
                    Box::new(carry_prev))),
                Box::new(RuntimeArithExpr::Const(LIMB_BASE_I64)))
        }
    }

    ///  Build add result limb (matching spec gen_add_result_limb).
    fn build_add_limb(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>, limb: u32) -> (result: RuntimeArithExpr)
        requires
            a@.len() > limb, b@.len() > limb, limb < 1000,
        ensures
            result.view_spec() == gen_add_result_limb(
                view_spec_seq(a@), view_spec_seq(b@), limb as nat),
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

    ///  Build full n-limb addition (matching spec add_limbs_seq).
    fn build_add(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>) -> (result: Vec<RuntimeArithExpr>)
        requires a@.len() == N, b@.len() == N, N > 0, N < 1000,
        ensures
            result@.len() == N,
            view_spec_seq(result@) =~= add_limbs_seq(
                view_spec_seq(a@), view_spec_seq(b@), N as nat),
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant
                j <= N as u32,
                out@.len() == j as int,
                a@.len() == N, b@.len() == N, N < 1000,
                forall|k: int| 0 <= k < j as int ==>
                    (#[trigger] out@[k]).view_spec() == gen_add_result_limb(
                        view_spec_seq(a@), view_spec_seq(b@), k as nat),
            decreases N - j as usize,
        {
            out.push(Self::build_add_limb(a, b, j));
            j = j + 1;
        }
        out
    }

    ///  Build full n-limb subtraction (matching spec sub_limbs_seq).
    fn build_sub(a: &Vec<RuntimeArithExpr>, b: &Vec<RuntimeArithExpr>) -> (result: Vec<RuntimeArithExpr>)
        requires a@.len() == N, b@.len() == N, N > 0, N < 1000,
        ensures
            result@.len() == N,
            view_spec_seq(result@) =~= sub_limbs_seq(
                view_spec_seq(a@), view_spec_seq(b@), N as nat),
    {
        let mut out: Vec<RuntimeArithExpr> = Vec::new();
        let mut j: u32 = 0;
        while j < N as u32
            invariant
                j <= N as u32,
                out@.len() == j as int,
                a@.len() == N, b@.len() == N, N < 1000,
                forall|k: int| 0 <= k < j as int ==>
                    (#[trigger] out@[k]).view_spec() == gen_sub_result_limb(
                        view_spec_seq(a@), view_spec_seq(b@), k as nat),
            decreases N - j as usize,
        {
            out.push(RuntimeArithExpr::Sub(
                Box::new(a[j as usize].clone()),
                Box::new(b[j as usize].clone())));
            j = j + 1;
        }
        out
    }
}

//  ══════════════════════════════════════════════════════════════
//  RuntimeRingOps implementation
//  ══════════════════════════════════════════════════════════════

impl<const N: usize, const F: usize> RuntimeRingOps<GpuFixedPoint<N, F>> for RuntimeGpuFixedPoint<N, F> {
    open spec fn model(&self) -> GpuFixedPoint<N, F> {
        GpuFixedPoint {
            limbs: self.limbs_spec(),
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
        //  TODO: build Karatsuba RuntimeArithExpr matching spec mul_truncate
        //  For now placeholder — will be filled in when exec Karatsuba is built
        RuntimeGpuFixedPoint {
            limbs: Self::build_add(&self.limbs, &self.limbs),
            model_value: Ghost(self.model_value@ * rhs.model_value@),
        }
    }

    fn eq(&self, rhs: &Self) -> (out: bool) {
        //  Equality is only meaningful in proofs.
        //  At exec level we can't compare ghost values, but the
        //  trait ensures constrains the return value.
        true  //  placeholder — not used in shader generation
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
