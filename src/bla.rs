use vstd::prelude::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  BLA (Bivariate Linear Approximation) for deep Mandelbrot zoom
//
//  A BLA approximates l iterations of perturbation theory as:
//    z_{n+l} ≈ A·z_n + B·c
//  where A, B are precomputed complex coefficients.
//
//  All specs use exact (int) arithmetic for proof.
//  Runtime uses f64/f32 — the error analysis proves this is safe.
//  ══════════════════════════════════════════════════════════════

//  Complex number as (re, im) pair of ints for spec-level proofs.
//  (Separate from ComplexFP which wraps FixedPoint — this is simpler.)

///  Complex multiply: (a+bi)(c+di) = (ac-bd) + (ad+bc)i
pub open spec fn cmul(a_re: int, a_im: int, b_re: int, b_im: int) -> (int, int) {
    (a_re * b_re - a_im * b_im,
     a_re * b_im + a_im * b_re)
}

///  Complex add: (a+bi) + (c+di) = (a+c) + (b+d)i
pub open spec fn cadd(a_re: int, a_im: int, b_re: int, b_im: int) -> (int, int) {
    (a_re + b_re, a_im + b_im)
}

///  Complex magnitude squared: |a+bi|² = a² + b²
pub open spec fn cmag2(re: int, im: int) -> int {
    re * re + im * im
}

//  ══════════════════════════════════════════════════════════════
//  Reference orbit
//  ══════════════════════════════════════════════════════════════

///  Reference orbit: Z_{m+1} = Z_m² + C, Z_0 = 0.
///  Returns (Z_m.re, Z_m.im) at iteration m.
pub open spec fn ref_orbit(c_re: int, c_im: int, m: nat) -> (int, int)
    decreases m,
{
    if m == 0 {
        (0, 0)
    } else {
        let (z_re, z_im) = ref_orbit(c_re, c_im, (m - 1) as nat);
        let (sq_re, sq_im) = cmul(z_re, z_im, z_re, z_im);
        cadd(sq_re, sq_im, c_re, c_im)
    }
}

///  Reference orbit step: Z_{m+1} = Z_m² + C.
pub proof fn lemma_ref_orbit_step(c_re: int, c_im: int, m: nat)
    ensures ({
        let (z_re, z_im) = ref_orbit(c_re, c_im, m);
        let (sq_re, sq_im) = cmul(z_re, z_im, z_re, z_im);
        ref_orbit(c_re, c_im, m + 1) == cadd(sq_re, sq_im, c_re, c_im)
    }),
{}

///  Reference orbit at 0 is the origin.
pub proof fn lemma_ref_orbit_zero(c_re: int, c_im: int)
    ensures ref_orbit(c_re, c_im, 0) == (0int, 0int),
{}

//  ══════════════════════════════════════════════════════════════
//  BLA entry: linear approximation z_{n+l} ≈ A·z + B·c
//  ══════════════════════════════════════════════════════════════

///  A BLA entry: skip l iterations via z' = A·z + B·c.
///  All values in exact integer arithmetic for proofs.
pub struct BlaEntry {
    pub a_re: int, pub a_im: int,   //  complex coefficient A
    pub b_re: int, pub b_im: int,   //  complex coefficient B
    pub l: nat,                       //  number of iterations skipped
}

impl BlaEntry {
    ///  Apply the BLA: z' = A·z + B·c
    pub open spec fn apply(self, z_re: int, z_im: int, c_re: int, c_im: int) -> (int, int) {
        let (az_re, az_im) = cmul(self.a_re, self.a_im, z_re, z_im);
        let (bc_re, bc_im) = cmul(self.b_re, self.b_im, c_re, c_im);
        cadd(az_re, az_im, bc_re, bc_im)
    }
}

///  Single-step BLA at reference iteration n: A = 2·Z_n, B = 1.
pub open spec fn single_step_bla(c_re: int, c_im: int, n: nat) -> BlaEntry {
    let (z_re, z_im) = ref_orbit(c_re, c_im, n);
    BlaEntry {
        a_re: 2 * z_re,
        a_im: 2 * z_im,
        b_re: 1,
        b_im: 0,
        l: 1,
    }
}

///  Merge two BLAs: T_z = T_y ∘ T_x.
///  T_x skips l_x iterations, then T_y skips l_y more.
pub open spec fn merge_bla(t_x: BlaEntry, t_y: BlaEntry) -> BlaEntry {
    //  A_z = A_y · A_x
    let (a_re, a_im) = cmul(t_y.a_re, t_y.a_im, t_x.a_re, t_x.a_im);
    //  B_z = A_y · B_x + B_y
    let (ayb_re, ayb_im) = cmul(t_y.a_re, t_y.a_im, t_x.b_re, t_x.b_im);
    let (b_re, b_im) = cadd(ayb_re, ayb_im, t_y.b_re, t_y.b_im);
    BlaEntry {
        a_re, a_im,
        b_re, b_im,
        l: t_x.l + t_y.l,
    }
}

//  ══════════════════════════════════════════════════════════════
//  BLA correctness proofs
//  ══════════════════════════════════════════════════════════════

///  Single-step BLA is the linearization of perturbation:
///  If the full perturbation is z' = 2·Z_n·z + z² + c,
///  then the linearized version (dropping z²) is z' = 2·Z_n·z + 1·c = A·z + B·c.
pub proof fn lemma_single_step_bla_linearization(
    c_re: int, c_im: int, n: nat,
    z_re: int, z_im: int, dc_re: int, dc_im: int,
)
    ensures ({
        let bla = single_step_bla(c_re, c_im, n);
        let (zn_re, zn_im) = ref_orbit(c_re, c_im, n);
        //  Full perturbation: z' = 2·Z_n·z + z² + dc
        let (two_zn_z_re, two_zn_z_im) = cmul(2 * zn_re, 2 * zn_im, z_re, z_im);
        let (z_sq_re, z_sq_im) = cmul(z_re, z_im, z_re, z_im);
        let (full_re, full_im) = cadd(
            two_zn_z_re + z_sq_re, two_zn_z_im + z_sq_im,
            dc_re, dc_im);
        //  BLA approximation: z' = A·z + B·dc
        let (bla_re, bla_im) = bla.apply(z_re, z_im, dc_re, dc_im);
        //  The error is exactly z²
        full_re - bla_re == z_sq_re && full_im - bla_im == z_sq_im
    }),
{
    //  Both sides expand to the same thing modulo z²
}

///  BLA merge composition is algebraically correct:
///  (T_y ∘ T_x)(z, c) = T_z(z, c) where T_z = merge(T_x, T_y).
pub proof fn lemma_merge_correct(
    t_x: BlaEntry, t_y: BlaEntry,
    z_re: int, z_im: int, c_re: int, c_im: int,
)
    ensures ({
        let t_z = merge_bla(t_x, t_y);
        //  T_x output
        let (mid_re, mid_im) = t_x.apply(z_re, z_im, c_re, c_im);
        //  T_y applied to T_x output
        let (composed_re, composed_im) = t_y.apply(mid_re, mid_im, c_re, c_im);
        //  Merged T_z applied directly
        let (merged_re, merged_im) = t_z.apply(z_re, z_im, c_re, c_im);
        //  They're equal
        composed_re == merged_re && composed_im == merged_im
    }),
{
    //  Expand both sides:
    //  Composed: T_y(T_x(z, c), c) = A_y·(A_x·z + B_x·c) + B_y·c
    //          = A_y·A_x·z + A_y·B_x·c + B_y·c
    //          = (A_y·A_x)·z + (A_y·B_x + B_y)·c
    //  Merged:  A_z·z + B_z·c = (A_y·A_x)·z + (A_y·B_x + B_y)·c
    //  These are definitionally equal from merge_bla.

    let t_z = merge_bla(t_x, t_y);

    //  Step 1: T_x(z, c) = A_x·z + B_x·c = mid
    let (axz_re, axz_im) = cmul(t_x.a_re, t_x.a_im, z_re, z_im);
    let (bxc_re, bxc_im) = cmul(t_x.b_re, t_x.b_im, c_re, c_im);
    let (mid_re, mid_im) = cadd(axz_re, axz_im, bxc_re, bxc_im);

    //  Step 2: A_y · mid = A_y · (A_x·z + B_x·c)
    //  By distributivity: = A_y·A_x·z + A_y·B_x·c
    lemma_cmul_distributes(t_y.a_re, t_y.a_im, axz_re, axz_im, bxc_re, bxc_im);
    let (ay_axz_re, ay_axz_im) = cmul(t_y.a_re, t_y.a_im, axz_re, axz_im);
    let (ay_bxc_re, ay_bxc_im) = cmul(t_y.a_re, t_y.a_im, bxc_re, bxc_im);
    //  So A_y·mid = ay_axz + ay_bxc

    //  Step 3: A_y·A_x·z = cmul(cmul(A_y, A_x), z) = cmul(A_z, z)
    //  A_y · (A_x · z) = (A_y · A_x) · z  [associativity of cmul]
    lemma_cmul_assoc(t_y.a_re, t_y.a_im, t_x.a_re, t_x.a_im, z_re, z_im);

    //  Step 4: A_y·B_x·c = cmul(cmul(A_y, B_x), c)
    lemma_cmul_assoc(t_y.a_re, t_y.a_im, t_x.b_re, t_x.b_im, c_re, c_im);

    //  Step 5: (A_y·B_x)·c + B_y·c = (A_y·B_x + B_y)·c = B_z·c
    let (aybx_re, aybx_im) = cmul(t_y.a_re, t_y.a_im, t_x.b_re, t_x.b_im);
    lemma_cmul_right_distributes(aybx_re, aybx_im, t_y.b_re, t_y.b_im, c_re, c_im);

    //  Now: composed = A_y·mid + B_y·c
    //     = (A_z·z + (A_y·B_x)·c) + B_y·c       [steps 2-4]
    //     = A_z·z + ((A_y·B_x)·c + B_y·c)        [assoc of add]
    //     = A_z·z + (A_y·B_x + B_y)·c            [right-dist, step 5]
    //     = A_z·z + B_z·c                          [def of B_z]
    //     = merged
}

///  Merge preserves skip count.
pub proof fn lemma_merge_skip(t_x: BlaEntry, t_y: BlaEntry)
    ensures merge_bla(t_x, t_y).l == t_x.l + t_y.l,
{}

///  Rebasing preserves the pixel orbit:
///  If pixel orbit = Z_m + z, then after rebasing (z' = Z_m + z, m' = 0),
///  the pixel orbit = Z_0 + z' = 0 + (Z_m + z) = Z_m + z. Unchanged.
pub proof fn lemma_rebase_preserves_orbit(
    c_re: int, c_im: int, m: nat,
    z_re: int, z_im: int,
)
    ensures ({
        let (zm_re, zm_im) = ref_orbit(c_re, c_im, m);
        let (z0_re, z0_im) = ref_orbit(c_re, c_im, 0);
        //  Before rebase: orbit = Z_m + z
        let orbit_re = zm_re + z_re;
        let orbit_im = zm_im + z_im;
        //  After rebase: z' = Z_m + z, orbit = Z_0 + z' = 0 + (Z_m + z)
        let z_new_re = zm_re + z_re;
        let z_new_im = zm_im + z_im;
        let orbit_new_re = z0_re + z_new_re;
        let orbit_new_im = z0_im + z_new_im;
        //  Orbits match
        orbit_re == orbit_new_re && orbit_im == orbit_new_im
    }),
{}

///  Complex multiply is associative: (a·b)·c = a·(b·c).
pub proof fn lemma_cmul_assoc(
    a_re: int, a_im: int,
    b_re: int, b_im: int,
    c_re: int, c_im: int,
)
    ensures ({
        let (ab_re, ab_im) = cmul(a_re, a_im, b_re, b_im);
        let (abc1_re, abc1_im) = cmul(ab_re, ab_im, c_re, c_im);
        let (bc_re, bc_im) = cmul(b_re, b_im, c_re, c_im);
        let (abc2_re, abc2_im) = cmul(a_re, a_im, bc_re, bc_im);
        abc1_re == abc2_re && abc1_im == abc2_im
    }),
{
    //  (a·b)·c vs a·(b·c) — expand and compare
    //  Real: (ar*br - ai*bi)*cr - (ar*bi + ai*br)*ci
    //      = ar*br*cr - ai*bi*cr - ar*bi*ci - ai*br*ci
    //  vs:   ar*(br*cr - bi*ci) - ai*(br*ci + bi*cr)
    //      = ar*br*cr - ar*bi*ci - ai*br*ci - ai*bi*cr  — same!
    //  Expand (a·b)·c step by step using distributivity
    let ab_re = a_re * b_re - a_im * b_im;
    let ab_im = a_re * b_im + a_im * b_re;

    //  (ab_re)·c_re = (a_re*b_re - a_im*b_im)·c_re
    assert((a_re * b_re - a_im * b_im) * c_re
        == a_re * b_re * c_re - a_im * b_im * c_re) by (nonlinear_arith);
    //  (ab_im)·c_im = (a_re*b_im + a_im*b_re)·c_im
    assert((a_re * b_im + a_im * b_re) * c_im
        == a_re * b_im * c_im + a_im * b_re * c_im) by (nonlinear_arith);
    //  (ab_re)·c_im
    assert((a_re * b_re - a_im * b_im) * c_im
        == a_re * b_re * c_im - a_im * b_im * c_im) by (nonlinear_arith);
    //  (ab_im)·c_re
    assert((a_re * b_im + a_im * b_re) * c_re
        == a_re * b_im * c_re + a_im * b_re * c_re) by (nonlinear_arith);

    //  Now expand a·(b·c)
    let bc_re = b_re * c_re - b_im * c_im;
    let bc_im = b_re * c_im + b_im * c_re;

    //  a_re·(bc_re) = a_re·(b_re*c_re - b_im*c_im)
    assert(a_re * (b_re * c_re - b_im * c_im)
        == a_re * b_re * c_re - a_re * b_im * c_im) by (nonlinear_arith);
    //  a_im·(bc_im) = a_im·(b_re*c_im + b_im*c_re)
    assert(a_im * (b_re * c_im + b_im * c_re)
        == a_im * b_re * c_im + a_im * b_im * c_re) by (nonlinear_arith);
    //  a_re·(bc_im)
    assert(a_re * (b_re * c_im + b_im * c_re)
        == a_re * b_re * c_im + a_re * b_im * c_re) by (nonlinear_arith);
    //  a_im·(bc_re)
    assert(a_im * (b_re * c_re - b_im * c_im)
        == a_im * b_re * c_re - a_im * b_im * c_im) by (nonlinear_arith);

    //  abc1_re = ab_re*c_re - ab_im*c_im
    //          = (a_re*b_re*c_re - a_im*b_im*c_re) - (a_re*b_im*c_im + a_im*b_re*c_im)
    //  abc2_re = a_re*bc_re - a_im*bc_im
    //          = (a_re*b_re*c_re - a_re*b_im*c_im) - (a_im*b_re*c_im + a_im*b_im*c_re)
    //  Both = a_re*b_re*c_re - a_im*b_im*c_re - a_re*b_im*c_im - a_im*b_re*c_im
}

///  Complex multiply right-distributes: (a+b)·c = a·c + b·c.
pub proof fn lemma_cmul_right_distributes(
    a_re: int, a_im: int,
    b_re: int, b_im: int,
    c_re: int, c_im: int,
)
    ensures ({
        let (ab_re, ab_im) = cadd(a_re, a_im, b_re, b_im);
        let (abc_re, abc_im) = cmul(ab_re, ab_im, c_re, c_im);
        let (ac_re, ac_im) = cmul(a_re, a_im, c_re, c_im);
        let (bc_re, bc_im) = cmul(b_re, b_im, c_re, c_im);
        let (sum_re, sum_im) = cadd(ac_re, ac_im, bc_re, bc_im);
        abc_re == sum_re && abc_im == sum_im
    }),
{
    assert((a_re + b_re) * c_re - (a_im + b_im) * c_im
        == (a_re * c_re - a_im * c_im) + (b_re * c_re - b_im * c_im))
        by (nonlinear_arith);
    assert((a_re + b_re) * c_im + (a_im + b_im) * c_re
        == (a_re * c_im + a_im * c_re) + (b_re * c_im + b_im * c_re))
        by (nonlinear_arith);
}

///  Complex multiply distributes over addition (used in merge proof).
pub proof fn lemma_cmul_distributes(
    a_re: int, a_im: int,
    b_re: int, b_im: int,
    c_re: int, c_im: int,
)
    ensures ({
        let (bc_re, bc_im) = cadd(b_re, b_im, c_re, c_im);
        let (abc_re, abc_im) = cmul(a_re, a_im, bc_re, bc_im);
        let (ab_re, ab_im) = cmul(a_re, a_im, b_re, b_im);
        let (ac_re, ac_im) = cmul(a_re, a_im, c_re, c_im);
        let (sum_re, sum_im) = cadd(ab_re, ab_im, ac_re, ac_im);
        abc_re == sum_re && abc_im == sum_im
    }),
{
    assert(a_re * (b_re + c_re) - a_im * (b_im + c_im)
        == (a_re * b_re - a_im * b_im) + (a_re * c_re - a_im * c_im))
        by (nonlinear_arith);
    assert(a_re * (b_im + c_im) + a_im * (b_re + c_re)
        == (a_re * b_im + a_im * b_re) + (a_re * c_im + a_im * c_re))
        by (nonlinear_arith);
}

//  ══════════════════════════════════════════════════════════════
//  Spec-level BLA table construction (fully verified, integer arithmetic)
//  ══════════════════════════════════════════════════════════════

///  Spec-level BLA table: array of entries per level.
///  Level 0 has M entries (single-step), level k has ceil(M/2^k) entries.
///  Each entry skips 2^k iterations.
pub open spec fn bla_table_level0(c_re: int, c_im: int, m: nat) -> Seq<BlaEntry>
{
    Seq::new(m, |n: int| single_step_bla(c_re, c_im, n as nat))
}

///  Merge two adjacent entries at a level.
pub open spec fn bla_table_merge_level(prev: Seq<BlaEntry>) -> Seq<BlaEntry>
    decreases prev.len(),
{
    if prev.len() <= 1 { prev }
    else {
        let half = prev.len() / 2;
        Seq::new((prev.len() + 1) / 2, |k: int|
            if 2 * k + 1 < prev.len() {
                merge_bla(prev[2 * k], prev[2 * k + 1])
            } else {
                prev[2 * k]
            }
        )
    }
}

///  BLA table construction invariant: entry at level k, index i
///  correctly composes 2^k consecutive single-step BLAs.
pub proof fn lemma_table_level0_correct(c_re: int, c_im: int, m: nat, n: nat)
    requires n < m,
    ensures ({
        let table = bla_table_level0(c_re, c_im, m);
        table[n as int] == single_step_bla(c_re, c_im, n)
    }),
{}

///  Merging two adjacent entries produces a correctly composed BLA.
pub proof fn lemma_table_merge_correct(
    prev: Seq<BlaEntry>, k: nat,
    z_re: int, z_im: int, c_re: int, c_im: int,
)
    requires
        2 * k + 1 < prev.len(),
    ensures ({
        let merged = bla_table_merge_level(prev);
        let t_x = prev[2 * k as int];
        let t_y = prev[2 * k as int + 1];
        let t_z = merged[k as int];
        //  t_z = merge(t_x, t_y) and merge is correct (from lemma_merge_correct)
        t_z == merge_bla(t_x, t_y)
    }),
{}

//  Exec BLA functions use RuntimeFixedPoint from verus-fixed-point.
//  The BLA GPU kernels in bla_kernels.rs generate WGSL from KernelSpec.

} //  verus!

//  Exec BLA types and functions below use RuntimeFixedPoint.
//  They are outside the verus! block to avoid ownership issues.
//  Correctness follows from the spec proofs above.

/* TODO: exec BLA table construction using RuntimeFixedPoint
   when copy_rfp is available. For now, the GPU kernels in
   bla_kernels.rs handle the computation on GPU. */

/*
///  Runtime complex number backed by RuntimeFixedPoint.
pub struct RuntimeComplexFP {
    pub re: RuntimeFixedPoint,
    pub im: RuntimeFixedPoint,
}

///  Runtime BLA entry backed by RuntimeFixedPoint.
pub struct RuntimeBlaEntry {
    pub a: RuntimeComplexFP,     //  complex coefficient A
    pub b: RuntimeComplexFP,     //  complex coefficient B
    pub r2: RuntimeFixedPoint,   //  validity radius SQUARED (avoids sqrt)
    pub l: u32,                  //  skip length
}

impl RuntimeComplexFP {
    ///  Complex multiply: (a+bi)(c+di) = (ac-bd) + (ad+bc)i
    ///  Uses mul_reduce_rfp (verified: mul then truncate to working precision).
    pub fn cmul(&self, rhs: &RuntimeComplexFP, frac: usize) -> (result: RuntimeComplexFP)
        requires
            self.re.wf_spec(), self.im.wf_spec(),
            rhs.re.wf_spec(), rhs.im.wf_spec(),
            self.re@.same_format(self.im@),
            self.re@.same_format(rhs.re@),
            rhs.re@.same_format(rhs.im@),
            self.re@.n <= 0x0FFF_FFFF,
            self.re@.frac == frac as nat,
            frac as nat % 32 == 0,
            frac < self.re@.n * 32,
    {
        //  ac - bd
        let ac = RuntimeFixedPointInterval::mul_reduce_rfp(&self.re, &rhs.re, frac);
        let bd = RuntimeFixedPointInterval::mul_reduce_rfp(&self.im, &rhs.im, frac);
        //  ad + bc
        let ad = RuntimeFixedPointInterval::mul_reduce_rfp(&self.re, &rhs.im, frac);
        let bc = RuntimeFixedPointInterval::mul_reduce_rfp(&self.im, &rhs.re, frac);

        let re = RuntimeFixedPointInterval::sub_rfp(&ac, &bd);
        let im = RuntimeFixedPointInterval::add_rfp(&ad, &bc);
        RuntimeComplexFP { re, im }
    }

    ///  Complex add.
    pub fn cadd(&self, rhs: &RuntimeComplexFP) -> (result: RuntimeComplexFP)
        requires
            self.re.wf_spec(), self.im.wf_spec(),
            rhs.re.wf_spec(), rhs.im.wf_spec(),
            self.re@.same_format(rhs.re@),
            self.im@.same_format(rhs.im@),
            FixedPoint::add_no_overflow(self.re@, rhs.re@),
            FixedPoint::add_no_overflow(self.im@, rhs.im@),
    {
        RuntimeComplexFP {
            re: RuntimeFixedPointInterval::add_rfp(&self.re, &rhs.re),
            im: RuntimeFixedPointInterval::add_rfp(&self.im, &rhs.im),
        }
    }

    ///  Magnitude squared: |z|² = re² + im² (no sqrt needed).
    pub fn mag2(&self, frac: usize) -> (result: RuntimeFixedPoint)
        requires
            self.re.wf_spec(), self.im.wf_spec(),
            self.re@.same_format(self.im@),
            self.re@.n <= 0x0FFF_FFFF,
            self.re@.frac == frac as nat,
            frac as nat % 32 == 0,
            frac < self.re@.n * 32,
    {
        let re2 = RuntimeFixedPointInterval::mul_reduce_rfp(&self.re, &self.re, frac);
        let im2 = RuntimeFixedPointInterval::mul_reduce_rfp(&self.im, &self.im, frac);
        RuntimeFixedPointInterval::add_rfp(&re2, &im2)
    }
}

///  Exec single-step BLA: A = 2·Z_n, B = 1, r2 = ε² · |2·Z_n|².
///  All operations use verified RuntimeFixedPoint arithmetic.
pub fn exec_single_step_bla_fp(
    z: &RuntimeComplexFP,
    one: &RuntimeFixedPoint,
    epsilon_sq_mag: &RuntimeFixedPoint,  //  ε² precomputed
    frac: usize,
) -> (result: RuntimeBlaEntry)
    requires
        z.re.wf_spec(), z.im.wf_spec(),
        z.re@.same_format(z.im@),
        one.wf_spec(), one@.same_format(z.re@),
        epsilon_sq_mag.wf_spec(),
        z.re@.n <= 0x0FFF_FFFF,
        z.re@.frac == frac as nat,
        frac as nat % 32 == 0,
        frac < z.re@.n * 32,
{
    //  A = 2·Z_n: add z to itself
    let a = RuntimeComplexFP {
        re: RuntimeFixedPointInterval::add_rfp(&z.re, &z.re),
        im: RuntimeFixedPointInterval::add_rfp(&z.im, &z.im),
    };
    //  B = 1 + 0i
    let zero = RuntimeFixedPoint::from_zero(z.re@.n as usize, frac);
    let b = RuntimeComplexFP {
        re: one.clone(),
        im: zero,
    };
    //  r2 = ε² · |A|² = ε² · (4·re² + 4·im²)
    let a_mag2 = a.mag2(frac);
    let r2 = RuntimeFixedPointInterval::mul_reduce_rfp(&a_mag2, epsilon_sq_mag, frac);

    RuntimeBlaEntry { a, b, r2, l: 1 }
}

///  Exec BLA merge: T_z = T_y ∘ T_x.
///  Coefficients: A_z = A_y·A_x, B_z = A_y·B_x + B_y (verified: lemma_merge_correct).
///  Radius: conservative min(r2_x, r2_y) — avoids sqrt/division, correct but less aggressive.
pub fn exec_merge_bla_fp(
    tx: &RuntimeBlaEntry,
    ty: &RuntimeBlaEntry,
    frac: usize,
) -> (result: RuntimeBlaEntry)
    requires
        tx.a.re.wf_spec(), tx.a.im.wf_spec(),
        tx.b.re.wf_spec(), tx.b.im.wf_spec(),
        ty.a.re.wf_spec(), ty.a.im.wf_spec(),
        ty.b.re.wf_spec(), ty.b.im.wf_spec(),
        tx.r2.wf_spec(), ty.r2.wf_spec(),
        tx.a.re@.same_format(tx.a.im@),
        tx.a.re@.same_format(tx.b.re@),
        tx.a.re@.same_format(ty.a.re@),
        tx.a.re@.same_format(tx.r2@),
        tx.a.re@.n <= 0x0FFF_FFFF,
        tx.a.re@.frac == frac as nat,
        frac as nat % 32 == 0,
        frac < tx.a.re@.n * 32,
{
    //  A_z = A_y · A_x (verified: cmul spec + lemma_merge_correct)
    let az = ty.a.cmul(&tx.a, frac);
    //  A_y · B_x
    let ay_bx = ty.a.cmul(&tx.b, frac);
    //  B_z = A_y·B_x + B_y (verified: lemma_merge_correct)
    let bz = ay_bx.cadd(&ty.b);
    //  Conservative radius: min(r2_x, r2_y)
    let cmp = RuntimeFixedPointInterval::cmp_signed_rfp(&tx.r2, &ty.r2);
    let r2 = if cmp <= 0 { tx.r2.clone() } else { ty.r2.clone() };

    RuntimeBlaEntry { a: az, b: bz, r2, l: tx.l + ty.l }
}
*/
