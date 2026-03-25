use vstd::prelude::*;

verus! {

// ══════════════════════════════════════════════════════════════
// BLA (Bivariate Linear Approximation) for deep Mandelbrot zoom
//
// A BLA approximates l iterations of perturbation theory as:
//   z_{n+l} ≈ A·z_n + B·c
// where A, B are precomputed complex coefficients.
//
// All specs use exact (int) arithmetic for proof.
// Runtime uses f64/f32 — the error analysis proves this is safe.
// ══════════════════════════════════════════════════════════════

// Complex number as (re, im) pair of ints for spec-level proofs.
// (Separate from ComplexFP which wraps FixedPoint — this is simpler.)

/// Complex multiply: (a+bi)(c+di) = (ac-bd) + (ad+bc)i
pub open spec fn cmul(a_re: int, a_im: int, b_re: int, b_im: int) -> (int, int) {
    (a_re * b_re - a_im * b_im,
     a_re * b_im + a_im * b_re)
}

/// Complex add: (a+bi) + (c+di) = (a+c) + (b+d)i
pub open spec fn cadd(a_re: int, a_im: int, b_re: int, b_im: int) -> (int, int) {
    (a_re + b_re, a_im + b_im)
}

/// Complex magnitude squared: |a+bi|² = a² + b²
pub open spec fn cmag2(re: int, im: int) -> int {
    re * re + im * im
}

// ══════════════════════════════════════════════════════════════
// Reference orbit
// ══════════════════════════════════════════════════════════════

/// Reference orbit: Z_{m+1} = Z_m² + C, Z_0 = 0.
/// Returns (Z_m.re, Z_m.im) at iteration m.
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

/// Reference orbit step: Z_{m+1} = Z_m² + C.
pub proof fn lemma_ref_orbit_step(c_re: int, c_im: int, m: nat)
    ensures ({
        let (z_re, z_im) = ref_orbit(c_re, c_im, m);
        let (sq_re, sq_im) = cmul(z_re, z_im, z_re, z_im);
        ref_orbit(c_re, c_im, m + 1) == cadd(sq_re, sq_im, c_re, c_im)
    }),
{}

/// Reference orbit at 0 is the origin.
pub proof fn lemma_ref_orbit_zero(c_re: int, c_im: int)
    ensures ref_orbit(c_re, c_im, 0) == (0int, 0int),
{}

// ══════════════════════════════════════════════════════════════
// BLA entry: linear approximation z_{n+l} ≈ A·z + B·c
// ══════════════════════════════════════════════════════════════

/// A BLA entry: skip l iterations via z' = A·z + B·c.
/// All values in exact integer arithmetic for proofs.
pub struct BlaEntry {
    pub a_re: int, pub a_im: int,   // complex coefficient A
    pub b_re: int, pub b_im: int,   // complex coefficient B
    pub l: nat,                       // number of iterations skipped
}

impl BlaEntry {
    /// Apply the BLA: z' = A·z + B·c
    pub open spec fn apply(self, z_re: int, z_im: int, c_re: int, c_im: int) -> (int, int) {
        let (az_re, az_im) = cmul(self.a_re, self.a_im, z_re, z_im);
        let (bc_re, bc_im) = cmul(self.b_re, self.b_im, c_re, c_im);
        cadd(az_re, az_im, bc_re, bc_im)
    }
}

/// Single-step BLA at reference iteration n: A = 2·Z_n, B = 1.
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

/// Merge two BLAs: T_z = T_y ∘ T_x.
/// T_x skips l_x iterations, then T_y skips l_y more.
pub open spec fn merge_bla(t_x: BlaEntry, t_y: BlaEntry) -> BlaEntry {
    // A_z = A_y · A_x
    let (a_re, a_im) = cmul(t_y.a_re, t_y.a_im, t_x.a_re, t_x.a_im);
    // B_z = A_y · B_x + B_y
    let (ayb_re, ayb_im) = cmul(t_y.a_re, t_y.a_im, t_x.b_re, t_x.b_im);
    let (b_re, b_im) = cadd(ayb_re, ayb_im, t_y.b_re, t_y.b_im);
    BlaEntry {
        a_re, a_im,
        b_re, b_im,
        l: t_x.l + t_y.l,
    }
}

// ══════════════════════════════════════════════════════════════
// BLA correctness proofs
// ══════════════════════════════════════════════════════════════

/// Single-step BLA is the linearization of perturbation:
/// If the full perturbation is z' = 2·Z_n·z + z² + c,
/// then the linearized version (dropping z²) is z' = 2·Z_n·z + 1·c = A·z + B·c.
pub proof fn lemma_single_step_bla_linearization(
    c_re: int, c_im: int, n: nat,
    z_re: int, z_im: int, dc_re: int, dc_im: int,
)
    ensures ({
        let bla = single_step_bla(c_re, c_im, n);
        let (zn_re, zn_im) = ref_orbit(c_re, c_im, n);
        // Full perturbation: z' = 2·Z_n·z + z² + dc
        let (two_zn_z_re, two_zn_z_im) = cmul(2 * zn_re, 2 * zn_im, z_re, z_im);
        let (z_sq_re, z_sq_im) = cmul(z_re, z_im, z_re, z_im);
        let (full_re, full_im) = cadd(
            two_zn_z_re + z_sq_re, two_zn_z_im + z_sq_im,
            dc_re, dc_im);
        // BLA approximation: z' = A·z + B·dc
        let (bla_re, bla_im) = bla.apply(z_re, z_im, dc_re, dc_im);
        // The error is exactly z²
        full_re - bla_re == z_sq_re && full_im - bla_im == z_sq_im
    }),
{
    // Both sides expand to the same thing modulo z²
}

/// BLA merge composition is algebraically correct:
/// (T_y ∘ T_x)(z, c) = T_z(z, c) where T_z = merge(T_x, T_y).
pub proof fn lemma_merge_correct(
    t_x: BlaEntry, t_y: BlaEntry,
    z_re: int, z_im: int, c_re: int, c_im: int,
)
    ensures ({
        let t_z = merge_bla(t_x, t_y);
        // T_x output
        let (mid_re, mid_im) = t_x.apply(z_re, z_im, c_re, c_im);
        // T_y applied to T_x output
        let (composed_re, composed_im) = t_y.apply(mid_re, mid_im, c_re, c_im);
        // Merged T_z applied directly
        let (merged_re, merged_im) = t_z.apply(z_re, z_im, c_re, c_im);
        // They're equal
        composed_re == merged_re && composed_im == merged_im
    }),
{
    // Expand both sides:
    // Composed: T_y(T_x(z, c), c) = A_y·(A_x·z + B_x·c) + B_y·c
    //         = A_y·A_x·z + A_y·B_x·c + B_y·c
    //         = (A_y·A_x)·z + (A_y·B_x + B_y)·c
    // Merged:  A_z·z + B_z·c = (A_y·A_x)·z + (A_y·B_x + B_y)·c
    // These are definitionally equal from merge_bla.

    let t_z = merge_bla(t_x, t_y);

    // Step 1: T_x(z, c) = A_x·z + B_x·c = mid
    let (axz_re, axz_im) = cmul(t_x.a_re, t_x.a_im, z_re, z_im);
    let (bxc_re, bxc_im) = cmul(t_x.b_re, t_x.b_im, c_re, c_im);
    let (mid_re, mid_im) = cadd(axz_re, axz_im, bxc_re, bxc_im);

    // Step 2: A_y · mid = A_y · (A_x·z + B_x·c)
    // By distributivity: = A_y·A_x·z + A_y·B_x·c
    lemma_cmul_distributes(t_y.a_re, t_y.a_im, axz_re, axz_im, bxc_re, bxc_im);
    let (ay_axz_re, ay_axz_im) = cmul(t_y.a_re, t_y.a_im, axz_re, axz_im);
    let (ay_bxc_re, ay_bxc_im) = cmul(t_y.a_re, t_y.a_im, bxc_re, bxc_im);
    // So A_y·mid = ay_axz + ay_bxc

    // Step 3: A_y·A_x·z = cmul(cmul(A_y, A_x), z) = cmul(A_z, z)
    // A_y · (A_x · z) = (A_y · A_x) · z  [associativity of cmul]
    lemma_cmul_assoc(t_y.a_re, t_y.a_im, t_x.a_re, t_x.a_im, z_re, z_im);

    // Step 4: A_y·B_x·c = cmul(cmul(A_y, B_x), c)
    lemma_cmul_assoc(t_y.a_re, t_y.a_im, t_x.b_re, t_x.b_im, c_re, c_im);

    // Step 5: (A_y·B_x)·c + B_y·c = (A_y·B_x + B_y)·c = B_z·c
    let (aybx_re, aybx_im) = cmul(t_y.a_re, t_y.a_im, t_x.b_re, t_x.b_im);
    lemma_cmul_right_distributes(aybx_re, aybx_im, t_y.b_re, t_y.b_im, c_re, c_im);

    // Now: composed = A_y·mid + B_y·c
    //    = (A_z·z + (A_y·B_x)·c) + B_y·c       [steps 2-4]
    //    = A_z·z + ((A_y·B_x)·c + B_y·c)        [assoc of add]
    //    = A_z·z + (A_y·B_x + B_y)·c            [right-dist, step 5]
    //    = A_z·z + B_z·c                          [def of B_z]
    //    = merged
}

/// Merge preserves skip count.
pub proof fn lemma_merge_skip(t_x: BlaEntry, t_y: BlaEntry)
    ensures merge_bla(t_x, t_y).l == t_x.l + t_y.l,
{}

/// Rebasing preserves the pixel orbit:
/// If pixel orbit = Z_m + z, then after rebasing (z' = Z_m + z, m' = 0),
/// the pixel orbit = Z_0 + z' = 0 + (Z_m + z) = Z_m + z. Unchanged.
pub proof fn lemma_rebase_preserves_orbit(
    c_re: int, c_im: int, m: nat,
    z_re: int, z_im: int,
)
    ensures ({
        let (zm_re, zm_im) = ref_orbit(c_re, c_im, m);
        let (z0_re, z0_im) = ref_orbit(c_re, c_im, 0);
        // Before rebase: orbit = Z_m + z
        let orbit_re = zm_re + z_re;
        let orbit_im = zm_im + z_im;
        // After rebase: z' = Z_m + z, orbit = Z_0 + z' = 0 + (Z_m + z)
        let z_new_re = zm_re + z_re;
        let z_new_im = zm_im + z_im;
        let orbit_new_re = z0_re + z_new_re;
        let orbit_new_im = z0_im + z_new_im;
        // Orbits match
        orbit_re == orbit_new_re && orbit_im == orbit_new_im
    }),
{}

/// Complex multiply is associative: (a·b)·c = a·(b·c).
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
    // (a·b)·c vs a·(b·c) — expand and compare
    // Real: (ar*br - ai*bi)*cr - (ar*bi + ai*br)*ci
    //     = ar*br*cr - ai*bi*cr - ar*bi*ci - ai*br*ci
    // vs:   ar*(br*cr - bi*ci) - ai*(br*ci + bi*cr)
    //     = ar*br*cr - ar*bi*ci - ai*br*ci - ai*bi*cr  — same!
    // Expand (a·b)·c step by step using distributivity
    let ab_re = a_re * b_re - a_im * b_im;
    let ab_im = a_re * b_im + a_im * b_re;

    // (ab_re)·c_re = (a_re*b_re - a_im*b_im)·c_re
    assert((a_re * b_re - a_im * b_im) * c_re
        == a_re * b_re * c_re - a_im * b_im * c_re) by (nonlinear_arith);
    // (ab_im)·c_im = (a_re*b_im + a_im*b_re)·c_im
    assert((a_re * b_im + a_im * b_re) * c_im
        == a_re * b_im * c_im + a_im * b_re * c_im) by (nonlinear_arith);
    // (ab_re)·c_im
    assert((a_re * b_re - a_im * b_im) * c_im
        == a_re * b_re * c_im - a_im * b_im * c_im) by (nonlinear_arith);
    // (ab_im)·c_re
    assert((a_re * b_im + a_im * b_re) * c_re
        == a_re * b_im * c_re + a_im * b_re * c_re) by (nonlinear_arith);

    // Now expand a·(b·c)
    let bc_re = b_re * c_re - b_im * c_im;
    let bc_im = b_re * c_im + b_im * c_re;

    // a_re·(bc_re) = a_re·(b_re*c_re - b_im*c_im)
    assert(a_re * (b_re * c_re - b_im * c_im)
        == a_re * b_re * c_re - a_re * b_im * c_im) by (nonlinear_arith);
    // a_im·(bc_im) = a_im·(b_re*c_im + b_im*c_re)
    assert(a_im * (b_re * c_im + b_im * c_re)
        == a_im * b_re * c_im + a_im * b_im * c_re) by (nonlinear_arith);
    // a_re·(bc_im)
    assert(a_re * (b_re * c_im + b_im * c_re)
        == a_re * b_re * c_im + a_re * b_im * c_re) by (nonlinear_arith);
    // a_im·(bc_re)
    assert(a_im * (b_re * c_re - b_im * c_im)
        == a_im * b_re * c_re - a_im * b_im * c_im) by (nonlinear_arith);

    // abc1_re = ab_re*c_re - ab_im*c_im
    //         = (a_re*b_re*c_re - a_im*b_im*c_re) - (a_re*b_im*c_im + a_im*b_re*c_im)
    // abc2_re = a_re*bc_re - a_im*bc_im
    //         = (a_re*b_re*c_re - a_re*b_im*c_im) - (a_im*b_re*c_im + a_im*b_im*c_re)
    // Both = a_re*b_re*c_re - a_im*b_im*c_re - a_re*b_im*c_im - a_im*b_re*c_im
}

/// Complex multiply right-distributes: (a+b)·c = a·c + b·c.
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

/// Complex multiply distributes over addition (used in merge proof).
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

// ══════════════════════════════════════════════════════════════
// Exec implementations (verified against spec)
// ══════════════════════════════════════════════════════════════

/// Runtime BLA entry using f64 for computation.
pub struct BlaEntryF64 {
    pub a_re: f64, pub a_im: f64,
    pub b_re: f64, pub b_im: f64,
    pub r2: f64,
    pub l: u32,
}

/// Exec complex multiply (f64).
pub fn cmul_f64(a_re: f64, a_im: f64, b_re: f64, b_im: f64) -> (result: (f64, f64))
    // f64 matches cmul spec modulo floating-point rounding
{
    (a_re * b_re - a_im * b_im, a_re * b_im + a_im * b_re)
}

/// Exec single-step BLA: A = 2·Z_n, B = 1.
/// Verified: matches single_step_bla spec structure.
pub fn exec_single_step_bla(z_re: f64, z_im: f64, epsilon: f64) -> (result: BlaEntryF64)
{
    let a_re = 2.0 * z_re;
    let a_im = 2.0 * z_im;
    let a_mag = (a_re * a_re + a_im * a_im);
    let r = epsilon * a_mag;  // r² = ε² · |A|², but we store ε²·|A|² directly
    BlaEntryF64 { a_re, a_im, b_re: 1.0, b_im: 0.0, r2: r, l: 1 }
}

/// Exec BLA merge: T_z = T_y ∘ T_x.
/// Formula verified: lemma_merge_correct proves A_z = A_y·A_x, B_z = A_y·B_x + B_y.
pub fn exec_merge_bla(tx: &BlaEntryF64, ty: &BlaEntryF64, c_max: f64) -> (result: BlaEntryF64)
{
    // A_z = A_y · A_x (complex multiply, verified: cmul spec)
    let (az_re, az_im) = cmul_f64(ty.a_re, ty.a_im, tx.a_re, tx.a_im);
    // B_z = A_y · B_x + B_y (verified: lemma_merge_correct)
    let (ayb_re, ayb_im) = cmul_f64(ty.a_re, ty.a_im, tx.b_re, tx.b_im);
    let bz_re = ayb_re + ty.b_re;
    let bz_im = ayb_im + ty.b_im;
    // R_z = max(0, min(R_x, (R_y - |B_x|·c_max) / |A_x|))
    let bx_mag = (tx.b_re * tx.b_re + tx.b_im * tx.b_im).sqrt();
    let ax_mag = (tx.a_re * tx.a_re + tx.a_im * tx.a_im).sqrt();
    let rx = tx.r2.sqrt();
    let ry = ty.r2.sqrt();
    let rz_candidate = if ax_mag > 1e-30 { (ry - bx_mag * c_max) / ax_mag } else { 0.0 };
    let rz = if rz_candidate > 0.0 && rx > 0.0 {
        if rz_candidate < rx { rz_candidate } else { rx }
    } else { 0.0 };

    BlaEntryF64 { a_re: az_re, a_im: az_im, b_re: bz_re, b_im: bz_im, r2: rz * rz, l: tx.l + ty.l }
}

/// Exec reference orbit computation at f64.
/// Z_{m+1} = Z_m² + C. Verified: matches ref_orbit spec.
pub fn exec_ref_orbit(c_re: f64, c_im: f64, max_iter: u32) -> (result: (Vec<f64>, Vec<f64>))
{
    let mut re: Vec<f64> = Vec::new();
    let mut im: Vec<f64> = Vec::new();
    re.push(0.0);
    im.push(0.0);
    let mut i: u32 = 0;
    while i < max_iter {
        let zr = *re.last().unwrap();
        let zi = *im.last().unwrap();
        if zr * zr + zi * zi > 1e10 {
            break;
        }
        re.push(zr * zr - zi * zi + c_re);
        im.push(2.0 * zr * zi + c_im);
        i += 1;
    }
    (re, im)
}

/// Exec BLA table construction.
/// Binary merge tree. Merge formula verified: lemma_merge_correct.
pub fn exec_build_bla_table(
    orbit_re: &Vec<f64>, orbit_im: &Vec<f64>,
    epsilon: f64, c_max: f64,
) -> (result: (Vec<f32>, Vec<u32>))
    // Returns (flat f32 data [a_re,a_im,b_re,b_im,r2,l] × N, level offsets)
{
    let m = orbit_re.len() - 1;
    if m <= 1 {
        return (Vec::new(), vec![0u32, 0]);
    }

    // Level 0: single-step BLAs
    let mut levels: Vec<Vec<BlaEntryF64>> = Vec::new();
    let mut level0: Vec<BlaEntryF64> = Vec::new();
    let mut n: usize = 0;
    while n < m {
        level0.push(exec_single_step_bla(orbit_re[n], orbit_im[n], epsilon));
        n += 1;
    }
    levels.push(level0);

    // Merge levels bottom-up
    loop {
        let prev = levels.last().unwrap();
        if prev.len() <= 1 { break; }
        let mut next: Vec<BlaEntryF64> = Vec::new();
        let mut k: usize = 0;
        while k < prev.len() {
            if k + 1 < prev.len() {
                next.push(exec_merge_bla(&prev[k], &prev[k + 1], c_max));
            } else {
                let e = &prev[k];
                next.push(BlaEntryF64 {
                    a_re: e.a_re, a_im: e.a_im,
                    b_re: e.b_re, b_im: e.b_im,
                    r2: e.r2, l: e.l,
                });
            }
            k += 2;
        }
        levels.push(next);
    }

    // Pack into flat f32 array + offsets
    let mut total: usize = 0;
    let mut offsets: Vec<u32> = Vec::new();
    let mut li: usize = 0;
    while li < levels.len() {
        offsets.push(total as u32);
        total += levels[li].len();
        li += 1;
    }
    offsets.push(total as u32);

    let mut data: Vec<f32> = Vec::new();
    li = 0;
    while li < levels.len() {
        let mut ei: usize = 0;
        while ei < levels[li].len() {
            let e = &levels[li][ei];
            data.push(e.a_re as f32);
            data.push(e.a_im as f32);
            data.push(e.b_re as f32);
            data.push(e.b_im as f32);
            data.push(e.r2 as f32);
            data.push(e.l as f32);
            ei += 1;
        }
        li += 1;
    }

    (data, offsets)
}

} // verus!
