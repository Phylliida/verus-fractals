use verus_rational::RuntimeRational;
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn escape_time(cr: &RuntimeRational, ci: &RuntimeRational, max_iters: u32) -> (out: u32)
    requires cr.wf_spec(), ci.wf_spec()
{
    let mut zr = RuntimeRational::from_int(0);
    let mut zi = RuntimeRational::from_int(0);
    let four = RuntimeRational::from_int(4);

    let mut iters: u32 = 0;
    while iters < max_iters {
        let two = RuntimeRational::from_int(2);
        let zr_sq = zr.mul(&zr);
        let zi_sq = zi.mul(&zi);
        let abs_sq = zr_sq.add(&zi_sq);
        if abs_sq.gt(&four) {
            return iters;
        }
        let zr_zi = zr.mul(&zi);
        let two_zr_zi = two.mul(&zr_zi);
        let new_zr = zr_sq.sub(&zi_sq).add(cr);
        let new_zi = two_zr_zi.add(ci);
        zr = new_zr;
        zi = new_zi;
        iters += 1;
    }

    max_iters
}

}
