use std::io::Write;
use verus_fractals::runtime_perturbation::escape_time;
use verus_rational::RuntimeRational;

fn main() {
    let width: u32 = 200;
    let height: u32 = 200;
    let max_iters: u32 = 100;

    let center_re = RuntimeRational::from_frac(-75, 100);
    let center_im = RuntimeRational::from_frac(1, 10);
    let scale = RuntimeRational::from_frac(1, 100);

    let half_w = RuntimeRational::from_int((width / 2) as i64);
    let half_h = RuntimeRational::from_int((height / 2) as i64);

    let mut pixels: Vec<u8> = Vec::with_capacity((width * height * 3) as usize);

    let mut py: u32 = 0;
    while py < height {
        let mut px: u32 = 0;
        while px < width {
            let px_r = RuntimeRational::from_int(px as i64);
            let py_r = RuntimeRational::from_int(py as i64);

            let px_centered = px_r.sub(&half_w);
            let py_centered = py_r.sub(&half_h);

            let cr = center_re.add(&scale.mul(&px_centered));
            let ci = center_im.add(&scale.mul(&py_centered));

            let iters = escape_time(&cr, &ci, max_iters);

            let color = if iters == max_iters {
                0u8
            } else {
                ((iters * 255) / max_iters) as u8
            };

            pixels.push(color);
            pixels.push(color);
            pixels.push(color);

            px += 1;
        }
        py += 1;
    }

    println!("P6");
    println!("{} {}", width, height);
    println!("255");
    std::io::stdout()
        .write_all(&pixels)
        .expect("Failed to write PPM");
}
