#[cfg(verus_keep_ghost)]
use crate::viewport::*;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::Ghost;
use vstd::prelude::*;

verus! {

pub struct Viewport {
    pub center_re: f64,
    pub center_im: f64,
    pub scale: f64,
    pub width: u32,
    pub height: u32,
}

impl Viewport {
    pub fn pixel_to_complex(self: &Viewport, px: u32, py: u32) -> (out: (f64, f64)) {
        let half_w = (self.width as f64) / 2.0;
        let half_h = (self.height as f64) / 2.0;
        let dx = (px as f64 - half_w) * self.scale;
        let dy = (py as f64 - half_h) * self.scale;
        (self.center_re + dx, self.center_im + dy)
    }

    pub fn zoom(self: &mut Viewport, factor: f64, focus_px: u32, focus_py: u32) {
        let old_cx = self.center_re;
        let old_cy = self.center_im;

        let (fx, fy) = self.pixel_to_complex(focus_px, focus_py);

        self.scale = self.scale / factor;

        let (new_fx, new_fy) = self.pixel_to_complex(focus_px, focus_py);

        self.center_re = self.center_re + (fx - new_fx);
        self.center_im = self.center_im + (fy - new_fy);
    }

    pub fn pan(self: &mut Viewport, dx: f64, dy: f64) {
        self.center_re = self.center_re + dx;
        self.center_im = self.center_im + dy;
    }
}

}
