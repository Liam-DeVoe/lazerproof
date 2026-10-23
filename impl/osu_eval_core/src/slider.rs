//! Slider path length cache. Spec: `OsuModel.Beatmap.SliderPath.calculateLength`
//! (Beatmap/SliderPath.lean), the part without `ExpectedDistance` adjustment.
use crate::float::{F32, F64};
use alloc::vec::Vec;

pub const K0: F64 = F64::from_bits(0);

#[derive(Clone, Copy)]
pub struct Vec2 {
    pub x: F32,
    pub y: F32,
}

/// `Vector2 operator -`
pub fn vsub(a: Vec2, b: Vec2) -> Vec2 {
    Vec2 { x: a.x.sub(b.x), y: a.y.sub(b.y) }
}

/// osuTK `Vector2.Length` = `(float)Math.Sqrt(x*x + y*y)`
pub fn length(a: Vec2) -> F32 {
    a.x.mul(a.x).add(a.y.mul(a.y)).to_f64().sqrt().to_f32()
}

/// The cumulative-length loop of `SliderPath.calculateLength()`: returns
/// (`cumulativeLength`, `calculatedLength`).
pub fn cumulative_lengths(path: &[Vec2], optimised_length: F64) -> (Vec<F64>, F64) {
    let mut calculated = optimised_length;
    let mut cumulative: Vec<F64> = Vec::new();
    cumulative.push(K0);
    let mut i: usize = 0;
    while i + 1 < path.len() {
        let diff = vsub(path[i + 1], path[i]);
        calculated = calculated.add(length(diff).to_f64());
        cumulative.push(calculated);
        i += 1;
    }
    (cumulative, calculated)
}
