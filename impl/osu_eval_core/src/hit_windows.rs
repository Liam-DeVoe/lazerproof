//! Difficulty ranges and osu! hit windows.
//! Spec: `OsuModel.Beatmap.difficultyRange`, `osuHitWindows` (Beatmap/Objects.lean),
//! `OsuModel.Sim.HitWindows.resultFor` (Sim/Playable.lean).
use crate::float::F64;

pub const K0: F64 = F64::from_bits(0x0000_0000_0000_0000); // 0
pub const K0_5: F64 = F64::from_bits(0x3FE0_0000_0000_0000); // 0.5
pub const K5: F64 = F64::from_bits(0x4014_0000_0000_0000); // 5
pub const K20: F64 = F64::from_bits(0x4034_0000_0000_0000);
pub const K50: F64 = F64::from_bits(0x4049_0000_0000_0000);
pub const K60: F64 = F64::from_bits(0x404E_0000_0000_0000);
pub const K80: F64 = F64::from_bits(0x4054_0000_0000_0000);
pub const K100: F64 = F64::from_bits(0x4059_0000_0000_0000);
pub const K140: F64 = F64::from_bits(0x4061_8000_0000_0000);
pub const K150: F64 = F64::from_bits(0x4062_C000_0000_0000);
pub const K200: F64 = F64::from_bits(0x4069_0000_0000_0000);
/// `OsuHitWindows.MISS_WINDOW`
pub const MISS_WINDOW: F64 = F64::from_bits(0x4079_0000_0000_0000); // 400

#[derive(Clone, Copy)]
pub struct HitWindows {
    pub great: F64,
    /// (named `ok_`: a field called `ok` clashes with `Result.ok` in the Aeneas output)
    pub ok_: F64,
    pub meh: F64,
    pub miss: F64,
}

/// The results `HitWindows.ResultFor` can return for osu! windows.
#[derive(Clone, Copy)]
pub enum HitResult {
    None,
    Miss,
    Meh,
    Ok,
    Great,
}

/// `DifficultyRange(d) = (d - 5) / 5`
pub fn difficulty_range1(d: F64) -> F64 {
    d.sub(K5).div(K5)
}

/// `DifficultyRange(difficulty, min, mid, max)`
pub fn difficulty_range(d: F64, min: F64, mid: F64, max: F64) -> F64 {
    if K5.lt(d) {
        mid.add(max.sub(mid).mul(difficulty_range1(d)))
    } else if d.lt(K5) {
        mid.add(mid.sub(min).mul(difficulty_range1(d)))
    } else {
        mid
    }
}

/// `OsuHitWindows.SetDifficulty(od)` (+ the fixed miss window)
pub fn osu_hit_windows(od: F64) -> HitWindows {
    HitWindows {
        great: difficulty_range(od, K80, K50, K20).floor().sub(K0_5),
        ok_: difficulty_range(od, K140, K100, K60).floor().sub(K0_5),
        meh: difficulty_range(od, K200, K150, K100).floor().sub(K0_5),
        miss: MISS_WINDOW,
    }
}

/// `HitWindows.ResultFor(timeOffset)`
pub fn result_for(hw: &HitWindows, time_offset: F64) -> HitResult {
    let o = time_offset.abs();
    if o.le(hw.great) {
        HitResult::Great
    } else if o.le(hw.ok_) {
        HitResult::Ok
    } else if o.le(hw.meh) {
        HitResult::Meh
    } else if o.le(hw.miss) {
        HitResult::Miss
    } else {
        HitResult::None
    }
}
