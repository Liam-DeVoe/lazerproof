//! Port of `OsuModel/Eval/Env.lean`: the fixed evaluation environment (DECISIONS D10) as data —
//! 1024x768 window, UI scale 1, default config, argon skin: the HitObjectContainer DrawInfo before
//! (first frame-stable step) and after the first layout pass, its draw size, the argon slider path
//! radius and the HitObjectContainer ancestor chains (BarrelRoll; fixed in 95499c3: without them
//! `composeChain #[]` = identity). Raw float bits of `difftest/env-1024x768.json`.
use crate::float::F32;
use crate::sim::basic::{DrawInfo, Mat3, Vec2};
use crate::sim::geometry::{ChainNode, Env};
use alloc::vec::Vec;

/// spec `f` (`Float32.ofBits`)
pub fn f(bits: u32) -> F32 {
    F32::from_bits(bits)
}

/// spec `nd` (one `hoc_chain` node; the type name is only tested against
/// `"OsuPlayfieldAdjustmentContainer"`, = `is_pac`)
pub fn nd(is_pac: bool, px: u32, py: u32, sx: u32, sy: u32, rot: u32, ox: u32, oy: u32) -> ChainNode {
    ChainNode { is_pac, pos: Vec2 { x: f(px), y: f(py) }, scale: Vec2 { x: f(sx), y: f(sy) }, rot: f(rot), origin: Vec2 { x: f(ox), y: f(oy) } }
}

/// a `Mat3` from its nine entries (row-major `m11 … m33`, raw bits)
pub fn mat(a: u32, b: u32, c: u32, d: u32, e: u32, g: u32, h: u32, i: u32, j: u32) -> Mat3 {
    Mat3 { m11: f(a), m12: f(b), m13: f(c), m21: f(d), m22: f(e), m23: f(g), m31: f(h), m32: f(i), m33: f(j) }
}

/// spec `defaultEnv`
pub fn default_env() -> Env {
    Env {
        hoc: DrawInfo {
            matrix: mat(0x3fcccccd, 0x00000000, 0x00000000, 0x00000000, 0x3fcccccd, 0x00000000, 0x42cccccc, 0x42b33334, 0x3f800000),
            inverse: mat(0x3f200000, 0x00000000, 0x00000000, 0x00000000, 0x3f200000, 0x00000000, 0xc2800000, 0xc2600004, 0x3f800000),
        },
        hoc_first: DrawInfo {
            matrix: mat(0x3f800000, 0x00000000, 0x00000000, 0x00000000, 0x3f800000, 0x00000000, 0x42cccccc, 0x4299999c, 0x3f800000),
            inverse: mat(0x3f800000, 0x00000000, 0x00000000, 0x00000000, 0x3f800000, 0x00000000, 0xc2cccccc, 0xc299999c, 0x3f800000),
        },
        argon_path_radius: f(0x425cb08d),
        hoc_size: Vec2 { x: f(0x44000000), y: f(0x43bfffff) },
        chain_first: chain_first(),
        chain: chain(),
    }
}

/// spec `defaultEnv.chainFirst` (`hoc_chain_first`)
pub fn chain_first() -> Vec<ChainNode> {
    let mut v: Vec<ChainNode> = Vec::with_capacity(36);
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuUserInputManager
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // PlatformActionContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // FrameworkActionContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SafeAreaDefiningContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OracleGame
    v.push(nd(false, 0x44000000, 0x43c00000, 0x3f800000, 0x3f800000, 0x00000000, 0x44000000, 0x43c00000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SafeAreaContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SizeableAlwaysInputContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingDrawSizePreservingFillContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // GlobalActionContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // GlobalCursorDisplay
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuTooltipContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OracleGameplay
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // RulesetSkinProvidingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // BeatmapSkinProvidingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SizeableAlwaysInputContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingDrawSizePreservingFillContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // DrawableOsuRuleset
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // FrameStabilityContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // AudioContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container`1
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuInputManager
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuKeyBindingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(true, 0x44000000, 0x43c00000, 0x3f800000, 0x3f800000, 0x00000000, 0x43cccccd, 0x4399999a)); // OsuPlayfieldAdjustmentContainer
    v.push(nd(false, 0x43cccccd, 0x4399999a, 0x3f800000, 0x3f800000, 0x00000000, 0x43cccccd, 0x43999999)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingContainer
    v.push(nd(false, 0x43cccccd, 0x43999999, 0x3f800000, 0x3f800000, 0x00000000, 0x43cccccd, 0x43999999)); // OsuPlayfield
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // HitObjectContainer
    v
}
/// spec `defaultEnv.chain` (`hoc_chain`)
pub fn chain() -> Vec<ChainNode> {
    let mut v: Vec<ChainNode> = Vec::with_capacity(36);
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuUserInputManager
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // PlatformActionContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // FrameworkActionContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SafeAreaDefiningContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OracleGame
    v.push(nd(false, 0x44000000, 0x43c00000, 0x3f800000, 0x3f800000, 0x00000000, 0x44000000, 0x43c00000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SafeAreaContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SizeableAlwaysInputContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingDrawSizePreservingFillContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // GlobalActionContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // GlobalCursorDisplay
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuTooltipContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OracleGameplay
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // RulesetSkinProvidingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // BeatmapSkinProvidingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // SizeableAlwaysInputContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // ScalingDrawSizePreservingFillContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // DrawableOsuRuleset
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // FrameStabilityContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // AudioContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container`1
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuInputManager
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // OsuKeyBindingContainer
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // Container
    v.push(nd(true, 0x44000000, 0x43c00000, 0x3f800000, 0x3f800000, 0x00000000, 0x43cccccd, 0x4399999a)); // OsuPlayfieldAdjustmentContainer
    v.push(nd(false, 0x43cccccd, 0x4399999a, 0x3f800000, 0x3f800000, 0x00000000, 0x43cccccd, 0x43999999)); // Container
    v.push(nd(false, 0x00000000, 0x414ccccd, 0x3fcccccd, 0x3fcccccd, 0x00000000, 0x00000000, 0x00000000)); // ScalingContainer
    v.push(nd(false, 0x43800000, 0x433fffff, 0x3f800000, 0x3f800000, 0x00000000, 0x43800000, 0x433fffff)); // OsuPlayfield
    v.push(nd(false, 0x00000000, 0x00000000, 0x3f800000, 0x3f800000, 0x00000000, 0x00000000, 0x00000000)); // HitObjectContainer
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::geometry::compose_chain;
    fn bit_eq(a: &Mat3, b: &Mat3) -> bool {
        let fa = [a.m11, a.m12, a.m13, a.m21, a.m22, a.m23, a.m31, a.m32, a.m33];
        let fb = [b.m11, b.m12, b.m13, b.m21, b.m22, b.m23, b.m31, b.m32, b.m33];
        fa.iter().zip(fb.iter()).all(|(x, y)| x.to_bits() == y.to_bits())
    }
    /// spec `#guard chainsConsistent`
    #[test]
    fn chains_consistent() {
        let e = default_env();
        let a = compose_chain(&e.chain, None);
        let b = compose_chain(&e.chain_first, None);
        assert!(bit_eq(&a.matrix, &e.hoc.matrix) && bit_eq(&a.inverse, &e.hoc.inverse));
        assert!(bit_eq(&b.matrix, &e.hoc_first.matrix) && bit_eq(&b.inverse, &e.hoc_first.inverse));
    }
}
