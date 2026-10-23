import OsuModel.Sim.Geometry

/-!
# The fixed evaluation environment (DECISIONS D10) as data

1024x768 window, UI scale 1, default config, argon skin: the HitObjectContainer DrawInfo before (first frame-stable
step) and after the first layout pass, its draw size, the argon slider path radius and the HitObjectContainer ancestor chains (BarrelRoll). Values are the raw float bits
of `difftest/env-1024x768.json` (from `oracle --dump-env`); `simtest --env` loads the same file.
-/

namespace OsuModel.Eval
open OsuModel.Net OsuModel.Sim

private def f (bits : UInt32) : F32 := Float32.ofBits bits

/-- The only chain type name the simulation reads (`composeChain`, Sim/Geometry.lean: the `==` test). -/
def pacName : String := "OsuPlayfieldAdjustmentContainer"

/-- One `hoc_chain` node of the env file: type name, `pos`, `scale`, `rotation`, `origin` (raw float bits).
The type name is kept only for `OsuPlayfieldAdjustmentContainer` and blanked ("") otherwise (final audit M2(a), D72):
the simulation only tests `typeName == "OsuPlayfieldAdjustmentContainer"`, so this is behaviour-preserving, and the
environment is then exactly what the Rust `Env` (an is-PAC flag per node) represents. The env-file names stay in
the call sites below as documentation. -/
def chainNode (name : String) (px py sx sy rot ox oy : UInt32) : ChainNode :=
  { typeName := if name == pacName then pacName else "", pos := ⟨f px, f py⟩, scale := ⟨f sx, f sy⟩, rot := f rot,
    origin := ⟨f ox, f oy⟩ }

def defaultEnv : Env where
  hoc := ⟨⟨f 0x3fcccccd, f 0x00000000, f 0x00000000, f 0x00000000, f 0x3fcccccd, f 0x00000000, f 0x42cccccc, f 0x42b33334, f 0x3f800000⟩,
          ⟨f 0x3f200000, f 0x00000000, f 0x00000000, f 0x00000000, f 0x3f200000, f 0x00000000, f 0xc2800000, f 0xc2600004, f 0x3f800000⟩⟩
  hocFirst := ⟨⟨f 0x3f800000, f 0x00000000, f 0x00000000, f 0x00000000, f 0x3f800000, f 0x00000000, f 0x42cccccc, f 0x4299999c, f 0x3f800000⟩,
               ⟨f 0x3f800000, f 0x00000000, f 0x00000000, f 0x00000000, f 0x3f800000, f 0x00000000, f 0xc2cccccc, f 0xc299999c, f 0x3f800000⟩⟩
  argonPathRadius := f 0x425cb08d
  hocSize := ⟨f 0x44000000, f 0x43bfffff⟩
  -- HitObjectContainer ancestor chains (`hoc_chain_first` / `hoc_chain`): BarrelRoll recomposes them with the rotated
  -- `OsuPlayfieldAdjustmentContainer` (`Sim.curHoc`). Without them `composeChain #[]` = identity (wrong under BR).
  chainFirst := #[
    chainNode "OsuUserInputManager" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "PlatformActionContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "FrameworkActionContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "SafeAreaDefiningContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OracleGame" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x44000000 0x43c00000 0x3f800000 0x3f800000 0x00000000 0x44000000 0x43c00000,
    chainNode "SafeAreaContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "SizeableAlwaysInputContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingDrawSizePreservingFillContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "GlobalActionContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "GlobalCursorDisplay" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuTooltipContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OracleGameplay" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "RulesetSkinProvidingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "BeatmapSkinProvidingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "SizeableAlwaysInputContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingDrawSizePreservingFillContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "DrawableOsuRuleset" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "FrameStabilityContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "AudioContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container`1" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuInputManager" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuKeyBindingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuPlayfieldAdjustmentContainer" 0x44000000 0x43c00000 0x3f800000 0x3f800000 0x00000000 0x43cccccd 0x4399999a,
    chainNode "Container" 0x43cccccd 0x4399999a 0x3f800000 0x3f800000 0x00000000 0x43cccccd 0x43999999,
    chainNode "ScalingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuPlayfield" 0x43cccccd 0x43999999 0x3f800000 0x3f800000 0x00000000 0x43cccccd 0x43999999,
    chainNode "HitObjectContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000]
  chain := #[
    chainNode "OsuUserInputManager" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "PlatformActionContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "FrameworkActionContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "SafeAreaDefiningContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OracleGame" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x44000000 0x43c00000 0x3f800000 0x3f800000 0x00000000 0x44000000 0x43c00000,
    chainNode "SafeAreaContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "SizeableAlwaysInputContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingDrawSizePreservingFillContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "GlobalActionContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "GlobalCursorDisplay" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuTooltipContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OracleGameplay" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "RulesetSkinProvidingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "BeatmapSkinProvidingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "SizeableAlwaysInputContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "ScalingDrawSizePreservingFillContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "DrawableOsuRuleset" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "FrameStabilityContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "AudioContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container`1" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuInputManager" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuKeyBindingContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "Container" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000,
    chainNode "OsuPlayfieldAdjustmentContainer" 0x44000000 0x43c00000 0x3f800000 0x3f800000 0x00000000 0x43cccccd 0x4399999a,
    chainNode "Container" 0x43cccccd 0x4399999a 0x3f800000 0x3f800000 0x00000000 0x43cccccd 0x43999999,
    chainNode "ScalingContainer" 0x00000000 0x414ccccd 0x3fcccccd 0x3fcccccd 0x00000000 0x00000000 0x00000000,
    chainNode "OsuPlayfield" 0x43800000 0x433fffff 0x3f800000 0x3f800000 0x00000000 0x43800000 0x433fffff,
    chainNode "HitObjectContainer" 0x00000000 0x00000000 0x3f800000 0x3f800000 0x00000000 0x00000000 0x00000000]

/-- Build-time consistency check (as `simtest --env` does at load): the recomposed chains reproduce the dumped
HitObjectContainer DrawInfos bit-exactly. -/
def chainsConsistent : Bool :=
  let a := composeChain defaultEnv.chain
  let b := composeChain defaultEnv.chainFirst
  a.matrix.bitEq defaultEnv.hoc.matrix && a.inverse.bitEq defaultEnv.hoc.inverse &&
  b.matrix.bitEq defaultEnv.hocFirst.matrix && b.inverse.bitEq defaultEnv.hocFirst.inverse

#guard chainsConsistent

end OsuModel.Eval
