/-
`sim::autogen` (sim2, part 4): `move_frame_step` / `move_frames` / `move_to_hit_object` (restated spec
`s2_mthS`, equal by `s2_mth_eq`), `add_hit_object_replay`, the `generate_objects` loop and `generate`.
`sim.autogen.generate_refines` holds for any type-name table `tn` (autogen never reads type names), under at most
`2^32` hit objects and slider paths shorter than `2^62`. The Rust tails are restated verbatim (`s2_mthTailB`,
`s2_mthTail2`, `s2_ahrJP`) and matched by `rfl`.
-/
import OsuProofs.Sim2.AutoGen3
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

/-- one iteration of the `moveToHitObject` frame loop (after the fuel decrement) -/
def s2_moveStepS (hs : F64) (lastPosition target : OsuTK.Vector2) (lfT : F64) (lfA : Nat) (easing : Easing)
    (time : F64) : M F64 := do
  addFrame { time := F64.ofInt32 time.toInt32, pos := Interpolation.valueAtV time lastPosition target lfT hs easing, actions := lfA }
  let d ← getFrameDelay time
  pure (time + d)

/-- the `moveToHitObject` loop as a fuel recursion; returns (fuel, time) -/
def s2_moveFramesS (hs : F64) (lastPosition target : OsuTK.Vector2) (lfT : F64) (lfA : Nat) (easing : Easing) :
    Nat → F64 → M (Nat × F64)
  | 0, time => pure (0, time)
  | k + 1, time =>
    if time < hs then do
      let t ← s2_moveStepS hs lastPosition target lfT lfA easing time
      s2_moveFramesS hs lastPosition target lfT lfA easing k t
    else pure (k + 1, time)

/-- the `moveToHitObject` `while` body (elaborated form, restated) -/
def s2_moveBodyS (h : HObj) (lastPosition target : OsuTK.Vector2) (lf : AFrame) (easing : Easing) :
    Unit → F64 × Nat → M (ForInStep (F64 × Nat)) := fun _ __s =>
  let time := __s.1
  let fuel := __s.2
  if (decide (time < h.start) && decide (fuel > 0)) = true then
    let fuel := fuel - 1
    let cur := Interpolation.valueAtV time lastPosition target lf.time h.start easing
    do
    addFrame { time := F64.ofInt32 time.toInt32, pos := cur, actions := lf.actions }
    let __do_lift ← getFrameDelay time
    let time : F64 := time + __do_lift
    pure (ForInStep.yield (time, fuel))
  else pure (ForInStep.done (time, fuel))

theorem s2_moveBody_step (h : HObj) (lp target : OsuTK.Vector2) (lf : AFrame) (easing : Easing) (time : F64) (k : Nat)
    (hlt : time < h.start) :
    s2_moveBodyS h lp target lf easing () (time, k + 1) =
      (do let t ← s2_moveStepS h.start lp target lf.time lf.actions easing time; pure (ForInStep.yield (t, k))) := by
  simp only [s2_moveBodyS, s2_moveStepS, hlt, decide_true, Bool.true_and, gt_iff_lt, Nat.zero_lt_succ,
    if_true, Nat.add_sub_cancel, bind_assoc, pure_bind]

theorem s2_moveLoop_eq (h : HObj) (lp target : OsuTK.Vector2) (lf : AFrame) (easing : Easing) :
    ∀ k time, (forIn Lean.Loop.mk (time, k) (s2_moveBodyS h lp target lf easing) : M _) =
      (fun r : Nat × F64 => (r.2, r.1)) <$> s2_moveFramesS h.start lp target lf.time lf.actions easing k time := by
  intro k
  induction k with
  | zero =>
    intro time
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [s2_moveBodyS, s2_moveFramesS]
  | succ k ih =>
    intro time
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    by_cases hlt : time < h.start
    · rw [s2_moveBody_step h lp target lf easing time k hlt]
      simp only [bind_assoc, pure_bind, s2_moveFramesS, hlt, if_true, map_bind]
      congr 1; funext t
      exact ih t
    · simp [s2_moveBodyS, s2_moveFramesS, hlt]

theorem s2_move_frame_step (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g : sim.autogen.G)
    (h : sim.playable.HObj) (lf : sim.autogen.AFrame) (target : net.osutk.Vector2) (easing : net.framework.Easing)
    (time : F64) (hfl : g.frames.val.length < 2^62) :
    ∃ r g', sim.autogen.move_frame_step mods g h lf lf.pos target easing time = ok (r, g') ∧
      s2_GR id g' r (s2_moveStepS h.start (v2S lf.pos) (v2S target) lf.time lf.actions.val (easingS easing) time
        (abs mods) (abs g)) ∧
      g'.heap = g.heap ∧ g'.frames.val.length = g.frames.val.length + 1 ∧ g'.button_index = g.button_index ∧
      (s2_gInv g → lf.actions.val < g.heap.val.length → s2_gInv g') := by
  let cur := Interpolation.valueAtV time (v2S lf.pos) (v2S target) lf.time h.start (easingS easing)
  let f : sim.autogen.AFrame := ⟨F64.ofInt ((i32I (F64.toInt32 time)).val : Int), v2I cur, lf.actions, false⟩
  obtain ⟨g1, hg1, eg1, hg1h, hg1f, hg1b⟩ := s2_add_frame h64 mods g f hfl
  have hf : (abs f : AFrame) = AFrame.mk (F64.ofInt32 (F64.toInt32 time)) cur lf.actions.val false := by
    show s2_aframeS f = _
    simp only [s2_aframeS, f, F64.ofInt32, s2_v2SI]
    rw [← i32S_toInt, i32S_i32I]
  obtain ⟨y, hy, ey⟩ := s2_fd_eval mods time (abs g1)
  have hi32 : ∀ x : Int32, (⟨x.toBitVec⟩ : I32) = i32I x := fun _ => rfl
  have hspec1 : (s2_moveStepS h.start (v2S lf.pos) (v2S target) lf.time lf.actions.val (easingS easing) time) (abs mods) (abs g) =
      (getFrameDelay time (abs mods) (abs g1)).bind (fun p => .ok (time + p.1, p.2)) := by
    unfold s2_moveStepS
    simp only [s2_am_bind]
    rw [← hf, eg1]
    rfl
  have hrust : ∀ {X : Type} (K : sim.autogen.G → Result X),
      (do let cur ← net.framework.value_at_v time lf.pos target lf.time h.start easing
          let i ← float.F64.to_i32_sat time
          let i1 ← lift (IScalar.cast .I64 i)
          let f ← float.F64.from_i64 i1
          let g1 ← sim.autogen.add_frame g { lf with time := f, pos := cur, key_up := false }
          K g1) = K g1 := by
    intro X K
    simp only [net.framework.value_at_v_refines, bind_ok, float.F64.to_i32_sat, hi32, lift, float.F64.from_i64]
    have : sim.autogen.add_frame g f = ok g1 := hg1
    simp only [f, cur] at this
    simp [this]
  cases y with
  | Ok d =>
    refine ⟨.Ok (time + d), g1, ?_, ?_, hg1h, hg1f, hg1b, fun hI ha => s2_inv_add_frame g g1 f _ hI ha eg1 hg1h⟩
    · unfold sim.autogen.move_frame_step
      rw [hrust]
      simp [hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add]
    · simp only [s2_GR, hspec1, ey, Except.bind]; rfl
  | Err e =>
    refine ⟨.Err e, g1, ?_, ?_, hg1h, hg1f, hg1b, fun hI ha => s2_inv_add_frame g g1 f _ hI ha eg1 hg1h⟩
    · unfold sim.autogen.move_frame_step
      rw [hrust]
      simp [hy, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · obtain ⟨m, hm⟩ := ey
      exact ⟨m, by simp only [hspec1, hm]; rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_move_frames_loopB (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (h : sim.playable.HObj) (lf : sim.autogen.AFrame) (target : net.osutk.Vector2) (easing : net.framework.Easing) :
    ∀ k (fuel : U32) (g : sim.autogen.G) (time : F64), fuel.val = k → g.frames.val.length + k < 2^62 →
      ∃ r g', sim.autogen.move_frames_loop mods g h lf target easing fuel time = ok (r, g') ∧
        s2_GR (fun x : U32 × F64 => (x.1.val, x.2)) g' r
          (s2_moveFramesS h.start (v2S lf.pos) (v2S target) lf.time lf.actions.val (easingS easing) k time
            (abs mods) (abs g)) ∧
        g'.heap = g.heap ∧ g'.button_index = g.button_index ∧ g.frames.val.length ≤ g'.frames.val.length ∧ g'.frames.val.length ≤ g.frames.val.length + k ∧
        (s2_gInv g → lf.actions.val < g.heap.val.length → s2_gInv g') := by
  intro k
  induction k with
  | zero =>
    intro fuel g time hf hfl
    have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hf])
    subst hf0
    refine ⟨.Ok (0#u32, time), g, ?_, rfl, rfl, rfl, le_refl _, by omega, fun hI _ => hI⟩
    unfold sim.autogen.move_frames_loop
    rw [loop_unfold]
    by_cases hlt : time < h.start <;> simp [sim.autogen.move_frames_loop.body, float.F64.lt, hlt]
  | succ k ih =>
    intro fuel g time hf hfl
    by_cases hlt : time < h.start
    · have hpos : fuel > 0#u32 := by scalar_tac
      obtain ⟨f1, hf1, hf1v⟩ : ∃ f1 : U32, fuel - 1#u32 = ok f1 ∧ f1.val = k := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U32.sub_spec (x := fuel) (y := 1#u32) (by scalar_tac))
        exact ⟨z, hz, by simp at hzv; omega⟩
      obtain ⟨r, g1, hr, er, eh, ef, eb, ei⟩ := s2_move_frame_step h64 mods g h lf target easing time (by omega)
      cases r with
      | Err e =>
        refine ⟨.Err e, g1, ?_, ?_, eh, eb, by omega, by omega, ei⟩
        · unfold sim.autogen.move_frames_loop
          rw [loop_unfold]
          simp [sim.autogen.move_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · obtain ⟨m, hm⟩ := er
          refine ⟨m, ?_⟩
          simp only [s2_moveFramesS, hlt, if_true, s2_am_bind, hm]
          rfl
      | Ok t =>
        obtain ⟨r', g', hr', er', eh', eb', ef1, ef2, ei'⟩ := ih f1 g1 t hf1v (by omega)
        refine ⟨r', g', ?_, ?_, by rw [eh', eh], by rw [eb', eb], by omega, by omega,
          fun hI ha => ei' (ei hI ha) (by rw [eh]; exact ha)⟩
        · unfold sim.autogen.move_frames_loop
          rw [loop_unfold]
          have hb : sim.autogen.move_frames_loop.body mods h lf target easing g fuel time =
              ok (.cont (g1, f1, t)) := by
            simp [sim.autogen.move_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
              core.result.Result.Insts.CoreOpsTry.branch]
          dsimp only; rw [hb]; simp only [bind_ok]
          unfold sim.autogen.move_frames_loop at hr'
          exact hr'
        · simp only [s2_GR] at er
          simp only [s2_moveFramesS, hlt, if_true, s2_am_bind, er, Except.bind]
          exact er'
    · refine ⟨.Ok (fuel, time), g, ?_, ?_, rfl, rfl, le_refl _, by omega, fun hI _ => hI⟩
      · unfold sim.autogen.move_frames_loop
        rw [loop_unfold]
        simp [sim.autogen.move_frames_loop.body, float.F64.lt, hlt]
      · simp only [s2_GR, s2_moveFramesS, hlt, if_false, hf]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

/-- the final button-index update of `moveToHitObject` -/
def s2_mthBtn (td : F64) : M Unit :=
  if (decide (0 ≤ td) && decide (td < minSeparationForAlternating)) = true then
    modify fun g => { frames := g.frames, buttonIndex := g.buttonIndex + 1, heap := g.heap }
  else modify fun g => { frames := g.frames, heap := g.heap }

/-- the frame loop of `moveToHitObject` followed by the fuel check and `s2_mthBtn` -/
def s2_mthLoop (h : HObj) (target : OsuTK.Vector2) (easing : Easing) (td : F64) (lf : AFrame) : M Unit := do
  let __do_lift ← getFrameDelay lf.time
  let __s ← forIn Lean.Loop.mk (lf.time + __do_lift, 10000000) (s2_moveBodyS h lf.pos target lf easing)
  if (__s.2 == 0 && decide (__s.1 < h.start)) = true then do
    let __r : Unit ← outOfFuel "time < h.start"
    s2_mthBtn td
  else s2_mthBtn td

/-- `moveToHitObject` after the optional wait frame -/
def s2_mthJP1 (h : HObj) (target : OsuTK.Vector2) (easing : Easing) (lf : AFrame) (hasWaited : Bool) : M Unit := do
  let timeDifference ← applyModsToTimeDelta lf.time h.start
  let g ← get
  let lastLast : Option AFrame := if g.frames.size ≥ 2 then g.frames[g.frames.size - 2]? else none
  if 0 ≤ timeDifference then
    match lastLast with
    | some ll =>
      if (lf.keyUp && !hasWaited) = true then
        let np := Interpolation.valueAtV lf.time lf.pos target ll.time h.start easing
        let lf : AFrame := { time := lf.time, pos := np, actions := lf.actions, keyUp := lf.keyUp }
        do
        let g ← get
        if hh : 0 < g.frames.size then do
          set ({ frames := g.frames.set (g.frames.size - 1) lf (by omega), buttonIndex := g.buttonIndex, heap := g.heap } : G)
          s2_mthLoop h target easing timeDifference lf
        else do
          let __r : Unit ← throw "internal: empty frame list"
          s2_mthLoop h target easing timeDifference lf
      else s2_mthLoop h target easing timeDifference lf
    | none => s2_mthLoop h target easing timeDifference lf
  else s2_mthBtn timeDifference

/-- `moveToHitObject` restated -/
def s2_mthS (h : HObj) (target : OsuTK.Vector2) (easing : Easing) : M Unit := do
  let lf ← lastFrame
  let reaction ← applyModsToRate (h.start - h.preempt) 100
  let waitTime : F64 := h.start - F64.max 0 (h.preempt - reaction)
  if lf.time < waitTime then do
    addFrame { time := waitTime, pos := lf.pos, actions := lf.actions }
    s2_mthJP1 h target easing { time := waitTime, pos := lf.pos, actions := lf.actions } true
  else s2_mthJP1 h target easing lf false

set_option maxHeartbeats 50000 in
theorem s2_mthLoop_eq (h : HObj) (target : OsuTK.Vector2) (easing : Easing) (td : F64) (lf : AFrame) :
    s2_mthLoop h target easing td lf = (do
      let __do_lift ← getFrameDelay lf.time
      let __s ← forIn Lean.Loop.mk (lf.time + __do_lift, 10000000) (s2_moveBodyS h lf.pos target lf easing)
      if (__s.2 == 0 && decide (__s.1 < h.start)) = true then do
        let __r : Unit ← outOfFuel "time < h.start"
        s2_mthBtn td
      else s2_mthBtn td) := rfl

set_option maxHeartbeats 50000 in
theorem s2_mth_eq (h : HObj) (target : OsuTK.Vector2) (easing : Easing) :
    moveToHitObject h target easing = s2_mthS h target easing := by
  unfold moveToHitObject s2_mthS
  congr 1; funext lf; congr 1; funext reaction
  show (if lf.time < _ then _ else _) = (if lf.time < _ then _ else _)
  by_cases hw : lf.time < h.start - F64.max 0 (h.preempt - reaction)
  · rw [if_pos hw, if_pos hw]
    beta_reduce
    apply bind_congr; intro u
    unfold s2_mthJP1
    apply bind_congr; intro td
    apply bind_congr; intro g
    show (if 0 ≤ td then _ else _) = (if 0 ≤ td then _ else _)
    by_cases h0 : 0 ≤ td
    · rw [if_pos h0, if_pos h0]
      generalize (if g.frames.size ≥ 2 then g.frames[g.frames.size - 2]? else none) = L
      cases L with
      | none => rfl
      | some ll =>
        show (if _ then _ else _) = (if _ then _ else _)
        split
        · show (get >>= _) = (get >>= _)
          apply bind_congr; intro g'
          show (dite _ _ _) = (dite _ _ _)
          split
          · apply bind_congr; intro u'; rfl
          · apply bind_congr; intro u'; rfl
        · rfl
    · rw [if_neg h0, if_neg h0]
      rfl
  · rw [if_neg hw, if_neg hw]
    beta_reduce
    unfold s2_mthJP1
    apply bind_congr; intro td
    apply bind_congr; intro g
    show (if 0 ≤ td then _ else _) = (if 0 ≤ td then _ else _)
    by_cases h0 : 0 ≤ td
    · rw [if_pos h0, if_pos h0]
      generalize (if g.frames.size ≥ 2 then g.frames[g.frames.size - 2]? else none) = L
      cases L with
      | none => rfl
      | some ll =>
        show (if _ then _ else _) = (if _ then _ else _)
        split
        · show (get >>= _) = (get >>= _)
          apply bind_congr; intro g'
          show (dite _ _ _) = (dite _ _ _)
          split
          · apply bind_congr; intro u'; rfl
          · apply bind_congr; intro u'; rfl
        · rfl
    · rw [if_neg h0, if_neg h0]
      rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the frame-loop part of `move_to_hit_object` (verbatim from the extraction) -/
def s2_mthTail2 (mods : Slice sim.mods.RateMod) (g1 : sim.autogen.G) (h : sim.playable.HObj) (lf : sim.autogen.AFrame)
    (target : net.osutk.Vector2) (easing : net.framework.Easing) (f3 f5 : F64) (b1 : Bool) (val1 : F64)
    (v : alloc.vec.Vec sim.autogen.AFrame) (v1 : net.osutk.Vector2) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.autogen.G) := do
  let r2 ← sim.autogen.get_frame_delay mods f5
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    let f6 ← float.F64.add f5 val2
    let (r3, g2) ←
      sim.autogen.move_frames mods { g1 with frames := v } h
        { lf with time := f5, pos := v1, key_up := b1 } target easing f6
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue val3 =>
      let (fuel, time) := val3
      if fuel = 0#u32
      then
        let b3 ← float.F64.lt time h.start
        if b3
        then
          ok (core.result.Result.Err (sim.err.SimErr.AutogenFuel 0#u8),
            g2)
        else
          let b4 ← float.F64.le f3 val1
          if b4
          then
            let f7 ← sim.autogen.MIN_SEPARATION_FOR_ALTERNATING
            let b5 ← float.F64.lt val1 f7
            if b5
            then
              let i ← g2.button_index + 1#u64
              ok (core.result.Result.Ok (),
                { g2 with button_index := i })
            else
              ok (core.result.Result.Ok (),
                { g2 with button_index := 0#u64 })
          else
            ok (core.result.Result.Ok (),
              { g2 with button_index := 0#u64 })
      else
        let b3 ← float.F64.le f3 val1
        if b3
        then
          let f7 ← sim.autogen.MIN_SEPARATION_FOR_ALTERNATING
          let b4 ← float.F64.lt val1 f7
          if b4
          then
            let i ← g2.button_index + 1#u64
            ok (core.result.Result.Ok (), { g2 with button_index := i })
          else
            ok (core.result.Result.Ok (),
              { g2 with button_index := 0#u64 })
        else
          ok (core.result.Result.Ok (),
            { g2 with button_index := 0#u64 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r4, g2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r3 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame sim.err.SimErr) residual
    ok (r3, { g1 with frames := v })
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

theorem s2_minsep : sim.autogen.MIN_SEPARATION_FOR_ALTERNATING = ok minSeparationForAlternating := by
  simp only [sim.autogen.MIN_SEPARATION_FOR_ALTERNATING, minSeparationForAlternating, float.F64.from_bits]; congr 1 <;> decide +kernel

theorem s2_f100 : float.F64.from_bits 4636737291354636288#u64 = ok (100 : F64) := by
  simp only [float.F64.from_bits]; congr 1 <;> decide +kernel

set_option maxHeartbeats 200000 in
theorem s2_mth_loop (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g1 : sim.autogen.G)
    (h : sim.playable.HObj) (lf : sim.autogen.AFrame) (target : net.osutk.Vector2) (easing : net.framework.Easing)
    (f5 : F64) (b1 : Bool) (td : F64) (v : alloc.vec.Vec sim.autogen.AFrame) (v1 : net.osutk.Vector2)
    (h0 : 0 ≤ td) (hfl : v.val.length + 10000000 < 2^62) (hbi : g1.button_index.val < U64.max) :
    ∃ r g', s2_mthTail2 mods g1 h lf target easing 0 f5 b1 td v v1 = ok (r, g') ∧
      s2_GR id g' r (s2_mthLoop (abs h) (v2S target) (easingS easing) td ⟨f5, v2S v1, lf.actions.val, b1⟩
        (abs mods) (abs ({ g1 with frames := v } : sim.autogen.G))) ∧
      g'.heap = g1.heap ∧ v.val.length ≤ g'.frames.val.length ∧ g'.frames.val.length ≤ v.val.length + 10000000 ∧
      g'.button_index.val ≤ g1.button_index.val + 1 ∧
      (s2_gInv ({ g1 with frames := v } : sim.autogen.G) → lf.actions.val < g1.heap.val.length → s2_gInv g') := by
  obtain ⟨gv, hgv⟩ : ∃ gv : sim.autogen.G, gv = { g1 with frames := v } := ⟨_, rfl⟩
  have hgvf : gv.frames = v := by rw [hgv]
  have hgvh : gv.heap = g1.heap := by rw [hgv]
  have hgvb : gv.button_index = g1.button_index := by rw [hgv]
  rw [← hgv]
  let lfR : sim.autogen.AFrame := { lf with time := f5, pos := v1, key_up := b1 }
  have hlfS : (⟨f5, v2S v1, lf.actions.val, b1⟩ : AFrame) = abs lfR := rfl
  obtain ⟨y, hy, ey⟩ := s2_fd_eval mods f5 (abs gv)
  cases y with
  | Err e =>
    refine ⟨.Err e, gv, ?_, ?_, hgvh, by rw [hgvf], by rw [hgvf]; omega, by rw [hgvb]; omega, fun hI _ => hI⟩
    · simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hgv]
    · obtain ⟨m, hm⟩ := ey
      exact ⟨m, by simp only [s2_mthLoop, s2_am_bind, hm]; rfl⟩
  | Ok d =>
    obtain ⟨r3, g2, h3, e3, eh3, eb3, ef3a, ef3b, ei3⟩ := s2_move_frames_loopB h64 mods h lfR target easing
      10000000 10000000#u32 gv (f5 + d) rfl (by rw [hgvf]; omega)
    have hloop := s2_moveLoop_eq (abs h) (v2S v1) (v2S target) (abs lfR) (easingS easing) 10000000 (f5 + d)
    have hspec0 : s2_mthLoop (abs h) (v2S target) (easingS easing) td ⟨f5, v2S v1, lf.actions.val, b1⟩ (abs mods) (abs gv) =
        (s2_moveFramesS (abs h : HObj).start (v2S v1) (v2S target) (abs lfR : AFrame).time (abs lfR : AFrame).actions (easingS easing) 10000000 (f5 + d) (abs mods) (abs gv)).bind
          (fun p => (if (p.1.1 == 0 && decide (p.1.2 < (abs h : HObj).start)) = true then (do let _r : Unit ← outOfFuel "time < h.start"; s2_mthBtn td) else s2_mthBtn td) (abs mods) p.2) := by
      simp only [s2_mthLoop, s2_am_bind, ey, Except.bind]
      rw [hlfS, hloop]
      simp only [s2_am_map]
      cases s2_moveFramesS (abs h : HObj).start (v2S v1) (v2S target) (abs lfR : AFrame).time (abs lfR : AFrame).actions (easingS easing) 10000000 (f5 + d) (abs mods) (abs gv) <;> rfl
    rw [hspec0]
    have hhs : (abs h : HObj).start = h.start := rfl
    have h3' : sim.autogen.move_frames_loop mods gv h { time := f5, pos := v1, actions := lf.actions, key_up := b1 } target easing 10000000#u32 (f5 + d) = ok (r3, g2) := h3
    cases r3 with
    | Err e =>
      refine ⟨.Err e, g2, ?_, ?_, by rw [eh3, hgvh], by rw [← hgvf]; exact ef3a, by rw [← hgvf]; exact ef3b,
        by rw [eb3, hgvb]; omega, fun hI ha => ei3 hI (by rw [hgvh]; exact ha)⟩
      · simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add, ← hgv, sim.autogen.move_frames, h3',
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := e3
        have hm' : s2_moveFramesS (abs h : HObj).start (v2S v1) (v2S target) (abs lfR : AFrame).time (abs lfR : AFrame).actions
            (easingS easing) 10000000 (f5 + d) (abs mods) (abs gv) = .error m := hm
        exact ⟨m, by rw [hm']; rfl⟩
    | Ok fv =>
      obtain ⟨fuel, time⟩ := fv
      have e3' : s2_moveFramesS (abs h : HObj).start (v2S v1) (v2S target) (abs lfR : AFrame).time (abs lfR : AFrame).actions
          (easingS easing) 10000000 (f5 + d) (abs mods) (abs gv) = .ok ((fuel.val, time), abs g2) := e3
      rw [e3']
      simp only [Except.bind]
      rw [hhs]
      obtain ⟨i, hi, hiv⟩ : ∃ i : U64, g2.button_index + 1#u64 = ok i ∧ i.val = g2.button_index.val + 1 := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U64.add_spec (x := g2.button_index) (y := 1#u64) (by rw [eb3, hgvb]; scalar_tac))
        exact ⟨z, hz, by scalar_tac⟩
      by_cases hft : fuel.val = 0 ∧ time < h.start
      · have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hft.1])
        refine ⟨.Err (.AutogenFuel 0#u8), g2, ?_, ?_, by rw [eh3, hgvh], by rw [← hgvf]; exact ef3a, by rw [← hgvf]; exact ef3b,
          by rw [eb3, hgvb]; omega, fun hI ha => ei3 hI (by rw [hgvh]; exact ha)⟩
        · simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add, ← hgv, sim.autogen.move_frames, h3', hf0, float.F64.lt, hft.2]
        · simp only [s2_GR]
          simp [hft.1, hft.2, outOfFuel]
          exact ⟨_, rfl⟩
      · have hc : (fuel.val == 0 && decide (time < h.start)) = false := by
          by_cases hf : fuel.val = 0
          · have : ¬ time < h.start := fun ht => hft ⟨hf, ht⟩
            simp [hf, this]
          · simp [hf]
        by_cases hms : td < minSeparationForAlternating
        · refine ⟨.Ok (), { g2 with button_index := i }, ?_, ?_, by simp [eh3, hgvh], by rw [← hgvf]; exact ef3a,
            by rw [← hgvf]; exact ef3b, by simp only [hiv, eb3, hgvb]; omega, fun hI ha => ei3 hI (by rw [hgvh]; exact ha)⟩
          · by_cases hf0 : fuel = 0#u32
            · have ht : ¬ time < h.start := fun ht => hft ⟨by rw [hf0]; rfl, ht⟩
              simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add, ← hgv, sim.autogen.move_frames, h3',
                hf0, float.F64.lt, ht, float.F64.le, h0, s2_minsep, hms, hi]
            · simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add, ← hgv, sim.autogen.move_frames, h3',
                hf0, float.F64.lt, float.F64.le, h0, s2_minsep, hms, hi]
          · simp only [hc, s2_GR]
            simp [s2_mthBtn, h0, hms, abs, s2_gS, hiv]
        · refine ⟨.Ok (), { g2 with button_index := 0#u64 }, ?_, ?_, by simp [eh3, hgvh], by rw [← hgvf]; exact ef3a,
            by rw [← hgvf]; exact ef3b, by simp, fun hI ha => ei3 hI (by rw [hgvh]; exact ha)⟩
          · by_cases hf0 : fuel = 0#u32
            · have ht : ¬ time < h.start := fun ht => hft ⟨by rw [hf0]; rfl, ht⟩
              simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add, ← hgv, sim.autogen.move_frames, h3',
                hf0, float.F64.lt, ht, float.F64.le, h0, s2_minsep, hms]
            · simp [s2_mthTail2, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F64.add, ← hgv, sim.autogen.move_frames, h3',
                hf0, float.F64.lt, float.F64.le, h0, s2_minsep, hms]
          · simp only [hc, s2_GR]
            simp [s2_mthBtn, h0, hms, abs, s2_gS]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the part of `move_to_hit_object` after the optional wait frame (verbatim from the extraction, frame-loop part folded into `s2_mthTail2`) -/
def s2_mthTailB (mods : Slice sim.mods.RateMod) (g1 : sim.autogen.G) (h : sim.playable.HObj) (lf : sim.autogen.AFrame)
    (target : net.osutk.Vector2) (easing : net.framework.Easing) (f3 f5 : F64) (b b1 : Bool) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.autogen.G) := do
  let r1 ← sim.autogen.apply_mods_to_time_delta mods f5 h.start
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let n := alloc.vec.Vec.len g1.frames
    let last_last ←
      if n >= 2#usize
      then
        do
        let i ← n - 2#usize
        let a ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            sim.autogen.AFrame) g1.frames i
        ok (some a)
      else ok none
    let b2 ← float.F64.le f3 val1
    if b2
    then
      let (v, v1) ←
        match last_last with
        | none => ok (g1.frames, lf.pos)
        | some ll =>
          if b1
          then
            if b
            then ok (g1.frames, lf.pos)
            else
              do
              let np ←
                net.framework.value_at_v f5 lf.pos target ll.time h.start
                  easing
              let m := alloc.vec.Vec.len g1.frames
              let i ← m - 1#usize
              let (_, index_mut_back) ←
                alloc.vec.Vec.index_mut
                  (core.slice.index.SliceIndexUsizeSlice sim.autogen.AFrame)
                  g1.frames i
              let v2 :=
                index_mut_back
                  { lf with time := f5, pos := np, key_up := b1 }
              ok (v2, np)
          else ok (g1.frames, lf.pos)
      s2_mthTail2 mods g1 h lf target easing f3 f5 b1 val1 v v1
    else
      let b3 ← float.F64.le f3 val1
      if b3
      then
        let f6 ← sim.autogen.MIN_SEPARATION_FOR_ALTERNATING
        let b4 ← float.F64.lt val1 f6
        if b4
        then
          let i ← g1.button_index + 1#u64
          ok (core.result.Result.Ok (), { g1 with button_index := i })
        else ok (core.result.Result.Ok (), { g1 with button_index := 0#u64 })
      else ok (core.result.Result.Ok (), { g1 with button_index := 0#u64 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame sim.err.SimErr) residual
    ok (r2, g1)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

theorem s2_abs_frames_set (g : sim.autogen.G) (i : Usize) (f : sim.autogen.AFrame) (hi : i.val < (abs g : G).frames.size) :
    (abs ({ g with frames := alloc.vec.Vec.set g.frames i f } : sim.autogen.G) : G) =
      { frames := (abs g : G).frames.set i.val (abs f) hi, buttonIndex := (abs g : G).buttonIndex, heap := (abs g : G).heap } := by
  simp only [abs, s2_gS, G.mk.injEq, and_true]
  apply Array.toList_inj.mp
  simp [vec_set_val', List.map_set]

theorem s2_inv_frames_set (g : sim.autogen.G) (i : Usize) (f : sim.autogen.AFrame) (hI : s2_gInv g)
    (hf : f.actions.val < g.heap.val.length) :
    s2_gInv ({ g with frames := alloc.vec.Vec.set g.frames i f } : sim.autogen.G) := by
  refine ⟨hI.1, ?_⟩
  intro x hx
  have hx' : x ∈ (g.frames.val.set i.val f).map s2_aframeS := by
    have : (abs ({ g with frames := alloc.vec.Vec.set g.frames i f } : sim.autogen.G) : G).frames =
        ((g.frames.val.set i.val f).map s2_aframeS).toArray := by simp [abs, s2_gS, vec_set_val']
    rw [this] at hx; simpa using hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
  rcases List.mem_or_eq_of_mem_set hy with hy | rfl
  · exact hI.2 _ (by show _ ∈ (g.frames.val.map s2_aframeS).toArray; simp; exact ⟨y, hy, rfl⟩)
  · exact hf

set_option maxHeartbeats 200000 in
theorem s2_mth_tail (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g1 : sim.autogen.G)
    (h : sim.playable.HObj) (lf : sim.autogen.AFrame) (target : net.osutk.Vector2) (easing : net.framework.Easing)
    (f5 : F64) (b b1 : Bool)
    (hI : s2_gInv g1) (ha : lf.actions.val < g1.heap.val.length)
    (hfl : g1.frames.val.length + 10000000 < 2^62) (hbi : g1.button_index.val < U64.max) :
    ∃ r g', s2_mthTailB mods g1 h lf target easing 0 f5 b b1 = ok (r, g') ∧
      s2_GR id g' r (s2_mthJP1 (abs h) (v2S target) (easingS easing) ⟨f5, v2S lf.pos, lf.actions.val, b1⟩ b
        (abs mods) (abs g1)) ∧
      (∀ v, r = .Ok v → g'.heap = g1.heap ∧ g1.frames.val.length ≤ g'.frames.val.length ∧
        g'.frames.val.length ≤ g1.frames.val.length + 10000000 ∧ g'.button_index.val ≤ g1.button_index.val + 1 ∧
        s2_gInv g') := by
  obtain ⟨x, hx, ex⟩ := s2_amd_eval mods f5 h.start (abs g1)
  have hsz : (abs g1 : G).frames.size = g1.frames.val.length := by simp [abs, s2_gS]
  have hhs : (abs h : HObj).start = h.start := rfl
  cases x with
  | Err e =>
    refine ⟨.Err e, g1, ?_, ?_, fun _ h => by cases h⟩
    · simp [s2_mthTailB, hx, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · obtain ⟨m, hm⟩ := ex
      exact ⟨m, by simp only [s2_mthJP1, hhs, s2_am_bind, hm]; rfl⟩
  | Ok td =>
    have hsp : s2_mthJP1 (abs h) (v2S target) (easingS easing) ⟨f5, v2S lf.pos, lf.actions.val, b1⟩ b (abs mods) (abs g1) =
        (if 0 ≤ td then
          match (if (abs g1 : G).frames.size ≥ 2 then (abs g1 : G).frames[(abs g1 : G).frames.size - 2]? else none) with
          | some ll =>
            if (b1 && !b) = true then
              let np := Interpolation.valueAtV f5 (v2S lf.pos) (v2S target) ll.time h.start (easingS easing)
              let lf2 : AFrame := { time := f5, pos := np, actions := lf.actions.val, keyUp := b1 }
              (do
                let g ← get
                if hh : 0 < g.frames.size then do
                  set ({ frames := g.frames.set (g.frames.size - 1) lf2 (by omega), buttonIndex := g.buttonIndex, heap := g.heap } : G)
                  s2_mthLoop (abs h) (v2S target) (easingS easing) td lf2
                else do
                  let __r : Unit ← throw "internal: empty frame list"
                  s2_mthLoop (abs h) (v2S target) (easingS easing) td lf2)
            else s2_mthLoop (abs h) (v2S target) (easingS easing) td ⟨f5, v2S lf.pos, lf.actions.val, b1⟩
          | none => s2_mthLoop (abs h) (v2S target) (easingS easing) td ⟨f5, v2S lf.pos, lf.actions.val, b1⟩
        else s2_mthBtn td) (abs mods) (abs g1) := by
      simp only [s2_mthJP1, hhs, s2_am_bind, ex, Except.bind, s2_am_get_bind]
      rfl
    rw [hsp]
    have hLL : ∃ LL : Option sim.autogen.AFrame,
        (if alloc.vec.Vec.len g1.frames >= 2#usize then (do
            let i ← alloc.vec.Vec.len g1.frames - 2#usize
            let a ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.autogen.AFrame) g1.frames i
            ok (some a)) else ok none) = ok LL ∧
        (if (abs g1 : G).frames.size ≥ 2 then (abs g1 : G).frames[(abs g1 : G).frames.size - 2]? else none) = LL.map abs ∧
        (∀ ll, LL = some ll → 2 ≤ g1.frames.val.length) := by
      by_cases hn : 2 ≤ g1.frames.val.length
      · obtain ⟨i, hi, hiv⟩ : ∃ i : Usize, alloc.vec.Vec.len g1.frames - 2#usize = ok i ∧ i.val = g1.frames.val.length - 2 := by
          obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len g1.frames) (y := 2#usize) (by scalar_tac))
          exact ⟨z, hz, by scalar_tac⟩
        have hil : i.val < g1.frames.val.length := by omega
        refine ⟨some (g1.frames.val[i.val]'hil), ?_, ?_, fun _ _ => hn⟩
        · have hge : alloc.vec.Vec.len g1.frames >= 2#usize := by scalar_tac
          simp [hge, hi, vec_index_eq' _ _ hil, vec_index_usize_ok _ _ hil]
        · rw [if_pos (by rw [hsz]; omega), hsz]
          simp [abs, s2_gS, hil, show g1.frames.val.length - 2 = i.val by omega]
      · refine ⟨none, ?_, ?_, fun _ h => by cases h⟩
        · have : ¬ (alloc.vec.Vec.len g1.frames >= 2#usize) := by scalar_tac
          simp [this]
        · rw [if_neg (by rw [hsz]; omega)]; rfl
    obtain ⟨LL, hLLr, hLLs, hLL2⟩ := hLL
    rw [hLLs]
    have hR : ∀ {X : Type} (K : Option sim.autogen.AFrame → Result X),
        (do let last_last ← (if alloc.vec.Vec.len g1.frames >= 2#usize then (do
            let i ← alloc.vec.Vec.len g1.frames - 2#usize
            let a ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.autogen.AFrame) g1.frames i
            ok (some a)) else ok none); K last_last) = K LL := by
      intro X K; rw [hLLr, bind_ok]
    by_cases h0 : 0 ≤ td
    swap
    · refine ⟨.Ok (), { g1 with button_index := 0#u64 }, ?_, ?_, fun _ _ => ⟨rfl, le_refl _, by simp, by simp, hI⟩⟩
      · unfold s2_mthTailB
        simp only [hx, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        rw [hR]
        simp [float.F64.le, h0]
      · rw [if_neg h0]; simp [s2_GR, s2_mthBtn, h0, abs, s2_gS]
    · rw [if_pos h0]
      cases LL with
      | none =>
        obtain ⟨r, g', hr, er, eh, ef1, ef2, eb, ei⟩ := s2_mth_loop h64 mods g1 h lf target easing f5 b1 td g1.frames lf.pos h0 (by omega) hbi
        refine ⟨r, g', ?_, er, fun _ _ => ⟨eh, ef1, ef2, eb, ei hI ha⟩⟩
        unfold s2_mthTailB
        simp only [hx, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        rw [hR]
        simpa [float.F64.le, h0] using hr
      | some ll =>
        have hn2 := hLL2 ll rfl
        cases b1 <;> cases b
        case true.false =>
          have hnp := net.framework.value_at_v_refines f5 lf.pos target ll.time h.start easing
          obtain ⟨m1, hm1, hm1v⟩ : ∃ i : Usize, alloc.vec.Vec.len g1.frames - 1#usize = ok i ∧ i.val = g1.frames.val.length - 1 := by
            obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len g1.frames) (y := 1#usize) (by scalar_tac))
            exact ⟨z, hz, by scalar_tac⟩
          have hil : m1.val < g1.frames.val.length := by omega
          let npS := Interpolation.valueAtV f5 (v2S lf.pos) (v2S target) ll.time h.start (easingS easing)
          let fR : sim.autogen.AFrame := { lf with time := f5, pos := v2I npS, key_up := true }
          obtain ⟨r, g', hr, er, eh, ef1, ef2, eb, ei⟩ := s2_mth_loop h64 mods g1 h lf target easing f5 true td
            (alloc.vec.Vec.set g1.frames m1 fR) (v2I npS) h0 (by simp [vec_set_val']; omega) hbi
          refine ⟨r, g', ?_, ?_, fun _ _ => ⟨eh, by simpa [vec_set_val'] using ef1, by simpa [vec_set_val'] using ef2, eb,
            ei (s2_inv_frames_set g1 m1 fR hI ha) ha⟩⟩
          · unfold s2_mthTailB
            simp only [hx, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
            rw [hR]
            simp [float.F64.le, h0, hnp, hm1, vec_index_mut_usize_ok _ _ hil]
            exact hr
          · have hpos : 0 < (abs g1 : G).frames.size := by rw [hsz]; omega
            have hst : ({ frames := (abs g1 : G).frames.set ((abs g1 : G).frames.size - 1) ⟨f5, Interpolation.valueAtV f5 (v2S lf.pos) (v2S target) (abs ll : AFrame).time h.start (easingS easing), lf.actions.val, true⟩ (by omega), buttonIndex := (abs g1 : G).buttonIndex, heap := (abs g1 : G).heap } : G) = abs ({ g1 with frames := alloc.vec.Vec.set g1.frames m1 fR } : sim.autogen.G) := by
              simp only [abs, s2_gS, G.mk.injEq, and_true]
              apply Array.toList_inj.mp
              simp [vec_set_val', List.map_set, hm1v, fR, s2_aframeS, npS]
            have hget : (get : M G) (abs mods) (abs g1) = .ok (abs g1, abs g1) := rfl
            simp only [Option.map_some, Bool.not_false, Bool.and_self, ite_true, s2_am_bind, hget, Except.bind, dif_pos hpos,
              s2_am_set]
            rw [hst]
            exact er
        all_goals
          obtain ⟨r, g', hr, er, eh, ef1, ef2, eb, ei⟩ := s2_mth_loop h64 mods g1 h lf target easing f5 _ td g1.frames lf.pos h0 (by omega) hbi
          refine ⟨r, g', ?_, er, fun _ _ => ⟨eh, ef1, ef2, eb, ei hI ha⟩⟩
          unfold s2_mthTailB
          simp only [hx, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
          rw [hR]
          simpa [float.F64.le, h0] using hr
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

theorem s2_amr_eval (mods : Slice sim.mods.RateMod) (time rate : F64) (S : G) :
    ∃ x, sim.autogen.apply_mods_to_rate mods time rate = ok x ∧
      match x with
      | .Ok v => applyModsToRate time rate (abs mods) S = .ok (v, S)
      | .Err _ => ∃ m, applyModsToRate time rate (abs mods) S = .error m := by
  obtain ⟨x, hx, ex⟩ := s2_amr_rust mods time mods.val.length rate 0#usize (by simp) (by simp)
  refine ⟨x, by simp [sim.autogen.apply_mods_to_rate, hx], ?_⟩
  have hs := s2_amr_spec time rate (abs mods) S
  simp only [ReaderT.run, StateT.run] at hs
  have ea : (abs mods : List RateMod) = mods.val.map abs := rfl
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at ex
  rw [ea] at hs ⊢
  cases h : s2_amr time (mods.val.map abs) rate with
  | none => rw [h] at ex hs; cases x with
    | Ok v => simp [s2_optRel] at ex
    | Err e => exact s2_eo_none hs
  | some v => rw [h] at ex hs; cases x with
    | Ok w => simp only [s2_optRel] at ex; subst ex; exact s2_eo_ok hs
    | Err e => simp [s2_optRel] at ex

theorem s2_lastFrame_mem (C : List RateMod) (S S' : G) (f : AFrame) (h : lastFrame C S = .ok (f, S')) :
    f ∈ S.frames := by
  unfold lastFrame at h
  simp only [s2_am_get_bind] at h
  cases hb : S.frames.back? with
  | none => rw [hb] at h; simp at h
  | some f' =>
    rw [hb] at h
    simp only [s2_am_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [Array.back?] at hb
    exact Array.mem_of_getElem? hb
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

set_option maxHeartbeats 200000 in
theorem sim.autogen.move_to_hit_object_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (h : sim.playable.HObj) (target : net.osutk.Vector2) (easing : net.framework.Easing)
    (hI : s2_gInv g) (hne : 0 < g.frames.val.length) (hfl : g.frames.val.length + 10000001 < 2^62)
    (hbi : g.button_index.val < U64.max) :
    ∃ r g', sim.autogen.move_to_hit_object mods g h target easing = ok (r, g') ∧
      s2_GR id g' r (moveToHitObject (abs h) (v2S target) (easingS easing) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.heap = g.heap ∧ g.frames.val.length ≤ g'.frames.val.length ∧
        g'.frames.val.length ≤ g.frames.val.length + 10000001 ∧ g'.button_index.val ≤ g.button_index.val + 1 ∧
        s2_gInv g') := by
  rw [s2_mth_eq]
  obtain ⟨lf, hlf, elf⟩ := sim.autogen.last_frame_refines g (abs mods) hne
  have ha : lf.actions.val < g.heap.val.length := hI.2 _ (s2_lastFrame_mem _ _ _ _ elf)
  have hhs : (abs h : HObj).start = h.start := rfl
  have hhp : (abs h : HObj).preempt = h.preempt := rfl
  have hlt' : (abs lf : AFrame).time = lf.time := rfl
  have hsub1 : float.F64.sub h.start h.preempt = ok (h.start - h.preempt) := rfl
  obtain ⟨x, hx, ex⟩ := s2_amr_eval mods (h.start - h.preempt) 100 (abs g)
  cases x with
  | Err e =>
    refine ⟨.Err e, g, ?_, ?_, fun _ h => by cases h⟩
    · unfold sim.autogen.move_to_hit_object
      simp only [hlf, bind_ok, hsub1, s2_f100, hx]
      simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · obtain ⟨m, hm⟩ := ex
      exact ⟨m, by simp only [s2_mthS, s2_am_bind, elf, Except.bind, hhs, hhp, hm]⟩
  | Ok reaction =>
    have hsub2 : float.F64.sub h.preempt reaction = ok (h.preempt - reaction) := rfl
    have hmax := net.max_refines 0 (h.preempt - reaction)
    have hsub3 : float.F64.sub h.start (F64.max 0 (h.preempt - reaction)) = ok (h.start - F64.max 0 (h.preempt - reaction)) := rfl
    have hlt : float.F64.lt lf.time (h.start - F64.max 0 (h.preempt - reaction)) =
        ok (decide (lf.time < h.start - F64.max 0 (h.preempt - reaction))) := rfl
    have hbr : core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok reaction : core.result.Result F64 sim.err.SimErr) =
        ok (core.ops.control_flow.ControlFlow.Continue reaction) := rfl
    have hspec0 : s2_mthS (abs h) (v2S target) (easingS easing) (abs mods) (abs g) =
        (if lf.time < h.start - F64.max 0 (h.preempt - reaction) then
          (addFrame { time := h.start - F64.max 0 (h.preempt - reaction), pos := v2S lf.pos, actions := lf.actions.val } >>= fun _ =>
            s2_mthJP1 (abs h) (v2S target) (easingS easing) { time := h.start - F64.max 0 (h.preempt - reaction), pos := v2S lf.pos, actions := lf.actions.val } true)
        else s2_mthJP1 (abs h) (v2S target) (easingS easing) (abs lf) false) (abs mods) (abs g) := by
      simp only [s2_mthS, s2_am_bind, elf, Except.bind, hhs, hhp, ex, hlt']
      split <;> rfl
    rw [hspec0]
    by_cases hw : lf.time < h.start - F64.max 0 (h.preempt - reaction)
    · obtain ⟨g2, hg2, eg2, hh2, hf2, hb2⟩ := s2_add_frame h64 mods g
        { lf with time := h.start - F64.max 0 (h.preempt - reaction), key_up := false } (by omega)
      have hI2 := s2_inv_add_frame g g2 { lf with time := h.start - F64.max 0 (h.preempt - reaction), key_up := false } _ hI ha eg2 hh2
      obtain ⟨r, g', hr, er, eb⟩ := s2_mth_tail h64 mods g2 h lf target easing (h.start - F64.max 0 (h.preempt - reaction))
        true false hI2 (by rw [hh2]; exact ha) (by omega) (by rw [hb2]; exact hbi)
      refine ⟨r, g', ?_, ?_, fun v hv => by obtain ⟨e1, e2, e3, e4, e5⟩ := eb v hv; exact ⟨by rw [e1, hh2], by omega, by omega, by rw [hb2] at e4; exact e4, e5⟩⟩
      · unfold sim.autogen.move_to_hit_object
        simp only [hlf, bind_ok, hsub1, s2_f100, hx, hbr, s2_ag_consts.1, hsub2, hmax, hsub3, hlt, hw, decide_true, ite_true, hg2]
        exact hr
      · rw [if_pos hw]
        have eg2' : addFrame { time := h.start - F64.max 0 (h.preempt - reaction), pos := v2S lf.pos, actions := lf.actions.val } (abs mods) (abs g) = .ok ((), abs g2) := eg2
        simp only [s2_am_bind, eg2', Except.bind]
        exact er
    · obtain ⟨r, g', hr, er, eb⟩ := s2_mth_tail h64 mods g h lf target easing lf.time false lf.key_up hI ha (by omega) hbi
      refine ⟨r, g', ?_, ?_, fun v hv => by obtain ⟨e1, e2, e3, e4, e5⟩ := eb v hv; exact ⟨e1, e2, by omega, e4, e5⟩⟩
      · unfold sim.autogen.move_to_hit_object
        simp only [hlf, bind_ok, hsub1, s2_f100, hx, hbr, s2_ag_consts.1, hsub2, hmax, hsub3, hlt, hw, decide_false,
          Bool.false_eq_true, ite_false]
        exact hr
      · rw [if_neg hw]
        exact er
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the non-skip part of `add_hit_object_replay` (verbatim from the extraction) -/
def s2_ahrJP (mods : Slice sim.mods.RateMod) (g : sim.autogen.G) (o : sim.playable.TopObj)
    (o1 : Option sim.playable.SpinnerData) (start_position1 : net.osutk.Vector2) (easing : net.framework.Easing)
    (spinner_direction1 : F32) (se : net.osutk.Vector2) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.autogen.G) := do
  let i := alloc.vec.Vec.len g.frames
  if i > 0#usize
  then
    let (r, g1) ←
      sim.autogen.move_to_hit_object mods g o.h start_position1 easing
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r1, g2) ←
        sim.autogen.add_click_frames mods g1 { o with spinner := o1 }
          start_position1 spinner_direction1 se
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok (), g2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr) residual
        ok (r2, g2)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r1, g1)
  else
    let (r, g1) ←
      sim.autogen.add_click_frames mods g { o with spinner := o1 }
        start_position1 spinner_direction1 se
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ok (core.result.Result.Ok (), g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r1, g1)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

set_option maxHeartbeats 50000 in
theorem s2_mth_tn (tn : Nat → String) (h : sim.playable.HObj) (t : OsuTK.Vector2) (e : Easing) :
    moveToHitObject (hobjS tn h) t e = moveToHitObject (abs h) t e := by
  rw [s2_mth_eq, s2_mth_eq]
  unfold s2_mthS s2_mthJP1 s2_mthLoop s2_moveBodyS
  rfl

set_option maxHeartbeats 40000 in
theorem s2_ahr_jp (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g : sim.autogen.G)
    (o : sim.playable.TopObj) (sp1 : net.osutk.Vector2) (easing : net.framework.Easing) (dir : F32)
    (se : net.osutk.Vector2) (tn : Nat → String) (hI : s2_gInv g) (hne : 0 < g.frames.val.length)
    (hsd : ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62)
    (hh : g.heap.val.length + 10000003 < Usize.max) (hfl : g.frames.val.length + 20000004 < 2^62)
    (hbi : g.button_index.val < U64.max) :
    ∃ r g', s2_ahrJP mods g o o.spinner sp1 easing dir se = ok (r, g') ∧
      s2_GR id g' r ((moveToHitObject (topS tn o).h (v2S sp1) (easingS easing) >>= fun _ =>
        addClickFrames (topS tn o) (v2S sp1) dir (v2S se)) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index.val ≤ g.button_index.val + 1 ∧ 0 < g'.frames.val.length ∧
        g'.heap.val.length ≤ g.heap.val.length + 10000003 ∧ g'.frames.val.length ≤ g.frames.val.length + 20000004 ∧
        s2_gInv g') := by
  obtain ⟨r1, g1, h1, e1, b1⟩ := sim.autogen.move_to_hit_object_refines h64 mods g o.h sp1 easing hI hne (by omega) hbi
  have hhh : (topS tn o).h = hobjS tn o.h := rfl
  have hoo : ({ o with spinner := o.spinner } : sim.playable.TopObj) = o := rfl
  have hpos : alloc.vec.Vec.len g.frames > 0#usize := by scalar_tac
  have hbrE : ∀ {α : Type} (e : sim.err.SimErr), core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result α sim.err.SimErr) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := fun _ => rfl
  have hbrO : ∀ {α : Type} (x : α), core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result α sim.err.SimErr) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := fun _ => rfl
  have hfr : ∀ (e : sim.err.SimErr), core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
      (core.convert.FromSame sim.err.SimErr) (core.result.Result.Err e) = ok (core.result.Result.Err e) := by
    intro e; simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
  cases r1 with
  | Err e =>
    refine ⟨.Err e, g1, ?_, ?_, fun _ h => by cases h⟩
    · simp only [s2_ahrJP, if_pos hpos, h1, bind_ok]; simp [hbrE, hfr]
    · obtain ⟨m, hm⟩ := e1
      exact ⟨m, by rw [hhh, s2_mth_tn]; simp only [s2_am_bind, hm, Except.bind]⟩
  | Ok u =>
    obtain ⟨c1, c2, c3, c4, c5⟩ := b1 u rfl
    simp only [s2_GR] at e1
    obtain ⟨r2, g2, h2, e2, b2⟩ := sim.autogen.add_click_frames_refines h64 mods g1 o sp1 dir se tn c5 hsd
      (by rw [c1]; omega) (by omega)
    have hsp : ((moveToHitObject (topS tn o).h (v2S sp1) (easingS easing) >>= fun _ =>
        addClickFrames (topS tn o) (v2S sp1) dir (v2S se)) (abs mods) (abs g)) =
        addClickFrames (topS tn o) (v2S sp1) dir (v2S se) (abs mods) (abs g1) := by
      rw [hhh, s2_mth_tn]; simp only [s2_am_bind, e1, Except.bind]
    rw [hsp]
    cases r2 with
    | Err e =>
      refine ⟨.Err e, g2, ?_, e2, fun _ h => by cases h⟩
      simp only [s2_ahrJP, if_pos hpos, h1, bind_ok]; simp [hbrO, h2, hbrE, hfr]
    | Ok u2 =>
      obtain ⟨d0, d1, d2, d3, d4⟩ := b2 u2 rfl
      refine ⟨.Ok (), g2, ?_, e2, fun _ _ => ⟨by rw [d0]; exact c4, d1, by rw [c1] at d2; exact d2, by omega, d4⟩⟩
      simp only [s2_ahrJP, if_pos hpos, h1, bind_ok]; simp [hbrO, h2]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

theorem s2_stackedEnd_tn (tn : Nat → String) (o : sim.playable.TopObj) :
    s2_stackedEndS (topS tn o) = s2_stackedEndS (abs o) := by
  have hf : ∀ tn' : Nat → String, (topS tn' o).nested.find? (·.kind == .tail) =
      (o.nested.val.find? (fun h => kindS h.kind == Kind.tail)).map (hobjS tn') := by
    intro tn'
    show ((o.nested.val.map (hobjS tn')).toArray).find? _ = _
    rw [List.find?_toArray, List.find?_map]; rfl
  have ha : (abs o : TopObj) = topS simTnDefault o := rfl
  unfold s2_stackedEndS
  rw [ha, hf, hf]
  cases o.nested.val.find? (fun h => kindS h.kind == Kind.tail) <;> rfl

theorem s2_kind_ne_spinner (k : sim.playable.Kind) (h : k ≠ .Spinner) : (kindS k == Kind.spinner) = false := by
  cases k <;> first | rfl | exact absurd rfl h

set_option maxHeartbeats 100000 in
theorem s2_ahr_rust_sp (mods : Slice sim.mods.RateMod) (g : sim.autogen.G) (o : sim.playable.TopObj)
    (sp : sim.playable.SpinnerData) (a : sim.autogen.AFrame) (sp2 : net.osutk.Vector2) (dir : F32) (cen : net.osutk.Vector2)
    (se : net.osutk.Vector2) (E : net.framework.Easing)
    (hks : o.h.kind = .Spinner) (hsp : o.spinner = some sp) (h0 : ¬ sp.spins_required = 0#i64)
    (hse : sim.autogen.stacked_end o = ok se)
    (hlf : sim.autogen.last_frame g = ok a) (hcs : sim.autogen.calc_spinner_start a.pos = ok (sp2, dir))
    (hcen : sim.autogen.spinner_centre = ok cen)
    (bE : Bool) (hlt2 : float.F32.lt spinRadius ((v2S cen).sub (v2S a.pos)).length = ok bE)
    (hE : (if bE = true then net.framework.Easing.In else net.framework.Easing.Out) = E) :
    sim.autogen.add_hit_object_replay mods g o = s2_ahrJP mods g o o.spinner sp2 E dir se := by
  obtain ⟨-, h1, hR⟩ := s2_ag_f32
  have hneg : float.F32.neg (1 : F32) = ok (-1) := rfl
  have hspv : sim.autogen.of_vec o.h.stacked = ok ⟨o.h.stacked.x, o.h.stacked.y⟩ := rfl
  have hkb' : (kindS o.h.kind == kindS sim.playable.Kind.Spinner) = true := by rw [hks]; rfl
  have hif : ∀ (c : Prop) [Decidable c], (if c then (ok net.framework.Easing.In : Result _) else ok net.framework.Easing.Out) =
      ok (if c then net.framework.Easing.In else net.framework.Easing.Out) := fun c _ => by split <;> rfl
  unfold sim.autogen.add_hit_object_replay
  simp only [hse, hspv, h1, hneg, kind_eq_ok, bind_ok, hkb', ite_true, hsp, h0, ite_false, hlf, hcs, hcen,
    net.osutk.v2_sub_refines, net.osutk.v2_length_refines, hR, s2_v2SI, hlt2, hif, hE, Function.uncurry_apply_pair, bind_ok, Bool.false_eq_true, ite_false]
  rw [← hsp]
  unfold s2_ahrJP
  simp
  rfl

set_option maxHeartbeats 300000 in
theorem sim.autogen.add_hit_object_replay_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (o : sim.playable.TopObj) (tn : Nat → String) (hI : s2_gInv g) (hne : 0 < g.frames.val.length)
    (hsd : ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62)
    (hh : g.heap.val.length + 10000003 < Usize.max) (hfl : g.frames.val.length + 20000004 < 2^62)
    (hbi : g.button_index.val < U64.max) :
    ∃ r g', sim.autogen.add_hit_object_replay mods g o = ok (r, g') ∧
      s2_GR id g' r (addHitObjectReplay (topS tn o) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index.val ≤ g.button_index.val + 1 ∧ 0 < g'.frames.val.length ∧
        g'.heap.val.length ≤ g.heap.val.length + 10000003 ∧ g'.frames.val.length ≤ g.frames.val.length + 20000004 ∧
        s2_gInv g') := by
  obtain ⟨se, hse, ese⟩ := sim.autogen.stacked_end_refines o
  obtain ⟨-, h1, hR⟩ := s2_ag_f32
  have hneg : float.F32.neg (1 : F32) = ok (-1) := rfl
  have hspv : sim.autogen.of_vec o.h.stacked = ok ⟨o.h.stacked.x, o.h.stacked.y⟩ := rfl
  have hsz : ((abs g : G).frames.size > 0) = True := by simp [abs, s2_gS]; omega
  have hget : (get : M G) (abs mods) (abs g) = .ok (abs g, abs g) := rfl
  by_cases hks : o.h.kind = .Spinner
  · have hkb' : (kindS o.h.kind == kindS sim.playable.Kind.Spinner) = true := by rw [hks]; rfl
    have hk' : ((topS tn o).h.kind == Kind.spinner) = true := by
      show (kindS o.h.kind == Kind.spinner) = true; rw [hks]; rfl
    have hsS : (topS tn o).spinner = o.spinner.map abs := rfl
    cases hsp : o.spinner with
    | none =>
      refine ⟨.Ok (), g, ?_, ?_, fun _ _ => ⟨by omega, hne, by omega, by omega, hI⟩⟩
      · unfold sim.autogen.add_hit_object_replay
        simp only [hse, hspv, h1, hneg, kind_eq_ok, bind_ok, hkb', ite_true, hsp]
        rfl
      · unfold addHitObjectReplay
        simp only [hk', ite_true, hsS, hsp, Option.map_none]
        rfl
    | some sp =>
      by_cases h0 : sp.spins_required = 0#i64
      · have hsr : ((abs sp : SpinnerData).spinsRequired == 0) = true := by
          show (sp.spins_required.val == (0 : Int)) = true; rw [h0]; rfl
        refine ⟨.Ok (), g, ?_, ?_, fun _ _ => ⟨by omega, hne, by omega, by omega, hI⟩⟩
        · unfold sim.autogen.add_hit_object_replay
          simp only [hse, hspv, h1, hneg, kind_eq_ok, bind_ok, hkb', ite_true, hsp, h0]
          simp
        · unfold addHitObjectReplay
          simp only [hk', ite_true, hsS, hsp, Option.map_some, hsr]
          rfl
      · have hsr : ((abs sp : SpinnerData).spinsRequired == 0) = false := by
          show (sp.spins_required.val == (0 : Int)) = false
          rw [beq_eq_false_iff_ne]; intro h; exact h0 (by scalar_tac)
        obtain ⟨a, hlf, elf⟩ := sim.autogen.last_frame_refines g (abs mods) hne
        obtain ⟨⟨sp2, dir⟩, hcs, ecs⟩ := sim.autogen.calc_spinner_start_refines a.pos
        obtain ⟨cen, hcen, ecen⟩ := sim.autogen.spinner_centre_refines
        have hcen' : v2S cen = spinnerCentre := ecen.symm
        have ecs' : calcSpinnerStart (v2S a.pos) = (v2S sp2, dir) := ecs
        have hpos' : (abs a : AFrame).pos = v2S a.pos := rfl
        by_cases hlt : spinRadius < ((v2S cen).sub (v2S a.pos)).length
        · obtain ⟨r, g', hr, er, eb⟩ := s2_ahr_jp h64 mods g o sp2 .In dir se tn hI hne hsd hh hfl hbi
          refine ⟨r, g', ?_, ?_, eb⟩
          · rw [s2_ahr_rust_sp mods g o sp a sp2 dir cen se .In hks hsp h0 hse hlf hcs hcen _ rfl (by simp [hlt])]
            exact hr
          · have hs : addHitObjectReplay (topS tn o) (abs mods) (abs g) =
                (moveToHitObject (topS tn o).h (v2S sp2) Easing.in_ >>= fun _ =>
                  addClickFrames (topS tn o) (v2S sp2) dir (s2_stackedEndS (topS tn o))) (abs mods) (abs g) := by
              unfold addHitObjectReplay
              simp only [hk', ite_true, hsS, hsp, Option.map_some, hsr, Bool.false_eq_true, ite_false, s2_am_bind, elf,
                Except.bind, hpos', ecs']
              rw [if_pos (by rw [← hcen']; exact hlt)]
              simp only [s2_am_get_bind, hsz, ite_true]
              rfl
            rw [hs, s2_stackedEnd_tn, ese]
            exact er
        · obtain ⟨r, g', hr, er, eb⟩ := s2_ahr_jp h64 mods g o sp2 .Out dir se tn hI hne hsd hh hfl hbi
          refine ⟨r, g', ?_, ?_, eb⟩
          · rw [s2_ahr_rust_sp mods g o sp a sp2 dir cen se .Out hks hsp h0 hse hlf hcs hcen _ rfl (by simp [hlt])]
            exact hr
          · have hs : addHitObjectReplay (topS tn o) (abs mods) (abs g) =
                (moveToHitObject (topS tn o).h (v2S sp2) Easing.out >>= fun _ =>
                  addClickFrames (topS tn o) (v2S sp2) dir (s2_stackedEndS (topS tn o))) (abs mods) (abs g) := by
              unfold addHitObjectReplay
              simp only [hk', ite_true, hsS, hsp, Option.map_some, hsr, Bool.false_eq_true, ite_false, s2_am_bind, elf,
                Except.bind, hpos', ecs']
              rw [if_neg (by rw [← hcen']; exact hlt)]
              simp only [s2_am_get_bind, hsz, ite_true]
              rfl
            rw [hs, s2_stackedEnd_tn, ese]
            exact er
  · have hkb := s2_kind_ne_spinner _ hks
    obtain ⟨r, g', hr, er, eb⟩ := s2_ahr_jp h64 mods g o ⟨o.h.stacked.x, o.h.stacked.y⟩ .Out (-1) se tn hI hne hsd hh hfl hbi
    refine ⟨r, g', ?_, ?_, eb⟩
    · unfold sim.autogen.add_hit_object_replay
      have hkb' : (kindS o.h.kind == kindS sim.playable.Kind.Spinner) = false := hkb
      simp only [hse, hspv, h1, hneg, kind_eq_ok, bind_ok, hkb', Bool.false_eq_true, ite_false]
      exact hr
    · have hk' : ((topS tn o).h.kind == Kind.spinner) = false := hkb
      have hs : addHitObjectReplay (topS tn o) (abs mods) (abs g) =
          (moveToHitObject (topS tn o).h (ofVec (topS tn o).h.stacked) Easing.out >>= fun _ =>
            addClickFrames (topS tn o) (ofVec (topS tn o).h.stacked) (-1) (s2_stackedEndS (topS tn o))) (abs mods) (abs g) := by
        unfold addHitObjectReplay
        simp only [hk', Bool.false_eq_true, ite_false, s2_am_get_bind, hsz, ite_true]
        rfl
      rw [hs, s2_stackedEnd_tn, ese]
      exact er
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

set_option maxHeartbeats 200000 in
theorem s2_gen_loop (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (pb : sim.playable.Playable)
    (tn : Nat → String)
    (hsd : ∀ o ∈ pb.objects.val, ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62) :
    ∀ (n : Nat) (i : Usize) (g : sim.autogen.G), pb.objects.val.length - i.val = n → i.val ≤ pb.objects.val.length →
      s2_gInv g → 0 < g.frames.val.length → g.heap.val.length + n * 10000003 < Usize.max →
      g.frames.val.length + n * 20000004 < 2^62 → g.button_index.val + n < U64.max →
      ∃ r g', sim.autogen.generate_objects_loop pb mods g i = ok (r, g') ∧
        s2_GR id g' r ((forIn ((pb.objects.val.drop i.val).map (topS tn)) PUnit.unit
          (fun o _ => do addHitObjectReplay o; pure (ForInStep.yield PUnit.unit)) : M PUnit) (abs mods) (abs g)) := by
  intro n
  induction n with
  | zero =>
    intro i g hn hi hI hne hh hfl hbi
    refine ⟨.Ok (), g, ?_, ?_⟩
    · unfold sim.autogen.generate_objects_loop
      rw [loop_unfold]
      have : ¬ (i < alloc.vec.Vec.len pb.objects) := by scalar_tac
      simp [sim.autogen.generate_objects_loop.body, this]
    · have : pb.objects.val.drop i.val = [] := by simp; omega
      rw [this]; rfl
  | succ n ih =>
    intro i g hn hi hI hne hh hfl hbi
    have hil : i.val < pb.objects.val.length := by omega
    let o := pb.objects.val[i.val]'hil
    have hdrop : pb.objects.val.drop i.val = o :: pb.objects.val.drop (i.val + 1) := List.drop_eq_getElem_cons hil
    obtain ⟨r1, g1, h1, e1, b1⟩ := sim.autogen.add_hit_object_replay_refines h64 mods g o tn hI hne
      (hsd o (List.getElem_mem hil)) (by nlinarith) (by nlinarith) (by omega)
    have hlt : i < alloc.vec.Vec.len pb.objects := by scalar_tac
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) pb.objects i = ok o := by
      simp [vec_index_eq' _ _ hil, vec_index_usize_ok _ _ hil, o]
    rw [hdrop]
    cases r1 with
    | Err e =>
      refine ⟨.Err e, g1, ?_, ?_⟩
      · unfold sim.autogen.generate_objects_loop
        rw [loop_unfold]
        simp [sim.autogen.generate_objects_loop.body, hlt, hidx, h1, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := e1
        refine ⟨m, ?_⟩
        simp only [List.map_cons, List.forIn_cons, s2_am_bind, hm]
        rfl
    | Ok u =>
      obtain ⟨c0, c1, c2, c3, c4⟩ := b1 u rfl
      obtain ⟨i2, hi2, hi2v⟩ : ∃ i2 : Usize, i + 1#usize = ok i2 ∧ i2.val = i.val + 1 := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        exact ⟨z, hz, by scalar_tac⟩
      obtain ⟨r, g', hr, er⟩ := ih i2 g1 (by omega) (by omega) c4 c1 (by nlinarith) (by nlinarith) (by omega)
      refine ⟨r, g', ?_, ?_⟩
      · unfold sim.autogen.generate_objects_loop
        rw [loop_unfold]
        have hb : sim.autogen.generate_objects_loop.body pb mods g i = ok (.cont (g1, i2)) := by
          simp [sim.autogen.generate_objects_loop.body, hlt, hidx, h1, core.result.Result.Insts.CoreOpsTry.branch, hi2]
        dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.autogen.generate_objects_loop at hr
        exact hr
      · simp only [s2_GR] at e1
        simp only [List.map_cons, List.forIn_cons, s2_am_bind, e1, Except.bind]
        rw [hi2v] at er
        exact er
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

set_option maxHeartbeats 200000 in
/-- `sim::autogen::generate` refines `OsuModel.Sim.AutoGen.generate`, for any type-name table `tn`, under at most
`2^32` hit objects and slider paths shorter than `2^62`. -/
theorem sim.autogen.generate_refines (h64 : System.Platform.numBits = 64) (pb : sim.playable.Playable)
    (mods : Slice sim.mods.RateMod) (tn : Nat → String)
    (hn : pb.objects.val.length < 2^32)
    (hsd : ∀ o ∈ pb.objects.val, ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62) :
    ∃ r, sim.autogen.generate pb mods = ok r ∧
      match r with
      | .Ok v => OsuModel.Sim.AutoGen.generate (playableS tn pb) (abs mods) = .ok ((v.val.map abs).toArray)
      | .Err _ => ∃ m, OsuModel.Sim.AutoGen.generate (playableS tn pb) (abs mods) = .error m := by
  have hU := usize_max_64 h64
  have hsz : (playableS tn pb).objects.size = pb.objects.val.length := by simp [playableS]
  by_cases h0 : pb.objects.val.length = 0
  · refine ⟨.Ok (alloc.vec.Vec.new sim.autogen.AFrame), ?_, ?_⟩
    · have : alloc.vec.Vec.len pb.objects = 0#usize := by scalar_tac
      simp [sim.autogen.generate, this]
    · unfold OsuModel.Sim.AutoGen.generate
      rw [dif_pos (by rw [hsz]; exact h0)]
      rfl
  · have hne0 : 0 < pb.objects.val.length := by omega
    have h1500 : float.F64.from_bits 4654311885213007872#u64 = ok (1500 : F64) := by
      simp only [float.F64.from_bits]; congr 1 <;> decide +kernel
    have h256 : float.F32.from_bits 1132462080#u32 = ok (256 : F32) := by
      simp only [float.F32.from_bits]; congr 1 <;> decide +kernel
    have h500 : float.F32.from_bits 1140457472#u32 = ok (500 : F32) := by
      simp only [float.F32.from_bits]; congr 1 <;> decide +kernel
    let g0 : sim.autogen.G := { frames := alloc.vec.Vec.new _, button_index := 0#u64, heap := alloc.vec.Vec.new _ }
    have hg0 : (abs g0 : G) = {} := by simp [abs, s2_gS, g0]
    have hI0 : s2_gInv g0 := ⟨by simp [g0], by simp [abs, s2_gS, g0]⟩
    obtain ⟨r, g, hr, hrv, er, hgh, hgf, hgb⟩ := s2_ag_new_list (abs mods) g0 replay.frames.ACTLIST_EMPTY (by simp [g0]; omega)
    have hIg := (s2_inv_new_list g0 g _ r hI0 (by simp [s2_empty_val.2]) (by simp [g0]; omega) hr).1
    have hrv0 : r.val = 0 := by rw [hrv]; simp [g0]
    let o0 := pb.objects.val[0]'hne0
    let f0 : sim.autogen.AFrame := { time := o0.h.start - 1500, pos := ⟨256, 500⟩, actions := r, key_up := false }
    obtain ⟨g1, hg1, eg1, hg1h, hg1f, hg1b⟩ := s2_add_frame h64 mods g f0 (by rw [hgf]; simp [g0])
    have hI1 : s2_gInv g1 := s2_inv_add_frame g g1 f0 _ hIg (by show r.val < _; rw [hgh, hrv0]; simp [g0]) eg1 hg1h
    have hf1 : g1.frames.val.length = 1 := by rw [hg1f, hgf]; simp [g0]
    have hh1 : g1.heap.val.length = 1 := by rw [hg1h, hgh]; simp [g0]
    have hb1 : g1.button_index.val = 0 := by rw [hg1b, hgb]; simp [g0]
    obtain ⟨R, G', hR, eR⟩ := s2_gen_loop h64 mods pb tn hsd pb.objects.val.length 0#usize g1 (by simp) (by simp) hI1
      (by omega) (by rw [hh1, hU]; omega) (by rw [hf1]; omega) (by rw [hb1]; scalar_tac)
    have er' : newList [] (abs mods) {} = .ok (0, abs g) := by
      rw [← hg0, ← hrv0, ← s2_abs_empty]; exact er
    have eg1' : addFrame { time := (topS tn o0).h.start - 1500, pos := v 256 500, actions := 0 } (abs mods) (abs g) = .ok ((), abs g1) := by
      rw [← hrv0]; exact eg1
    have hobj : (playableS tn pb).objects = (pb.objects.val.map (topS tn)).toArray := rfl
    have h0s : (playableS tn pb).objects[0]'(by rw [hsz]; exact hne0) = topS tn o0 := by simp [playableS, o0]
    have hspec : generate (playableS tn pb) (abs mods) =
        (forIn ((pb.objects.val.drop 0).map (topS tn)) PUnit.unit
          (fun o _ => do addHitObjectReplay o; pure (ForInStep.yield PUnit.unit)) (abs mods) (abs g1)).bind
          (fun p => .ok p.2.frames) := by
      unfold OsuModel.Sim.AutoGen.generate
      rw [dif_neg (by rw [hsz]; exact h0)]
      simp only [ReaderT.run, StateT.run, s2_am_bind, er', Except.bind, h0s]
      simp only [eg1']
      simp only [hobj, List.forIn_toArray, List.drop_zero]
      generalize (forIn (List.map (topS tn) pb.objects.val) PUnit.unit
          (fun o _ => do addHitObjectReplay o; pure (ForInStep.yield PUnit.unit)) : M PUnit) (abs mods) (abs g1) = X
      cases X <;> rfl
    have hlen0 : alloc.vec.Vec.len pb.objects ≠ 0#usize := by intro h; apply h0; scalar_tac
    have hidx0 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) pb.objects 0#usize = ok o0 := by
      have hz : (0#usize : Usize).val < pb.objects.val.length := by simpa using hne0
      simp [vec_index_eq' _ _ hz, vec_index_usize_ok _ _ hz, o0]
    have hg1' : sim.autogen.add_frame g { time := o0.h.start - 1500, pos := ⟨256, 500⟩, actions := r, key_up := false } = ok g1 := hg1
    have hR' : sim.autogen.generate_objects pb mods g1 = ok (R, G') := hR
    have hr' : sim.autogen.new_list { frames := alloc.vec.Vec.new sim.autogen.AFrame, button_index := 0#u64, heap := alloc.vec.Vec.new replay.frames.ActList } replay.frames.ACTLIST_EMPTY = ok (r, g) := hr
    simp only [s2_GR, show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at eR
    rw [hspec]
    cases R with
    | Ok u =>
      refine ⟨.Ok G'.frames, ?_, ?_⟩
      · simp only [sim.autogen.generate, hlen0, ite_false, hr', bind_ok, hidx0, h1500, float.F64.sub, h256, h500]
        simp [net.osutk.v2, hg1', hR', core.result.Result.Insts.CoreOpsTry.branch]
      · simp only [List.drop_zero, eR, Except.bind]
        rfl
    | Err e =>
      refine ⟨.Err e, ?_, ?_⟩
      · simp only [sim.autogen.generate, hlen0, ite_false, hr', bind_ok, hidx0, h1500, float.F64.sub, h256, h500]
        simp [net.osutk.v2, hg1', hR', core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := eR
        exact ⟨m, by simp only [List.drop_zero, hm, Except.bind]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay OsuModel.Net.Framework

/-! Named refinement theorems for the autogen helpers (the `s2_` lemmas above, under the audit's names). -/

/-- FRAGMENT-OF: sim.autogen.add_click_frames (spec side: the restated fixup continuation `s2_fixJP`) -/
theorem sim.autogen.click_frames_fixup_refines : type_of% @s2_fixup := @s2_fixup

/-- FRAGMENT-OF: sim.autogen.add_click_frames (spec side: one iteration `s2_sliderStepS` of the slider loop) -/
theorem sim.autogen.slider_frame_step_refines : type_of% @s2_slider_frame_step := @s2_slider_frame_step

/-- FRAGMENT-OF: sim.autogen.add_click_frames (spec side: the slider branch `s2_sliderClickS`) -/
theorem sim.autogen.slider_click_frames_refines : type_of% @s2_slider_click_frames := @s2_slider_click_frames

/-- FRAGMENT-OF: sim.autogen.add_click_frames (spec side: the spinner branch `s2_spinClickS`) -/
theorem sim.autogen.spinner_click_frames_refines : type_of% @s2_spinner_click_frames := @s2_spinner_click_frames

/-- FRAGMENT-OF: sim.autogen.move_to_hit_object (spec side: one iteration `s2_moveStepS` of the move loop) -/
theorem sim.autogen.move_frame_step_refines : type_of% @s2_move_frame_step := @s2_move_frame_step

/-- FRAGMENT-OF: sim.autogen.add_click_frames (spec side: the slider loop as fuel recursion `s2_sliderFramesS`) -/
theorem sim.autogen.slider_frames_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (h : sim.playable.HObj) (sd : sim.playable.SliderData) (j : F64) (action : replay.frames.Action)
    (hc : sd.cum_len.val.length < 2^62) (hp : sd.path.val.length < 2^62)
    (hh : g.heap.val.length + 10000000 < Usize.max) (hfl : g.frames.val.length + 10000000 < 2^62) :
    ∃ r g', sim.autogen.slider_frames mods g h sd j action = ok (r, g') ∧
      s2_GR (fun x : U32 × F64 => (x.1.val, x.2)) g' r
        (s2_sliderFramesS (abs h.stacked) h.start (abs sd) (s2_actS action) 10000000 j (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g.heap.val.length ≤ g'.heap.val.length ∧
        g'.heap.val.length ≤ g.heap.val.length + 10000000 ∧ g'.frames.val.length ≤ g.frames.val.length + 10000000 ∧
        (s2_gInv g → s2_gInv g')) :=
  s2_slider_frames_loopB h64 mods h sd action hc hp 10000000 10000000#u32 g j rfl hh hfl

/-- FRAGMENT-OF: sim.autogen.move_to_hit_object (spec side: the move loop as fuel recursion `s2_moveFramesS`) -/
theorem sim.autogen.move_frames_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (h : sim.playable.HObj) (lf : sim.autogen.AFrame) (target : net.osutk.Vector2)
    (easing : net.framework.Easing) (time : F64) (hfl : g.frames.val.length + 10000000 < 2^62) :
    ∃ r g', sim.autogen.move_frames mods g h lf target easing time = ok (r, g') ∧
      s2_GR (fun x : U32 × F64 => (x.1.val, x.2)) g' r
        (s2_moveFramesS h.start (v2S lf.pos) (v2S target) lf.time lf.actions.val (easingS easing) 10000000 time
          (abs mods) (abs g)) ∧
      g'.heap = g.heap ∧ g'.button_index = g.button_index ∧ g.frames.val.length ≤ g'.frames.val.length ∧
      g'.frames.val.length ≤ g.frames.val.length + 10000000 ∧
      (s2_gInv g → lf.actions.val < g.heap.val.length → s2_gInv g') :=
  s2_move_frames_loopB h64 mods h lf target easing 10000000 10000000#u32 g time rfl hfl

/-- FRAGMENT-OF: sim.autogen.generate (spec side: the `for o in pb.objects` loop of `generate`) -/
theorem sim.autogen.generate_objects_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (pb : sim.playable.Playable) (tn : Nat → String) (g : sim.autogen.G)
    (hsd : ∀ o ∈ pb.objects.val, ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62)
    (hI : s2_gInv g) (hne : 0 < g.frames.val.length)
    (hh : g.heap.val.length + pb.objects.val.length * 10000003 < Usize.max)
    (hfl : g.frames.val.length + pb.objects.val.length * 20000004 < 2^62)
    (hbi : g.button_index.val + pb.objects.val.length < U64.max) :
    ∃ r g', sim.autogen.generate_objects pb mods g = ok (r, g') ∧
      s2_GR id g' r ((forIn (pb.objects.val.map (topS tn)) PUnit.unit
        (fun o _ => do addHitObjectReplay o; pure (ForInStep.yield PUnit.unit)) : M PUnit) (abs mods) (abs g)) := by
  obtain ⟨r, g', h1, h2⟩ := s2_gen_loop h64 mods pb tn hsd pb.objects.val.length 0#usize g (by simp) (by simp)
    hI hne hh hfl hbi
  exact ⟨r, g', h1, by simpa using h2⟩
end OsuProofs
