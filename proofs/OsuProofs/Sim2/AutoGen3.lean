/-
`sim::autogen` click frames (sim2): `add_frame` with its length postcondition, the spinner and slider branches of
`OsuModel.Sim.AutoGen.addClickFrames`. The spec `while` loops are restated by their elaborated bodies
(`s2_spinBodyS`, `s2_sliderBodyS`, equal by `rfl` inside `addClickFrames`) and turned into fuel recursions
(`s2_spinFramesS` = sim3a's `s3aSpinFramesS`, `s2_sliderFramesS`). `add_frame` needs `frames.len < 2^62`, so the loops
carry heap/frames budgets instead of sim3a's unconditional `s3aAddFrameOk`, and the invariant `s2_gInv` (heap lists
have length <= 3, frame action refs are in range). `click_frames_fixup` is modelled by `s2_cfxS`/`s2_fixJP`, and
`add_click_frames` refines `addClickFrames` (`sim.autogen.add_click_frames_refines`) through the prefix lemma
`s2_acf_pre` and the verbatim tail `s2_acfTail`.
-/
import OsuProofs.Sim2.AutoGen2
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_add_frame (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (f : sim.autogen.AFrame) (h : g.frames.val.length < 2^62) :
    ∃ g', sim.autogen.add_frame g f = ok g' ∧
      OsuModel.Sim.AutoGen.addFrame (abs f) (abs mods) (abs g) = .ok ((), abs g') ∧ g'.heap = g.heap ∧
      g'.frames.val.length = g.frames.val.length + 1 ∧ g'.button_index = g.button_index := by
  obtain ⟨g', h1, h2, h3⟩ := sim.autogen.add_frame_refines h64 mods g f h
  refine ⟨g', h1, h2, h3, ?_⟩
  unfold OsuModel.Sim.AutoGen.addFrame at h2
  simp only [s2_am_get_bind] at h2
  split at h2
  · simp only [s2_am_set, Except.ok.injEq, Prod.mk.injEq] at h2
    have e1 := congrArg (fun G => G.frames.size) h2.2
    have e2 := congrArg (fun G => G.buttonIndex) h2.2
    simp only [abs, s2_gS, Array.size_insertIdx, List.size_toArray, List.length_map] at e1 e2
    exact ⟨e1.symm, UScalar.eq_of_val_eq e2.symm⟩
  · simp at h2
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

/-- generator invariant: action lists have length ≤ 3, every frame's action reference is in the heap -/
def s2_gInv (g : sim.autogen.G) : Prop :=
  (∀ l ∈ g.heap.val, l.len.val ≤ 3) ∧ ∀ x ∈ (abs g : G).frames, x.actions < g.heap.val.length

theorem s2_addFrame_mem (F : OsuModel.Sim.AFrame) (C : List OsuModel.Sim.RateMod) (S S' : G)
    (h : addFrame F C S = .ok ((), S')) : ∀ x ∈ S'.frames, x ∈ S.frames ∨ x = F := by
  unfold addFrame at h
  simp only [s2_am_get_bind] at h
  split at h
  · simp only [s2_am_set, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    intro x hx
    simp only [Array.mem_insertIdx] at hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx
  · simp at h

theorem s2_inv_add_frame (g g' : sim.autogen.G) (f : sim.autogen.AFrame) (C : List OsuModel.Sim.RateMod)
    (hI : s2_gInv g) (hf : f.actions.val < g.heap.val.length)
    (eg : addFrame (abs f) C (abs g) = .ok ((), abs g')) (hh : g'.heap = g.heap) : s2_gInv g' := by
  refine ⟨by rw [hh]; exact hI.1, ?_⟩
  intro x hx
  rw [hh]
  rcases s2_addFrame_mem _ _ _ _ eg x hx with hx | hx
  · exact hI.2 x hx
  · rw [hx]; exact hf

theorem s2_inv_new_list (g g' : sim.autogen.G) (xs : replay.frames.ActList) (k : Usize)
    (hI : s2_gInv g) (hxs : xs.len.val ≤ 3) (hl : g.heap.val.length < Usize.max) (hk : sim.autogen.new_list g xs = ok (k, g')) :
    s2_gInv g' ∧ k.val = g.heap.val.length ∧ g'.heap.val.length = g.heap.val.length + 1 := by
  unfold sim.autogen.new_list at hk
  simp [vec_push_ok _ _ hl] at hk
  obtain ⟨rfl, rfl⟩ := hk
  refine ⟨⟨?_, ?_⟩, by simp, by simp⟩
  · intro l hl'
    simp [vpush_val] at hl'
    rcases hl' with hl' | rfl
    · exact hI.1 l hl'
    · exact hxs
  · intro x hx
    have : x.actions < g.heap.val.length := hI.2 x hx
    simp [vpush_val]; omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_cast_i32I (v : Int32) : (IScalar.cast .I64 (i32I v)).val = v.toInt := by
  have hv : ((i32I v).val : Int) = v.toInt := by rw [← i32S_toInt, i32S_i32I]
  simp [IScalar.cast_val_eq, hv]

/-- one iteration of the spinner frame loop of `addClickFrames` (after the fuel decrement) -/
def s2_spinStepS (angle0 : F32) (prev next : F64) (dir : F32) (action : OsuModel.Replay.Action) :
    OsuModel.Sim.AutoGen.M (F32 × F64) := do
  let t := (← OsuModel.Sim.AutoGen.applyModsToTimeDelta prev next) * F32.toF64 dir
  let angle := angle0 + F64.toF32 t * OsuModel.Sim.AutoGen.radsPerMillisecond
  let pos := OsuModel.Sim.AutoGen.spinnerCentre +
    OsuModel.Sim.AutoGen.circlePosition (F32.toF64 angle) (F32.toF64 OsuModel.Sim.AutoGen.spinRadius)
  OsuModel.Sim.AutoGen.addFrame
    { time := F64.ofInt32 (F64.toInt32 next), pos, actions := ← OsuModel.Sim.AutoGen.newList [action] }
  return (angle, next + (← OsuModel.Sim.AutoGen.getFrameDelay next))

theorem s2_ag_new_list (mods : List OsuModel.Sim.RateMod) (g : sim.autogen.G) (xs : replay.frames.ActList)
    (h : g.heap.val.length < Usize.max) :
    ∃ k g', sim.autogen.new_list g xs = ok (k, g') ∧ k.val = g.heap.val.length ∧
      OsuModel.Sim.AutoGen.newList (s2_actListS xs) mods (abs g) = .ok (k.val, abs g') ∧
      g'.heap.val.length = g.heap.val.length + 1 ∧ g'.frames = g.frames ∧ g'.button_index = g.button_index := by
  refine ⟨alloc.vec.Vec.len g.heap, { g with heap := vpush g.heap xs h }, ?_, by simp, ?_, by simp, rfl, rfl⟩
  · simp [sim.autogen.new_list, vec_push_ok _ _ h]
  · simp only [OsuModel.Sim.AutoGen.newList, s2_am_bind, s2_am_get_bind]
    show Except.ok _ = _
    simp [abs, s2_gS]

theorem s2_eo_ok {α : Type} {E : Except String α} {p : α} (h : s2_eo E = some p) : E = .ok p := by
  cases E <;> simp_all [s2_eo]
theorem s2_eo_none {α : Type} {E : Except String α} (h : s2_eo E = none) : ∃ m, E = .error m := by
  cases E <;> simp_all [s2_eo]

/-- `applyModsToTimeDelta` at any spec state: the Rust value, the state unchanged -/
theorem s2_amd_eval (mods : Slice sim.mods.RateMod) (start endT : F64) (S : OsuModel.Sim.AutoGen.G) :
    ∃ x, sim.autogen.apply_mods_to_time_delta mods start endT = ok x ∧
      match x with
      | .Ok v => OsuModel.Sim.AutoGen.applyModsToTimeDelta start endT (abs mods) S = .ok (v, S)
      | .Err _ => ∃ m, OsuModel.Sim.AutoGen.applyModsToTimeDelta start endT (abs mods) S = .error m := by
  obtain ⟨x, hx, ex⟩ := s2_amd_rust mods start mods.val.length (endT - start) 0#usize (by simp) (by simp)
  refine ⟨x, by simp [sim.autogen.apply_mods_to_time_delta, float.F64.sub, hx], ?_⟩
  have hs := s2_amd_spec start endT (abs mods) S
  simp only [ReaderT.run, StateT.run] at hs
  have ea : (abs mods : List OsuModel.Sim.RateMod) = mods.val.map abs := rfl
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at ex
  rw [ea] at hs ⊢
  cases h : s2_amd start (mods.val.map abs) (endT - start) with
  | none => rw [h] at ex hs; cases x with
    | Ok v => simp [s2_optRel] at ex
    | Err e => exact s2_eo_none hs
  | some v => rw [h] at ex hs; cases x with
    | Ok w => simp only [s2_optRel] at ex; subst ex; exact s2_eo_ok hs
    | Err e => simp [s2_optRel] at ex

theorem s2_fd_eval (mods : Slice sim.mods.RateMod) (time : F64) (S : OsuModel.Sim.AutoGen.G) :
    ∃ x, sim.autogen.get_frame_delay mods time = ok x ∧
      match x with
      | .Ok v => OsuModel.Sim.AutoGen.getFrameDelay time (abs mods) S = .ok (v, S)
      | .Err _ => ∃ m, OsuModel.Sim.AutoGen.getFrameDelay time (abs mods) S = .error m := by
  have hsx : sim.autogen.SIXTY_FRAME = ok (1000.0 / 60 : F64) := by
    unfold sim.autogen.SIXTY_FRAME; simp; decide +kernel
  obtain ⟨x, hx, ex⟩ := s2_amr_rust mods time mods.val.length (1000.0 / 60) 0#usize (by simp) (by simp)
  refine ⟨x, by simp [sim.autogen.get_frame_delay, sim.autogen.apply_mods_to_rate, hsx, hx], ?_⟩
  have hs := s2_amr_spec time (1000.0 / 60) (abs mods) S
  simp only [ReaderT.run, StateT.run] at hs
  have ea : (abs mods : List OsuModel.Sim.RateMod) = mods.val.map abs := rfl
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at ex
  unfold OsuModel.Sim.AutoGen.getFrameDelay
  rw [ea] at hs ⊢
  cases h : s2_amr time (mods.val.map abs) (1000.0 / 60) with
  | none => rw [h] at ex hs; cases x with
    | Ok v => simp [s2_optRel] at ex
    | Err e => exact s2_eo_none hs
  | some v => rw [h] at ex hs; cases x with
    | Ok w => simp only [s2_optRel] at ex; subst ex; exact s2_eo_ok hs
    | Err e => simp [s2_optRel] at ex

@[simp] theorem s2_ag_rads : sim.autogen.RADS_PER_MILLISECOND = ok OsuModel.Sim.AutoGen.radsPerMillisecond := by
  simp [sim.autogen.RADS_PER_MILLISECOND, OsuModel.Sim.AutoGen.radsPerMillisecond, float.F32.from_bits]
@[simp] theorem s2_ag_spinr : sim.autogen.SPIN_RADIUS = ok OsuModel.Sim.AutoGen.spinRadius := by
  simp [sim.autogen.SPIN_RADIUS, OsuModel.Sim.AutoGen.spinRadius]; decide +kernel

/-- Rust `Result<T, SimErr>` + generator state vs the spec `M` evaluation -/
def s2_GR {α β : Type} (f : α → β) (g' : sim.autogen.G) :
    core.result.Result α sim.err.SimErr → Except String (β × OsuModel.Sim.AutoGen.G) → Prop
  | .Ok v, e => e = .ok (f v, abs g')
  | .Err _, e => ∃ m, e = .error m

theorem s2_spinner_frame_step (mods : Slice sim.mods.RateMod) (g : sim.autogen.G) (angle0 : F32)
    (prev next : F64) (dir : F32) (action : replay.frames.Action) (h64 : System.Platform.numBits = 64)
    (hh : g.heap.val.length < Usize.max) (hfl : g.frames.val.length < 2^62) :
    ∃ r g', sim.autogen.spinner_frame_step mods g angle0 prev next dir action = ok (r, g') ∧
      s2_GR id g' r (s2_spinStepS angle0 prev next dir (s2_actS action) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g'.heap.val.length = g.heap.val.length + 1 ∧ g'.frames.val.length = g.frames.val.length + 1 ∧
        (s2_gInv g → s2_gInv g')) := by
  obtain ⟨cen, hcen, ecen⟩ := sim.autogen.spinner_centre_refines
  obtain ⟨x, hx, ex⟩ := s2_amd_eval mods prev next (abs g)
  unfold sim.autogen.spinner_frame_step
  simp only [hcen, hx, bind_ok]
  cases x with
  | Err e =>
    refine ⟨.Err e, g, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun _ h => by cases h⟩
    obtain ⟨m, hm⟩ := ex
    exact ⟨m, by unfold s2_spinStepS; simp only [s2_am_bind, hm]; rfl⟩
  | Ok v =>
    let angle : F32 := angle0 + F64.toF32 (v * F32.toF64 dir) * OsuModel.Sim.AutoGen.radsPerMillisecond
    obtain ⟨cp, hcp, ecp⟩ := sim.autogen.circle_position_refines (F32.toF64 angle) (F32.toF64 OsuModel.Sim.AutoGen.spinRadius)
    obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
    obtain ⟨r1, g1, hr1, hr1v, er1, hg1h, hg1f, hg1bi⟩ := s2_ag_new_list (abs mods) g al hh
    let f : sim.autogen.AFrame := ⟨F64.ofInt (IScalar.cast .I64 (i32I (F64.toInt32 next))).val,
      v2I (OsuTK.Vector2.add (v2S cen) (v2S cp)), r1, false⟩
    obtain ⟨g2, hg2, eg2, hg2h, hg2f, hg2bi⟩ := s2_add_frame h64 mods g1 f (by rw [hg1f]; exact hfl)
    have hf : (abs f : OsuModel.Sim.AFrame) = OsuModel.Sim.AFrame.mk (F64.ofInt32 (F64.toInt32 next))
        (OsuModel.Sim.AutoGen.spinnerCentre + OsuModel.Sim.AutoGen.circlePosition (F32.toF64 angle)
          (F32.toF64 OsuModel.Sim.AutoGen.spinRadius)) r1.val false := by
      show s2_aframeS f = _
      simp only [s2_aframeS, f, s2_cast_i32I, F64.ofInt32, v2S_I, ecen, ecp]
      rfl
    obtain ⟨y, hy, ey⟩ := s2_fd_eval mods next (abs g2)
    have hi32 : ∀ x : Int32, (⟨x.toBitVec⟩ : I32) = i32I x := fun _ => rfl
    have hg2' := hg2
    simp only [f] at hg2'
    have hg3 := hg2'
    have ecast : (IScalar.cast .I64 (i32I (F64.toInt32 next))).val = ((i32I (F64.toInt32 next)).val : Int) := by
      rw [s2_cast_i32I, ← i32S_toInt, i32S_i32I]
    rw [ecast] at hg3
    have hcp' := hcp
    simp only [angle] at hcp'
    have hspec1 : (s2_spinStepS angle0 prev next dir (s2_actS action)) (abs mods) (abs g) =
        (OsuModel.Sim.AutoGen.getFrameDelay next (abs mods) (abs g2)).bind (fun p => .ok ((angle, next + p.1), p.2)) := by
      unfold s2_spinStepS
      simp only [s2_am_bind, ex, Except.bind, eal, er1]
      rw [← hf, eg2]
      rfl
    cases y with
    | Ok d =>
      refine ⟨.Ok (angle, next + d), g2, ?_, ?_, fun _ _ => ⟨by rw [hg2bi, hg1bi], by rw [hg2h, hg1h], by rw [hg2f, hg1f], fun hI => s2_inv_add_frame g1 g2 f _ (s2_inv_new_list g g1 al r1 hI hall (by omega) hr1).1 (by show r1.val < _; omega) eg2 hg2h⟩⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, float.F32.to_f64, float.F64.mul, float.F64.to_f32,
          s2_ag_rads, float.F32.mul, float.F32.add, s2_ag_spinr, hcp', net.osutk.v2_add_refines, hal, hr1, bind_ok,
          float.F64.to_i32_sat, hi32, lift, float.F64.from_i64, hg2', hy, float.F64.add]
        first
          | (split; rename_i a b hab; simp only [Prod.mk.injEq] at hab; obtain ⟨rfl, rfl⟩ := hab; simp only [hg2', bind_ok, angle]; done)
          | (unfold Bind.bind; simp only [hg2', bind_ok, angle]; done)
          | (rw [hg2']; simp only [bind_ok, angle]; done)
          | (simp [hg2', angle]; done)
          | (simp [hg2']; simp [hg3, angle]; done)
      · simp only [s2_GR, hspec1, ey, Except.bind]; rfl
    | Err e =>
      refine ⟨.Err e, g2, ?_, ?_, fun _ h => by cases h⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, float.F32.to_f64, float.F64.mul, float.F64.to_f32,
          s2_ag_rads, float.F32.mul, float.F32.add, s2_ag_spinr, hcp', net.osutk.v2_add_refines, hal, hr1, bind_ok,
          float.F64.to_i32_sat, hi32, lift, float.F64.from_i64, hg2', hy, float.F64.add]
        first
          | (split; rename_i a b hab; simp only [Prod.mk.injEq] at hab; obtain ⟨rfl, rfl⟩ := hab; simp only [hg2', bind_ok])
          | (simp [hg2']; simp [hg3])
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := ey
        exact ⟨m, by simp only [hspec1, hm]; rfl⟩

/-- the spinner frame `while nextFrame < endT && fuel > 0` loop of `addClickFrames` as a fuel recursion over
`s2_spinStepS`; returns `(fuel left, angle, previousFrame, nextFrame)` -/
def s2_spinFramesS (endT : F64) (dir : F32) (action : OsuModel.Replay.Action) :
    Nat → F32 → F64 → F64 → OsuModel.Sim.AutoGen.M (Nat × F32 × F64 × F64)
  | 0, a, p, n => pure (0, a, p, n)
  | k + 1, a, p, n =>
    if n < endT then do
      let (a2, n2) ← s2_spinStepS a p n dir action
      s2_spinFramesS endT dir action k a2 n n2
    else pure (k + 1, a, p, n)

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

/-- the spinner `while` body of `addClickFrames` (elaborated form, restated) -/
def s2_spinBodyS (endT : F64) (spinnerDirection : F32) (action : OsuModel.Replay.Action) :
    Unit → F32 × F64 × F64 × Nat → M (ForInStep (F32 × F64 × F64 × Nat)) := fun _ __s =>
  let angle := __s.1
  let previousFrame := __s.2.1
  let nextFrame := __s.2.2.1
  let fuel := __s.2.2.2
  if (decide (nextFrame < endT) && decide (fuel > 0)) = true then
    let fuel := fuel - 1
    do
    let __do_lift ← applyModsToTimeDelta previousFrame nextFrame
    let t : F64 := __do_lift * spinnerDirection.toF64
    let angle : F32 := angle + t.toF32 * radsPerMillisecond
    let pos : OsuModel.Net.OsuTK.Vector2 := spinnerCentre + circlePosition angle.toF64 spinRadius.toF64
    let __do_lift ← newList [action]
    addFrame { time := F64.ofInt32 nextFrame.toInt32, pos := pos, actions := __do_lift }
    let previousFrame : F64 := nextFrame
    let __do_lift ← getFrameDelay nextFrame
    let nextFrame : F64 := nextFrame + __do_lift
    pure (ForInStep.yield (angle, previousFrame, nextFrame, fuel))
  else pure (ForInStep.done (angle, previousFrame, nextFrame, fuel))

theorem s2_spinBody_step (endT : F64) (dir : F32) (action : OsuModel.Replay.Action) (a : F32) (p n : F64) (k : Nat)
    (hlt : n < endT) :
    s2_spinBodyS endT dir action () (a, p, n, k + 1) =
      (do let r ← s2_spinStepS a p n dir action; pure (ForInStep.yield (r.1, n, r.2, k))) := by
  simp only [s2_spinBodyS, s2_spinStepS, hlt, decide_true, Bool.true_and, gt_iff_lt, Nat.zero_lt_succ,
    if_true, Nat.add_sub_cancel, bind_assoc, pure_bind]

theorem s2_spinLoop_eq (endT : F64) (dir : F32) (action : OsuModel.Replay.Action) :
    ∀ k a p n, (forIn Lean.Loop.mk (a, p, n, k) (s2_spinBodyS endT dir action) : M _) =
      (fun r : Nat × F32 × F64 × F64 => (r.2.1, r.2.2.1, r.2.2.2, r.1)) <$> s2_spinFramesS endT dir action k a p n := by
  intro k
  induction k with
  | zero =>
    intro a p n
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [s2_spinBodyS, s2_spinFramesS]
  | succ k ih =>
    intro a p n
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    by_cases hlt : n < endT
    · rw [s2_spinBody_step endT dir action a p n k hlt]
      simp only [bind_assoc, pure_bind, s2_spinFramesS, hlt, if_true, map_bind]
      congr 1; funext r
      exact ih r.1 n r.2
    · simp [s2_spinBodyS, s2_spinFramesS, hlt]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_spin_frames_loopB (mods : Slice sim.mods.RateMod) (endT : F64) (dir : F32) (action : replay.frames.Action)
    (h64 : System.Platform.numBits = 64) :
    ∀ k (fuel : U32) (g : sim.autogen.G) (a : F32) (p n : F64), fuel.val = k → g.heap.val.length + k < Usize.max →
      g.frames.val.length + k < 2^62 →
      ∃ r g', sim.autogen.spinner_frames_loop mods g endT dir action fuel a p n = ok (r, g') ∧
        s2_GR (fun x : U32 × F32 × F64 × F64 => (x.1.val, x.2.1, x.2.2.1, x.2.2.2)) g' r
          (s2_spinFramesS endT dir (s2_actS action) k a p n (abs mods) (abs g)) ∧
        (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g.heap.val.length ≤ g'.heap.val.length ∧ g'.heap.val.length ≤ g.heap.val.length + k ∧ g'.frames.val.length ≤ g.frames.val.length + k ∧
          (s2_gInv g → s2_gInv g')) := by
  intro k
  induction k with
  | zero =>
    intro fuel g a p n hf hh hfl
    have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hf])
    subst hf0
    refine ⟨.Ok (0#u32, a, p, n), g, ?_, rfl, fun _ _ => ⟨rfl, by omega, by omega, by omega, id⟩⟩
    unfold sim.autogen.spinner_frames_loop
    rw [loop_unfold]
    by_cases hlt : n < endT <;> simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt]
  | succ k ih =>
    intro fuel g a p n hf hh hfl
    by_cases hlt : n < endT
    · have hpos : fuel > 0#u32 := by scalar_tac
      obtain ⟨f1, hf1, hf1v⟩ : ∃ f1 : U32, fuel - 1#u32 = ok f1 ∧ f1.val = k := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U32.sub_spec (x := fuel) (y := 1#u32) (by scalar_tac))
        exact ⟨z, hz, by simp at hzv; omega⟩
      obtain ⟨r, g1, hr, er, eh⟩ := s2_spinner_frame_step mods g a p n dir action h64 (by omega) (by omega)
      cases r with
      | Err e =>
        refine ⟨.Err e, g1, ?_, ?_, fun _ h => by cases h⟩
        · unfold sim.autogen.spinner_frames_loop
          rw [loop_unfold]
          simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · obtain ⟨m, hm⟩ := er
          refine ⟨m, ?_⟩
          simp only [s2_spinFramesS, hlt, if_true, s2_am_bind, hm]
          rfl
      | Ok v =>
        obtain ⟨a2, n2⟩ := v
        obtain ⟨hg1z, hg1a, hg1b, hg1c⟩ := eh _ rfl
        obtain ⟨r', g', hr', er', eb⟩ := ih f1 g1 a2 n n2 hf1v (by omega) (by omega)
        refine ⟨r', g', ?_, ?_, fun v hv => by obtain ⟨ez, e0, e1, e2, e3⟩ := eb v hv; exact ⟨by rw [ez, hg1z], by omega, by omega, by omega, fun hI => e3 (hg1c hI)⟩⟩
        · unfold sim.autogen.spinner_frames_loop
          rw [loop_unfold]
          have hb : sim.autogen.spinner_frames_loop.body mods endT dir action g fuel a p n =
              ok (.cont (g1, f1, a2, n, n2)) := by
            simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
              core.result.Result.Insts.CoreOpsTry.branch]
          dsimp only; rw [hb]; simp only [bind_ok]
          unfold sim.autogen.spinner_frames_loop at hr'
          exact hr'
        · simp only [s2_GR] at er
          simp only [s2_spinFramesS, hlt, if_true, s2_am_bind, er, Except.bind]
          exact er'
    · refine ⟨.Ok (fuel, a, p, n), g, ?_, ?_, fun _ _ => ⟨rfl, by omega, by omega, by omega, id⟩⟩
      · unfold sim.autogen.spinner_frames_loop
        rw [loop_unfold]
        simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt]
      · simp only [s2_GR, s2_spinFramesS, hlt, if_false, hf]; rfl

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

/-- the spinner branch of `addClickFrames` up to the shared tail (returns `endPosition`) -/
def s2_spinClickS (start endT : F64) (startPosition : OsuTK.Vector2) (spinnerDirection : F32)
    (action : OsuModel.Replay.Action) : M OsuTK.Vector2 := do
  let difference := startPosition - spinnerCentre
  let radius := difference.length
  let angle := if (radius == 0) = true then 0 else difference.y.atan2 difference.x
  let __do_lift ← getFrameDelay start
  let __s ← forIn Lean.Loop.mk (angle, start, start + __do_lift, 10000000) (s2_spinBodyS endT spinnerDirection action)
  if (__s.2.2.2 == 0 && decide (__s.2.2.1 < endT)) = true then outOfFuel "nextFrame < endT" else pure ()
  let __do_lift ← applyModsToTimeDelta __s.2.1 endT
  let t := __do_lift * spinnerDirection.toF64
  let angle := __s.1 + t.toF32 * radsPerMillisecond
  let endPosition := spinnerCentre + circlePosition angle.toF64 spinRadius.toF64
  let __do_lift ← newList [action]
  addFrame { time := endT, pos := endPosition, actions := __do_lift }
  pure endPosition

theorem s2_spinner_click_frames (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (h : sim.playable.HObj) (sp : net.osutk.Vector2) (dir : F32) (action : replay.frames.Action)
    (hh : g.heap.val.length + 10000001 < Usize.max) (hfl : g.frames.val.length + 10000001 < 2^62) :
    ∃ r g', sim.autogen.spinner_click_frames mods g h sp dir action = ok (r, g') ∧
      s2_GR v2S g' r (s2_spinClickS h.start h.end_time (v2S sp) dir (s2_actS action) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g.heap.val.length ≤ g'.heap.val.length ∧ g'.heap.val.length ≤ g.heap.val.length + 10000001 ∧
        g'.frames.val.length ≤ g.frames.val.length + 10000001 ∧ 0 < g'.frames.val.length ∧ (s2_gInv g → s2_gInv g')) := by
  obtain ⟨cen, hcen, ecen⟩ := sim.autogen.spinner_centre_refines
  obtain ⟨h0, -, -⟩ := s2_ag_f32
  have ecen' : v2S cen = spinnerCentre := ecen.symm
  let angle0 : F32 := if (((v2S sp).sub spinnerCentre).length == 0) = true then 0
    else F32.atan2 ((v2S sp).sub spinnerCentre).y ((v2S sp).sub spinnerCentre).x
  have hpre : ∀ (K : net.osutk.Vector2 → F32 → Result ((core.result.Result net.osutk.Vector2 sim.err.SimErr) × sim.autogen.G)),
      (do let centre ← sim.autogen.spinner_centre
          let difference ← net.osutk.v2_sub sp centre
          let radius ← net.osutk.v2_length difference
          let f ← sim.autogen.F32_0
          let b ← float.F32.eq radius f
          let angle ← if b then ok f else float.F32.atan2 difference.y difference.x
          K centre angle) = K cen angle0 := by
    intro K
    simp only [hcen, bind_ok, net.osutk.v2_sub_refines, net.osutk.v2_length_refines, h0, float.F32.eq, s2_v2SI, ecen',
      float.F32.atan2, angle0]
    split <;> simp_all
  have hspec0 : ∀ C S, s2_spinClickS h.start h.end_time (v2S sp) dir (s2_actS action) C S =
      (do let d ← getFrameDelay h.start
          let s ← (fun r : Nat × F32 × F64 × F64 => (r.2.1, r.2.2.1, r.2.2.2, r.1)) <$>
            s2_spinFramesS h.end_time dir (s2_actS action) 10000000 angle0 h.start (h.start + d)
          if (s.2.2.2 == 0 && decide (s.2.2.1 < h.end_time)) = true then outOfFuel "nextFrame < endT" else pure ()
          let x ← applyModsToTimeDelta s.2.1 h.end_time
          let endPosition := spinnerCentre + circlePosition (s.1 + (x * dir.toF64).toF32 * radsPerMillisecond).toF64 spinRadius.toF64
          let l ← newList [s2_actS action]
          addFrame { time := h.end_time, pos := endPosition, actions := l }
          pure endPosition : M OsuTK.Vector2) C S := by
    intro C S
    unfold s2_spinClickS
    simp only [s2_spinLoop_eq]
    rfl
  obtain ⟨x, hx, ex⟩ := s2_fd_eval mods h.start (abs g)
  unfold sim.autogen.spinner_click_frames
  rw [hpre]
  simp only [hx, bind_ok]
  cases x with
  | Err e =>
    refine ⟨.Err e, g, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun _ h => by cases h⟩
    obtain ⟨m, hm⟩ := ex
    exact ⟨m, by rw [hspec0]; simp only [s2_am_bind, hm]; rfl⟩
  | Ok d =>
    simp only at ex
    obtain ⟨r1, g1, hr1, er1, eb1⟩ := s2_spin_frames_loopB mods h.end_time dir action h64 10000000 10000000#u32 g
      angle0 h.start (h.start + d) rfl (by omega) (by omega)
    have hr1' : sim.autogen.spinner_frames mods g angle0 h.start (h.start + d) h.end_time dir action = ok (r1, g1) := hr1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, float.F64.add, hr1']
    cases r1 with
    | Err e =>
      refine ⟨.Err e, g1, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_,
        fun _ h => by cases h⟩
      obtain ⟨m, hm⟩ := er1
      exact ⟨m, by rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map, Except.bind, hm, Except.map]⟩
    | Ok v =>
      obtain ⟨fuel, a1, pf, nf⟩ := v
      simp only [s2_GR] at er1
      have hsp1 : ∀ (K : F32 × F64 × F64 × Nat → M OsuTK.Vector2),
          ((Except.ok (d, abs g)).bind fun p =>
            (Except.map (fun p => ((p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.1.1), p.2))
              (s2_spinFramesS h.end_time dir (s2_actS action) 10000000 angle0 h.start (h.start + p.1) (abs mods) p.2)).bind
            fun p => K p.1 (abs mods) p.2) = K (a1, pf, nf, fuel.val) (abs mods) (abs g1) := by
        intro K; simp only [Except.bind, er1, Except.map]
      by_cases hz : fuel = 0#u32 ∧ nf < h.end_time
      · refine ⟨.Err (.AutogenFuel 1#u8), g1, ?_, ?_, fun _ h => by cases h⟩
        · simp [hz.1, hz.2, float.F64.lt]
        · rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map]
          simp only [Except.bind, er1, Except.map]
          have hz1 : fuel.val = 0 := by simp [hz.1]
          simp [hz1, hz.2, outOfFuel, s2_GR, Except.bind]
      · obtain ⟨y, hy, ey⟩ := s2_amd_eval mods pf h.end_time (abs g1)
        have hnz : ¬ ((fuel.val == 0 && decide (nf < h.end_time)) = true) := by
          intro hc; apply hz; simp at hc; exact ⟨UScalar.eq_of_val_eq (by simpa using hc.1), hc.2⟩
        obtain ⟨ebw, ebz, eba, ebb, ebc⟩ := eb1 _ rfl
        cases y with
        | Err e2 =>
          refine ⟨.Err e2, g1, ?_, ?_, fun _ h => by cases h⟩
          · by_cases hf0 : fuel = 0#u32
            · have : ¬ nf < h.end_time := fun hl => hz ⟨hf0, hl⟩
              simp [hf0, this, float.F64.lt, hy, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            · simp [hf0, hy, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          · obtain ⟨m, hm⟩ := ey
            rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map]
            simp only [Except.bind, er1, Except.map]
            simp only [hnz, Bool.false_eq_true, if_false]
            simp [hm, s2_GR, Except.bind]
        | Ok tv =>
          simp only at ey
          let ang : F32 := a1 + (tv * dir.toF64).toF32 * radsPerMillisecond
          obtain ⟨cp, hcp, ecp⟩ := sim.autogen.circle_position_refines ang.toF64 spinRadius.toF64
          obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
          obtain ⟨r3, g2, hr3, hr3v, er3, hg2h, hg2f, hg2bi⟩ := s2_ag_new_list (abs mods) g1 al (by omega)
          let f : sim.autogen.AFrame := ⟨h.end_time, v2I (OsuTK.Vector2.add (v2S cen) (v2S cp)), r3, false⟩
          obtain ⟨g3, hg3, eg3, hg3h, hg3f, hg3bi⟩ := s2_add_frame h64 mods g2 f (by rw [hg2f]; omega)
          refine ⟨.Ok (v2I (OsuTK.Vector2.add (v2S cen) (v2S cp))), g3, ?_, ?_, fun _ _ => ⟨by rw [hg3bi, hg2bi, ebw], by rw [hg3h, hg2h]; omega, by rw [hg3h, hg2h]; omega, by rw [hg3f, hg2f]; omega, by rw [hg3f]; omega, fun hI => s2_inv_add_frame g2 g3 f _ (s2_inv_new_list g1 g2 al r3 (ebc hI) hall (by omega) hr3).1 (by show r3.val < _; omega) eg3 hg3h⟩⟩
          · have hcp' := hcp
            simp only [ang] at hcp'
            by_cases hf0 : fuel = 0#u32
            · have : ¬ nf < h.end_time := fun hl => hz ⟨hf0, hl⟩
              simp [hf0, this, float.F64.lt, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F32.to_f64,
                float.F64.mul, float.F64.to_f32, s2_ag_rads, float.F32.mul, float.F32.add, s2_ag_spinr, hcp',
                net.osutk.v2_add_refines, hal, hr3, f] at hg3 ⊢
              simp only [hg3, bind_ok]
            · simp [hf0, hy, core.result.Result.Insts.CoreOpsTry.branch, float.F32.to_f64,
                float.F64.mul, float.F64.to_f32, s2_ag_rads, float.F32.mul, float.F32.add, s2_ag_spinr, hcp',
                net.osutk.v2_add_refines, hal, hr3, f] at hg3 ⊢
              simp only [hg3, bind_ok]
          · have hf : (abs f : OsuModel.Sim.AFrame) = { time := h.end_time, pos := spinnerCentre + circlePosition (a1 + (tv * dir.toF64).toF32 * radsPerMillisecond).toF64 spinRadius.toF64, actions := r3.val } := by
              show s2_aframeS f = _
              simp only [s2_aframeS, f, v2S_I, ecen']
              rw [ecp]; rfl
            rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map]
            simp only [Except.bind, er1, Except.map]
            simp only [hnz, Bool.false_eq_true, if_false]
            simp only [s2_am_bind, ey, Except.bind, eal, er3, s2_am_pure]
            rw [← hf, eg3]
            simp only [s2_GR, Except.map, v2S_I, ecen']
            rw [ecp]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

/-- one iteration of the slider loop of `addClickFrames` -/
def s2_sliderStepS (stacked : OsuModel.Sim.Vec2) (start : F64) (sd : OsuModel.Sim.SliderData)
    (action : OsuModel.Replay.Action) (j : F64) : M F64 := do
  let cp ← liftS (sd.curvePositionAt (j / sd.duration))
  let pos := ofVec stacked + ofVec cp
  let l ← newList [action]
  addFrame { time := start + j, pos := pos, actions := l }
  let d ← getFrameDelay (start + j)
  pure (j + d)

/-- the slider `while` loop as a fuel recursion over `s2_sliderStepS`; returns `(fuel left, j)` -/
def s2_sliderFramesS (stacked : OsuModel.Sim.Vec2) (start : F64) (sd : OsuModel.Sim.SliderData)
    (action : OsuModel.Replay.Action) : Nat → F64 → M (Nat × F64)
  | 0, j => pure (0, j)
  | k + 1, j =>
    if j < sd.duration then do
      let j2 ← s2_sliderStepS stacked start sd action j
      s2_sliderFramesS stacked start sd action k j2
    else pure (k + 1, j)

/-- the slider `while` body of `addClickFrames` (elaborated form, restated) -/
def s2_sliderBodyS (stacked : OsuModel.Sim.Vec2) (start : F64) (sd : OsuModel.Sim.SliderData)
    (action : OsuModel.Replay.Action) : Unit → F64 × Nat → M (ForInStep (F64 × Nat)) := fun _ __s =>
  let j := __s.1
  let fuel := __s.2
  if (decide (j < sd.duration) && decide (fuel > 0)) = true then
    let fuel := fuel - 1
    do
    let __do_lift ← liftS (sd.curvePositionAt (j / sd.duration))
    let pos : OsuTK.Vector2 := ofVec stacked + ofVec __do_lift
    let __do_lift ← newList [action]
    addFrame { time := start + j, pos := pos, actions := __do_lift }
    let __do_lift ← getFrameDelay (start + j)
    let j : F64 := j + __do_lift
    pure (ForInStep.yield (j, fuel))
  else pure (ForInStep.done (j, fuel))

theorem s2_sliderLoop_eq (stacked : OsuModel.Sim.Vec2) (start : F64) (sd : OsuModel.Sim.SliderData)
    (action : OsuModel.Replay.Action) :
    ∀ k j, (forIn Lean.Loop.mk (j, k) (s2_sliderBodyS stacked start sd action) : M _) =
      (fun r : Nat × F64 => (r.2, r.1)) <$> s2_sliderFramesS stacked start sd action k j := by
  intro k
  induction k with
  | zero =>
    intro j
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [s2_sliderBodyS, s2_sliderFramesS]
  | succ k ih =>
    intro j
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    by_cases hlt : j < sd.duration
    · have hb : s2_sliderBodyS stacked start sd action () (j, k + 1) =
          (do let r ← s2_sliderStepS stacked start sd action j; pure (ForInStep.yield (r, k))) := by
        simp only [s2_sliderBodyS, s2_sliderStepS, hlt, decide_true, Bool.true_and, gt_iff_lt, Nat.zero_lt_succ,
          ite_true, Nat.add_sub_cancel, bind_assoc, pure_bind, decide_eq_true_eq]
      rw [hb]
      simp only [bind_assoc, pure_bind, s2_sliderFramesS, hlt, ite_true, map_bind]
      congr 1; funext r
      exact ih r
    · simp [s2_sliderBodyS, s2_sliderFramesS, hlt]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

theorem s2_slider_frame_step (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (h : sim.playable.HObj) (sd : sim.playable.SliderData) (j : F64) (action : replay.frames.Action)
    (hh : g.heap.val.length < Usize.max) (hfl : g.frames.val.length < 2^62)
    (hc : sd.cum_len.val.length < 2^62) (hp : sd.path.val.length < 2^62) :
    ∃ r g', sim.autogen.slider_frame_step mods g h sd j action = ok (r, g') ∧
      s2_GR id g' r (s2_sliderStepS (abs h.stacked) h.start (abs sd) (s2_actS action) j (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g'.heap.val.length = g.heap.val.length + 1 ∧ g'.frames.val.length = g.frames.val.length + 1 ∧
        (s2_gInv g → s2_gInv g')) := by
  obtain ⟨x, hx, ex⟩ := sim.geometry.curve_position_at_refines h64 sd (j / sd.duration) hc hp
  have hdur : (abs sd : OsuModel.Sim.SliderData).duration = sd.duration := rfl
  unfold sim.autogen.slider_frame_step
  simp only [float.F64.div, bind_ok, hx]
  cases x with
  | Err e =>
    refine ⟨.Err e, g, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun _ h => by cases h⟩
    cases hs : (abs sd : OsuModel.Sim.SliderData).curvePositionAt (abs (j / sd.duration)) with
    | ok b => rw [hs] at ex; simp [s2_rel] at ex
    | error m =>
      refine ⟨m, ?_⟩
      simp only [abs_id] at hs
      simp [s2_sliderStepS, hdur, hs, liftS, Except.bind]
  | Ok cp =>
    cases hs : (abs sd : OsuModel.Sim.SliderData).curvePositionAt (abs (j / sd.duration)) with
    | error m => rw [hs] at ex; simp [s2_rel] at ex
    | ok b =>
    rw [hs] at ex; simp only [s2_rel] at ex
    simp only [abs_id] at hs
    obtain ⟨v, hv, ev⟩ := sim.autogen.of_vec_refines h.stacked
    obtain ⟨v1, hv1, ev1⟩ := sim.autogen.of_vec_refines cp
    obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
    obtain ⟨r1, g1, hr1, hr1v, er1, hg1h, hg1f, hg1bi⟩ := s2_ag_new_list (abs mods) g al hh
    let f : sim.autogen.AFrame := ⟨h.start + j, v2I (OsuTK.Vector2.add (v2S v) (v2S v1)), r1, false⟩
    obtain ⟨g2, hg2, eg2, hg2h, hg2f, hg2bi⟩ := s2_add_frame h64 mods g1 f (by rw [hg1f]; exact hfl)
    obtain ⟨y, hy, ey⟩ := s2_fd_eval mods (h.start + j) (abs g2)
    have hf : (abs f : OsuModel.Sim.AFrame) = { time := h.start + j, pos := ofVec (abs h.stacked) + ofVec b, actions := r1.val } := by
      show s2_aframeS f = _
      simp only [s2_aframeS, f, v2S_I, ev, ← ex, ev1]
      rfl
    have hspec : s2_sliderStepS (abs h.stacked) h.start (abs sd) (s2_actS action) j (abs mods) (abs g) =
        (getFrameDelay (h.start + j) (abs mods) (abs g2)).bind (fun p => .ok (j + p.1, p.2)) := by
      simp only [s2_sliderStepS, hdur, hs, liftS, s2_am_bind, s2_am_pure, Except.bind, eal, er1]
      rw [← hf, eg2]
    cases y with
    | Ok d =>
      simp only at ey
      refine ⟨.Ok (j + d), g2, ?_, ?_, fun _ _ => ⟨by rw [hg2bi, hg1bi], by rw [hg2h, hg1h], by rw [hg2f, hg1f], fun hI => s2_inv_add_frame g1 g2 f _ (s2_inv_new_list g g1 al r1 hI hall (by omega) hr1).1 (by show r1.val < _; omega) eg2 hg2h⟩⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch, hv, hv1, net.osutk.v2_add_refines, hal, hr1,
          float.F64.add, f] at hg2 hy ⊢
        simp [hg2, hy]
      · simp only [s2_GR, hspec, ey, Except.bind]; rfl
    | Err e =>
      refine ⟨.Err e, g2, ?_, ?_, fun _ h => by cases h⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch, hv, hv1, net.osutk.v2_add_refines, hal, hr1,
          float.F64.add, f] at hg2 hy ⊢
        simp [hg2, hy, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := ey
        exact ⟨m, by simp only [hspec, hm, Except.bind]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_slider_frames_loopB (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (h : sim.playable.HObj) (sd : sim.playable.SliderData) (action : replay.frames.Action)
    (hc : sd.cum_len.val.length < 2^62) (hp : sd.path.val.length < 2^62) :
    ∀ k (fuel : U32) (g : sim.autogen.G) (j : F64), fuel.val = k → g.heap.val.length + k < Usize.max →
      g.frames.val.length + k < 2^62 →
      ∃ r g', sim.autogen.slider_frames_loop mods g h sd action fuel j = ok (r, g') ∧
        s2_GR (fun x : U32 × F64 => (x.1.val, x.2)) g' r
          (s2_sliderFramesS (abs h.stacked) h.start (abs sd) (s2_actS action) k j (abs mods) (abs g)) ∧
        (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g.heap.val.length ≤ g'.heap.val.length ∧ g'.heap.val.length ≤ g.heap.val.length + k ∧ g'.frames.val.length ≤ g.frames.val.length + k ∧
          (s2_gInv g → s2_gInv g')) := by
  have hdur : (abs sd : OsuModel.Sim.SliderData).duration = sd.duration := rfl
  intro k
  induction k with
  | zero =>
    intro fuel g j hf hh hfl
    have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hf])
    subst hf0
    refine ⟨.Ok (0#u32, j), g, ?_, rfl, fun _ _ => ⟨rfl, by omega, by omega, by omega, id⟩⟩
    unfold sim.autogen.slider_frames_loop
    rw [loop_unfold]
    by_cases hlt : j < sd.duration <;> simp [sim.autogen.slider_frames_loop.body, float.F64.lt, hlt]
  | succ k ih =>
    intro fuel g j hf hh hfl
    by_cases hlt : j < sd.duration
    · have hpos : fuel > 0#u32 := by scalar_tac
      obtain ⟨f1, hf1, hf1v⟩ : ∃ f1 : U32, fuel - 1#u32 = ok f1 ∧ f1.val = k := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U32.sub_spec (x := fuel) (y := 1#u32) (by scalar_tac))
        exact ⟨z, hz, by simp at hzv; omega⟩
      obtain ⟨r, g1, hr, er, eh⟩ := s2_slider_frame_step h64 mods g h sd j action (by omega) (by omega) hc hp
      cases r with
      | Err e =>
        refine ⟨.Err e, g1, ?_, ?_, fun _ h => by cases h⟩
        · unfold sim.autogen.slider_frames_loop
          rw [loop_unfold]
          simp [sim.autogen.slider_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · obtain ⟨m, hm⟩ := er
          refine ⟨m, ?_⟩
          simp only [s2_sliderFramesS, hdur, hlt, if_true, s2_am_bind, hm]
          rfl
      | Ok j2 =>
        obtain ⟨hg1z, hg1a, hg1b, hg1c⟩ := eh _ rfl
        obtain ⟨r', g', hr', er', eb⟩ := ih f1 g1 j2 hf1v (by omega) (by omega)
        refine ⟨r', g', ?_, ?_, fun v hv => by obtain ⟨ez, e0, e1, e2, e3⟩ := eb v hv; exact ⟨by rw [ez, hg1z], by omega, by omega, by omega, fun hI => e3 (hg1c hI)⟩⟩
        · unfold sim.autogen.slider_frames_loop
          rw [loop_unfold]
          have hb : sim.autogen.slider_frames_loop.body mods h sd action g fuel j = ok (.cont (g1, f1, j2)) := by
            simp [sim.autogen.slider_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
              core.result.Result.Insts.CoreOpsTry.branch]
          dsimp only; rw [hb]; simp only [bind_ok]
          unfold sim.autogen.slider_frames_loop at hr'
          exact hr'
        · simp only [s2_GR] at er
          simp only [s2_sliderFramesS, hdur, hlt, if_true, s2_am_bind, er, Except.bind]
          exact er'
    · refine ⟨.Ok (fuel, j), g, ?_, ?_, fun _ _ => ⟨rfl, by omega, by omega, by omega, id⟩⟩
      · unfold sim.autogen.slider_frames_loop
        rw [loop_unfold]
        simp [sim.autogen.slider_frames_loop.body, float.F64.lt, hlt]
      · simp only [s2_GR, s2_sliderFramesS, hdur, hlt, if_false, hf]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

/-- the slider branch of `addClickFrames` up to the shared tail -/
def s2_sliderClickS (stacked : OsuModel.Sim.Vec2) (start endTime : F64) (slider : Option OsuModel.Sim.SliderData)
    (stackedEnd : OsuTK.Vector2) (action : OsuModel.Replay.Action) : M Unit :=
  match slider with
  | some sd => do
    let j ← getFrameDelay start
    let __s ← forIn Lean.Loop.mk (j, 10000000) (s2_sliderBodyS stacked start sd action)
    if (__s.2 == 0 && decide (__s.1 < sd.duration)) = true then outOfFuel "j < sd.duration" else pure ()
    let l ← newList [action]
    addFrame { time := endTime, pos := stackedEnd, actions := l }
  | none => throw "malformed: slider without slider data"

theorem s2_slider_click_frames (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (o : sim.playable.TopObj) (se : net.osutk.Vector2) (action : replay.frames.Action)
    (hsd : ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62)
    (hh : g.heap.val.length + 10000001 < Usize.max) (hfl : g.frames.val.length + 10000001 < 2^62) :
    ∃ r g', sim.autogen.slider_click_frames mods g o se action = ok (r, g') ∧
      s2_GR id g' r (s2_sliderClickS (abs o.h.stacked) o.h.start o.h.end_time (o.slider.map abs) (v2S se)
        (s2_actS action) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ g.heap.val.length ≤ g'.heap.val.length ∧ g'.heap.val.length ≤ g.heap.val.length + 10000001 ∧
        g'.frames.val.length ≤ g.frames.val.length + 10000001 ∧ 0 < g'.frames.val.length ∧ (s2_gInv g → s2_gInv g')) := by
  unfold sim.autogen.slider_click_frames
  cases hs : o.slider with
  | none =>
    refine ⟨.Err .NoSliderData, g, rfl, ⟨_, rfl⟩, fun _ h => by cases h⟩
  | some sd =>
    obtain ⟨hc, hp⟩ := hsd sd hs
    have hdur : (abs sd : OsuModel.Sim.SliderData).duration = sd.duration := rfl
    simp only [Option.map_some]
    obtain ⟨x, hx, ex⟩ := s2_fd_eval mods o.h.start (abs g)
    simp only [hx, bind_ok]
    have hspec0 : ∀ C S, s2_sliderClickS (abs o.h.stacked) o.h.start o.h.end_time (some (abs sd)) (v2S se)
        (s2_actS action) C S =
        (do let d ← getFrameDelay o.h.start
            let s ← (fun r : Nat × F64 => (r.2, r.1)) <$>
              s2_sliderFramesS (abs o.h.stacked) o.h.start (abs sd) (s2_actS action) 10000000 d
            if (s.2 == 0 && decide (s.1 < sd.duration)) = true then outOfFuel "j < sd.duration" else pure ()
            let l ← newList [s2_actS action]
            addFrame { time := o.h.end_time, pos := v2S se, actions := l } : M Unit) C S := by
      intro C S
      unfold s2_sliderClickS
      simp only [s2_sliderLoop_eq]
      rfl
    cases x with
    | Err e =>
      refine ⟨.Err e, g, by simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun _ h => by cases h⟩
      obtain ⟨m, hm⟩ := ex
      exact ⟨m, by rw [hspec0]; simp only [s2_am_bind, hm]; rfl⟩
    | Ok d =>
      simp only at ex
      obtain ⟨r1, g1, hr1, er1, eb1⟩ := s2_slider_frames_loopB h64 mods o.h sd action hc hp 10000000 10000000#u32 g d
        rfl (by omega) (by omega)
      have hr1' : sim.autogen.slider_frames mods g o.h sd d action = ok (r1, g1) := hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hr1']
      cases r1 with
      | Err e =>
        refine ⟨.Err e, g1, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_,
          fun _ h => by cases h⟩
        obtain ⟨m, hm⟩ := er1
        exact ⟨m, by rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map, Except.bind, hm, Except.map]⟩
      | Ok v =>
        obtain ⟨fuel, j⟩ := v
        simp only [s2_GR] at er1
        obtain ⟨ebw, ebz, eba, ebb, ebc⟩ := eb1 _ rfl
        by_cases hz : fuel = 0#u32 ∧ j < sd.duration
        · refine ⟨.Err (.AutogenFuel 2#u8), g1, ?_, ?_, fun _ h => by cases h⟩
          · simp [hz.1, hz.2, float.F64.lt]
          · rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map]
            simp only [Except.bind, er1, Except.map]
            have hz1 : fuel.val = 0 := by simp [hz.1]
            simp [hz1, hz.2, outOfFuel, s2_GR, Except.bind]
        · have hnz : ¬ ((fuel.val == 0 && decide (j < sd.duration)) = true) := by
            intro hc; apply hz; simp at hc; exact ⟨UScalar.eq_of_val_eq (by simpa using hc.1), hc.2⟩
          obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
          obtain ⟨r3, g2, hr3, hr3v, er3, hg2h, hg2f, hg2bi⟩ := s2_ag_new_list (abs mods) g1 al (by omega)
          let f : sim.autogen.AFrame := ⟨o.h.end_time, se, r3, false⟩
          obtain ⟨g3, hg3, eg3, hg3h, hg3f, hg3bi⟩ := s2_add_frame h64 mods g2 f (by rw [hg2f]; omega)
          refine ⟨.Ok (), g3, ?_, ?_, fun _ _ => ⟨by rw [hg3bi, hg2bi, ebw], by rw [hg3h, hg2h]; omega, by rw [hg3h, hg2h]; omega, by rw [hg3f, hg2f]; omega, by rw [hg3f]; omega, fun hI => s2_inv_add_frame g2 g3 f _ (s2_inv_new_list g1 g2 al r3 (ebc hI) hall (by omega) hr3).1 (by show r3.val < _; omega) eg3 hg3h⟩⟩
          · by_cases hf0 : fuel = 0#u32
            · have : ¬ j < sd.duration := fun hl => hz ⟨hf0, hl⟩
              simp [hf0, this, float.F64.lt, hal, hr3, f] at hg3 ⊢
              simp only [hg3, bind_ok]
            · simp [hf0, hal, hr3, f] at hg3 ⊢
              simp only [hg3, bind_ok]
          · have hf : (abs f : OsuModel.Sim.AFrame) = { time := o.h.end_time, pos := v2S se, actions := r3.val } := rfl
            rw [hspec0]; simp only [s2_am_bind, ex, s2_am_map]
            simp only [Except.bind, er1, Except.map]
            simp only [hnz, Bool.false_eq_true, if_false]
            simp only [s2_am_bind, s2_am_pure, Except.bind, eal, er3]
            rw [← hf, eg3]
            rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen OsuModel.Replay

/-- pure model of one iteration of the action-list rewrite loop of `addClickFrames` -/
def s2_fxStep (fs : Array OsuModel.Sim.AFrame) (prevRef : Nat) (action : Action) (H : Array (List Action)) (j : Nat) :
    Array (List Action) :=
  if (decide (j < fs.size - 1) || H[fs[j]!.actions]?.getD [] == H[prevRef]?.getD []) = true then
    H.setIfInBounds fs[j]!.actions [action]
  else H

theorem s2_fxStep_size (fs : Array OsuModel.Sim.AFrame) (prevRef : Nat) (action : Action) (H : Array (List Action))
    (j : Nat) : (s2_fxStep fs prevRef action H j).size = H.size := by
  unfold s2_fxStep; split <;> simp

theorem s2_fxFold_size (fs : Array OsuModel.Sim.AFrame) (prevRef : Nat) (action : Action) :
    ∀ (L : List Nat) (H : Array (List Action)), (L.foldl (s2_fxStep fs prevRef action) H).size = H.size
  | [], H => rfl
  | j :: L, H => by simp only [List.foldl_cons]; rw [s2_fxFold_size fs prevRef action L, s2_fxStep_size]

theorem s2_fxLoopS (fs : Array OsuModel.Sim.AFrame) (prevRef : Nat) (action : Action) :
    ∀ (L : List Nat) (B : (j : Nat) → j ∈ L → PUnit → M (ForInStep PUnit)),
      (∀ j h C (S : G), prevRef < S.heap.size → (∀ x ∈ fs, x.actions < S.heap.size) →
        B j h PUnit.unit C S = .ok (.yield PUnit.unit, { S with heap := s2_fxStep fs prevRef action S.heap j })) →
      ∀ C (S : G), prevRef < S.heap.size → (∀ x ∈ fs, x.actions < S.heap.size) →
        forIn' L PUnit.unit B C S = .ok (PUnit.unit, { S with heap := L.foldl (s2_fxStep fs prevRef action) S.heap }) := by
  intro L
  induction L with
  | nil => intro B hB C S h1 h2; rfl
  | cons a L ih =>
    intro B hB C S h1 h2
    rw [List.forIn'_cons]
    simp only [s2_am_bind, hB a _ C S h1 h2, Except.bind]
    have hs := s2_fxStep_size fs prevRef action S.heap a
    rw [ih _ (fun j h C S h1 h2 => hB j _ C S h1 h2) C _ (by simp only; omega) (by simp only; intro x hx; have := h2 x hx; omega)]
    rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

/-- the frame-list surgery prefix of `addClickFrames` (elaborated form, continuation `K` = the join point) -/
def s2_cfxS (g : G) (index : Int) (startFrame endFrame : AFrame) (action : Action) (K : Unit → Action → M Unit) :
    M Unit :=
  if 0 ≤ index then
    match g.frames[index.toNat]? with
    | some prevFrame =>
      let prevRef := prevFrame.actions
      do
      let __do_lift_2 ← listOf prevRef
      if (!__do_lift_2.isEmpty) = true then do
          let __do_lift_3 ← listOf prevRef
          let __do_jp : Unit → Action → M Unit := fun __r action =>
            let endIndex := findInsertionIndex g.frames endFrame.time
            let fs := g.frames
            let __do_jp := fun (__r : Unit) (fs : Array AFrame) => do
              modify fun g => { frames := fs, buttonIndex := g.buttonIndex, heap := g.heap }
              forIn' [index.toNat + 1:fs.size] PUnit.unit fun j h __s =>
                  let f := fs[j]'h.upper
                  do
                  let __do_lift ← listOf f.actions
                  let __do_lift_4 ← listOf prevRef
                  if (decide (j < fs.size - 1) || __do_lift == __do_lift_4) = true then do
                      setList f.actions [action]
                      pure (ForInStep.yield PUnit.unit)
                    else pure (ForInStep.yield PUnit.unit)
              K () action
            if index < ↑fs.size - 1 then
              let cnt := endIndex - (index.toNat + 1)
              let fs := fs.extract 0 (index.toNat + 1) ++ fs.extract (index.toNat + 1 + cnt)
              __do_jp () fs
            else __do_jp () fs
          if __do_lift_3.contains action = true then
              let action := if (action == Action.left) = true then Action.right else Action.left
              do
              let __r ← setList startFrame.actions [action]
              __do_jp __r action
            else __do_jp () action
        else K () action
    | _ => do
      let __r ← throw "internal: insertion index out of range"
      K __r action
  else K () action

/-- the join point of `addClickFrames` after the frame-list surgery (elaborated form) -/
def s2_acfJP (o : TopObj) (startPosition : OsuTK.Vector2) (spinnerDirection : F32) (stackedEnd : OsuTK.Vector2)
    (startFrame endFrame : AFrame) : Unit → Action → M Unit := fun __r action =>
  let h := o.h
  do
  addFrame startFrame
  let __do_jp : Unit → AFrame → M Unit := fun __r endFrame => do
    let __do_lift ← lastFrame
    if __do_lift.time ≤ endFrame.time then addFrame endFrame else pure ()
  match h.kind with
    | Kind.spinner =>
      let difference := startPosition - spinnerCentre
      let radius := difference.length
      let angle := if (radius == 0) = true then 0 else difference.y.atan2 difference.x
      let previousFrame := h.start
      let endT := h.endTime
      do
      let __do_lift ← getFrameDelay h.start
      let nextFrame : F64 := h.start + __do_lift
      let fuel : Nat := 10000000
      let __s ← forIn Lean.Loop.mk (angle, previousFrame, nextFrame, fuel) (s2_spinBodyS endT spinnerDirection action)
      let angle : F32 := __s.1
      let __s : F64 × F64 × Nat := __s.2
      let previousFrame : F64 := __s.1
      let __s : F64 × Nat := __s.2
      let nextFrame : F64 := __s.1
      let fuel : Nat := __s.2
      let __do_jp : Unit → M Unit := fun __r => do
        let __do_lift ← applyModsToTimeDelta previousFrame endT
        let t : F64 := __do_lift * spinnerDirection.toF64
        let angle : F32 := angle + t.toF32 * radsPerMillisecond
        let endPosition : OsuTK.Vector2 := spinnerCentre + circlePosition angle.toF64 spinRadius.toF64
        let __do_lift ← newList [action]
        addFrame { time := endT, pos := endPosition, actions := __do_lift }
        let endFrame : AFrame :=
          { time := endFrame.time, pos := endPosition, actions := endFrame.actions, keyUp := endFrame.keyUp }
        __do_jp () endFrame
      if (fuel == 0 && decide (nextFrame < endT)) = true then do
          let __r ← outOfFuel "nextFrame < endT"
          __do_jp __r
        else __do_jp ()
    | Kind.slider =>
      match o.slider with
      | some sd => do
        let j ← getFrameDelay h.start
        let fuel : Nat := 10000000
        let __s ← forIn Lean.Loop.mk (j, fuel) (s2_sliderBodyS h.stacked h.start sd action)
        let j : F64 := __s.1
        let fuel : Nat := __s.2
        let __do_jp : Unit → M Unit := fun __r => do
          let __do_lift ← newList [action]
          let __r ← addFrame { time := h.endTime, pos := stackedEnd, actions := __do_lift }
          __do_jp __r endFrame
        if (fuel == 0 && decide (j < sd.duration)) = true then do
            let __r ← outOfFuel "j < sd.duration"
            __do_jp __r
          else __do_jp ()
      | x => do
        let __r ← throw "malformed: slider without slider data"
        __do_jp __r endFrame
    | x => __do_jp () endFrame

/-- `addClickFrames`, restated over `s2_cfxS` / `s2_acfJP` -/
def s2_acfS (o : TopObj) (startPosition : OsuTK.Vector2) (spinnerDirection : F32) (stackedEnd : OsuTK.Vector2) :
    M Unit :=
  let h := o.h
  do
  let __do_lift ← get
  let action : Action := if (__do_lift.buttonIndex % 2 == 0) = true then Action.left else Action.right
  let __do_lift ← newList [action]
  let startFrame : AFrame := { time := h.start, pos := startPosition, actions := __do_lift }
  let hEndTime : F64 := h.endTime + keyUpDelay
  let endDelay : F64 := if (h.kind == Kind.spinner) = true then 1 else 0
  let __do_lift_1 ← newList []
  let endFrame : AFrame := { time := hEndTime + endDelay, pos := stackedEnd, actions := __do_lift_1, keyUp := true }
  let g ← get
  let index : Int := ↑(findInsertionIndex g.frames startFrame.time) - 1
  s2_cfxS g index startFrame endFrame action (s2_acfJP o startPosition spinnerDirection stackedEnd startFrame endFrame)

theorem s2_acf_eq (o : TopObj) (sp : OsuTK.Vector2) (dir : F32) (se : OsuTK.Vector2) :
    addClickFrames o sp dir se = s2_acfS o sp dir se := rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_cut_step {α} (l : List α) (i c k : Nat) (hk : k < l.length) :
    l.take (min (k + 1) i) ++ (l.take (k + 1)).drop (i + c) =
      if k < i then (l.take (min k i) ++ (l.take k).drop (i + c)) ++ [l[k]]
      else if i + c ≤ k then (l.take (min k i) ++ (l.take k).drop (i + c)) ++ [l[k]]
      else l.take (min k i) ++ (l.take k).drop (i + c) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  split
  · rw [show min (k + 1) i = k + 1 by omega, show min k i = k by omega, List.take_add_one, List.getElem?_eq_getElem hk]
    simp [List.drop_eq_nil_of_le, show k + 1 ≤ i + c by omega, show k ≤ i + c by omega]
  · rw [show min (k + 1) i = i by omega, show min k i = i by omega]
    split
    · rw [List.drop_append_of_le_length (by simp; omega)]; simp
    · simp [List.drop_eq_nil_of_le, show k + 1 ≤ i + c by omega, show k ≤ i + c by omega]

theorem s2_fix_loop0 (fs : alloc.vec.Vec sim.autogen.AFrame) (index size cnt : Usize)
    (hs : size.val = fs.val.length) (hi : index.val < fs.val.length) (hc : index.val + 1 + cnt.val ≤ fs.val.length) :
    ∀ (n : Nat) (acc : alloc.vec.Vec sim.autogen.AFrame) (k : Usize), fs.val.length - k.val = n → k.val ≤ fs.val.length →
      acc.val = fs.val.take (min k.val (index.val + 1)) ++ (fs.val.take k.val).drop (index.val + 1 + cnt.val) →
      ∃ r, sim.autogen.click_frames_fixup_loop0 fs index size cnt acc k = ok r ∧
        r.val = fs.val.take (index.val + 1) ++ fs.val.drop (index.val + 1 + cnt.val) := by
  have hmax := fs.property
  intro n
  induction n with
  | zero =>
    intro acc k hn hk hacc
    refine ⟨acc, ?_, ?_⟩
    · unfold sim.autogen.click_frames_fixup_loop0; rw [loop_unfold]
      simp [sim.autogen.click_frames_fixup_loop0.body, show ¬ k < size by scalar_tac]
    · rw [hacc, show k.val = fs.val.length by omega, List.take_length, show min fs.val.length (index.val + 1) = index.val + 1 by omega]
  | succ n ih =>
    intro acc k hn hk hacc
    have hkl : k.val < fs.val.length := by omega
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    obtain ⟨i, hi1, hiv⟩ := usize_add_one index (by omega)
    have hacc' := s2_cut_step fs.val (index.val + 1) cnt.val k.val hkl
    by_cases h1 : k.val < index.val + 1
    · have hp : acc.val.length < Usize.max := by
        have : acc.val.length ≤ k.val := by rw [hacc]; simp; omega
        omega
      obtain ⟨r, hr, hrv⟩ := ih (vpush acc (fs.val[k.val]'hkl) hp) k1 (by omega) (by omega)
        (by rw [hk1v, hacc', if_pos h1, vpush_val, hacc])
      refine ⟨r, ?_, hrv⟩
      unfold sim.autogen.click_frames_fixup_loop0; rw [loop_unfold]
      have hb : sim.autogen.click_frames_fixup_loop0.body fs index size cnt acc k =
          ok (.cont (vpush acc (fs.val[k.val]'hkl) hp, k1)) := by
        simp [sim.autogen.click_frames_fixup_loop0.body, show k < size by scalar_tac, hi1,
          show k < i by scalar_tac, hiv, h1, vec_index_eq' fs k hkl, vec_push_ok _ _ hp, hk1]
      dsimp only; rw [hb]; simp only [bind_ok]
      unfold sim.autogen.click_frames_fixup_loop0 at hr; exact hr
    · obtain ⟨i2, hi2, hi2v⟩ : ∃ i2 : Usize, i + cnt = ok i2 ∧ i2.val = index.val + 1 + cnt.val := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := cnt) (by scalar_tac))
        exact ⟨z, hz, by scalar_tac⟩
      by_cases h2 : index.val + 1 + cnt.val ≤ k.val
      · have hp : acc.val.length < Usize.max := by
          have : acc.val.length ≤ k.val := by
            rw [hacc]; simp; omega
          omega
        obtain ⟨r, hr, hrv⟩ := ih (vpush acc (fs.val[k.val]'hkl) hp) k1 (by omega) (by omega)
          (by rw [hk1v, hacc', if_neg h1, if_pos h2, vpush_val, hacc])
        refine ⟨r, ?_, hrv⟩
        unfold sim.autogen.click_frames_fixup_loop0; rw [loop_unfold]
        have hb : sim.autogen.click_frames_fixup_loop0.body fs index size cnt acc k =
            ok (.cont (vpush acc (fs.val[k.val]'hkl) hp, k1)) := by
          simp [sim.autogen.click_frames_fixup_loop0.body, show k < size by scalar_tac, hi1,
            show ¬ k < i by scalar_tac, hiv, h1, hi2, hi2v, h2, show k ≥ i2 by scalar_tac, vec_index_eq' fs k hkl, vec_push_ok _ _ hp, hk1]
        dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.autogen.click_frames_fixup_loop0 at hr; exact hr
      · obtain ⟨r, hr, hrv⟩ := ih acc k1 (by omega) (by omega)
          (by rw [hk1v, hacc', if_neg h1, if_neg h2, hacc])
        refine ⟨r, ?_, hrv⟩
        unfold sim.autogen.click_frames_fixup_loop0; rw [loop_unfold]
        have hb : sim.autogen.click_frames_fixup_loop0.body fs index size cnt acc k = ok (.cont (acc, k1)) := by
          simp [sim.autogen.click_frames_fixup_loop0.body, show k < size by scalar_tac, hi1,
            show ¬ k < i by scalar_tac, hiv, h1, hi2, hi2v, h2, show ¬ k ≥ i2 by scalar_tac, hk1]
        dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.autogen.click_frames_fixup_loop0 at hr; exact hr
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_heap_set (v : alloc.vec.Vec replay.frames.ActList) (i : Usize) (al : replay.frames.ActList) :
    ((alloc.vec.Vec.set v i al).val.map s2_actListS).toArray =
      ((v.val.map s2_actListS).toArray).setIfInBounds i.val (s2_actListS al) := by
  apply Array.toList_inj.mp
  simp [vec_set_val', List.map_set]

theorem s2_fix_loop1 (fs : alloc.vec.Vec sim.autogen.AFrame) (prevRef : Usize) (action : replay.frames.Action)
    (fsize : Usize) (hfs : fsize.val = fs.val.length) :
    ∀ (n : Nat) (v : alloc.vec.Vec replay.frames.ActList) (j : Usize), fs.val.length - j.val = n →
      (∀ x ∈ fs.val, x.actions.val < v.val.length) → prevRef.val < v.val.length → (∀ l ∈ v.val, l.len.val ≤ 3) →
      ∃ r, sim.autogen.click_frames_fixup_loop1 fs v prevRef action fsize j = ok r ∧
        (r.val.map s2_actListS).toArray = (List.range' j.val (fs.val.length - j.val)).foldl
          (s2_fxStep (fs.val.map s2_aframeS).toArray prevRef.val (s2_actS action)) (v.val.map s2_actListS).toArray ∧
        r.val.length = v.val.length ∧ (∀ l ∈ r.val, l.len.val ≤ 3) := by
  have hmax := fs.property
  intro n
  induction n with
  | zero =>
    intro v j hn hfr hpr hl3
    refine ⟨v, ?_, by simp [show fs.val.length - j.val = 0 by omega], rfl, hl3⟩
    unfold sim.autogen.click_frames_fixup_loop1; rw [loop_unfold]
    simp [sim.autogen.click_frames_fixup_loop1.body, show ¬ j < fsize by scalar_tac]
  | succ n ih =>
    intro v j hn hfr hpr hl3
    have hj : j.val < fs.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    obtain ⟨i, hi, hiv⟩ : ∃ i : Usize, fsize - 1#usize = ok i ∧ i.val = fs.val.length - 1 := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := fsize) (y := 1#usize) (by scalar_tac))
      exact ⟨z, hz, by scalar_tac⟩
    let f := fs.val[j.val]'hj
    have hfa : f.actions.val < v.val.length := hfr f (List.getElem_mem hj)
    obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
    have eal' : (abs al : List OsuModel.Replay.Action) = [s2_actS action] := eal.symm
    have hmu := vec_index_mut_usize_ok v f.actions hfa
    have hiu := vec_index_usize_ok v f.actions hfa
    have hpu := vec_index_usize_ok v prevRef hpr
    have hfj : ((fs.val.map s2_aframeS).toArray)[j.val]! = s2_aframeS f := by
      simp [f, getElem!_pos, hj]
    have hrange : List.range' j.val (fs.val.length - j.val) = j.val :: List.range' (j.val + 1) (fs.val.length - (j.val + 1)) := by
      rw [show fs.val.length - j.val = (fs.val.length - (j.val + 1)) + 1 by omega, List.range'_succ]
    have hHi : ∀ (r : Nat) (h : r < v.val.length), ((v.val.map s2_actListS).toArray)[r]?.getD [] = s2_actListS (v.val[r]'h) := by
      intro r h; simp [h]
    -- the new heap value of this iteration and its spec image
    obtain ⟨v1, hb, ev1, hl1, hl31⟩ : ∃ v1, sim.autogen.click_frames_fixup_loop1.body fs prevRef action fsize v j =
        ok (.cont (v1, j1)) ∧
        (v1.val.map s2_actListS).toArray = s2_fxStep (fs.val.map s2_aframeS).toArray prevRef.val (s2_actS action)
          (v.val.map s2_actListS).toArray j.val ∧ v1.val.length = v.val.length ∧ (∀ l ∈ v1.val, l.len.val ≤ 3) := by
      by_cases hlt : j.val < fs.val.length - 1
      · refine ⟨alloc.vec.Vec.set v f.actions al, ?_, ?_, by simp [vec_set_val'], ?_⟩
        · simp [sim.autogen.click_frames_fixup_loop1.body, show j < fsize by scalar_tac, vec_index_eq' fs j hj, hi,
            hiv, hlt, hal, hmu, hj1, f]
        · rw [s2_heap_set, s2_fxStep, hfj]
          simp [s2_aframeS, hlt, ← eal]
        · intro l hl; simp [vec_set_val'] at hl
          rcases List.mem_or_eq_of_mem_set hl with hl | hl
          · exact hl3 l hl
          · rw [hl]; exact hall
      · have heq := replay.frames.act_eq_refines (v.val[f.actions.val]'hfa) (v.val[prevRef.val]'hpr)
          (hl3 _ (List.getElem_mem _)) (hl3 _ (List.getElem_mem _))
        by_cases hb : ((abs (v.val[f.actions.val]'hfa) : List OsuModel.Replay.Action) == abs (v.val[prevRef.val]'hpr)) = true
        · refine ⟨alloc.vec.Vec.set v f.actions al, ?_, ?_, by simp [vec_set_val'], ?_⟩
          · simp [sim.autogen.click_frames_fixup_loop1.body, show j < fsize by scalar_tac, vec_index_eq' fs j hj, hi,
              hiv, hlt, hal, hmu, hj1, f, hiu, hpu, heq, hb]
          · rw [s2_heap_set, s2_fxStep, hfj]
            simp only [s2_aframeS, hHi _ hfa, hHi _ hpr]
            simp only [s2_actListS_eq] at ⊢
            simp [hb, eal']
          · intro l hl; simp [vec_set_val'] at hl
            rcases List.mem_or_eq_of_mem_set hl with hl | hl
            · exact hl3 l hl
            · rw [hl]; exact hall
        · refine ⟨v, ?_, ?_, rfl, hl3⟩
          · simp [sim.autogen.click_frames_fixup_loop1.body, show j < fsize by scalar_tac, vec_index_eq' fs j hj, hi,
              hiv, hlt, hj1, f, hiu, hpu, heq, hb]
          · rw [s2_fxStep, hfj]
            simp only [s2_aframeS, hHi _ hfa, hHi _ hpr]
            simp only [s2_actListS_eq] at ⊢
            simp [hb, hlt]
    obtain ⟨r, hr, er, hrl, hr3⟩ := ih v1 j1 (by omega) (by rw [hl1]; exact hfr) (by omega) hl31
    refine ⟨r, ?_, ?_, by omega, hr3⟩
    · unfold sim.autogen.click_frames_fixup_loop1; rw [loop_unfold]
      dsimp only; rw [hb]; simp only [bind_ok]
      unfold sim.autogen.click_frames_fixup_loop1 at hr; exact hr
    · rw [er, hrange, List.foldl_cons, ← ev1, hj1v]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_fix_loop2 (fs : alloc.vec.Vec sim.autogen.AFrame) (prevRef : Usize) (action : replay.frames.Action)
    (fsize : Usize) (hfs : fsize.val = fs.val.length) :
    ∀ (n : Nat) (v : alloc.vec.Vec replay.frames.ActList) (j : Usize), fs.val.length - j.val = n →
      (∀ x ∈ fs.val, x.actions.val < v.val.length) → prevRef.val < v.val.length → (∀ l ∈ v.val, l.len.val ≤ 3) →
      ∃ r, sim.autogen.click_frames_fixup_loop2 fs v prevRef action fsize j = ok r ∧
        (r.val.map s2_actListS).toArray = (List.range' j.val (fs.val.length - j.val)).foldl
          (s2_fxStep (fs.val.map s2_aframeS).toArray prevRef.val (s2_actS action)) (v.val.map s2_actListS).toArray ∧
        r.val.length = v.val.length ∧ (∀ l ∈ r.val, l.len.val ≤ 3) := by
  have hmax := fs.property
  intro n
  induction n with
  | zero =>
    intro v j hn hfr hpr hl3
    refine ⟨v, ?_, by simp [show fs.val.length - j.val = 0 by omega], rfl, hl3⟩
    unfold sim.autogen.click_frames_fixup_loop2; rw [loop_unfold]
    simp [sim.autogen.click_frames_fixup_loop2.body, show ¬ j < fsize by scalar_tac]
  | succ n ih =>
    intro v j hn hfr hpr hl3
    have hj : j.val < fs.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    obtain ⟨i, hi, hiv⟩ : ∃ i : Usize, fsize - 1#usize = ok i ∧ i.val = fs.val.length - 1 := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := fsize) (y := 1#usize) (by scalar_tac))
      exact ⟨z, hz, by scalar_tac⟩
    let f := fs.val[j.val]'hj
    have hfa : f.actions.val < v.val.length := hfr f (List.getElem_mem hj)
    obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
    have eal' : (abs al : List OsuModel.Replay.Action) = [s2_actS action] := eal.symm
    have hmu := vec_index_mut_usize_ok v f.actions hfa
    have hiu := vec_index_usize_ok v f.actions hfa
    have hpu := vec_index_usize_ok v prevRef hpr
    have hfj : ((fs.val.map s2_aframeS).toArray)[j.val]! = s2_aframeS f := by
      simp [f, getElem!_pos, hj]
    have hrange : List.range' j.val (fs.val.length - j.val) = j.val :: List.range' (j.val + 1) (fs.val.length - (j.val + 1)) := by
      rw [show fs.val.length - j.val = (fs.val.length - (j.val + 1)) + 1 by omega, List.range'_succ]
    have hHi : ∀ (r : Nat) (h : r < v.val.length), ((v.val.map s2_actListS).toArray)[r]?.getD [] = s2_actListS (v.val[r]'h) := by
      intro r h; simp [h]
    -- the new heap value of this iteration and its spec image
    obtain ⟨v1, hb, ev1, hl1, hl31⟩ : ∃ v1, sim.autogen.click_frames_fixup_loop2.body fs prevRef action fsize v j =
        ok (.cont (v1, j1)) ∧
        (v1.val.map s2_actListS).toArray = s2_fxStep (fs.val.map s2_aframeS).toArray prevRef.val (s2_actS action)
          (v.val.map s2_actListS).toArray j.val ∧ v1.val.length = v.val.length ∧ (∀ l ∈ v1.val, l.len.val ≤ 3) := by
      by_cases hlt : j.val < fs.val.length - 1
      · refine ⟨alloc.vec.Vec.set v f.actions al, ?_, ?_, by simp [vec_set_val'], ?_⟩
        · simp [sim.autogen.click_frames_fixup_loop2.body, show j < fsize by scalar_tac, vec_index_eq' fs j hj, hi,
            hiv, hlt, hal, hmu, hj1, f]
        · rw [s2_heap_set, s2_fxStep, hfj]
          simp [s2_aframeS, hlt, ← eal]
        · intro l hl; simp [vec_set_val'] at hl
          rcases List.mem_or_eq_of_mem_set hl with hl | hl
          · exact hl3 l hl
          · rw [hl]; exact hall
      · have heq := replay.frames.act_eq_refines (v.val[f.actions.val]'hfa) (v.val[prevRef.val]'hpr)
          (hl3 _ (List.getElem_mem _)) (hl3 _ (List.getElem_mem _))
        by_cases hb : ((abs (v.val[f.actions.val]'hfa) : List OsuModel.Replay.Action) == abs (v.val[prevRef.val]'hpr)) = true
        · refine ⟨alloc.vec.Vec.set v f.actions al, ?_, ?_, by simp [vec_set_val'], ?_⟩
          · simp [sim.autogen.click_frames_fixup_loop2.body, show j < fsize by scalar_tac, vec_index_eq' fs j hj, hi,
              hiv, hlt, hal, hmu, hj1, f, hiu, hpu, heq, hb]
          · rw [s2_heap_set, s2_fxStep, hfj]
            simp only [s2_aframeS, hHi _ hfa, hHi _ hpr]
            simp only [s2_actListS_eq] at ⊢
            simp [hb, eal']
          · intro l hl; simp [vec_set_val'] at hl
            rcases List.mem_or_eq_of_mem_set hl with hl | hl
            · exact hl3 l hl
            · rw [hl]; exact hall
        · refine ⟨v, ?_, ?_, rfl, hl3⟩
          · simp [sim.autogen.click_frames_fixup_loop2.body, show j < fsize by scalar_tac, vec_index_eq' fs j hj, hi,
              hiv, hlt, hj1, f, hiu, hpu, heq, hb]
          · rw [s2_fxStep, hfj]
            simp only [s2_aframeS, hHi _ hfa, hHi _ hpr]
            simp only [s2_actListS_eq] at ⊢
            simp [hb, hlt]
    obtain ⟨r, hr, er, hrl, hr3⟩ := ih v1 j1 (by omega) (by rw [hl1]; exact hfr) (by omega) hl31
    refine ⟨r, ?_, ?_, by omega, hr3⟩
    · unfold sim.autogen.click_frames_fixup_loop2; rw [loop_unfold]
      dsimp only; rw [hb]; simp only [bind_ok]
      unfold sim.autogen.click_frames_fixup_loop2 at hr; exact hr
    · rw [er, hrange, List.foldl_cons, ← ev1, hj1v]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

/-- the inner join point of `s2_cfxS` (cut + action-list rewrite, then `K`) -/
def s2_fixJP (g : G) (index : Int) (endFrame : AFrame) (prevRef : Nat) (K : Unit → Action → M Unit) :
    Unit → Action → M Unit := fun __r action =>
  let endIndex := findInsertionIndex g.frames endFrame.time
  let fs := g.frames
  let __do_jp := fun (__r : Unit) (fs : Array AFrame) => do
    modify fun g => { frames := fs, buttonIndex := g.buttonIndex, heap := g.heap }
    forIn' [index.toNat + 1:fs.size] PUnit.unit fun j h __s =>
        let f := fs[j]'h.upper
        do
        let __do_lift ← listOf f.actions
        let __do_lift_4 ← listOf prevRef
        if (decide (j < fs.size - 1) || __do_lift == __do_lift_4) = true then do
            setList f.actions [action]
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)
    K () action
  if index < ↑fs.size - 1 then
    let cnt := endIndex - (index.toNat + 1)
    let fs := fs.extract 0 (index.toNat + 1) ++ fs.extract (index.toNat + 1 + cnt)
    __do_jp () fs
  else __do_jp () fs

theorem s2_fixS_eq (g : G) (index : Int) (startFrame endFrame : AFrame) (action : Action) (K : Unit → Action → M Unit) :
    s2_cfxS g index startFrame endFrame action K =
      if 0 ≤ index then
        match g.frames[index.toNat]? with
        | some prevFrame => do
          let l2 ← listOf prevFrame.actions
          if (!l2.isEmpty) = true then do
            let l3 ← listOf prevFrame.actions
            if l3.contains action = true then do
              let a := if (action == Action.left) = true then Action.right else Action.left
              setList startFrame.actions [a]
              s2_fixJP g index endFrame prevFrame.actions K () a
            else s2_fixJP g index endFrame prevFrame.actions K () action
          else K () action
        | _ => do
          let __r ← throw "internal: insertion index out of range"
          K __r action
      else K () action := rfl

theorem s2_listOf_ok (r : Nat) (C : List OsuModel.Sim.RateMod) (S : G) (h : r < S.heap.size) :
    listOf r C S = .ok (S.heap[r], S) := by
  simp only [listOf, s2_am_get_bind]
  simp [h]

theorem s2_setList_ok (r : Nat) (xs : List Action) (C : List OsuModel.Sim.RateMod) (S : G) (h : r < S.heap.size) :
    setList r xs C S = .ok ((), { S with heap := S.heap.setIfInBounds r xs }) := by
  simp only [setList, s2_am_get_bind]
  simp [h, Array.setIfInBounds]

theorem s2_mem_extract {α} {xs : Array α} {x : α} {i j : Nat} (h : x ∈ xs.extract i j) : x ∈ xs := by
  rw [Array.mem_extract_iff_getElem] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact Array.getElem_mem _

theorem s2_fixJP_spec (G0 : G) (index : Nat) (ef : AFrame) (prevRef : Nat) (a : Action) (K : Unit → Action → M Unit)
    (C : List OsuModel.Sim.RateMod) (H : Array (List Action))
    (hpr : prevRef < H.size) (hrefs : ∀ x ∈ G0.frames, x.actions < H.size) :
    s2_fixJP G0 (index : Int) ef prevRef K () a C { G0 with heap := H } =
      K () a C { G0 with
        frames := (if index + 1 < G0.frames.size then
          G0.frames.extract 0 (index + 1) ++ G0.frames.extract (index + 1 + (findInsertionIndex G0.frames ef.time - (index + 1)))
          else G0.frames),
        heap := (List.range' (index + 1) ((if index + 1 < G0.frames.size then
          G0.frames.extract 0 (index + 1) ++ G0.frames.extract (index + 1 + (findInsertionIndex G0.frames ef.time - (index + 1)))
          else G0.frames).size - (index + 1))).foldl
            (s2_fxStep (if index + 1 < G0.frames.size then
              G0.frames.extract 0 (index + 1) ++ G0.frames.extract (index + 1 + (findInsertionIndex G0.frames ef.time - (index + 1)))
              else G0.frames) prevRef a) H } := by
  generalize hfs : (if index + 1 < G0.frames.size then
    G0.frames.extract 0 (index + 1) ++ G0.frames.extract (index + 1 + (findInsertionIndex G0.frames ef.time - (index + 1)))
    else G0.frames) = fs
  have hsub : ∀ x ∈ fs, x ∈ G0.frames := by
    rw [← hfs]; split
    · intro x hx
      simp only [Array.mem_append] at hx
      rcases hx with hx | hx <;> exact s2_mem_extract hx
    · exact fun x hx => hx
  have hJ : s2_fixJP G0 (index : Int) ef prevRef K () a =
      (do
        modify fun g => { frames := fs, buttonIndex := g.buttonIndex, heap := g.heap }
        forIn' [index + 1:fs.size] PUnit.unit fun j h __s =>
            let f := fs[j]'h.upper
            do
            let l1 ← listOf f.actions
            let l4 ← listOf prevRef
            if (decide (j < fs.size - 1) || l1 == l4) = true then do
                setList f.actions [a]
                pure (ForInStep.yield PUnit.unit)
              else pure (ForInStep.yield PUnit.unit)
        K () a) := by
    rw [← hfs]
    unfold s2_fixJP
    simp only [Int.toNat_natCast]
    by_cases hc : index + 1 < G0.frames.size
    · rw [if_pos (by omega), if_pos hc]
    · rw [if_neg (by omega), if_neg hc]
  rw [hJ]
  simp only [s2_am_bind, s2_am_modify]
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp only [Except.bind]
  rw [s2_fxLoopS fs prevRef a _ _ ?hB C _ (by simpa using hpr) (fun x hx => by simpa using hrefs x (hsub x hx))]
  · simp only [Except.bind, Std.Legacy.Range.size]
    congr 3
    simp
  case hB =>
    intro j hj C S h1 h2
    have hjl : j < fs.size := by
      simp [List.mem_range', Std.Legacy.Range.size] at hj
      omega
    have hfa : (fs[j]'hjl).actions < S.heap.size := h2 _ (Array.getElem_mem hjl)
    simp only [s2_am_bind, s2_listOf_ok _ _ _ hfa, s2_listOf_ok _ _ _ h1, Except.bind]
    unfold s2_fxStep
    have hgj : fs[j]! = fs[j]'hjl := by simp [getElem!_pos, hjl]
    rw [hgj, getElem?_pos S.heap _ hfa, getElem?_pos S.heap _ h1]
    simp only [Option.getD_some]
    split
    · simp only [s2_am_bind, s2_setList_ok _ _ _ _ hfa, Except.bind, s2_am_pure]
    · rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim.AutoGen

theorem s2_extract_cut {α} (L : List α) (a b : Nat) :
    L.toArray.extract 0 a ++ L.toArray.extract b = (L.take a ++ L.drop b).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

theorem s2_fixup (h64 : System.Platform.numBits = 64) (g : sim.autogen.G) (index prevRef startRef : Usize)
    (endTime : F64) (action0 : replay.frames.Action)
    (hI : s2_gInv g) (hidx : index.val < g.frames.val.length) (hpr : prevRef = (g.frames.val[index.val]'hidx).actions)
    (hsr : startRef.val < g.heap.val.length) (hfl : g.frames.val.length < 2^62) :
    ∃ a g', sim.autogen.click_frames_fixup g index prevRef startRef endTime action0 = ok (a, g') ∧
      s2_gInv g' ∧ g'.button_index = g.button_index ∧ g'.frames.val.length ≤ g.frames.val.length ∧
      g'.heap.val.length = g.heap.val.length ∧
      ∀ (ef : OsuModel.Sim.AFrame) (K : Unit → OsuModel.Replay.Action → M Unit) C, ef.time = endTime →
        (do let l3 ← listOf prevRef.val
            if l3.contains (s2_actS action0) = true then do
              let a := if (s2_actS action0 == OsuModel.Replay.Action.left) = true then OsuModel.Replay.Action.right
                else OsuModel.Replay.Action.left
              setList startRef.val [a]
              s2_fixJP (abs g) (index.val : Int) ef prevRef.val K () a
            else s2_fixJP (abs g) (index.val : Int) ef prevRef.val K () (s2_actS action0) : M Unit) C (abs g) =
        K () (s2_actS a) C (abs g') := by
  have hmax := g.frames.property
  have hgl : (abs g : G).frames.size = g.frames.val.length := by simp [abs, s2_gS]
  have hgh : (abs g : G).heap = (g.heap.val.map s2_actListS).toArray := rfl
  have hgfr : (abs g : G).frames = (g.frames.val.map s2_aframeS).toArray := rfl
  have hpr' : prevRef.val < g.heap.val.length := by
    have hm : s2_aframeS (g.frames.val[index.val]'hidx) ∈ (abs g : G).frames := by
      rw [hgfr]; simp only [List.mem_toArray, List.mem_map]; exact ⟨_, List.getElem_mem hidx, rfl⟩
    have := hI.2 _ hm
    rw [hpr]; exact this
  obtain ⟨e, he, ee⟩ := sim.autogen.find_insertion_index_refines h64 (alloc.vec.Vec.deref g.frames) endTime
    (by simpa [ms_deref_val] using hfl)
  have efr : (abs (alloc.vec.Vec.deref g.frames) : _root_.Array OsuModel.Sim.AFrame) = (abs g : G).frames := by
    show (List.map abs (alloc.vec.Vec.deref g.frames).val).toArray = (g.frames.val.map s2_aframeS).toArray
    simp [ms_deref_val]; intro a _; rfl
  rw [efr] at ee
  have hele := s2_fii_le (abs g : G).frames endTime
  rw [ee, hgl] at hele
  obtain ⟨i, hi1, hiv⟩ := usize_add_one index (by omega)
  -- the action-list state before the cut/rewrite (heap `v`, action `act`)
  obtain ⟨v, act, hvact, hvl, hv3, hspec1⟩ : ∃ (v : alloc.vec.Vec replay.frames.ActList) (act : replay.frames.Action),
      (∀ (R : alloc.vec.Vec replay.frames.ActList × replay.frames.Action →
          Result (replay.frames.Action × sim.autogen.G)), (do
        let al ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice replay.frames.ActList) g.heap prevRef
        let b ← replay.frames.act_contains al action0
        let p ← if b then do
          let b1 ← replay.frames.Action.Insts.CoreCmpPartialEqAction.eq action0 replay.frames.Action.Left
          let action1 ← if b1 then ok replay.frames.Action.Right else ok replay.frames.Action.Left
          let al1 ← sim.autogen.single action1
          let (_, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
            replay.frames.ActList) g.heap startRef
          ok (index_mut_back al1, action1)
        else ok (g.heap, action0)
        R p) = R (v, act)) ∧
      v.val.length = g.heap.val.length ∧ (∀ l ∈ v.val, l.len.val ≤ 3) ∧
      ∀ (ef : OsuModel.Sim.AFrame) (K : Unit → OsuModel.Replay.Action → M Unit) C,
        (do let l3 ← listOf prevRef.val
            if l3.contains (s2_actS action0) = true then do
              let a := if (s2_actS action0 == OsuModel.Replay.Action.left) = true then OsuModel.Replay.Action.right
                else OsuModel.Replay.Action.left
              setList startRef.val [a]
              s2_fixJP (abs g) (index.val : Int) ef prevRef.val K () a
            else s2_fixJP (abs g) (index.val : Int) ef prevRef.val K () (s2_actS action0) : M Unit) C (abs g) =
        s2_fixJP (abs g) (index.val : Int) ef prevRef.val K () (s2_actS act) C
          { (abs g : G) with heap := (v.val.map s2_actListS).toArray } := by
    have hc := replay.frames.act_contains_refines (g.heap.val[prevRef.val]'hpr') action0 (hI.1 _ (List.getElem_mem _))
    have hl3 : listOf prevRef.val = (fun C S => listOf prevRef.val C S) := rfl
    have hlo : ∀ C, listOf prevRef.val C (abs g) = .ok (s2_actListS (g.heap.val[prevRef.val]'hpr'), abs g) := by
      intro C
      rw [s2_listOf_ok _ _ _ (by rw [hgh]; simpa using hpr')]
      simp [hgh]
    by_cases hb : ((abs (g.heap.val[prevRef.val]'hpr') : List OsuModel.Replay.Action).contains (abs action0)) = true
    · let a1 : replay.frames.Action := if (s2_actS action0 == s2_actS replay.frames.Action.Left) = true then
        replay.frames.Action.Right else replay.frames.Action.Left
      obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines a1
      refine ⟨alloc.vec.Vec.set g.heap startRef al, a1, ?_, by simp [vec_set_val'], ?_, ?_⟩
      · intro R
        have hbm : (abs action0 : OsuModel.Replay.Action) ∈ (abs (g.heap.val[prevRef.val]'hpr') : List OsuModel.Replay.Action) := by
          simpa using hb
        have hal' : sim.autogen.single (if s2_actS action0 = s2_actS replay.frames.Action.Left then
            replay.frames.Action.Right else replay.frames.Action.Left) = ok al := by
          rw [← hal]; simp [a1]
        simp [vec_index_eq' g.heap prevRef hpr', hc, hbm, hal', vec_index_mut_eq g.heap startRef hsr]
        try simp [a1]
      · intro l hl; simp [vec_set_val'] at hl
        rcases List.mem_or_eq_of_mem_set hl with hl | hl
        · exact hI.1 l hl
        · rw [hl]; exact hall
      · intro ef K C
        simp only [s2_am_bind, hlo, Except.bind]
        have hb' : (s2_actListS (g.heap.val[prevRef.val]'hpr')).contains (s2_actS action0) = true := hb
        rw [if_pos hb']
        simp only [s2_am_bind]
        rw [s2_setList_ok _ _ _ _ (by rw [hgh]; simpa using hsr)]
        simp only [Except.bind]
        have ha1 : (if (s2_actS action0 == OsuModel.Replay.Action.left) = true then OsuModel.Replay.Action.right
            else OsuModel.Replay.Action.left) = s2_actS a1 := by
          cases action0 <;> rfl
        rw [ha1, s2_heap_set, ← eal]
        rfl
    · refine ⟨g.heap, action0, ?_, rfl, hI.1, ?_⟩
      · have hbf : ((abs (g.heap.val[prevRef.val]'hpr') : List OsuModel.Replay.Action).contains (abs action0)) = false :=
          Bool.eq_false_iff.mpr hb
        intro R
        simp only [vec_index_eq' g.heap prevRef hpr', hc, hbf, bind_ok, Bool.false_eq_true, if_false]
      · intro ef K C
        simp only [s2_am_bind, hlo, Except.bind]
        have hb' : ¬ (s2_actListS (g.heap.val[prevRef.val]'hpr')).contains (s2_actS action0) = true := hb
        rw [if_neg hb']
        rfl
  unfold sim.autogen.click_frames_fixup
  rw [hvact]
  have hrefsG : ∀ x ∈ g.frames.val, x.actions.val < v.val.length := by
    intro x hx; rw [hvl]
    exact hI.2 (s2_aframeS x) (by rw [hgfr]; simp only [List.mem_toArray, List.mem_map]; exact ⟨x, hx, rfl⟩)
  have hprv : prevRef.val < v.val.length := by omega
  have hHsz : ((v.val.map s2_actListS).toArray).size = v.val.length := by simp
  by_cases hcut : index.val + 1 < g.frames.val.length
  · obtain ⟨cU, hcU, hcUv⟩ : ∃ c : Usize, (if e > i then e - i else ok 0#usize) = ok c ∧
        c.val = e.val - (index.val + 1) := by
      by_cases hg : e > i
      · obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := e) (y := i) (by scalar_tac))
        exact ⟨z, by simp [hg, hz], by scalar_tac⟩
      · exact ⟨0#usize, by simp [hg], by scalar_tac⟩
    obtain ⟨fsR, hfsR, efsR⟩ := s2_fix_loop0 g.frames index (alloc.vec.Vec.len g.frames) cU (by simp) hidx
      (by rw [hcUv]; omega) _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    have hfsl : fsR.val.length ≤ g.frames.val.length := by rw [efsR]; simp; omega
    have hfsl' : index.val + 1 ≤ fsR.val.length := by rw [efsR]; simp; omega
    have hfsub : ∀ x ∈ fsR.val, x ∈ g.frames.val := by
      rw [efsR]; intro x hx; simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact List.mem_of_mem_take hx
      · exact List.mem_of_mem_drop hx
    obtain ⟨v1, hv1, ev1, hv1l, hv13⟩ := s2_fix_loop1 fsR prevRef act (alloc.vec.Vec.len fsR) (by simp) _ v i rfl
      (fun x hx => hrefsG x (hfsub x hx)) hprv hv3
    refine ⟨act, ({ g with frames := fsR, heap := v1 } : sim.autogen.G), ?_, ⟨hv13, ?_⟩, rfl, hfsl, by simp; omega, ?_⟩
    · have hiu : i.val < g.frames.val.length := by omega
      have hcU' : (if i.val < e.val then e - i else ok 0#usize) = ok cU := by
        rw [← hcU]; simp [gt_iff_lt]
      simp at hfsR hv1
      simp [he, hi1, hiu, hcU', hfsR, hv1]
    · intro x hx
      have hx' : x ∈ (fsR.val.map s2_aframeS).toArray := hx
      simp only [List.mem_toArray, List.mem_map] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      show y.actions.val < _
      rw [hv1l]; exact hrefsG y (hfsub y hy)
    · intro ef K C hef
      rw [hspec1, s2_fixJP_spec (abs g) index.val ef prevRef.val (s2_actS act) K C _ (by omega)
        (by intro x hx; rw [hgfr] at hx; simp only [List.mem_toArray, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx; simp only [hHsz]; exact hrefsG y hy)]
      have hfs' : (if index.val + 1 < (abs g : G).frames.size then
          (abs g : G).frames.extract 0 (index.val + 1) ++ (abs g : G).frames.extract
            (index.val + 1 + (findInsertionIndex (abs g : G).frames ef.time - (index.val + 1)))
          else (abs g : G).frames) = (fsR.val.map s2_aframeS).toArray := by
        rw [if_pos (by omega), hef, ee, hgfr, s2_extract_cut, efsR, hcUv, ← List.map_take, ← List.map_drop, List.map_append]
      rw [hfs']
      congr 1
      show _ = ({ frames := (fsR.val.map s2_aframeS).toArray, buttonIndex := g.button_index.val, heap := (v1.val.map s2_actListS).toArray } : G)
      rw [ev1, hiv]
      simp only [List.length_map, List.size_toArray]
      rfl
  · have hge : g.frames.val.length ≤ index.val + 1 := by omega
    obtain ⟨v1, hv1, ev1, hv1l, hv13⟩ := s2_fix_loop2 g.frames prevRef act (alloc.vec.Vec.len g.frames) (by simp) _ v i
      rfl hrefsG hprv hv3
    refine ⟨act, ({ g with heap := v1 } : sim.autogen.G), ?_, ⟨hv13, ?_⟩, rfl, le_refl _, by simp; omega, ?_⟩
    · have hiu : ¬ i.val < g.frames.val.length := by omega
      simp at hv1
      simp [he, hi1, hiu, hv1]
    · intro x hx
      have hx' : x ∈ (g.frames.val.map s2_aframeS).toArray := hx
      simp only [List.mem_toArray, List.mem_map] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      show y.actions.val < _
      rw [hv1l]; exact hrefsG y hy
    · intro ef K C hef
      rw [hspec1, s2_fixJP_spec (abs g) index.val ef prevRef.val (s2_actS act) K C _ (by omega)
        (by intro x hx; rw [hgfr] at hx; simp only [List.mem_toArray, List.mem_map] at hx
            obtain ⟨y, hy, rfl⟩ := hx; simp only [hHsz]; exact hrefsG y hy)]
      rw [if_neg (by omega)]
      congr 1
      show _ = ({ frames := (g.frames.val.map s2_aframeS).toArray, buttonIndex := g.button_index.val, heap := (v1.val.map s2_actListS).toArray } : G)
      rw [ev1, hiv, hgfr]
      simp only [List.length_map, List.size_toArray]
      rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

/-- the trailing `if (← lastFrame).time ≤ endFrame.time then addFrame endFrame` of `addClickFrames` -/
def s2_lastS (ef : AFrame) : M Unit := do
  let lf ← lastFrame
  if lf.time ≤ ef.time then addFrame ef else pure ()

theorem s2_ite_bind {α β : Type} (c : Prop) [Decidable c] (a b : M α) (f : α → M β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem s2_throw_bind {α β : Type} (m : String) (f : α → M β) : ((throw m : M α) >>= f) = throw m := rfl

theorem s2_acfJP_eq (o : TopObj) (sp : OsuTK.Vector2) (dir : F32) (se : OsuTK.Vector2) (sf ef : AFrame) (action : Action) :
    s2_acfJP o sp dir se sf ef () action = (do
      addFrame sf
      match o.h.kind with
      | .spinner => do
        let ep ← s2_spinClickS o.h.start o.h.endTime sp dir action
        s2_lastS { ef with pos := ep }
      | .slider => do
        s2_sliderClickS o.h.stacked o.h.start o.h.endTime o.slider se action
        s2_lastS ef
      | _ => s2_lastS ef) := by
  simp only [s2_acfJP, s2_spinClickS, s2_sliderClickS, s2_lastS, bind_assoc, pure_bind, s2_ite_bind]
  congr 1; funext _
  split
  · rfl
  · cases hs : o.slider <;> (try simp only [bind_assoc, pure_bind, s2_ite_bind, s2_throw_bind]) <;> rfl
  · rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

theorem s2_bi_mod (x : U64) : x % 2#u64 = ok (if x.val % 2 = 0 then 0#u64 else 1#u64) := by
  obtain ⟨m2, hm2, hm2v⟩ := eq_ok_of_spec (U64.rem_spec x (y := 2#u64) (by simp))
  rw [hm2]; congr 1
  apply UScalar.eq_of_val_eq
  rw [hm2v]
  by_cases h : x.val % 2 = 0
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp; omega

theorem s2_act_sel (n : Nat) :
    (if (n % 2 == 0) = true then Action.left else Action.right) =
      s2_actS (if n % 2 = 0 then replay.frames.Action.Left else replay.frames.Action.Right) := by
  by_cases h : n % 2 = 0
  · simp [h]; rfl
  · simp [h]; rfl

theorem s2_nl_keep (g g' : sim.autogen.G) (xs : replay.frames.ActList) (r : Usize)
    (hl : g.heap.val.length < Usize.max) (h : sim.autogen.new_list g xs = ok (r, g')) :
    g'.button_index = g.button_index ∧ g'.frames = g.frames := by
  unfold sim.autogen.new_list at h; simp [vec_push_ok _ _ hl] at h
  rw [← h.2]; exact ⟨rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

theorem s2_acfS_shape (o : TopObj) (sp : OsuTK.Vector2) (dir : F32) (se : OsuTK.Vector2) :
    s2_acfS o sp dir se = (do
      let d ← get
      let r1 ← newList [if (d.buttonIndex % 2 == 0) = true then Action.left else Action.right]
      let r2 ← newList []
      let g ← get
      s2_cfxS g ((findInsertionIndex g.frames o.h.start : Int) - 1) ⟨o.h.start, sp, r1, false⟩
        ⟨o.h.endTime + keyUpDelay + (if (o.h.kind == Kind.spinner) = true then 1 else 0), se, r2, true⟩
        (if (d.buttonIndex % 2 == 0) = true then Action.left else Action.right)
        (s2_acfJP o sp dir se ⟨o.h.start, sp, r1, false⟩
          ⟨o.h.endTime + keyUpDelay + (if (o.h.kind == Kind.spinner) = true then 1 else 0), se, r2, true⟩)) := rfl

theorem s2_eval_shape {β : Type} (A : G → List Action) (F : G → Nat → Nat → G → M β) (C : List OsuModel.Sim.RateMod)
    (S S1 S2 : G) (n1 n2 : Nat) (h1 : newList (A S) C S = .ok (n1, S1)) (h2 : newList [] C S1 = .ok (n2, S2)) :
    (do
      let d ← get
      let r1 ← newList (A d)
      let r2 ← newList []
      let g ← get
      F d r1 r2 g : M β) C S = F S n1 n2 S2 C S2 := by
  have hg : ∀ S' : G, (get : M G) C S' = .ok (S', S') := fun _ => rfl
  simp only [s2_am_bind, hg, Except.bind, h1, h2]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

theorem s2_key_up : sim.autogen.KEY_UP_DELAY = ok keyUpDelay := by
  simp only [sim.autogen.KEY_UP_DELAY, keyUpDelay, float.F64.from_bits]; congr 1 <;> decide +kernel

set_option maxHeartbeats 30000 in
theorem s2_acf_spec0 (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g : sim.autogen.G)
    (o : sim.playable.TopObj) (tn : Nat → String) (sp se : net.osutk.Vector2) (dir : F32)
    (hI : s2_gInv g) (hh : g.heap.val.length + 2 < Usize.max) (hfl : g.frames.val.length < 2^62) :
    ∃ (action : replay.frames.Action) (al : replay.frames.ActList) (r1 r2 : Usize) (g1 g2 : sim.autogen.G) (e : Usize),
      g.button_index % 2#u64 = ok (if g.button_index.val % 2 = 0 then 0#u64 else 1#u64) ∧
      action = (if g.button_index.val % 2 = 0 then replay.frames.Action.Left else replay.frames.Action.Right) ∧
      sim.autogen.single action = ok al ∧ sim.autogen.new_list g al = ok (r1, g1) ∧
      sim.autogen.new_list g1 replay.frames.ACTLIST_EMPTY = ok (r2, g2) ∧
      sim.autogen.find_insertion_index (alloc.vec.Vec.deref g2.frames) o.h.start = ok e ∧
      findInsertionIndex (abs g2 : G).frames o.h.start = e.val ∧
      e.val ≤ g2.frames.val.length ∧ g2.frames = g.frames ∧ g2.button_index = g.button_index ∧
      g2.heap.val.length = g.heap.val.length + 2 ∧ r1.val = g.heap.val.length ∧ r2.val = g.heap.val.length + 1 ∧
      s2_gInv g2 ∧
      ∀ C, addClickFrames (topS tn o) (v2S sp) dir (v2S se) C (abs g) =
        s2_cfxS (abs g2) ((findInsertionIndex (abs g2 : G).frames (topS tn o).h.start : Int) - 1)
          ⟨(topS tn o).h.start, v2S sp, r1.val, false⟩
          ⟨(topS tn o).h.endTime + keyUpDelay + (if ((topS tn o).h.kind == Kind.spinner) = true then 1 else 0),
            v2S se, r2.val, true⟩
          (s2_actS action)
          (s2_acfJP (topS tn o) (v2S sp) dir (v2S se) ⟨(topS tn o).h.start, v2S sp, r1.val, false⟩
            ⟨(topS tn o).h.endTime + keyUpDelay + (if ((topS tn o).h.kind == Kind.spinner) = true then 1 else 0),
              v2S se, r2.val, true⟩) C (abs g2) := by
  let action : replay.frames.Action := if g.button_index.val % 2 = 0 then .Left else .Right
  obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
  obtain ⟨r1, g1, hr1, hr1v, er1, hg1h, hg1f, -⟩ := s2_ag_new_list (abs mods) g al (by omega)
  have hI1 := (s2_inv_new_list g g1 al r1 hI hall (by omega) hr1).1
  have hg1b : g1.button_index = g.button_index := (s2_nl_keep g g1 al r1 (by omega) hr1).1
  obtain ⟨r2, g2, hr2, hr2v, er2, hg2h, hg2f, -⟩ := s2_ag_new_list (abs mods) g1 replay.frames.ACTLIST_EMPTY (by omega)
  have hI2 := (s2_inv_new_list g1 g2 _ r2 hI1 (by simp [s2_empty_val.2]) (by omega) hr2).1
  have hg2b : g2.button_index = g1.button_index := (s2_nl_keep g1 g2 _ r2 (by omega) hr2).1
  obtain ⟨e, he, ee⟩ := sim.autogen.find_insertion_index_refines h64 (alloc.vec.Vec.deref g2.frames) o.h.start
    (by simpa [ms_deref_val, hg2f, hg1f] using hfl)
  have efr : (abs (alloc.vec.Vec.deref g2.frames) : _root_.Array OsuModel.Sim.AFrame) = (abs g2 : G).frames := by
    show (List.map abs (alloc.vec.Vec.deref g2.frames).val).toArray = (g2.frames.val.map s2_aframeS).toArray
    simp [ms_deref_val]; intro a _; rfl
  rw [efr] at ee
  have hele := s2_fii_le (abs g2 : G).frames o.h.start
  rw [ee] at hele
  have hsz2 : (abs g2 : G).frames.size = g2.frames.val.length := by simp [abs, s2_gS]
  refine ⟨action, al, r1, r2, g1, g2, e, s2_bi_mod _, rfl, hal, hr1, hr2, he, ee, by omega, by rw [hg2f, hg1f],
    by rw [hg2b, hg1b], by omega, hr1v, by omega, hI2, ?_⟩
  intro C
  have hact : (if ((abs g : G).buttonIndex % 2 == 0) = true then Action.left else Action.right) = s2_actS action :=
    s2_act_sel g.button_index.val
  have hget : ∀ S : G, (get : M G) C S = .ok (S, S) := fun _ => rfl
  have hnl : ∀ xs S, newList xs C S = newList xs (abs mods) S := fun _ _ => rfl
  have er2' := er2
  rw [show s2_actListS replay.frames.ACTLIST_EMPTY = [] from s2_abs_empty] at er2'
  have h1 : newList [if ((abs g : G).buttonIndex % 2 == 0) = true then Action.left else Action.right] C (abs g) =
      .ok (r1.val, abs g1) := by rw [hact, hnl, eal, er1]
  have h2 : newList [] C (abs g1) = .ok (r2.val, abs g2) := by rw [hnl, er2']
  rw [s2_acf_eq, s2_acfS_shape, s2_eval_shape _ _ C _ _ _ _ _ h1 h2, hact]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

set_option maxHeartbeats 100000 in
theorem s2_acf_pre (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g : sim.autogen.G)
    (o : sim.playable.TopObj) (tn : Nat → String) (sp se : net.osutk.Vector2) (dir : F32)
    (hI : s2_gInv g) (hh : g.heap.val.length + 2 < Usize.max) (hfl : g.frames.val.length < 2^62) :
    ∃ (r1 r2 : Usize) (g3 : sim.autogen.G) (a3 : replay.frames.Action),
      (∀ {X : Type} (T : Usize → Usize → F64 → Bool → sim.autogen.G → replay.frames.Action → Result X),
        (do
          let i ← g.button_index % 2#u64
          let action ← if i = 0#u64 then ok replay.frames.Action.Left else ok replay.frames.Action.Right
          let al ← sim.autogen.single action
          let p1 ← sim.autogen.new_list g al
          let f ← sim.autogen.KEY_UP_DELAY
          let h_end_time ← float.F64.add o.h.end_time f
          let b ← sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq o.h.kind sim.playable.Kind.Spinner
          let end_delay ← if b then sim.autogen.F64_1 else sim.autogen.F64_0
          let p2 ← sim.autogen.new_list p1.2 replay.frames.ACTLIST_EMPTY
          let f1 ← float.F64.add h_end_time end_delay
          let s := alloc.vec.Vec.deref p2.2.frames
          let ins ← sim.autogen.find_insertion_index s o.h.start
          let p3 ←
            if ins >= 1#usize then do
              let index ← ins - 1#usize
              let a ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.autogen.AFrame) p2.2.frames index
              let al1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice replay.frames.ActList) p2.2.heap a.actions
              if al1.len != 0#usize then do
                let q ← sim.autogen.click_frames_fixup p2.2 index a.actions p1.1 f1 action
                ok (q.2, q.1)
              else ok (p2.2, action)
            else ok (p2.2, action)
          T p1.1 p2.1 f1 b p3.1 p3.2) =
        T r1 r2 (o.h.end_time + keyUpDelay + (if (kindS o.h.kind == Kind.spinner) = true then 1 else 0))
          (kindS o.h.kind == Kind.spinner) g3 a3) ∧
      s2_gInv g3 ∧ g3.button_index = g.button_index ∧ g3.frames.val.length ≤ g.frames.val.length ∧
      g3.heap.val.length = g.heap.val.length + 2 ∧ r1.val < g3.heap.val.length ∧ r2.val < g3.heap.val.length ∧
      ∀ C, addClickFrames (topS tn o) (v2S sp) dir (v2S se) C (abs g) =
        s2_acfJP (topS tn o) (v2S sp) dir (v2S se) ⟨(topS tn o).h.start, v2S sp, r1.val, false⟩
          ⟨(topS tn o).h.endTime + keyUpDelay + (if ((topS tn o).h.kind == Kind.spinner) = true then 1 else 0),
            v2S se, r2.val, true⟩ () (s2_actS a3) C (abs g3) := by
  obtain ⟨action, al, r1, r2, g1, g2, e, hbi, hact, hal, hr1, hr2, he, ee, hele, hg2f, hg2b, hg2h, hr1v, hr2v, hI2,
    hspec⟩ := s2_acf_spec0 h64 mods g o tn sp se dir hI hh hfl
  subst hact
  have hsz2 : (abs g2 : G).frames.size = g2.frames.val.length := by simp [abs, s2_gS]
  have hkS : kindS sim.playable.Kind.Spinner = Kind.spinner := rfl
  have ee' : findInsertionIndex (abs g2 : G).frames (topS tn o).h.start = e.val := ee
  by_cases he0 : e.val = 0
  · refine ⟨r1, r2, g2, (if g.button_index.val % 2 = 0 then replay.frames.Action.Left else replay.frames.Action.Right), ?_, hI2, hg2b, by rw [hg2f], hg2h, by omega, by omega, ?_⟩
    · intro X T
      have hn : ¬ (1 ≤ e.val) := by omega
      simp [hbi, hal, hr1, s2_key_up, float.F64.add, hkS, s2_ag_consts, hr2, he, hn]
    · intro C
      rw [hspec C, s2_fixS_eq, ee', if_neg (by omega)]
  · have he1 : 1 ≤ e.val := by omega
    obtain ⟨idx, hidx, hidxv⟩ : ∃ idx : Usize, e - 1#usize = ok idx ∧ idx.val = e.val - 1 := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := e) (y := 1#usize) (by scalar_tac))
      exact ⟨z, hz, by scalar_tac⟩
    have hil : idx.val < g2.frames.val.length := by omega
    have hfr : (abs g2 : G).frames[idx.val]? = some (s2_aframeS (g2.frames.val[idx.val]'hil)) := by
      show (g2.frames.val.map s2_aframeS).toArray[idx.val]? = _
      simp [hil]
    have hfa : (g2.frames.val[idx.val]'hil).actions.val < g2.heap.val.length :=
      hI2.2 _ (Array.mem_of_getElem? hfr)
    have hI' : ((e.val : Int) - 1) = ((idx.val : Nat) : Int) := by omega
    have hlo : ∀ C, listOf (s2_aframeS (g2.frames.val[idx.val]'hil)).actions C (abs g2) =
        .ok (s2_actListS (g2.heap.val[(g2.frames.val[idx.val]'hil).actions.val]'hfa), abs g2) := by
      intro C
      rw [s2_listOf_ok _ _ _ (by show _ < (g2.heap.val.map s2_actListS).toArray.size; simpa [abs, s2_gS, s2_aframeS] using hfa)]
      simp [abs, s2_gS, s2_aframeS]
    have hal3 := hI2.1 _ (List.getElem_mem hfa)
    by_cases hz : (g2.heap.val[(g2.frames.val[idx.val]'hil).actions.val]'hfa).len.val = 0
    · refine ⟨r1, r2, g2, (if g.button_index.val % 2 = 0 then replay.frames.Action.Left else replay.frames.Action.Right),
        ?_, hI2, hg2b, by rw [hg2f], hg2h, by omega, by omega, ?_⟩
      · intro X T
        have hz' : (g2.heap.val[(g2.frames.val[idx.val]'hil).actions.val]'hfa).len = 0#usize := UScalar.eq_of_val_eq (by simp [hz])
        simp [hbi, hal, hr1, s2_key_up, float.F64.add, hkS, s2_ag_consts, hr2, he, he1, hidx,
          vec_index_usize_ok _ _ hil, vec_index_usize_ok _ _ hfa, hz']
      · intro C
        rw [hspec C, s2_fixS_eq, ee', if_pos (by omega), hI', Int.toNat_natCast, hfr]
        simp only [s2_am_bind, hlo, Except.bind]
        have hemp : (s2_actListS (g2.heap.val[(g2.frames.val[idx.val]'hil).actions.val]'hfa)).isEmpty = true := by
          simp [s2_actListS, actListS, hz]
        rw [hemp]
        rfl
    · obtain ⟨a3, g4, hfx, hI4, hb4, hfl4, hhl4, hspec4⟩ := s2_fixup h64 g2 idx (g2.frames.val[idx.val]'hil).actions r1
        (o.h.end_time + keyUpDelay + (if (kindS o.h.kind == Kind.spinner) = true then 1 else 0))
        (if g.button_index.val % 2 = 0 then replay.frames.Action.Left else replay.frames.Action.Right)
        hI2 hil rfl (by omega) (by rw [hg2f]; exact hfl)
      refine ⟨r1, r2, g4, a3, ?_, hI4, by rw [hb4, hg2b], by rw [← hg2f]; exact hfl4, by omega, by omega, by omega, ?_⟩
      · intro X T
        have hz' : ¬ (g2.heap.val[(g2.frames.val[idx.val]'hil).actions.val]'hfa).len = 0#usize := by
          intro h; apply hz; rw [h]; rfl
        simp [hbi, hal, hr1, s2_key_up, float.F64.add, hkS, s2_ag_consts, hr2, he, he1, hidx,
          vec_index_usize_ok _ _ hil, vec_index_usize_ok _ _ hfa, hz, hfx]
      · intro C
        rw [hspec C, s2_fixS_eq, ee', if_pos (by omega), hI', Int.toNat_natCast, hfr]
        simp only [s2_am_bind, hlo, Except.bind]
        have key : ∀ l : replay.frames.ActList, l.len.val ≠ 0 → l.len.val ≤ 3 → (s2_actListS l).isEmpty = false := by
          intro l hl hl3
          have h3 : l.items.val.length = 3 := by simpa using l.items.property
          rw [Bool.eq_false_iff]; intro hE
          have := congrArg List.length (List.isEmpty_iff.mp hE)
          simp [s2_actListS, actListS] at this
          omega
        have hne := key _ hz hal3
        rw [hne]
        exact hspec4 _ _ C rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

set_option maxHeartbeats 100000 in
theorem s2_last (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod) (g : sim.autogen.G)
    (f1 : F64) (pos : net.osutk.Vector2) (r2 : Usize)
    (hI : s2_gInv g) (hne : 0 < g.frames.val.length) (hfl : g.frames.val.length < 2^62)
    (hr : r2.val < g.heap.val.length) :
    ∃ g', (do
        let a ← sim.autogen.last_frame g
        let b ← float.F64.le a.time f1
        if b then do
          let g6 ← sim.autogen.add_frame g { time := f1, pos := pos, actions := r2, key_up := true }
          ok (core.result.Result.Ok (), g6)
        else ok (core.result.Result.Ok (), g) : Result ((core.result.Result Unit sim.err.SimErr) × sim.autogen.G))
        = ok (core.result.Result.Ok (), g') ∧
      s2_lastS ⟨f1, v2S pos, r2.val, true⟩ (abs mods) (abs g) = .ok ((), abs g') ∧
      s2_gInv g' ∧ g'.heap = g.heap ∧ g'.frames.val.length ≤ g.frames.val.length + 1 ∧
      g.frames.val.length ≤ g'.frames.val.length ∧ g'.button_index = g.button_index := by
  obtain ⟨lf, hlf, elf⟩ := sim.autogen.last_frame_refines g (abs mods) hne
  have ht : (abs lf : AFrame).time = lf.time := rfl
  by_cases hle : lf.time ≤ f1
  · obtain ⟨g', ha, ea, hh', hfl', hb'⟩ := s2_add_frame h64 mods g
      { time := f1, pos := pos, actions := r2, key_up := true } hfl
    refine ⟨g', by simp [hlf, float.F64.le, hle, ha], ?_, s2_inv_add_frame g g' _ _ hI hr ea hh', hh', by omega, by omega, hb'⟩
    simp only [s2_lastS, s2_am_bind, elf, Except.bind, ht, hle, ite_true]
    exact ea
  · refine ⟨g, by simp [hlf, float.F64.le, hle], ?_, hI, rfl, by omega, by omega, rfl⟩
    simp only [s2_lastS, s2_am_bind, elf, Except.bind, ht, hle, ite_false]
    rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

/-- the part of `add_click_frames` after the prefix of `s2_acf_pre` (verbatim from the extraction) -/
def s2_acfTail (mods : Slice sim.mods.RateMod) (o : sim.playable.TopObj) (start_position : net.osutk.Vector2)
    (spinner_direction : F32) (stacked_end : net.osutk.Vector2) (start_ref end_ref : Usize) (f1 : F64) (b : Bool)
    (g3 : sim.autogen.G) (action1 : replay.frames.Action) :
    Result ((core.result.Result Unit sim.err.SimErr) × sim.autogen.G) := do
  let g4 ←
    sim.autogen.add_frame g3
      {
        time := o.h.start,
        pos := start_position,
        actions := start_ref,
        key_up := false
      }
  if b
  then
    let (r, g5) ←
      sim.autogen.spinner_click_frames mods g4 o.h start_position
        spinner_direction action1
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let a ← sim.autogen.last_frame g5
      let b1 ← float.F64.le a.time f1
      if b1
      then
        let g6 ←
          sim.autogen.add_frame g5
            { time := f1, pos := val, actions := end_ref, key_up := true }
        ok (core.result.Result.Ok (), g6)
      else ok (core.result.Result.Ok (), g5)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r1, g5)
  else
    let b1 ←
      sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq o.h.kind
        sim.playable.Kind.Slider
    if b1
    then
      let (r, g5) ←
        sim.autogen.slider_click_frames mods g4 o stacked_end action1
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let a ← sim.autogen.last_frame g5
        let b2 ← float.F64.le a.time f1
        if b2
        then
          let g6 ←
            sim.autogen.add_frame g5
              {
                time := f1,
                pos := stacked_end,
                actions := end_ref,
                key_up := true
              }
          ok (core.result.Result.Ok (), g6)
        else ok (core.result.Result.Ok (), g5)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr) residual
        ok (r1, g5)
    else
      let a ← sim.autogen.last_frame g4
      let b2 ← float.F64.le a.time f1
      if b2
      then
        let g5 ←
          sim.autogen.add_frame g4
            {
              time := f1,
              pos := stacked_end,
              actions := end_ref,
              key_up := true
            }
        ok (core.result.Result.Ok (), g5)
      else ok (core.result.Result.Ok (), g4)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net OsuModel.Sim OsuModel.Sim.AutoGen OsuModel.Replay

set_option maxHeartbeats 200000 in
theorem sim.autogen.add_click_frames_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (o : sim.playable.TopObj) (sp : net.osutk.Vector2) (dir : F32) (se : net.osutk.Vector2)
    (tn : Nat → String) (hI : s2_gInv g)
    (hsd : ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62)
    (hh : g.heap.val.length + 10000003 < Usize.max) (hfl : g.frames.val.length + 10000003 < 2^62) :
    ∃ r g', sim.autogen.add_click_frames mods g o sp dir se = ok (r, g') ∧
      s2_GR id g' r (addClickFrames (topS tn o) (v2S sp) dir (v2S se) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.button_index = g.button_index ∧ 0 < g'.frames.val.length ∧
        g'.heap.val.length ≤ g.heap.val.length + 10000003 ∧
        g'.frames.val.length ≤ g.frames.val.length + 10000003 ∧ s2_gInv g') := by
  obtain ⟨r1, r2, g3, a3, hpre, hI3, hb3, hf3, hh3, hr1, hr2, hspec⟩ :=
    s2_acf_pre h64 mods g o tn sp se dir hI (by omega) (by omega)
  have e : sim.autogen.add_click_frames mods g o sp dir se = s2_acfTail mods o sp dir se r1 r2
      (o.h.end_time + keyUpDelay + (if (kindS o.h.kind == Kind.spinner) = true then 1 else 0))
      (kindS o.h.kind == Kind.spinner) g3 a3 := by
    rw [← hpre (T := s2_acfTail mods o sp dir se)]; rfl
  rw [e, hspec (abs mods), s2_acfJP_eq]
  obtain ⟨g4, ha4, ea4, hh4, hf4, hb4⟩ := s2_add_frame h64 mods g3 { time := o.h.start, pos := sp, actions := r1, key_up := false } (by omega)
  have hI4 := s2_inv_add_frame g3 g4 _ _ hI3 hr1 ea4 hh4
  have ea4' : addFrame ⟨(topS tn o).h.start, v2S sp, r1.val, false⟩ (abs mods) (abs g3) = .ok ((), abs g4) := ea4
  have hk' : (topS tn o).h.kind = kindS o.h.kind := rfl
  have hst : (topS tn o).h.stacked = abs o.h.stacked := rfl
  have hsl : (topS tn o).slider = o.slider.map abs := rfl
  have hhs : (topS tn o).h.start = o.h.start := rfl
  have hhe : (topS tn o).h.endTime = o.h.end_time := rfl
  simp only [s2_am_bind, ea4', Except.bind, hk', hhe]
  have hbr : ∀ {α : Type} (x : α), core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x : core.result.Result α sim.err.SimErr) = ok (core.ops.control_flow.ControlFlow.Continue x) := fun _ => rfl
  generalize (o.h.end_time + keyUpDelay + if (kindS o.h.kind == Kind.spinner) = true then 1 else 0) = F
  cases hk : o.h.kind
  case Spinner =>
    have hkb : (kindS sim.playable.Kind.Spinner == Kind.spinner) = true := rfl
    obtain ⟨r5, g5, h5, e5, b5⟩ := s2_spinner_click_frames h64 mods g4 o.h sp dir a3 (by rw [hh4]; omega) (by omega)
    have hsS : s2_spinClickS (topS tn o).h.start o.h.end_time (v2S sp) dir (s2_actS a3) =
        s2_spinClickS o.h.start o.h.end_time (v2S sp) dir (s2_actS a3) := rfl
    cases r5 with
    | Err e =>
      refine ⟨.Err e, g5, ?_, ?_, fun _ h => by cases h⟩
      · simp [s2_acfTail, hkb, ha4, h5, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := e5
        refine ⟨m, ?_⟩
        simp only [kindS, hsS, s2_am_bind, hm, Except.bind]
    | Ok v =>
      obtain ⟨bw, b0, b1, b2, b3, b4⟩ := b5 v rfl
      obtain ⟨g6, h6, e6, hI6, hh6, hf6, hf6', hb6⟩ := s2_last h64 mods g5
        F
        v r2 (b4 hI4) b3 (by omega) (by rw [hh4] at b0; omega)
      refine ⟨.Ok (), g6, ?_, ?_, fun _ _ => ⟨by rw [hb6, bw, hb4, hb3], by omega, by rw [hh6]; rw [hh4] at b1; omega, by omega, hI6⟩⟩
      · simp [s2_acfTail, ha4, h5, hkb, hbr]
        simpa using h6
      · simp only [s2_GR] at e5
        simp only [kindS, hsS, s2_am_bind, e5, Except.bind, s2_GR]
        exact e6
  case Slider =>
    have hkb : (kindS sim.playable.Kind.Slider == Kind.spinner) = false := rfl
    have hkl : (kindS sim.playable.Kind.Slider == kindS sim.playable.Kind.Slider) = true := rfl
    obtain ⟨r5, g5, h5, e5, b5⟩ := s2_slider_click_frames h64 mods g4 o se a3 hsd (by rw [hh4]; omega) (by omega)
    have hsL : s2_sliderClickS (topS tn o).h.stacked (topS tn o).h.start o.h.end_time (topS tn o).slider (v2S se) (s2_actS a3) =
        s2_sliderClickS (abs o.h.stacked) o.h.start o.h.end_time (o.slider.map abs) (v2S se) (s2_actS a3) := rfl
    cases r5 with
    | Err e =>
      refine ⟨.Err e, g5, ?_, ?_, fun _ h => by cases h⟩
      · simp [s2_acfTail, hkb, hk, hkl, ha4, h5, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := e5
        refine ⟨m, ?_⟩
        simp only [kindS, hsL, s2_am_bind, hm, Except.bind]
    | Ok v =>
      obtain ⟨bw, b0, b1, b2, b3, b4⟩ := b5 v rfl
      obtain ⟨g6, h6, e6, hI6, hh6, hf6, hf6', hb6⟩ := s2_last h64 mods g5
        F
        se r2 (b4 hI4) b3 (by omega) (by rw [hh4] at b0; omega)
      refine ⟨.Ok (), g6, ?_, ?_, fun _ _ => ⟨by rw [hb6, bw, hb4, hb3], by omega, by rw [hh6]; rw [hh4] at b1; omega, by omega, hI6⟩⟩
      · simp [s2_acfTail, ha4, h5, hkb, hk, hkl, hbr]
        simpa using h6
      · simp only [s2_GR] at e5
        simp only [kindS, hsL, s2_am_bind, e5, Except.bind, s2_GR]
        exact e6
  all_goals
    obtain ⟨g6, h6, e6, hI6, hh6, hf6, hf6', hb6⟩ := s2_last h64 mods g4
      F
      se r2 hI4 (by omega) (by omega) (by rw [hh4]; omega)
    have hkb : (kindS o.h.kind == Kind.spinner) = false := by rw [hk]; rfl
    have hkl : (kindS o.h.kind == kindS sim.playable.Kind.Slider) = false := by rw [hk]; rfl
    rw [hk] at hkb hkl
    refine ⟨.Ok (), g6, ?_, ?_, fun _ _ => ⟨by rw [hb6, hb4, hb3], by omega, by rw [hh6, hh4]; omega, by omega, hI6⟩⟩
    · simp [s2_acfTail, ha4, hk, hkb, hkl]
      simpa using h6
    · simp only [kindS, s2_GR]
      exact e6
end OsuProofs
