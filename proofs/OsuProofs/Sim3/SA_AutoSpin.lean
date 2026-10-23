/-
sim3a (D37): the spinner branch of `OsuAutoGenerator.addClickFrames` (Autopilot frame generation, Rust
`sim::autogen::spinner_frame_step` / `spinner_frames`) refines the spinner `while` loop of
`OsuModel.Sim.AutoGen.addClickFrames`. One iteration = `s3aSpinStepS`. `add_frame` (sim2's slice; binary-search
insertion) enters as the hypothesis `s3aAddFrameOk`; `new_list` is proved here (`s3a_new_list`).
-/
import OsuProofs.Sim2.AutoGen
import OsuProofs.Sim3.SA_Track
import OsuProofs.Sim3.SA_Spin
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- one iteration of the spinner frame loop of `addClickFrames` (after the fuel decrement) -/
def s3aSpinStepS (angle0 : F32) (prev next : F64) (dir : F32) (action : OsuModel.Replay.Action) :
    OsuModel.Sim.AutoGen.M (F32 × F64) := do
  let t := (← OsuModel.Sim.AutoGen.applyModsToTimeDelta prev next) * F32.toF64 dir
  let angle := angle0 + F64.toF32 t * OsuModel.Sim.AutoGen.radsPerMillisecond
  let pos := OsuModel.Sim.AutoGen.spinnerCentre +
    OsuModel.Sim.AutoGen.circlePosition (F32.toF64 angle) (F32.toF64 OsuModel.Sim.AutoGen.spinRadius)
  OsuModel.Sim.AutoGen.addFrame
    { time := F64.ofInt32 (F64.toInt32 next), pos, actions := ← OsuModel.Sim.AutoGen.newList [action] }
  return (angle, next + (← OsuModel.Sim.AutoGen.getFrameDelay next))

/-- `add_frame` refines `addFrame` (hypothesis; sim2's slice) -/
def s3aAddFrameOk (mods : Slice sim.mods.RateMod) : Prop :=
  ∀ (g : sim.autogen.G) (f : sim.autogen.AFrame), ∃ g', sim.autogen.add_frame g f = ok g' ∧
    OsuModel.Sim.AutoGen.addFrame (abs f) (abs mods) (abs g) = .ok ((), abs g') ∧ g'.heap = g.heap

theorem s3a_new_list (mods : List OsuModel.Sim.RateMod) (g : sim.autogen.G) (xs : replay.frames.ActList)
    (h : g.heap.val.length < Usize.max) :
    ∃ k g', sim.autogen.new_list g xs = ok (k, g') ∧ k.val = g.heap.val.length ∧
      OsuModel.Sim.AutoGen.newList (s2_actListS xs) mods (abs g) = .ok (k.val, abs g') ∧
      g'.heap.val.length = g.heap.val.length + 1 ∧ g'.frames = g.frames := by
  refine ⟨alloc.vec.Vec.len g.heap, { g with heap := vpush g.heap xs h }, ?_, by simp, ?_, by simp, rfl⟩
  · simp [sim.autogen.new_list, vec_push_ok _ _ h]
  · simp only [OsuModel.Sim.AutoGen.newList, s2_am_bind, s2_am_get_bind]
    show Except.ok _ = _
    simp [abs, s2_gS]

theorem s3a_eo_ok {α : Type} {E : Except String α} {p : α} (h : s2_eo E = some p) : E = .ok p := by
  cases E <;> simp_all [s2_eo]
theorem s3a_eo_none {α : Type} {E : Except String α} (h : s2_eo E = none) : ∃ m, E = .error m := by
  cases E <;> simp_all [s2_eo]

/-- `applyModsToTimeDelta` at any spec state: the Rust value, the state unchanged -/
theorem s3a_amd_eval (mods : Slice sim.mods.RateMod) (start endT : F64) (S : OsuModel.Sim.AutoGen.G) :
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
    | Err e => exact s3a_eo_none hs
  | some v => rw [h] at ex hs; cases x with
    | Ok w => simp only [s2_optRel] at ex; subst ex; exact s3a_eo_ok hs
    | Err e => simp [s2_optRel] at ex

theorem s3a_fd_eval (mods : Slice sim.mods.RateMod) (time : F64) (S : OsuModel.Sim.AutoGen.G) :
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
    | Err e => exact s3a_eo_none hs
  | some v => rw [h] at ex hs; cases x with
    | Ok w => simp only [s2_optRel] at ex; subst ex; exact s3a_eo_ok hs
    | Err e => simp [s2_optRel] at ex

@[simp] theorem s3a_ag_rads : sim.autogen.RADS_PER_MILLISECOND = ok OsuModel.Sim.AutoGen.radsPerMillisecond := by
  simp [sim.autogen.RADS_PER_MILLISECOND, OsuModel.Sim.AutoGen.radsPerMillisecond, float.F32.from_bits]
@[simp] theorem s3a_ag_spinr : sim.autogen.SPIN_RADIUS = ok OsuModel.Sim.AutoGen.spinRadius := by
  simp [sim.autogen.SPIN_RADIUS, OsuModel.Sim.AutoGen.spinRadius]; decide +kernel

/-- Rust `Result<T, SimErr>` + generator state vs the spec `M` evaluation -/
def s3aGR {α β : Type} (f : α → β) (g' : sim.autogen.G) :
    core.result.Result α sim.err.SimErr → Except String (β × OsuModel.Sim.AutoGen.G) → Prop
  | .Ok v, e => e = .ok (f v, abs g')
  | .Err _, e => ∃ m, e = .error m

theorem sim.autogen.spinner_frame_step_refines (mods : Slice sim.mods.RateMod) (g : sim.autogen.G) (angle0 : F32)
    (prev next : F64) (dir : F32) (action : replay.frames.Action) (hA : s3aAddFrameOk mods)
    (hh : g.heap.val.length < Usize.max) :
    ∃ r g', sim.autogen.spinner_frame_step mods g angle0 prev next dir action = ok (r, g') ∧
      s3aGR id g' r (s3aSpinStepS angle0 prev next dir (s2_actS action) (abs mods) (abs g)) ∧
      (∀ v, r = .Ok v → g'.heap.val.length = g.heap.val.length + 1) := by
  obtain ⟨cen, hcen, ecen⟩ := sim.autogen.spinner_centre_refines
  obtain ⟨x, hx, ex⟩ := s3a_amd_eval mods prev next (abs g)
  unfold sim.autogen.spinner_frame_step
  simp only [hcen, hx, bind_ok]
  cases x with
  | Err e =>
    refine ⟨.Err e, g, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun _ h => by cases h⟩
    obtain ⟨m, hm⟩ := ex
    exact ⟨m, by unfold s3aSpinStepS; simp only [s2_am_bind, hm]; rfl⟩
  | Ok v =>
    let angle : F32 := angle0 + F64.toF32 (v * F32.toF64 dir) * OsuModel.Sim.AutoGen.radsPerMillisecond
    obtain ⟨cp, hcp, ecp⟩ := sim.autogen.circle_position_refines (F32.toF64 angle) (F32.toF64 OsuModel.Sim.AutoGen.spinRadius)
    obtain ⟨al, hal, eal, hall⟩ := sim.autogen.single_refines action
    obtain ⟨r1, g1, hr1, hr1v, er1, hg1h, hg1f⟩ := s3a_new_list (abs mods) g al hh
    let f : sim.autogen.AFrame := ⟨F64.ofInt (IScalar.cast .I64 (i32I (F64.toInt32 next))).val,
      v2I (OsuTK.Vector2.add (v2S cen) (v2S cp)), r1, false⟩
    obtain ⟨g2, hg2, eg2, hg2h⟩ := hA g1 f
    have hf : (abs f : OsuModel.Sim.AFrame) = OsuModel.Sim.AFrame.mk (F64.ofInt32 (F64.toInt32 next))
        (OsuModel.Sim.AutoGen.spinnerCentre + OsuModel.Sim.AutoGen.circlePosition (F32.toF64 angle)
          (F32.toF64 OsuModel.Sim.AutoGen.spinRadius)) r1.val false := by
      show s2_aframeS f = _
      simp only [s2_aframeS, f, s3a_cast_i32I, F64.ofInt32, v2S_I, ecen, ecp]
      rfl
    obtain ⟨y, hy, ey⟩ := s3a_fd_eval mods next (abs g2)
    have hi32 : ∀ x : Int32, (⟨x.toBitVec⟩ : I32) = i32I x := fun _ => rfl
    have hg2' := hg2
    simp only [f] at hg2'
    have hg3 := hg2'
    have ecast : (IScalar.cast .I64 (i32I (F64.toInt32 next))).val = ((i32I (F64.toInt32 next)).val : Int) := by
      rw [s3a_cast_i32I, ← i32S_toInt, i32S_i32I]
    rw [ecast] at hg3
    have hcp' := hcp
    simp only [angle] at hcp'
    have hspec1 : (s3aSpinStepS angle0 prev next dir (s2_actS action)) (abs mods) (abs g) =
        (OsuModel.Sim.AutoGen.getFrameDelay next (abs mods) (abs g2)).bind (fun p => .ok ((angle, next + p.1), p.2)) := by
      unfold s3aSpinStepS
      simp only [s2_am_bind, ex, Except.bind, eal, er1]
      rw [← hf, eg2]
      rfl
    cases y with
    | Ok d =>
      refine ⟨.Ok (angle, next + d), g2, ?_, ?_, fun _ _ => by rw [hg2h, hg1h]⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, float.F32.to_f64, float.F64.mul, float.F64.to_f32,
          s3a_ag_rads, float.F32.mul, float.F32.add, s3a_ag_spinr, hcp', net.osutk.v2_add_refines, hal, hr1, bind_ok,
          float.F64.to_i32_sat, hi32, lift, float.F64.from_i64, hg2', hy, float.F64.add]
        first
          | (split; rename_i a b hab; simp only [Prod.mk.injEq] at hab; obtain ⟨rfl, rfl⟩ := hab; simp only [hg2', bind_ok, angle]; done)
          | (unfold Bind.bind; simp only [hg2', bind_ok, angle]; done)
          | (rw [hg2']; simp only [bind_ok, angle]; done)
          | (simp [hg2', angle]; done)
          | (simp [hg2']; simp [hg3, angle]; done)
      · simp only [s3aGR, hspec1, ey, Except.bind]; rfl
    | Err e =>
      refine ⟨.Err e, g2, ?_, ?_, fun _ h => by cases h⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, float.F32.to_f64, float.F64.mul, float.F64.to_f32,
          s3a_ag_rads, float.F32.mul, float.F32.add, s3a_ag_spinr, hcp', net.osutk.v2_add_refines, hal, hr1, bind_ok,
          float.F64.to_i32_sat, hi32, lift, float.F64.from_i64, hg2', hy, float.F64.add]
        first
          | (split; rename_i a b hab; simp only [Prod.mk.injEq] at hab; obtain ⟨rfl, rfl⟩ := hab; simp only [hg2', bind_ok])
          | (simp [hg2']; simp [hg3])
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨m, hm⟩ := ey
        exact ⟨m, by simp only [hspec1, hm]; rfl⟩

/-- the spinner frame `while nextFrame < endT && fuel > 0` loop of `addClickFrames` as a fuel recursion over
`s3aSpinStepS`; returns `(fuel left, angle, previousFrame, nextFrame)` -/
def s3aSpinFramesS (endT : F64) (dir : F32) (action : OsuModel.Replay.Action) :
    Nat → F32 → F64 → F64 → OsuModel.Sim.AutoGen.M (Nat × F32 × F64 × F64)
  | 0, a, p, n => pure (0, a, p, n)
  | k + 1, a, p, n =>
    if n < endT then do
      let (a2, n2) ← s3aSpinStepS a p n dir action
      s3aSpinFramesS endT dir action k a2 n n2
    else pure (k + 1, a, p, n)

theorem s3a_spin_frames_loop (mods : Slice sim.mods.RateMod) (endT : F64) (dir : F32) (action : replay.frames.Action)
    (hA : s3aAddFrameOk mods) :
    ∀ k (fuel : U32) (g : sim.autogen.G) (a : F32) (p n : F64), fuel.val = k → g.heap.val.length + k < Usize.max →
      ∃ r g', sim.autogen.spinner_frames_loop mods g endT dir action fuel a p n = ok (r, g') ∧
        s3aGR (fun x : U32 × F32 × F64 × F64 => (x.1.val, x.2.1, x.2.2.1, x.2.2.2)) g' r
          (s3aSpinFramesS endT dir (s2_actS action) k a p n (abs mods) (abs g)) := by
  intro k
  induction k with
  | zero =>
    intro fuel g a p n hf hh
    have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hf])
    subst hf0
    refine ⟨.Ok (0#u32, a, p, n), g, ?_, rfl⟩
    unfold sim.autogen.spinner_frames_loop
    rw [loop_unfold]
    by_cases hlt : n < endT <;> simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt]
  | succ k ih =>
    intro fuel g a p n hf hh
    by_cases hlt : n < endT
    · have hpos : fuel > 0#u32 := by scalar_tac
      obtain ⟨f1, hf1, hf1v⟩ : ∃ f1 : U32, fuel - 1#u32 = ok f1 ∧ f1.val = k := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U32.sub_spec (x := fuel) (y := 1#u32) (by scalar_tac))
        exact ⟨z, hz, by simp at hzv; omega⟩
      obtain ⟨r, g1, hr, er, eh⟩ := sim.autogen.spinner_frame_step_refines mods g a p n dir action hA (by omega)
      cases r with
      | Err e =>
        refine ⟨.Err e, g1, ?_, ?_⟩
        · unfold sim.autogen.spinner_frames_loop
          rw [loop_unfold]
          simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · obtain ⟨m, hm⟩ := er
          refine ⟨m, ?_⟩
          simp only [s3aSpinFramesS, hlt, if_true, s2_am_bind, hm]
          rfl
      | Ok v =>
        obtain ⟨a2, n2⟩ := v
        have hg1 := eh _ rfl
        obtain ⟨r', g', hr', er'⟩ := ih f1 g1 a2 n n2 hf1v (by omega)
        refine ⟨r', g', ?_, ?_⟩
        · unfold sim.autogen.spinner_frames_loop
          rw [loop_unfold]
          have hb : sim.autogen.spinner_frames_loop.body mods endT dir action g fuel a p n =
              ok (.cont (g1, f1, a2, n, n2)) := by
            simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt, hpos, hf1, hr,
              core.result.Result.Insts.CoreOpsTry.branch]
          dsimp only; rw [hb]; simp only [bind_ok]
          unfold sim.autogen.spinner_frames_loop at hr'
          exact hr'
        · simp only [s3aGR] at er
          simp only [s3aSpinFramesS, hlt, if_true, s2_am_bind, er, Except.bind]
          exact er'
    · refine ⟨.Ok (fuel, a, p, n), g, ?_, ?_⟩
      · unfold sim.autogen.spinner_frames_loop
        rw [loop_unfold]
        simp [sim.autogen.spinner_frames_loop.body, float.F64.lt, hlt]
      · simp only [s3aGR, s3aSpinFramesS, hlt, if_false, hf]; rfl

theorem sim.autogen.spinner_frames_refines (mods : Slice sim.mods.RateMod) (g : sim.autogen.G) (angle0 : F32)
    (prev0 next0 endT : F64) (dir : F32) (action : replay.frames.Action) (hA : s3aAddFrameOk mods)
    (hh : g.heap.val.length + 10000000 < Usize.max) :
    ∃ r g', sim.autogen.spinner_frames mods g angle0 prev0 next0 endT dir action = ok (r, g') ∧
      s3aGR (fun x : U32 × F32 × F64 × F64 => (x.1.val, x.2.1, x.2.2.1, x.2.2.2)) g' r
        (s3aSpinFramesS endT dir (s2_actS action) 10000000 angle0 prev0 next0 (abs mods) (abs g)) :=
  s3a_spin_frames_loop mods endT dir action hA 10000000 10000000#u32 g angle0 prev0 next0 rfl hh

end OsuProofs
