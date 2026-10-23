/-
`sim::autogen` (Rust, OsuAutoGenerator for Autopilot) refines `OsuModel.Sim.AutoGen`. The generator monad
`M = ReaderT (List RateMod) (StateT G (Except String))` is evaluated at the mods and a state; `Result<_, SimErr>`
results are related to the spec's `Except` by `s2_optRel` / `s2_eo` (both reject, or both succeed with the same value).
AFrame/G ↦ `s2_aframeS`/`s2_gS`.
-/
import OsuProofs.Sim2.Transforms
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

def s2_aframeS (f : sim.autogen.AFrame) : OsuModel.Sim.AFrame :=
  { time := f.time, pos := v2S f.pos, actions := f.actions.val, keyUp := f.key_up }
instance s2_absAFrame : AbsTo sim.autogen.AFrame OsuModel.Sim.AFrame := ⟨s2_aframeS⟩
def s2_gS (g : sim.autogen.G) : OsuModel.Sim.AutoGen.G :=
  { frames := (g.frames.val.map s2_aframeS).toArray, buttonIndex := g.button_index.val,
    heap := (g.heap.val.map s2_actListS).toArray }
instance s2_absG : AbsTo sim.autogen.G OsuModel.Sim.AutoGen.G := ⟨s2_gS⟩

@[simp] theorem s2_ag_consts : sim.autogen.F64_0 = ok (0 : F64) ∧ sim.autogen.F64_1 = ok (1 : F64) := by
  simp [sim.autogen.F64_0, sim.autogen.F64_1]

theorem sim.autogen.rate_mod_apply_refines (m : sim.mods.RateMod) (time rate : F64) :
    sim.autogen.rate_mod_apply m time rate = ok (exceptI id (OsuModel.Sim.RateMod.apply (abs m) time rate)) := by
  cases m with
  | Speed s => simp [sim.autogen.rate_mod_apply, OsuModel.Sim.RateMod.apply, abs, float.F64.mul, exceptI, pure, Except.pure]
  | Adaptive i => simp [sim.autogen.rate_mod_apply, OsuModel.Sim.RateMod.apply, abs, float.F64.mul, exceptI, pure, Except.pure]
  | TimeRamp i f b ft =>
    simp only [sim.autogen.rate_mod_apply, OsuModel.Sim.RateMod.apply, abs, float.F64.sub, float.F64.div, s2_ag_consts,
      net.max_refines, bind_ok, net.mathops.f64_clamp_refines]
    cases hc : F64.clamp ((time - b) / F64.max 1 (ft - b)) 0 1 with
    | error e => simp [exceptI, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind]
    | ok c =>
      simp only [exceptI, id, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, float.F64.mul, float.F64.add,
        net.mathops.f64_round_digits_refines]
      have h2 : (2#i64 : I64).val = 2 := rfl
      rw [h2]
      cases hr : F64.roundDigits (i + (f - i) * c) 2 with
      | error e => simp [exceptI, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          Bind.bind, Except.bind, hr]
      | ok v => simp [exceptI, Bind.bind, Except.bind, pure, Except.pure, hr]

theorem sim.autogen.lift_n_refines (e : core.result.Result F64 net.basic.NetExn) :
    ∃ r, sim.autogen.lift_n e = ok r ∧ (match e with | .Ok v => r = .Ok v | .Err _ => ∃ x, r = .Err x) := by
  cases e <;> simp [sim.autogen.lift_n]

theorem sim.autogen.circle_position_refines (t radius : F64) :
    ∃ r, sim.autogen.circle_position t radius = ok r ∧ OsuModel.Sim.AutoGen.circlePosition t radius = abs r := by
  simp [sim.autogen.circle_position, OsuModel.Sim.AutoGen.circlePosition, float.F64.cos, float.F64.sin, float.F64.mul,
    float.F64.to_f32, net.osutk.v2, abs, v2S]

theorem sim.autogen.spinner_centre_refines :
    ∃ r, sim.autogen.spinner_centre = ok r ∧ OsuModel.Sim.AutoGen.spinnerCentre = abs r := by
  simp [sim.autogen.spinner_centre, OsuModel.Sim.AutoGen.spinnerCentre, float.F32.div, net.osutk.v2, abs, v2S]
  exact ⟨by rw [show (512.0 : F32) = 512 by decide +kernel, show (2.0 : F32) = 2 by decide +kernel],
    by rw [show (384.0 : F32) = 384 by decide +kernel, show (2.0 : F32) = 2 by decide +kernel]⟩

theorem sim.autogen.single_refines (a : replay.frames.Action) :
    ∃ r, sim.autogen.single a = ok r ∧ [s2_actS a] = s2_actListS r ∧ r.len.val ≤ 3 := by
  obtain ⟨r, h1, h2, h3, _⟩ := replay.frames.act_push_refines replay.frames.ACTLIST_EMPTY a (by simp [s2_empty_val.2])
  refine ⟨r, by simpa [sim.autogen.single] using h1, by rw [show s2_actListS r = _ from h2, s2_abs_empty]; rfl, by rw [h3]; simp [s2_empty_val.2]⟩

theorem sim.autogen.of_vec_refines (p : sim.basic.Vec2) :
    ∃ r, sim.autogen.of_vec p = ok r ∧ OsuModel.Sim.AutoGen.ofVec (abs p) = abs r := by
  simp [sim.autogen.of_vec, OsuModel.Sim.AutoGen.ofVec, net.osutk.v2, abs, v2S]

open OsuModel.Sim.AutoGen in
section
@[simp] theorem s2_am_read_bind {α} (f : List OsuModel.Sim.RateMod → M α) (C : List OsuModel.Sim.RateMod) (S : G) :
    ((read : M (List OsuModel.Sim.RateMod)) >>= f) C S = f C C S := rfl
@[simp] theorem s2_am_get_bind {α} (f : G → M α) (C : List OsuModel.Sim.RateMod) (S : G) :
    ((get : M G) >>= f) C S = f S C S := rfl
@[simp] theorem s2_am_pure {α} (a : α) (C : List OsuModel.Sim.RateMod) (S : G) : (pure a : M α) C S = .ok (a, S) := rfl
@[simp] theorem s2_am_bind {α β} (m : M α) (f : α → M β) (C : List OsuModel.Sim.RateMod) (S : G) :
    (m >>= f) C S = (m C S).bind (fun p => f p.1 C p.2) := rfl
@[simp] theorem s2_am_set (S' : G) (C : List OsuModel.Sim.RateMod) (S : G) : (set S' : M PUnit) C S = .ok (PUnit.unit, S') := rfl
@[simp] theorem s2_am_modify (g : G → G) (C : List OsuModel.Sim.RateMod) (S : G) :
    (modify g : M PUnit) C S = .ok (PUnit.unit, g S) := rfl
@[simp] theorem s2_am_throw {α} (e : String) (C : List OsuModel.Sim.RateMod) (S : G) : (throw e : M α) C S = .error e := rfl
@[simp] theorem s2_am_liftN {α} (e : Except NetExn α) (C : List OsuModel.Sim.RateMod) (S : G) :
    liftN e C S = (match e with | .ok v => .ok (v, S) | .error x => .error s!"lazer would throw: {repr x}") := by
  cases e <;> rfl
end

/-- `applyModsToRate` as an `Option` fold (`none` = a rejected `RateMod.apply`) -/
def s2_amr (time : F64) : List OsuModel.Sim.RateMod → F64 → Option F64
  | [], r => some r
  | m :: t, r => match OsuModel.Sim.RateMod.apply m time r with
    | .ok r' => s2_amr time t r'
    | .error _ => none

theorem s2_amr_loop (time : F64) (mods : List OsuModel.Sim.RateMod) (g : OsuModel.Sim.AutoGen.G) :
    ∀ (l : List OsuModel.Sim.RateMod) (r : F64),
      s2_eo ((l.foldlM (fun b a => OsuModel.Sim.AutoGen.liftN (a.apply time b)) r : OsuModel.Sim.AutoGen.M F64) mods g)
        = (s2_amr time l r).map (·, g) := by
  intro l
  induction l with
  | nil => intro r; rfl
  | cons m t ih =>
    intro r
    rw [List.foldlM_cons]
    cases h : OsuModel.Sim.RateMod.apply m time r with
    | error e => simp [s2_amr, h, Except.bind, s2_eo]
    | ok r' =>
      have := ih r'
      simp [s2_amr, h, Except.bind] at this ⊢
      exact this

theorem s2_amr_spec (time rate : F64) (mods : List OsuModel.Sim.RateMod) (g : OsuModel.Sim.AutoGen.G) :
    s2_eo (((OsuModel.Sim.AutoGen.applyModsToRate time rate).run mods).run g) = (s2_amr time mods rate).map (·, g) := by
  unfold OsuModel.Sim.AutoGen.applyModsToRate
  simp only [ReaderT.run, StateT.run]
  rw [← s2_amr_loop time mods g mods rate]
  simp [Except.bind]
  have hr : (read : OsuModel.Sim.AutoGen.M (List OsuModel.Sim.RateMod)) mods g = .ok (mods, g) := rfl
  simp only [hr]

/-- Rust `Result<F64, SimErr>` vs an `Option` model -/
def s2_optRel (o : Option F64) (r : core.result.Result F64 sim.err.SimErr) : Prop :=
  match o, r with
  | some a, .Ok b => a = b
  | none, .Err _ => True
  | _, _ => False

theorem s2_amr_rust (mods : Slice sim.mods.RateMod) (time : F64) :
    ∀ (n : Nat) (r : F64) (i : Usize), mods.val.length - i.val = n → i.val ≤ mods.val.length →
      ∃ x, sim.autogen.apply_mods_to_rate_loop mods time r i = ok x ∧
        s2_optRel (s2_amr time ((mods.val.drop i.val).map abs) r) x := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro r i hn hi
    have hge : ¬ i < Slice.len mods := by rw [slice_lt_len_iff]; omega
    refine ⟨.Ok r, ?_, ?_⟩
    · unfold sim.autogen.apply_mods_to_rate_loop; rw [loop_unfold]
      simp [sim.autogen.apply_mods_to_rate_loop.body, hge]
    · rw [List.drop_eq_nil_of_le (by omega)]; simp [s2_amr, s2_optRel]
  | succ n ih =>
    intro r i hn hi
    have hlt : i.val < mods.val.length := by omega
    have hlt' : i < Slice.len mods := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hdrop := List.drop_eq_getElem_cons hlt
    have happ := sim.autogen.rate_mod_apply_refines (mods.val[i.val]'hlt) time r
    cases ha : OsuModel.Sim.RateMod.apply (abs (mods.val[i.val]'hlt)) time r with
    | error e =>
      refine ⟨.Err (sim.err.SimErr.Net (exnI e)), ?_, ?_⟩
      · unfold sim.autogen.apply_mods_to_rate_loop; rw [loop_unfold]
        simp [sim.autogen.apply_mods_to_rate_loop.body, hlt', slice_index_ok _ _ hlt, happ, ha, exceptI,
          sim.autogen.lift_n, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · rw [hdrop, List.map_cons]; simp only [s2_amr, ha]; trivial
    | ok r' =>
      obtain ⟨x, hx, ex⟩ := ih r' i1 (by omega) (by omega)
      refine ⟨x, ?_, ?_⟩
      · have hb : sim.autogen.apply_mods_to_rate_loop.body mods time r i = ok (.cont (r', i1)) := by
          simp [sim.autogen.apply_mods_to_rate_loop.body, hlt', slice_index_ok _ _ hlt, happ, ha, exceptI,
            sim.autogen.lift_n, core.result.Result.Insts.CoreOpsTry.branch, hi1]
        unfold sim.autogen.apply_mods_to_rate_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.autogen.apply_mods_to_rate_loop at hx; exact hx
      · rw [hdrop]; simp only [List.map_cons, s2_amr, ha]; rw [hi1v] at ex; exact ex

theorem sim.autogen.apply_mods_to_rate_refines (mods : Slice sim.mods.RateMod) (time rate : F64) (g : sim.autogen.G) :
    ∃ x, sim.autogen.apply_mods_to_rate mods time rate = ok x ∧
      s2_optRel ((s2_eo ((((OsuModel.Sim.AutoGen.applyModsToRate time rate).run (abs mods)).run (abs g)))).map (·.1)) x := by
  obtain ⟨x, hx, ex⟩ := s2_amr_rust mods time mods.val.length rate 0#usize (by simp) (by simp)
  refine ⟨x, hx, ?_⟩
  rw [s2_amr_spec]
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at ex
  have ea : (abs mods : List OsuModel.Sim.RateMod) = mods.val.map abs := rfl
  rw [ea]; cases h : s2_amr time (mods.val.map abs) rate <;> rw [h] at ex <;> simpa using ex

theorem sim.autogen.get_frame_delay_refines (mods : Slice sim.mods.RateMod) (time : F64) (g : sim.autogen.G) :
    ∃ x, sim.autogen.get_frame_delay mods time = ok x ∧
      s2_optRel ((s2_eo ((((OsuModel.Sim.AutoGen.getFrameDelay time).run (abs mods)).run (abs g)))).map (·.1)) x := by
  have hs : sim.autogen.SIXTY_FRAME = ok (1000.0 / 60 : F64) := by
    unfold sim.autogen.SIXTY_FRAME; simp; decide +kernel
  obtain ⟨x, hx, ex⟩ := sim.autogen.apply_mods_to_rate_refines mods time (1000.0 / 60) g
  exact ⟨x, by simp [sim.autogen.get_frame_delay, hs, hx], ex⟩

@[simp] theorem s2_am_map {α β} (f : α → β) (m : OsuModel.Sim.AutoGen.M α) (C : List OsuModel.Sim.RateMod)
    (S : OsuModel.Sim.AutoGen.G) : (f <$> m) C S = (m C S).map (fun p => (f p.1, p.2)) := by
  show (do let a ← m C S; pure (f a.1, a.2)) = _
  cases m C S <;> rfl

/-- `applyModsToTimeDelta` as an `Option` fold -/
def s2_amd (start : F64) : List OsuModel.Sim.RateMod → F64 → Option F64
  | [], d => some d
  | m :: t, d => match OsuModel.Sim.RateMod.apply m start 1 with
    | .ok r => s2_amd start t (d / r)
    | .error _ => none

theorem s2_amd_loop (start : F64) (mods : List OsuModel.Sim.RateMod) (g : OsuModel.Sim.AutoGen.G) :
    ∀ (l : List OsuModel.Sim.RateMod) (d : F64),
      s2_eo ((l.foldlM (fun b a => do let x ← OsuModel.Sim.AutoGen.liftN (a.apply start 1); pure (b / x)) d :
        OsuModel.Sim.AutoGen.M F64) mods g) = (s2_amd start l d).map (·, g) := by
  intro l
  induction l with
  | nil => intro d; rfl
  | cons m t ih =>
    intro d
    rw [List.foldlM_cons]
    cases h : OsuModel.Sim.RateMod.apply m start 1 with
    | error e => simp [s2_amd, h, Except.bind, s2_eo, Except.map]
    | ok r' =>
      have := ih (d / r')
      simp [s2_amd, h, Except.bind, Except.map] at this ⊢
      exact this

theorem s2_amd_spec (start endT : F64) (mods : List OsuModel.Sim.RateMod) (g : OsuModel.Sim.AutoGen.G) :
    s2_eo (((OsuModel.Sim.AutoGen.applyModsToTimeDelta start endT).run mods).run g) = (s2_amd start mods (endT - start)).map (·, g) := by
  unfold OsuModel.Sim.AutoGen.applyModsToTimeDelta
  simp only [ReaderT.run, StateT.run]
  rw [← s2_amd_loop start mods g mods (endT - start)]
  simp [Except.bind]
  have hr : (read : OsuModel.Sim.AutoGen.M (List OsuModel.Sim.RateMod)) mods g = .ok (mods, g) := rfl
  simp only [hr]

theorem s2_amd_rust (mods : Slice sim.mods.RateMod) (time : F64) :
    ∀ (n : Nat) (r : F64) (i : Usize), mods.val.length - i.val = n → i.val ≤ mods.val.length →
      ∃ x, sim.autogen.apply_mods_to_time_delta_loop mods time r i = ok x ∧
        s2_optRel (s2_amd time ((mods.val.drop i.val).map abs) r) x := by
  have hmax := mods.property
  intro n
  induction n with
  | zero =>
    intro r i hn hi
    have hge : ¬ i < Slice.len mods := by rw [slice_lt_len_iff]; omega
    refine ⟨.Ok r, ?_, ?_⟩
    · unfold sim.autogen.apply_mods_to_time_delta_loop; rw [loop_unfold]
      simp [sim.autogen.apply_mods_to_time_delta_loop.body, hge]
    · rw [List.drop_eq_nil_of_le (by omega)]; simp [s2_amd, s2_optRel]
  | succ n ih =>
    intro r i hn hi
    have hlt : i.val < mods.val.length := by omega
    have hlt' : i < Slice.len mods := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hdrop := List.drop_eq_getElem_cons hlt
    have happ := sim.autogen.rate_mod_apply_refines (mods.val[i.val]'hlt) time 1
    cases ha : OsuModel.Sim.RateMod.apply (abs (mods.val[i.val]'hlt)) time 1 with
    | error e =>
      refine ⟨.Err (sim.err.SimErr.Net (exnI e)), ?_, ?_⟩
      · unfold sim.autogen.apply_mods_to_time_delta_loop; rw [loop_unfold]
        simp [sim.autogen.apply_mods_to_time_delta_loop.body, hlt', slice_index_ok _ _ hlt, happ, ha, exceptI, s2_ag_consts,
          sim.autogen.lift_n, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · rw [hdrop, List.map_cons]; simp only [s2_amd, ha]; trivial
    | ok r' =>
      obtain ⟨x, hx, ex⟩ := ih (r / r') i1 (by omega) (by omega)
      refine ⟨x, ?_, ?_⟩
      · have hb : sim.autogen.apply_mods_to_time_delta_loop.body mods time r i = ok (.cont (r / r', i1)) := by
          simp [sim.autogen.apply_mods_to_time_delta_loop.body, hlt', slice_index_ok _ _ hlt, happ, ha, exceptI, s2_ag_consts,
            sim.autogen.lift_n, core.result.Result.Insts.CoreOpsTry.branch, hi1, float.F64.div]
        unfold sim.autogen.apply_mods_to_time_delta_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.autogen.apply_mods_to_time_delta_loop at hx; exact hx
      · rw [hdrop]; simp only [List.map_cons, s2_amd, ha]; rw [hi1v] at ex; exact ex


theorem sim.autogen.apply_mods_to_time_delta_refines (mods : Slice sim.mods.RateMod) (start endT : F64) (g : sim.autogen.G) :
    ∃ x, sim.autogen.apply_mods_to_time_delta mods start endT = ok x ∧
      s2_optRel ((s2_eo ((((OsuModel.Sim.AutoGen.applyModsToTimeDelta start endT).run (abs mods)).run (abs g)))).map (·.1)) x := by
  obtain ⟨x, hx, ex⟩ := s2_amd_rust mods start mods.val.length (endT - start) 0#usize (by simp) (by simp)
  refine ⟨x, by simp [sim.autogen.apply_mods_to_time_delta, float.F64.sub, hx], ?_⟩
  rw [s2_amd_spec]
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at ex
  have ea : (abs mods : List OsuModel.Sim.RateMod) = mods.val.map abs := rfl
  rw [ea]; cases h : s2_amd start (mods.val.map abs) (endT - start) <;> rw [h] at ex <;> simpa using ex

end OsuProofs
