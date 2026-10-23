/-
Sim3b part 2: rate mods of `playfieldUpdate` / `OnNewResult`: `dyn_rate_update` (`Sim.dynRateUpdate`: WU/WD
`ApplyToRate`, AS `DampContinuously`), `adaptive_speed_one` / `adaptive_speed_on_result` (`Sim.adaptiveSpeedOnResult`).
-/
import OsuProofs.Sim3.SB_Basic
import OsuProofs.Sim2.Mods
import OsuProofs.Sim.Processors
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- spec `elapsedNow` (generic) -/
theorem s3b_elapsedNow (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (hstep : S.k ≠ 0 → S.k - 1 < C.steps.size) :
    OsuModel.Sim.Sim.elapsedNow C S = .ok (if S.k = 0 then 0 else S.t - (C.steps[S.k - 1]!).time, S) := by
  unfold OsuModel.Sim.Sim.elapsedNow OsuModel.Sim.Sim.stepAt
  by_cases h0 : S.k = 0
  · simp [h0, OsuModel.Sim.Sim.st, Except.bind]
  · have hl := hstep h0
    simp [h0, OsuModel.Sim.Sim.st, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.getA, hl, Except.bind, Except.map,
      getElem!_def]

theorem s3b_ctxS_step_time (tn fo) (c : sim.state.Ctx) (i : Nat) (h : i < c.steps.val.length) :
    ((simCtxS tn fo c).steps[i]!).time = (c.steps.val[i]'h).time := by
  simp [simCtxS, abs, getElem!_def, h]

/-- Rust `elapsed` of `dynRateUpdate`/`magnetUpdate`/`processorsPhase` -/
theorem s3b_elapsed_rust (tn fo) (c : sim.state.Ctx) (s : sim.state.St)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) :
    (if s.k = 0#usize then (do let e ← sim.step.F64_0; ok (c, e))
      else do let i ← s.k - 1#usize; let s1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice schedule.Step) c.steps i
              let e ← float.F64.sub s.t s1.time; ok (c, e)) =
      ok (c, if s.k.val = 0 then 0 else s.t - ((simCtxS tn fo c).steps[s.k.val - 1]!).time) := by
  by_cases h0 : s.k.val = 0
  · have : s.k = 0#usize := by scalar_tac
    simp [this, h0, sim.step.F64_0]
  · have : s.k ≠ 0#usize := by intro h; apply h0; rw [h]; rfl
    have hl := hstep h0
    obtain ⟨i, hi, hiv, _⟩ := eq_ok_of_spec (UScalar.sub_spec (x := s.k) (y := 1#usize) (by simp; omega))
    have hi' : i.val < c.steps.val.length := by rw [hiv]; simpa using hl
    rw [s3b_ctxS_step_time tn fo c _ hl]
    have e1 : i.val = s.k.val - 1 := by rw [hiv]; rfl
    simp [this, h0, hi, vec_index_eq _ _ hi', vec_index_usize_ok _ _ hi', float.F64.sub, e1]

instance s3b_inhDynRate : Inhabited sim.mods.DynRate := ⟨.Adaptive 0⟩

def s3b_isAd : sim.mods.DynRate → Bool
  | .Adaptive _ => true
  | .TimeRamp .. => false

/-- the AS index loop of `dyn_rate_update` = the number of AS mods before `k` -/
theorem s3b_dyn_ai_loop (v : alloc.vec.Vec sim.mods.DynRate) (k : Usize) (hk : k.val ≤ v.val.length) :
    ∃ ai : Usize, sim.step.dyn_rate_update_loop v k 0#usize 0#usize = ok ai ∧
      ai.val = ((v.val.take k.val).filter s3b_isAd).length := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen' (fun x => sim.step.dyn_rate_update_loop.body v k x.1 x.2) (·.2)
    k.val (by have := v.property; omega)
    (fun x => x.1.val ≤ x.2.val) (fun x => x.1.val)
    (fun j a => if s3b_isAd ((v.val.take k.val)[j]!) then a + 1 else a) (fun y a => y.val = a)
    (by
      rintro ⟨ai, j⟩ hI hj j1 hj1 hj1v
      simp only at hI hj hj1 hj1v ⊢
      have hjv : j.val < v.val.length := by omega
      have hjk : j < k := by scalar_tac
      have htk : (v.val.take k.val)[j.val]! = v.val[j.val]'hjv := by
        simp [getElem!_def, List.getElem?_take, hj, hjv]
      cases hd : v.val[j.val]'hjv with
      | TimeRamp a b c d =>
        refine ⟨(ai, j1), ?_, rfl, ?_, ?_⟩
        · simp [sim.step.dyn_rate_update_loop.body, hjk, vec_index_eq _ _ hjv, hd, hj1]
        · simp [htk, hd, s3b_isAd]
        · simp only; omega
      | Adaptive a =>
        obtain ⟨a1, ha1, ha1v⟩ := usize_add_one ai (by have := v.property; scalar_tac)
        refine ⟨(a1, j1), ?_, rfl, ?_, ?_⟩
        · simp [sim.step.dyn_rate_update_loop.body, hjk, vec_index_eq _ _ hjv, hd, hj1, ha1]
        · simp [htk, hd, s3b_isAd, ha1v]
        · simp only; omega)
    (by
      rintro ⟨ai, j⟩ _ hge
      simp only at hge
      have : ¬ j < k := by intro h; have : j.val < k.val := h; omega
      exact ⟨ai, by simp only [sim.step.dyn_rate_update_loop.body, this, ite_false], rfl⟩)
    (0#usize, 0#usize) (by simp) (by simp)
  refine ⟨y, by unfold sim.step.dyn_rate_update_loop; exact hl, ?_⟩
  rw [hv]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  have hlen : (v.val.take k.val).length = k.val := by simp; omega
  have := foldl_iterR (v.val.take k.val) (fun a x => if s3b_isAd x then a + 1 else a) 0
  rw [hlen] at this
  rw [← this]
  generalize v.val.take k.val = l
  suffices ∀ n, l.foldl (fun a x => if s3b_isAd x then a + 1 else a) n = n + (l.filter s3b_isAd).length by
    simpa using this 0
  induction l with
  | nil => intro n; simp
  | cons x t ih => intro n; simp only [List.foldl_cons, List.filter_cons]; cases hx : s3b_isAd x <;> simp [ih] <;> omega

@[simp] theorem s3b_abs_tr (i f b ft : F64) :
    (abs (sim.mods.DynRate.TimeRamp i f b ft) : OsuModel.Sim.DynRate) = .timeRamp i f b ft := rfl
@[simp] theorem s3b_abs_ad (a : F64) : (abs (sim.mods.DynRate.Adaptive a) : OsuModel.Sim.DynRate) = .adaptive a := rfl

/-- the new speed of `dynRateUpdate` (Except NetExn: `liftNet` rejects) -/
def s3b_dynV (d : OsuModel.Sim.DynRate) (old tgt elapsed t : F64) : Except NetExn F64 := do
  let v ← match d with
    | .timeRamp i f b ft => OsuModel.Sim.timeRampRate i f b ft t
    | .adaptive _ => pure (Framework.Interpolation.dampContinuously old tgt 50 elapsed)
  d.setSpeed old v

/-- Rust `dyn_rate_update` normal form -/
theorem s3b_dyn_rust (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (k : Usize)
    (hk : k.val < c.cfg.dyn_rates.val.length) (hsp : k.val < s.speed.val.length)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (has : s3b_isAd (c.cfg.dyn_rates.val[k.val]'hk) →
      ((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length < s.as_target.val.length) :
    sim.step.dyn_rate_update c s k = ok (match s3b_dynV (abs (c.cfg.dyn_rates.val[k.val]'hk)) (s.speed.val[k.val]'hsp)
        (s.as_target.val[((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length]!)
        (if s.k.val = 0 then 0 else s.t - ((simCtxS tn fo c).steps[s.k.val - 1]!).time) s.t with
      | .ok nv => (.Ok (), { s with speed := s.speed.set k nv })
      | .error e => (.Err (.Net (exnI e)), s)) := by
  obtain ⟨ai, hai, haiv⟩ := s3b_dyn_ai_loop c.cfg.dyn_rates k (by omega)
  unfold sim.step.dyn_rate_update
  rw [s3b_elapsed_rust tn fo c s hstep]
  simp only [bind_ok]
  simp only [vec_index_eq _ _ hk, hai, vec_index_eq _ _ hsp, bind_ok, uncurry_apply_pair]
  generalize (if s.k.val = 0 then 0 else s.t - ((simCtxS tn fo c).steps[s.k.val - 1]!).time) = el
  have has' := has
  generalize c.cfg.dyn_rates.val[k.val]'hk = d at has'
  cases d with
  | TimeRamp i f b ft =>
    simp only [sim.mods.time_ramp_rate_refines, bind_ok, s3b_dynV]
    cases h1 : OsuModel.Sim.timeRampRate i f b ft s.t with
    | error e => simp [exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Bind.bind, Except.bind, abs, h1]
    | ok v =>
      simp only [exceptI, id, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        sim.mods.dyn_rate_set_speed_refines]
      cases h2 : OsuModel.Sim.DynRate.setSpeed (abs (sim.mods.DynRate.TimeRamp i f b ft)) (s.speed.val[k.val]'hsp) v with
      | error e =>
        rw [s3b_abs_tr] at h2
        simp [h2, Bind.bind, Except.bind, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, h1]
      | ok nv =>
        rw [s3b_abs_tr] at h2
        simp [h2, Bind.bind, Except.bind, vec_index_mut_eq _ _ hsp, h1]
  | Adaptive a =>
    have hlt := has' rfl
    rw [← haiv] at hlt
    have hg : s.as_target.val[((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length]! = s.as_target.val[ai.val]'hlt := by
      rw [getElem!_pos s.as_target.val _ (by rw [← haiv]; exact hlt)]; simp [haiv]
    rw [hg]
    simp only [vec_index_eq _ _ hlt, bind_ok, fb64_4632233691727265792, net.framework.damp_continuously_refines,
      sim.mods.dyn_rate_set_speed_refines, s3b_dynV, s3b_abs_ad]
    generalize hv : Framework.Interpolation.dampContinuously (s.speed.val[k.val]'hsp) (s.as_target.val[ai.val]'hlt) 50 el = v
    cases h2 : OsuModel.Sim.DynRate.setSpeed (.adaptive a) (s.speed.val[k.val]'hsp) v with
    | error e => simp [h2, exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, Bind.bind, Except.bind,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | ok nv => simp [h2, exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, Bind.bind, Except.bind,
        vec_index_mut_eq _ _ hsp]

theorem s3b_exc_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem s3b_exc_bind_err {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f : Except ε β) = .error e := rfl
theorem s3b_exc_pure_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (pure a >>= f : Except ε β) = f a := rfl

def s3b_isAdS : OsuModel.Sim.DynRate → Bool
  | .adaptive _ => true
  | .timeRamp .. => false

/-- spec `dynRateUpdate` normal form (generic; `ai` = the number of AS mods before `k`) -/
theorem s3b_dynRateUpdate_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (k ai : Nat)
    (hk : k < C.cfg.dynRates.size) (hsp : k < S.speed.size) (hstep : S.k ≠ 0 → S.k - 1 < C.steps.size)
    (hai : ∀ g : OsuModel.Sim.DynRate → Bool, (∀ d, g d = s3b_isAdS d) → ((C.cfg.dynRates.extract 0 k).filter g).size = ai)
    (has : s3b_isAdS C.cfg.dynRates[k] → ai < S.asTarget.size) :
    OsuModel.Sim.Sim.dynRateUpdate k C S =
      match s3b_dynV C.cfg.dynRates[k] S.speed[k] (S.asTarget[ai]!) (if S.k = 0 then 0 else S.t - (C.steps[S.k - 1]!).time) S.t with
      | .ok nv => .ok ((), { S with speed := S.speed.set k nv })
      | .error e => .error s!"lazer would throw: {repr e}" := by
  unfold OsuModel.Sim.Sim.dynRateUpdate
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, OsuModel.Sim.Sim.ctx, simM_read, Except.bind]
  rw [s3b_elapsedNow C S hstep]
  simp only [OsuModel.Sim.Sim.getA, dif_pos hk, dif_pos hsp, simM_pure]
  rw [hai _ (by intro d; cases d <;> rfl)]
  generalize C.cfg.dynRates[k] = d at has ⊢
  generalize (if S.k = 0 then 0 else S.t - (C.steps[S.k - 1]!).time) = el
  cases d with
  | timeRamp i f b ft =>
    simp only [s3b_dynV]
    cases h1 : OsuModel.Sim.timeRampRate i f b ft S.t with
    | error e => simp only [h1, OsuModel.Sim.Sim.liftNet, simM_bind, simM_pure, simM_throw, Except.bind, OsuModel.Sim.Sim.setA, dif_pos hsp, simM_set, s3b_exc_bind_ok, s3b_exc_bind_err, s3b_exc_pure_bind]
    | ok v =>
      cases h2 : (OsuModel.Sim.DynRate.timeRamp i f b ft).setSpeed S.speed[k] v with
      | error e => simp only [h1, h2, OsuModel.Sim.Sim.liftNet, simM_bind, simM_pure, simM_throw, Except.bind, OsuModel.Sim.Sim.setA, dif_pos hsp, simM_set, s3b_exc_bind_ok, s3b_exc_bind_err, s3b_exc_pure_bind]
      | ok nv => simp only [h1, h2, OsuModel.Sim.Sim.liftNet, simM_bind, simM_pure, simM_throw, Except.bind, OsuModel.Sim.Sim.setA, dif_pos hsp, simM_set, s3b_exc_bind_ok, s3b_exc_bind_err, s3b_exc_pure_bind]
  | adaptive a =>
    have ha := has rfl
    simp only [s3b_dynV, dif_pos ha, simM_pure, getElem!_pos S.asTarget ai ha]
    cases h2 : (OsuModel.Sim.DynRate.adaptive a).setSpeed S.speed[k]
        (Framework.Interpolation.dampContinuously S.speed[k] S.asTarget[ai] 50 el) with
    | error e => simp only [h2, OsuModel.Sim.Sim.liftNet, simM_bind, simM_pure, simM_throw, Except.bind, OsuModel.Sim.Sim.setA, dif_pos hsp, simM_set, s3b_exc_bind_ok, s3b_exc_bind_err, s3b_exc_pure_bind]
    | ok nv => simp only [h2, OsuModel.Sim.Sim.liftNet, simM_bind, simM_pure, simM_throw, Except.bind, OsuModel.Sim.Sim.setA, dif_pos hsp, simM_set, s3b_exc_bind_ok, s3b_exc_bind_err, s3b_exc_pure_bind]

theorem s3b_isAdS_abs (d : sim.mods.DynRate) : s3b_isAdS (abs d) = s3b_isAd d := by cases d <;> rfl

theorem s3b_filter_extract (l : List sim.mods.DynRate) (k : Nat) (g : OsuModel.Sim.DynRate → Bool)
    (hg : ∀ d, g d = s3b_isAdS d) :
    (((l.map (fun d => (abs d : OsuModel.Sim.DynRate))).toArray.extract 0 k).filter g).size =
      ((l.take k).filter s3b_isAd).length := by
  have hg' : g = s3b_isAdS := funext hg
  subst hg'
  simp only [List.extract_toArray, List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero]
  rw [← List.map_take]
  generalize l.take k = m
  rw [List.filter_toArray, List.size_toArray, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr; intro d _; simp [s3b_isAdS_abs]

theorem sim.step.dyn_rate_update_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (k : Usize)
    (hinv : SimInv c s)
    (hk : k.val < c.cfg.dyn_rates.val.length) (hsp : k.val < s.speed.val.length)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length)
    (has : s3b_isAd (c.cfg.dyn_rates.val[k.val]'hk) →
      ((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length < s.as_target.val.length) :
    ∃ r s', sim.step.dyn_rate_update c s k = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (OsuModel.Sim.Sim.dynRateUpdate k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (∃ sp, s' = { s with speed := sp }) ∧ SimInv c s' ∧ s'.future_order = s.future_order := by
  rw [s3b_dyn_rust tn fo c s k hk hsp hstep has]
  have hkC : k.val < (simCtxS tn fo c).cfg.dynRates.size := by simpa [simCtxS, abs, configS] using hk
  have hspS : k.val < (simStS tn s).speed.size := by simpa [simStS, abs] using hsp
  have hstepS : (simStS tn s).k ≠ 0 → (simStS tn s).k - 1 < (simCtxS tn fo c).steps.size := by
    intro h; have := hstep h; simpa [simCtxS, simStS, abs] using this
  have hd : (simCtxS tn fo c).cfg.dynRates[k.val]'hkC = abs (c.cfg.dyn_rates.val[k.val]'hk) := by
    simp [simCtxS, abs, configS]
  have hasS : s3b_isAdS ((simCtxS tn fo c).cfg.dynRates[k.val]'hkC) →
      ((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length < (simStS tn s).asTarget.size := by
    rw [hd, s3b_isAdS_abs]; intro h; have := has h; simpa [simStS, abs] using this
  rw [s3b_dynRateUpdate_spec _ _ k.val _ hkC hspS hstepS
    (fun g hg => by simpa [simCtxS, abs, configS] using s3b_filter_extract c.cfg.dyn_rates.val k.val g hg) hasS]
  have e1 : (simStS tn s).speed[k.val]'hspS = s.speed.val[k.val]'hsp := by simp [simStS, abs]
  have e2 : ∀ j : Nat, ((simStS tn s).asTarget[j]! : F64) = s.as_target.val[j]! := by
    intro j; simp [simStS, abs, getElem!_def]
  have e3 : (simStS tn s).k = s.k.val := rfl
  have e4 : (simStS tn s).t = s.t := rfl
  rw [hd, e1, e2, e3, e4]
  cases h : s3b_dynV (abs (c.cfg.dyn_rates.val[k.val]'hk)) (s.speed.val[k.val]'hsp)
      (s.as_target.val[((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length]!)
      (if s.k.val = 0 then 0 else s.t - ((simCtxS tn fo c).steps[s.k.val - 1]!).time) s.t with
  | error e => exact ⟨_, _, rfl, ⟨_, rfl⟩, ⟨s.speed, rfl⟩, hinv, rfl⟩
  | ok nv =>
    refine ⟨_, _, rfl, ?_, ⟨_, rfl⟩, s3b_inv_of hinv rfl rfl, rfl⟩
    show Except.ok _ = Except.ok _
    have : (simStS tn { s with speed := s.speed.set k nv }) = { simStS tn s with speed := (simStS tn s).speed.set k.val nv hspS } := by
      have : ((s.speed.set k nv).val.map (fun x => (abs x : F64))).toArray = (simStS tn s).speed.set k.val nv hspS := by
        simp [simStS, abs, alloc.vec.Vec.set, List.map_set]
      rw [← this]; rfl
    rw [this]; rfl

/-! ## Adaptive Speed (`adaptive_speed_one`) -/
/-- the consistency sum of `adaptiveSpeedOnResult`: `Σ sign(x_i - x_{i-1})` (from previous element `p`) -/
def s3b_cons : F64 → List F64 → Int → Except NetExn Int
  | _, [], c => .ok c
  | p, x :: t, c => match F64.sign (x - p) with
    | .ok sg => s3b_cons x t (c + sg.toInt)
    | .error e => .error e

theorem s3b_sign_bound (x : F64) (sg : Int32) (h : F64.sign x = .ok sg) : sg.toInt = -1 ∨ sg.toInt = 0 ∨ sg.toInt = 1 := by
  unfold F64.sign at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · cases h

theorem s3b_i32I_val (x : Int32) : (i32I x).val = x.toInt := rfl

theorem s3b_loop1_cont (v : alloc.vec.Vec F64) (v1 : alloc.vec.Vec (alloc.vec.Vec F64))
    (v2 : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref)) (ai : Usize) (r : sim.step.Ref) (recent : alloc.vec.Vec F64)
    (c : I64) (i : Usize) (x) (hb : sim.step.adaptive_speed_one_loop1.body v v1 v2 ai r recent c i = ok (.cont x)) :
    sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c i = sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent x.1 x.2 := by
  unfold sim.step.adaptive_speed_one_loop1; rw [loop_unfold]; simp [hb]
theorem s3b_loop1_done (v : alloc.vec.Vec F64) (v1 : alloc.vec.Vec (alloc.vec.Vec F64))
    (v2 : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref)) (ai : Usize) (r : sim.step.Ref) (recent : alloc.vec.Vec F64)
    (c : I64) (i : Usize) (y) (hb : sim.step.adaptive_speed_one_loop1.body v v1 v2 ai r recent c i = ok (.done y)) :
    sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c i = ok y := by
  unfold sim.step.adaptive_speed_one_loop1; rw [loop_unfold]; simp [hb]

/-- the Rust consistency loop (`adaptive_speed_one_loop1`): runs `s3b_cons` and then the final (`i = len`) body -/
theorem s3b_cons_loop (v : alloc.vec.Vec F64) (v1 : alloc.vec.Vec (alloc.vec.Vec F64))
    (v2 : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref)) (ai : Usize) (r : sim.step.Ref) (recent : alloc.vec.Vec F64)
    (hlen : recent.val.length ≤ 8) :
    ∀ n (i : Usize) (c : I64), recent.val.length - i.val = n → 1 ≤ i.val → i.val ≤ recent.val.length →
      c.val.natAbs ≤ i.val →
      (∃ c' : I64, s3b_cons (recent.val[i.val - 1]!) (recent.val.drop i.val) c.val = .ok c'.val ∧
        c'.val.natAbs ≤ recent.val.length ∧
        sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c i =
          sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c' (alloc.vec.Vec.len recent)) ∨
      (∃ e, s3b_cons (recent.val[i.val - 1]!) (recent.val.drop i.val) c.val = .error e ∧
        sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c i = ok (.Err (.Net (exnI e)), v, v1, v2)) := by
  intro n
  induction n with
  | zero =>
    intro i c hn h1 hi hc
    have hil : i.val = recent.val.length := by omega
    have hie : i = alloc.vec.Vec.len recent := by scalar_tac
    left
    refine ⟨c, ?_, by omega, by rw [hie]⟩
    rw [hil, List.drop_length]; rfl
  | succ n ih =>
    intro i c hn h1 hi hc
    have hlt : i.val < recent.val.length := by omega
    obtain ⟨i2, hi2, hi2v, _⟩ := eq_ok_of_spec (UScalar.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi2' : i2.val < recent.val.length := by rw [hi2v]; simp; omega
    have hdrop : recent.val.drop i.val = recent.val[i.val]'hlt :: recent.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hlt
    have hprev : recent.val[i.val - 1]! = recent.val[i2.val]'hi2' := by
      rw [getElem!_pos recent.val _ (by omega)]; congr 1; rw [hi2v]; simp
    rw [hdrop, hprev]
    simp only [s3b_cons]
    have hlt' : i < alloc.vec.Vec.len recent := by rw [vec_lt_len_iff]; exact hlt
    have hbody : sim.step.adaptive_speed_one_loop1.body v v1 v2 ai r recent c i = (do
        let r1 ← net.mathops.f64_sign (recent.val[i.val]'hlt - recent.val[i2.val]'hi2')
        let r2 ← sim.err.lift_net r1
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => do
          let sg ← lift (IScalar.cast .I64 val)
          let consistency1 ← c + sg
          let i3 ← i + 1#usize
          ok (ControlFlow.cont (consistency1, i3))
        | core.ops.control_flow.ControlFlow.Break residual => do
          let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr) residual
          ok (ControlFlow.done (r3, v, v1, v2))) := by
      simp only [sim.step.adaptive_speed_one_loop1.body, hlt', if_true, vec_index_eq _ _ hlt, hi2,
        vec_index_eq _ _ hi2', bind_ok, float.F64.sub]
      rfl
    cases hs : F64.sign (recent.val[i.val]'hlt - recent.val[i2.val]'hi2') with
    | error e =>
      right
      refine ⟨e, rfl, ?_⟩
      apply s3b_loop1_done
      rw [hbody, net.mathops.f64_sign_refines, hs]
      simp [exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | ok sg =>
      have hb := s3b_sign_bound _ sg hs
      have hcast : (IScalar.cast .I64 (i32I sg)).val = sg.toInt := by
        rw [IScalar.cast_val_eq, s3b_i32I_val]; rcases hb with h | h | h <;> rw [h] <;> decide
      obtain ⟨c1, hc1, hc1v⟩ : ∃ c1 : I64, c + IScalar.cast .I64 (i32I sg) = ok c1 ∧ c1.val = c.val + sg.toInt := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (IScalar.add_spec (x := c) (y := IScalar.cast .I64 (i32I sg))
          (by rw [hcast]; scalar_tac) (by rw [hcast]; scalar_tac))
        exact ⟨z, hz, by rw [hzv, hcast]⟩
      obtain ⟨i3, hi3, hi3v⟩ := usize_add_one i (by scalar_tac)
      have hcont : sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c i =
          sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c1 i3 := by
        apply s3b_loop1_cont _ _ _ _ _ _ _ _ (c1, i3)
        rw [hbody, net.mathops.f64_sign_refines, hs]
        simp only [exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, hc1, hi3]
      rw [hcont]
      have hprev' : recent.val[i3.val - 1]! = recent.val[i.val]'hlt := by
        rw [getElem!_pos recent.val _ (by omega)]; congr 1; omega
      rcases ih i3 c1 (by omega) (by omega) (by omega) (by omega) with ⟨c', hc', hb', hl'⟩ | ⟨e, he, hl'⟩
      · left
        refine ⟨c', ?_, hb', ?_⟩
        · simp only []; rw [← hc1v]; rw [hprev', hi3v] at hc'; exact hc'
        · rw [hl']
      · right
        refine ⟨e, ?_, ?_⟩
        · simp only []; rw [← hc1v]; rw [hprev', hi3v] at he; exact he
        · rw [hl']

theorem s3b_iterR_push (w : List F64) :
    ∀ n a (acc : List F64), a + n ≤ w.length →
      iterR (fun j l => .yield (l ++ [w[j]!])) a n acc = acc ++ (w.drop a).take n := by
  intro n
  induction n with
  | zero => intro a acc _; simp [iterR]
  | succ n ih =>
    intro a acc h
    simp only [iterR]
    rw [ih (a + 1) _ (by omega)]
    have h' : a < w.length := by omega
    rw [List.drop_eq_getElem_cons h', List.take_succ_cons]
    simp [getElem!_def, h']

/-- the Rust copy loop of `adaptive_speed_one` (`recent0[1..min(8, len)]`) -/
theorem s3b_recent_loop (v : alloc.vec.Vec (alloc.vec.Vec F64)) (ai : Usize) (hai : ai.val < v.val.length) :
    ∃ rv : alloc.vec.Vec F64, sim.step.adaptive_speed_one_loop0 v ai (alloc.vec.Vec.new F64) 1#usize = ok rv ∧
      rv.val = ((v.val[ai.val]'hai).val.drop 1).take 7 := by
  have hv : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec F64)) v ai = ok (v.val[ai.val]'hai) :=
    vec_index_eq _ _ hai
  generalize hw : v.val[ai.val]'hai = w at hv
  by_cases h0 : w.val.length ≤ 1
  · refine ⟨alloc.vec.Vec.new F64, ?_, ?_⟩
    · unfold sim.step.adaptive_speed_one_loop0; rw [loop_unfold]
      have : ¬ (1#usize : Usize) < alloc.vec.Vec.len w := by rw [vec_lt_len_iff]; simp; omega
      have : ¬ 1 < w.val.length := by omega
      simp [sim.step.adaptive_speed_one_loop0.body, hv, this]
    · simp [List.drop_eq_nil_of_le h0]
  · obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.step.adaptive_speed_one_loop0.body v ai x.1 x.2) (·.2)
      (min 8 w.val.length) (by have := w.property; omega)
      (fun x => x.1.val.length + 1 = x.2.val) (fun x => x.1.val)
      (fun j l => l ++ [w.val[j]!]) (fun y l => y.val = l)
      (by
        rintro ⟨rv, q⟩ hI hq j1 hj1 hj1v
        simp only at hI hq hj1 hj1v ⊢
        have hq8 : q < 8#usize := by scalar_tac
        have hqw : q.val < w.val.length := by omega
        have hql : q < alloc.vec.Vec.len w := by rw [vec_lt_len_iff]; exact hqw
        have hcap : rv.val.length < Usize.max := by scalar_tac
        refine ⟨(vpush rv (w.val[q.val]'hqw) hcap, j1), ?_, rfl, ?_, ?_⟩
        · have hq8' : q.val < 8 := hq8
          simp [sim.step.adaptive_speed_one_loop0.body, hq8, hq8', hv, hql, hqw, vec_index_eq _ _ hqw,
            vec_index_usize_ok _ _ hqw, vec_push_ok _ _ hcap, hj1]
        · simp [getElem!_def, hqw]
        · simp; omega)
      (by
        rintro ⟨rv, q⟩ _ hge
        simp only at hge
        refine ⟨rv, ?_, rfl⟩
        by_cases hq8 : q < 8#usize
        · have hql : ¬ q < alloc.vec.Vec.len w := by
            rw [vec_lt_len_iff]; have : q.val < 8 := hq8; omega
          have hq8' : q.val < 8 := hq8
          have hql' : ¬ q.val < w.val.length := by rw [vec_lt_len_iff] at hql; exact hql
          simp [sim.step.adaptive_speed_one_loop0.body, hq8, hq8', hv, hql, hql']
        · have hq8' : ¬ q.val < 8 := hq8
          simp [sim.step.adaptive_speed_one_loop0.body, hq8, hq8'])
      (alloc.vec.Vec.new F64, 1#usize) (by simp) (by simp; omega)
    refine ⟨y, by unfold sim.step.adaptive_speed_one_loop0; exact hl, ?_⟩
    rw [hy]
    simp only [show (1#usize : Usize).val = 1 from rfl]
    rw [s3b_iterR_push w.val (min 8 w.val.length - 1) 1 _ (by omega)]
    simp only [alloc.vec.Vec.new, List.nil_append]
    by_cases h8 : w.val.length ≤ 8
    · rw [show min 8 w.val.length - 1 = (w.val.drop 1).length by simp; omega, List.take_length,
        List.take_of_length_le (by simp; omega), alloc.vec.Vec.from_val, List.nil_append]
    · rw [show min 8 w.val.length - 1 = 7 by omega, alloc.vec.Vec.from_val, List.nil_append]

theorem s3b_abs_i64 (c : I64) (hc : c.val.natAbs ≤ 8) :
    ∃ a : I64, (if c < 0#i64 then -. c else ok c) = ok a ∧ a.val = (c.val.natAbs : Int) := by
  by_cases h : c < 0#i64
  · have hv : c.val < 0 := by scalar_tac
    obtain ⟨a, ha, hav⟩ := eq_ok_of_spec (IScalar.neg_step c (by
      intro e; have : c.val = IScalar.min .I64 := by rw [e]
      rw [this] at hc; simp [IScalar.min, I64.min, I64.numBits] at hc))
    refine ⟨a, by simp only [h, if_true]; exact ha, ?_⟩
    rw [hav]; omega
  · have hv : 0 ≤ c.val := by scalar_tac
    exact ⟨c, by simp [h], by omega⟩

/-- the final iteration (`i = len`) of the Rust consistency loop: average, target, and the three AS state writes -/
theorem s3b_as_final (v : alloc.vec.Vec F64) (v1 : alloc.vec.Vec (alloc.vec.Vec F64))
    (v2 : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref)) (ai : Usize) (r : sim.step.Ref) (recent : alloc.vec.Vec F64)
    (c : I64) (hc : c.val.natAbs ≤ 8) (h0 : ai.val < v.val.length) (h1 : ai.val < v1.val.length)
    (h2 : ai.val < v2.val.length) (hcap : (v2.val[ai.val]'h2).val.length < Usize.max) :
    sim.step.adaptive_speed_one_loop1 v v1 v2 ai r recent c (alloc.vec.Vec.len recent) =
      ok (match SysMisc.averageF64 recent.val with
        | .ok avg => (.Ok (), v.set ai (Framework.Interpolation.lerp (v.val[ai.val]'h0) avg
              (F64.ofInt (c.val.natAbs : Int) / (F64.ofInt 8 - 1))), v1.set ai recent,
            v2.set ai (vpush (v2.val[ai.val]'h2) r hcap))
        | .error e => (.Err (.Net (exnI e)), v, v1, v2)) := by
  apply s3b_loop1_done
  have hlt : ¬ alloc.vec.Vec.len recent < alloc.vec.Vec.len recent := by simp
  obtain ⟨a, ha, hav⟩ := s3b_abs_i64 c hc
  simp only [sim.step.adaptive_speed_one_loop1.body, hlt, if_false, net.sysmisc.average_f64_refines]
  cases hav' : SysMisc.averageF64 (alloc.vec.Vec.deref recent).val with
  | error e =>
    have : SysMisc.averageF64 recent.val = .error e := by simpa using hav'
    simp [this, exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | ok avg =>
    have : SysMisc.averageF64 recent.val = .ok avg := by simpa using hav'
    have hd : (alloc.vec.Vec.deref recent).val = recent.val := by simp
    simp only [hd, this, exceptI, id, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [ha]
    simp [vec_index_eq _ _ h0,
      float.F64.from_i64, float.F64.sub, float.F64.div, net.framework.lerp_refines, vec_index_mut_eq _ _ h2,
      vec_index_mut_eq _ _ h1, vec_index_mut_eq _ _ h0, vec_push_ok _ _ hcap, hav]

/-- `rel` of `adaptiveSpeedOnResult` -/
def s3b_asRel (hit : Bool) (endT ta prev : F64) : Except NetExn F64 :=
  if !hit then .ok 0.95 else F64.clamp ((endT - prev) / (ta - prev)) 0.9 1.11

/-- the AS update proper: new target and new recent-rates list -/
def s3b_asCore (recent0 : List F64) (speed rel tgt0 : F64) : Except NetExn (F64 × List F64) :=
  match F64.clamp (rel * speed) 0.4 2.5 with
  | .error e => .error e
  | .ok last =>
    match s3b_cons (((recent0.drop 1).take 7 ++ [last])[0]!) (((recent0.drop 1).take 7 ++ [last]).drop 1) 0 with
    | .error e => .error e
    | .ok c =>
      match SysMisc.averageF64 ((recent0.drop 1).take 7 ++ [last]) with
      | .error e => .error e
      | .ok avg => .ok (Framework.Interpolation.lerp tgt0 avg (F64.ofInt (c.natAbs : Int) / (F64.ofInt 8 - 1)),
          (recent0.drop 1).take 7 ++ [last])

def s3b_asStep (hit : Bool) (endT ta prev : F64) (recent0 : List F64) (speed tgt0 : F64) :
    Except NetExn (F64 × List F64) :=
  match s3b_asRel hit endT ta prev with
  | .error e => .error e
  | .ok rel => s3b_asCore recent0 speed rel tgt0

theorem s3b_ref_seen_vec (v : alloc.vec.Vec sim.step.Ref) (r : sim.step.Ref) :
    sim.step.ref_seen (alloc.vec.Vec.deref v) r = ok ((v.val.map (fun x => (abs x : Nat × Int))).contains (abs r)) := by
  rw [sim.step.ref_seen_refines]; simp

theorem s3b_loop20 : @sim.step.adaptive_speed_one_loop2 = @sim.step.adaptive_speed_one_loop0 := by
  funext a b c d
  unfold sim.step.adaptive_speed_one_loop2 sim.step.adaptive_speed_one_loop0
    sim.step.adaptive_speed_one_loop2.body sim.step.adaptive_speed_one_loop0.body
  rfl
theorem s3b_loop31 : @sim.step.adaptive_speed_one_loop3 = @sim.step.adaptive_speed_one_loop1 := by
  funext a b c d e f g h
  unfold sim.step.adaptive_speed_one_loop3 sim.step.adaptive_speed_one_loop1
    sim.step.adaptive_speed_one_loop3.body sim.step.adaptive_speed_one_loop1.body
  rfl

theorem s3b_clamp_net_eq (x lo hi : F64) : sim.step.clamp_net x lo hi =
    ok (match F64.clamp x lo hi with | .ok v => .Ok v | .error e => .Err (.Net (exnI e))) := by
  unfold sim.step.clamp_net; rw [net.mathops.f64_clamp_refines]
  cases F64.clamp x lo hi <;> simp [exceptI, sim.err.lift_net]

/-- the common tail of `adaptive_speed_one` after `rel` -/
theorem s3b_as_tail (s : sim.state.St) (ai : Usize) (r : sim.step.Ref) (speed rel : F64)
    (h0 : ai.val < s.as_target.val.length) (h1 : ai.val < s.as_recent.val.length)
    (h2 : ai.val < s.as_seen.val.length) (hcap : (s.as_seen.val[ai.val]'h2).val.length < Usize.max) :
    ∃ res s', (do
        let recent ← sim.step.adaptive_speed_one_loop0 s.as_recent ai (alloc.vec.Vec.new float.F64) 1#usize
        let f6 ← float.F64.mul rel speed
        let r2 ← sim.step.clamp_net f6 (0.4 : OsuModel.Net.F64) (2.5 : OsuModel.Net.F64)
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 => do
          let recent1 ← alloc.vec.Vec.push recent val1
          let (r3, v1, v2, v3) ← sim.step.adaptive_speed_one_loop1 s.as_target s.as_recent s.as_seen ai r recent1 0#i64 1#usize
          ok (r3, { s with as_target := v1, as_recent := v2, as_seen := v3 })
        | core.ops.control_flow.ControlFlow.Break residual => do
          let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr) residual
          ok (r3, s)) = ok (res, s') ∧
      match s3b_asCore (s.as_recent.val[ai.val]'h1).val speed rel (s.as_target.val[ai.val]'h0) with
        | .ok (tgt, rec) => res = .Ok () ∧ ∃ rv : alloc.vec.Vec F64, rv.val = rec ∧
            s' = { s with as_target := s.as_target.set ai tgt, as_recent := s.as_recent.set ai rv,
                          as_seen := s.as_seen.set ai (vpush (s.as_seen.val[ai.val]'h2) r hcap) }
        | .error e => res = .Err (.Net (exnI e)) ∧ s' = s := by
  obtain ⟨rv0, hrv0, hrv0v⟩ := s3b_recent_loop s.as_recent ai h1
  simp only [hrv0, bind_ok, float.F64.mul]
  rw [s3b_clamp_net_eq]
  unfold s3b_asCore
  cases hcl : F64.clamp (rel * speed) 0.4 2.5 with
  | error e =>
    exact ⟨_, _, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], rfl, rfl⟩
  | ok last =>
    have hl0 : rv0.val.length ≤ 7 := by rw [hrv0v]; simp
    have h7 : (7 : Nat) < Usize.max := by scalar_tac
    have hcap0 : rv0.val.length < Usize.max := by omega
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_push_ok _ _ hcap0]
    generalize hrec : vpush rv0 last hcap0 = rec
    have hrecv : rec.val = ((s.as_recent.val[ai.val]'h1).val.drop 1).take 7 ++ [last] := by
      rw [← hrec, vpush_val, hrv0v]
    have hlen : rec.val.length ≤ 8 := by rw [hrecv]; simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]; omega
    have hpos : 1 ≤ rec.val.length := by rw [hrecv]; simp
    rcases s3b_cons_loop s.as_target s.as_recent s.as_seen ai r rec hlen (rec.val.length - 1) 1#usize 0#i64
      (by simp) (by simp) (by simpa using hpos) (by simp) with ⟨c', hc', hb', hl'⟩ | ⟨e, he, hl'⟩
    · rw [hl', s3b_as_final _ _ _ _ _ _ c' (by omega) h0 h1 h2 hcap]
      have hc'' : s3b_cons (rec.val[0]!) (rec.val.drop 1) 0 = .ok c'.val := by simpa using hc'
      rw [← hrecv, hc'']
      cases hav : SysMisc.averageF64 rec.val with
      | error e => exact ⟨_, _, by simp only [bind_ok, uncurry_apply_pair], rfl, rfl⟩
      | ok avg => exact ⟨_, _, by simp only [bind_ok, uncurry_apply_pair], rfl, rec, rfl, rfl⟩
    · rw [hl']
      have he' : s3b_cons (rec.val[0]!) (rec.val.drop 1) 0 = .error e := by simpa using he
      rw [← hrecv, he']
      exact ⟨_, _, by simp only [bind_ok, uncurry_apply_pair], rfl, rfl⟩

/-- Rust `adaptive_speed_one` (the AS step for the `ai`-th AS mod, dyn-rate index `k`) -/
theorem sim.step.adaptive_speed_one_eq (s : sim.state.St) (k ai : Usize) (r : sim.step.Ref) (h : sim.playable.HObj)
    (ty : sim.basic.HitResult) (t : F64) (prev : Option F64)
    (hk : k.val < s.speed.val.length) (h0 : ai.val < s.as_target.val.length) (h1 : ai.val < s.as_recent.val.length)
    (h2 : ai.val < s.as_seen.val.length) (hcap : (s.as_seen.val[ai.val]'h2).val.length < Usize.max) :
    ∃ res s', sim.step.adaptive_speed_one s k ai r h ty t prev = ok (res, s') ∧
      (if ((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).contains (abs r) ||
          !(abs ty : OsuModel.Sim.HitResult).affectsAccuracy || prev.isNone then res = .Ok () ∧ s' = s
       else match s3b_asStep (abs ty : OsuModel.Sim.HitResult).isHit h.end_time
          (OsuModel.Sim.Sim.timeAbsolute (abs h) t) (prev.getD 0) (s.as_recent.val[ai.val]'h1).val
          (s.speed.val[k.val]'hk) (s.as_target.val[ai.val]'h0) with
        | .ok (tgt, rec) => res = .Ok () ∧ ∃ rv : alloc.vec.Vec F64, rv.val = rec ∧
            s' = { s with as_target := s.as_target.set ai tgt, as_recent := s.as_recent.set ai rv,
                          as_seen := s.as_seen.set ai (vpush (s.as_seen.val[ai.val]'h2) r hcap) }
        | .error e => res = .Err (.Net (exnI e)) ∧ s' = s) := by
  unfold sim.step.adaptive_speed_one
  simp only [vec_index_eq _ _ h2, bind_ok, s3b_ref_seen_vec]
  by_cases hsn : ((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).contains (abs r) = true
  · refine ⟨.Ok (), s, by simp only [hsn, if_true], ?_⟩
    rw [if_pos (by simp only [hsn, Bool.true_or])]; exact ⟨rfl, rfl⟩
  · simp only [hsn, Bool.false_eq_true, if_false, Bool.false_or]
    obtain ⟨b1, hb1, eb1⟩ := sim.basic.affects_accuracy_refines ty
    have eb1' : (abs ty : OsuModel.Sim.HitResult).affectsAccuracy = b1 := eb1
    rw [hb1, eb1']
    cases b1 with
    | false =>
      refine ⟨.Ok (), s, by simp only [bind_ok, Bool.false_eq_true, if_false], ?_⟩
      rw [if_pos (by simp only [Bool.not_false, Bool.true_or])]; exact ⟨rfl, rfl⟩
    | true =>
      cases prev with
      | none =>
        refine ⟨.Ok (), s, by simp only [bind_ok, if_true], ?_⟩
        rw [if_pos (by simp only [Option.isNone_none, Bool.or_true])]; exact ⟨rfl, rfl⟩
      | some prev =>
        simp only [bind_ok, if_true, Bool.not_true, Bool.false_or, Option.isNone_some, Bool.false_eq_true, if_false,
          Option.getD_some]
        obtain ⟨b2, hb2, eb2⟩ := sim.basic.is_hit_refines ty
        have eb2' : (abs ty : OsuModel.Sim.HitResult).isHit = b2 := eb2
        rw [hb2, eb2']
        unfold s3b_asStep s3b_asRel
        cases b2 with
        | true =>
          obtain ⟨ta, hta, eta⟩ := sim.step.time_absolute_refines h t
          have eta' : OsuModel.Sim.Sim.timeAbsolute (abs h) t = ta := eta
          rw [eta']
          simp only [bind_ok, if_true, float.F64.sub, hta, float.F64.div, fb64_4606281698874543309,
            fb64_4607677814759028163, s3b_clamp_net_eq, Bool.not_true, Bool.false_eq_true, if_false]
          cases hcl : F64.clamp ((h.end_time - prev) / (ta - prev)) 0.9 1.11 with
          | error e => exact ⟨_, _, by simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], rfl, rfl⟩
          | ok rel =>
            obtain ⟨res, s', ht, hR⟩ := s3b_as_tail s ai r (s.speed.val[k.val]'hk) rel h0 h1 h2 hcap
            refine ⟨res, s', ?_, hR⟩
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_index_eq _ _ hk,
              fb64_4600877379321698714, fb64_4612811918334230528]
            simp only [s3b_clamp_net_eq, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ht ⊢
            convert ht using 3
        | false =>
          obtain ⟨res, s', ht, hR⟩ := s3b_as_tail s ai r (s.speed.val[k.val]'hk) 0.95 h0 h1 h2 hcap
          refine ⟨res, s', ?_, hR⟩
          simp only [bind_ok, Bool.false_eq_true, if_false, fb64_4606732058837280358, vec_index_eq _ _ hk,
            fb64_4600877379321698714, fb64_4612811918334230528, s3b_loop20, s3b_loop31]
          simp only [s3b_clamp_net_eq, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ht ⊢
          convert ht using 3

end OsuProofs
