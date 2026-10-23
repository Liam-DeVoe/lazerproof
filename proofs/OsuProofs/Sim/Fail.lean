/-
`sim::step::trigger_failure` (Rust) refines `Sim.triggerFailure` (`HealthProcessor.TriggerFailure` + the
fail-override pass `Mods.OfType<IApplicableFailOverride>().All(m => m.PerformFail())`).
Both sides are related to one recursive model of the override pass (`simTFR`, over the override list), assuming
every EZ index is in range of `retries` (an invariant of `initState`: one entry per EZ).
-/
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

theorem sim_clone_vec_u64 (s : alloc.vec.Vec U64) : alloc.vec.CloneVec.clone core.clone.CloneU64 s = ok s := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := core.clone.CloneU64.clone) (s := s.slice)
    (by intro x _; rfl))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp
@[simp] theorem sim_health_clone (h : sim.scoring.HealthSt) : sim.scoring.HealthSt.Insts.CoreCloneClone.clone h = ok h := by
  rcases h with ⟨a, b, c, d, e, f, g, r⟩
  cases g <;> simp [sim.scoring.HealthSt.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone,
    core.option.Option.Insts.CoreCloneClone.clone, sim_clone_vec_u64, lift]

/-- The override pass on the Rust state `(health, retries)`: `(health', retries', stopped)`. -/
def simTFR (f : F64) (v : List U64) : List sim.mods.FailOverride → F64 × List U64 × Bool
  | [] => (f, v, false)
  | .Veto :: _ => (f, v, true)
  | .Allow :: t => simTFR f v t
  | .Easy k :: t =>
    if (v.getD k.val 0#u64).val ≠ 0 then (1, v.set k.val (core.num.U64.wrapping_sub (v.getD k.val 0#u64) 1#u64), true)
    else simTFR f v t

theorem sim_tfr_nostop (f : F64) (v : List U64) :
    ∀ l, (simTFR f v l).2.2 = false → (simTFR f v l).1 = f ∧ (simTFR f v l).2.1 = v := by
  intro l
  induction l with
  | nil => intro _; simp [simTFR]
  | cons o t ih =>
    cases o with
    | Veto => simp [simTFR]
    | Allow => simpa [simTFR] using ih
    | Easy k => by_cases h0 : (v.getD k.val 0#u64).val ≠ 0 <;> simp_all [simTFR]

theorem sim_tf_loop_body_eq (c : sim.mods.Config) :
    sim.step.trigger_failure_loop0.body c = sim.step.trigger_failure_loop1.body c := rfl

theorem sim_tf_loop (c : sim.mods.Config) (f : F64) (v : alloc.vec.Vec U64)
    (hk : ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < v.val.length) :
    ∀ (i : Usize), i.val ≤ c.fail_overrides.val.length →
      ∃ r, sim.step.trigger_failure_loop1 c f v false i = ok r ∧
        (r.1, r.2.1.val, r.2.2) = simTFR f v.val (c.fail_overrides.val.drop i.val) := by
  intro i
  induction hn : c.fail_overrides.val.length - i.val generalizing i with
  | zero =>
    intro hi
    have : i.val = c.fail_overrides.val.length := by omega
    refine ⟨(f, v, false), ?_, ?_⟩
    · unfold sim.step.trigger_failure_loop1; rw [loop_unfold]; simp [sim.step.trigger_failure_loop1.body, vec_lt_len_iff, this]
    · simp [this, simTFR]
  | succ n ih =>
    intro hi
    have hlt : i.val < c.fail_overrides.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one i (by have := c.fail_overrides.property; omega)
    rw [List.drop_eq_getElem_cons hlt]
    have hmem : c.fail_overrides.val[i.val] ∈ c.fail_overrides.val := List.getElem_mem hlt
    cases ho : c.fail_overrides.val[i.val] with
    | Veto =>
      refine ⟨(f, v, true), ?_, by simp [simTFR]⟩
      unfold sim.step.trigger_failure_loop1; rw [loop_unfold]; dsimp only; rw [show sim.step.trigger_failure_loop1.body c f v false i = ok (.cont (f, v, true, j1)) by
        simp [sim.step.trigger_failure_loop1.body, vec_lt_len_iff, hlt, vec_index_usize_ok, ho, hj1]]
      simp only [bind_ok]
      rw [loop_unfold]
      simp [sim.step.trigger_failure_loop1.body]
    | Allow =>
      obtain ⟨r, hr, er⟩ := ih j1 (by omega) (by omega)
      refine ⟨r, ?_, by rw [er, hj1v]; simp [simTFR]⟩
      unfold sim.step.trigger_failure_loop1; rw [loop_unfold]; dsimp only; rw [show sim.step.trigger_failure_loop1.body c f v false i = ok (.cont (f, v, false, j1)) by
        simp [sim.step.trigger_failure_loop1.body, vec_lt_len_iff, hlt, vec_index_usize_ok, ho, hj1]]
      simp only [bind_ok]; unfold sim.step.trigger_failure_loop1 at hr; exact hr
    | Easy k =>
      have hkl := hk k (ho ▸ hmem)
      by_cases h0 : (v.val[k.val]'hkl).val = 0
      · obtain ⟨r, hr, er⟩ := ih j1 (by omega) (by omega)
        refine ⟨r, ?_, by rw [er, hj1v]; simp [simTFR, List.getD_eq_getElem?_getD, hkl, h0]⟩
        unfold sim.step.trigger_failure_loop1; rw [loop_unfold]; dsimp only; rw [show sim.step.trigger_failure_loop1.body c f v false i = ok (.cont (f, v, false, j1)) by
          simp [sim.step.trigger_failure_loop1.body, vec_lt_len_iff, hlt, vec_index_usize_ok, ho, hj1, hkl, h0]]
        simp only [bind_ok]; unfold sim.step.trigger_failure_loop1 at hr; exact hr
      · obtain ⟨_, hm, hmv⟩ := (⟨_, vec_index_mut_usize_ok v k hkl, rfl⟩ : ∃ x, _ = x ∧ x = x)
        refine ⟨(1, alloc.vec.Vec.set v k (core.num.U64.wrapping_sub (v.val[k.val]'hkl) 1#u64), true), ?_, ?_⟩
        · unfold sim.step.trigger_failure_loop1; rw [loop_unfold]; dsimp only; rw [show sim.step.trigger_failure_loop1.body c f v false i = ok (.cont
              (1, alloc.vec.Vec.set v k (core.num.U64.wrapping_sub (v.val[k.val]'hkl) 1#u64), true, j1)) by
            simp [sim.step.trigger_failure_loop1.body, vec_lt_len_iff, hlt, vec_index_usize_ok, ho, hj1, hkl, h0,
              vec_index_mut_usize_ok, lift]]
          simp only [bind_ok]
          rw [loop_unfold]
          simp [sim.step.trigger_failure_loop1.body]
        · simp [simTFR, List.getD_eq_getElem?_getD, hkl, h0]

/-- The spec's override pass (`forIn c.failOverrides` of `triggerFailure`), on the state `h` after the
`failTriggers` increment: the state returned early, or `none` (every override allowed the fail). -/
def simTFS (h : OsuModel.Sim.HealthSt) : List OsuModel.Sim.FailOverride → Option OsuModel.Sim.HealthSt
  | [] => none
  | .veto :: _ => some h
  | .allow :: t => simTFS h t
  | .easy k :: t =>
    if hk : k < h.retries.size then
      if (h.retries[k] != 0) = true then some { h with health := 1, retries := h.retries.set k (h.retries[k] - 1) hk }
      else simTFS h t
    else none

/-- One step of the spec's loop body. -/
def simTFStep (h : OsuModel.Sim.HealthSt) (o : OsuModel.Sim.FailOverride) :
    Except String (ForInStep (Option OsuModel.Sim.HealthSt × Unit)) :=
  match o with
  | .veto => pure (ForInStep.done (some h, ()))
  | .allow => pure (ForInStep.yield (none, ()))
  | .easy k =>
    if hk : k < h.retries.size then
      if (h.retries[k] != 0) = true then
        pure (ForInStep.done (some { h with health := 1, retries := h.retries.set k (h.retries[k] - 1) hk }, ()))
      else pure (ForInStep.yield (none, ()))
    else do
      throw (toString "internal: EZ lives index " ++ toString k ++ toString " out of range")
      pure (ForInStep.yield (none, ()))

theorem sim_tf_spec_loop (h : OsuModel.Sim.HealthSt)
    (F : OsuModel.Sim.FailOverride → Option OsuModel.Sim.HealthSt × Unit →
      Except String (ForInStep (Option OsuModel.Sim.HealthSt × Unit)))
    (hF : ∀ o r, F o r = simTFStep h o) :
    ∀ (l : List OsuModel.Sim.FailOverride), (∀ k, OsuModel.Sim.FailOverride.easy k ∈ l → k < h.retries.size) →
      forIn l (none, ()) F = .ok (simTFS h l, ()) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o t ih =>
    intro hk
    rw [List.forIn_cons, hF]
    cases o with
    | veto => rfl
    | allow =>
      simp only [simTFStep, simTFS]
      exact ih (fun k hm => hk k (List.mem_cons_of_mem _ hm))
    | easy k =>
      have hkk := hk k List.mem_cons_self
      simp only [simTFStep, simTFS, dif_pos hkk]
      by_cases hr : (h.retries[k] != 0) = true
      · rw [if_pos hr, if_pos hr]; rfl
      · rw [if_neg hr, if_neg hr]
        exact ih (fun k hm => hk k (List.mem_cons_of_mem _ hm))
theorem sim_wsub1 (x : U64) (h : x.val ≠ 0) : (core.num.U64.wrapping_sub x 1#u64).val = x.val - 1 := by
  have hb : (core.num.U64.wrapping_sub x 1#u64).bv = x.bv - 1#64 := by simp
  have hv : x.val = x.bv.toNat := rfl
  have hw : (core.num.U64.wrapping_sub x 1#u64).val = (core.num.U64.wrapping_sub x 1#u64).bv.toNat := rfl
  rw [hw, hb, hv]; rw [hv] at h
  rw [BitVec.toNat_sub]; simp; omega

theorem sim_tf_spec_arr (h : OsuModel.Sim.HealthSt)
    (F : OsuModel.Sim.FailOverride → Option OsuModel.Sim.HealthSt × Unit →
      Except String (ForInStep (Option OsuModel.Sim.HealthSt × Unit)))
    (hF : ∀ o r, F o r = simTFStep h o) (l : List sim.mods.FailOverride)
    (hk : ∀ k, sim.mods.FailOverride.Easy k ∈ l → k.val < h.retries.size) :
    forIn (l.map (fun x => (abs x : OsuModel.Sim.FailOverride))).toArray (none, ()) F = .ok (simTFS h (l.map abs), ()) := by
  rw [List.forIn_toArray]
  apply sim_tf_spec_loop h F hF
  intro k hm
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hm
  cases o with
  | Easy k' => simp [abs] at e; subst e; exact hk k' ho
  | _ => simp [abs] at e

/-- The Rust model and the spec model of the override pass agree (on `abs`-related states). -/
theorem sim_tf_models (h : OsuModel.Sim.HealthSt) (f : F64) (v : List U64)
    (hf : h.health = f) (hv : h.retries = (v.map (·.val)).toArray) :
    ∀ (l : List sim.mods.FailOverride), (∀ k, sim.mods.FailOverride.Easy k ∈ l → k.val < v.length) →
      simTFS h (l.map abs) = (if (simTFR f v l).2.2 then
        some { h with health := (simTFR f v l).1, retries := ((simTFR f v l).2.1.map (·.val)).toArray } else none) := by
  intro l
  induction l with
  | nil => intro _; simp [simTFS, simTFR]
  | cons o t ih =>
    intro hk
    have ih' := ih (fun k hm => hk k (List.mem_cons_of_mem _ hm))
    cases o with
    | Veto => simp [simTFS, simTFR, abs]; cases h; simp_all
    | Allow =>
      show simTFS h (.allow :: t.map abs) = _
      simp only [simTFS, simTFR]; exact ih'
    | Easy k =>
      have hkk := hk k List.mem_cons_self
      have hks : k.val < h.retries.size := by rw [hv]; simpa using hkk
      show simTFS h (.easy k.val :: t.map abs) = _
      simp only [simTFS, dif_pos hks]
      have hr : h.retries[k.val]'hks = (v[k.val]'hkk).val := by simp [hv]
      by_cases h0 : (v[k.val]'hkk).val = 0
      · have : ¬ (h.retries[k.val]'hks != 0) = true := by simp [hr, h0]
        rw [if_neg this]
        have e : simTFR f v (.Easy k :: t) = simTFR f v t := by simp [simTFR, List.getD_eq_getElem?_getD, hkk, h0]
        rw [e]; exact ih'
      · have : (h.retries[k.val]'hks != 0) = true := by simp [hr, h0]
        rw [if_pos this]
        simp [simTFR, List.getD_eq_getElem?_getD, hkk, h0]
        have hb : (v[k.val]'hkk).val < U64.size := by scalar_tac
        have key : ((v[k.val]'hkk).val + (U64.size - 1)) % U64.size = (v[k.val]'hkk).val - 1 := by
          clear * - h0 hb
          rw [show (v[k.val]'hkk).val + (U64.size - 1) = ((v[k.val]'hkk).val - 1) + U64.size by
            have : 0 < U64.size := by simp [U64.size]
            omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        cases h; simp_all [sim_wsub1, List.map_set]

/-- Guarded: every EZ index of the config is in range of `retries` (initState's invariant) and the
`failTriggers` increment does not overflow. -/
theorem sim.step.trigger_failure_refines (c : sim.mods.Config) (h : sim.scoring.HealthSt) (t : F64)
    (rp : Bool) (lf : Option F64)
    (hk : ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < h.retries.val.length)
    (ht : h.fail_triggers.val + 1 ≤ U64.max) :
    ∃ r, sim.step.trigger_failure c h t rp lf = ok r ∧
      OsuModel.Sim.Sim.triggerFailure (abs c) (abs h) (abs t) (abs rp) (abs lf) = .ok (abs r) := by
  cases hf : h.has_failed
  · obtain ⟨i1, hi1, hi1v⟩ : ∃ i1, h.fail_triggers + 1#u64 = ok i1 ∧ i1.val = h.fail_triggers.val + 1 := by
      have := U64.add_spec (x := h.fail_triggers) (y := 1#u64) (by simpa using ht)
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec this
      exact ⟨z, hz, by simpa using hzv⟩
    obtain ⟨r1, hr1, er1⟩ := sim_tf_loop c h.health h.retries hk 0#usize (by simp)
    have hr0 : sim.step.trigger_failure_loop0 c h.health h.retries false 0#usize = ok r1 := by
      unfold sim.step.trigger_failure_loop1 at hr1; unfold sim.step.trigger_failure_loop0; exact hr1
    unfold sim.step.trigger_failure OsuModel.Sim.Sim.triggerFailure
    simp only [hf, sim_health_clone, hi1, hr0, hr1, bind_ok, Bool.false_eq_true, ite_false]
    let hS : OsuModel.Sim.HealthSt := { (abs h : OsuModel.Sim.HealthSt) with failTriggers := (abs h : OsuModel.Sim.HealthSt).failTriggers + 1 }
    have hkS : ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < hS.retries.size := by
      intro k hm; simpa [hS, abs] using hk k hm
    have hmod := sim_tf_models hS h.health h.retries.val rfl rfl c.fail_overrides.val hk
    rw [show (abs c : OsuModel.Sim.Config).failOverrides =
        (c.fail_overrides.val.map (fun x => (abs x : OsuModel.Sim.FailOverride))).toArray from rfl]
    rw [sim_tf_spec_arr hS _ ?hF c.fail_overrides.val hkS]
    case hF => intro o r; cases o <;> rfl
    rw [hmod]
    obtain ⟨f', v', st⟩ := r1
    have e0 : (0#usize : Usize).val = 0 := rfl
    rw [e0, List.drop_zero] at er1
    have hns := sim_tfr_nostop h.health h.retries.val c.fail_overrides.val
    rw [← er1] at hns
    rw [← er1]
    simp only at hns ⊢
    cases rp <;> cases lf <;> cases st <;> simp [hf, abs, hS, hi1v, Except.bind, pure, Except.pure] <;>
      (try split_ifs) <;> simp_all [abs, hS]
  · refine ⟨h, by simp [sim.step.trigger_failure, hf], ?_⟩
    simp [OsuModel.Sim.Sim.triggerFailure, abs, hf]

end OsuProofs
