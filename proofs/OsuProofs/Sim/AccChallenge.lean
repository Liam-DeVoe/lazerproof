/-
`sim::step::acc_challenge` (Rust) refines `Sim.accChallenge` (ModAccuracyChallenge handlers: two passes, Standard
`Accuracy` then `MaximumAccuracy`, each triggering `triggerFailure` for the AC entries below their minimum).
-/
import OsuProofs.Sim.HealthApply
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs

section
open OsuImpl OsuModel.Net

theorem sim_tfr_len (f : F64) (v : List U64) : ∀ l, (simTFR f v l).2.1.length = v.length := by
  intro l; induction l with
  | nil => rfl
  | cons o t ih => cases o <;> simp [simTFR, ih] <;> split <;> simp [ih]

/-- `trigger_failure` keeps the number of EZ lives and adds at most one fail trigger. -/
theorem sim.step.trigger_failure_props (c : sim.mods.Config) (h : sim.scoring.HealthSt) (t : F64)
    (rp : Bool) (lf : Option F64)
    (hk : ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < h.retries.val.length)
    (ht : h.fail_triggers.val + 1 ≤ U64.max) (r : sim.scoring.HealthSt)
    (hr : sim.step.trigger_failure c h t rp lf = ok r) :
    r.retries.val.length = h.retries.val.length ∧ r.fail_triggers.val ≤ h.fail_triggers.val + 1 := by
  cases hf : h.has_failed
  · obtain ⟨i1, hi1, hi1v⟩ : ∃ i1, h.fail_triggers + 1#u64 = ok i1 ∧ i1.val = h.fail_triggers.val + 1 := by
      have := U64.add_spec (x := h.fail_triggers) (y := 1#u64) (by simpa using ht)
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec this
      exact ⟨z, hz, by simpa using hzv⟩
    obtain ⟨r1, hr1, er1⟩ := sim_tf_loop c h.health h.retries hk 0#usize (by simp)
    have hr0 : sim.step.trigger_failure_loop0 c h.health h.retries false 0#usize = ok r1 := by
      unfold sim.step.trigger_failure_loop1 at hr1; unfold sim.step.trigger_failure_loop0; exact hr1
    have hlen : r1.2.1.val.length = h.retries.val.length := by
      have := congrArg (fun p => p.2.1.length) er1; simp only at this; rw [this, sim_tfr_len]
    unfold sim.step.trigger_failure at hr
    simp only [hf, sim_health_clone, hi1, hr0, hr1, bind_ok, Bool.false_eq_true, ite_false] at hr
    obtain ⟨f', v', st⟩ := r1
    simp only at hlen
    cases rp <;> cases lf <;> cases st <;> simp at hr <;> (try split at hr) <;>
      first | (subst hr; simp [hi1v, hlen]) | (have := Result.ok_injective hr; subst this; simp [hi1v, hlen])
  · simp [sim.step.trigger_failure, hf] at hr
    first | (subst hr; simp) | (have := Result.ok_injective hr; subst this; simp)

end
section
open OsuImpl OsuModel.Net

/-- the configuration tuple the translated inner AC loop returns -/
def simCfgT (c : sim.mods.Config) (h : sim.scoring.HealthSt) :=
  (c.policy, c.classic_head_block, c.legacy_health, c.fail_overrides, c.easy_retries, c.fail_conds, c.acc_challenges,
    c.rank_adjust, c.rate_sources, c.dyn_rates, c.score_multiplier, c.updatables, c.input_blockers, c.spun_out,
    c.strict_tracking, c.lazer_replay, c.rate_mods, c.vis_mods, c.depth_max, c.magnet_strength, c.repel_strength,
    c.barrel_roll, h)

theorem sim_except_forIn_cons {α β ε} (a : α) (t : List α) (b : β) (F : α → β → Except ε (ForInStep β)) :
    forIn (a :: t) b F = (F a b).bind (fun r => match r with | .done c => .ok c | .yield c => forIn t c F) := by
  rw [List.forIn_cons]; rfl

theorem sim_acc_inner (c : sim.mods.Config) (t : F64) (rp : Bool) (lf : Option F64) (std : Bool) (n : F64)
    (F : (F64 × Bool) → OsuModel.Sim.HealthSt → Except String (ForInStep OsuModel.Sim.HealthSt))
    (hF : ∀ x b, F x b = if (x.2 == std && decide (n < x.1)) = true then
      (OsuModel.Sim.Sim.triggerFailure (abs c) b t rp (abs lf)).bind (fun y => .ok (.yield y)) else .ok (.yield b)) :
    ∀ m (k : Usize) (h : sim.scoring.HealthSt), c.acc_challenges.val.length - k.val = m → k.val ≤ c.acc_challenges.val.length →
      (∀ e, sim.mods.FailOverride.Easy e ∈ c.fail_overrides.val → e.val < h.retries.val.length) →
      h.fail_triggers.val + m ≤ U64.max →
      ∃ h', sim.step.acc_challenge_loop0_loop0 c t rp lf h std n k = ok (simCfgT c h') ∧
        forIn ((c.acc_challenges.val.drop k.val).map (fun a => (abs a : F64 × Bool))) (abs h) F = .ok (abs h') ∧
        h'.retries.val.length = h.retries.val.length ∧ h'.fail_triggers.val ≤ h.fail_triggers.val + m := by
  intro m
  induction m with
  | zero =>
    intro k h hm hk hk2 ht
    have hd : c.acc_challenges.val.drop k.val = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨h, ?_, by rw [hd]; rfl, rfl, by omega⟩
    unfold sim.step.acc_challenge_loop0_loop0; rw [loop_unfold]
    have : ¬ k < alloc.vec.Vec.len c.acc_challenges := by rw [vec_lt_len_iff]; omega
    simp [sim.step.acc_challenge_loop0_loop0.body, this, simCfgT]
  | succ m ih =>
    intro k h hm hk hk2 ht
    have hkl : k.val < c.acc_challenges.val.length := by omega
    have hkv : k < alloc.vec.Vec.len c.acc_challenges := by rw [vec_lt_len_iff]; exact hkl
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := c.acc_challenges.property; omega)
    rw [List.drop_eq_getElem_cons hkl, List.map_cons, sim_except_forIn_cons, hF]
    set ac := c.acc_challenges.val[k.val]'hkl with hac
    by_cases hc : (ac.standard == std && decide (n < ac.min_acc)) = true
    · obtain ⟨tf, htf, etf⟩ := sim.step.trigger_failure_refines c h t rp lf hk2 (by omega)
      obtain ⟨hl1, hl2⟩ := sim.step.trigger_failure_props c h t rp lf hk2 (by omega) tf htf
      obtain ⟨h', hh', eh', hl', ht'⟩ := ih k1 tf (by omega) (by omega) (by rw [hl1]; exact hk2) (by omega)
      refine ⟨h', ?_, ?_, by rw [hl', hl1], by omega⟩
      · unfold sim.step.acc_challenge_loop0_loop0; rw [loop_unfold]; dsimp only
        have hstd : ac.standard = std := by simp at hc; exact hc.1
        have hlt : n < ac.min_acc := by simp at hc; exact hc.2
        rw [show sim.step.acc_challenge_loop0_loop0.body c t rp lf std n h k = ok (.cont (tf, k1)) by
          simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hlt, htf, hk1]]
        simp only [bind_ok]
        unfold sim.step.acc_challenge_loop0_loop0 at hh'; exact hh'
      · have hc' : ((abs ac : F64 × Bool).2 == std && decide (n < (abs ac : F64 × Bool).1)) = true := hc
        simp only [hc', ite_true]
        have etf' : OsuModel.Sim.Sim.triggerFailure (abs c) (abs h) t rp (abs lf) = .ok (abs tf) := etf
        rw [etf']; simp only [Except.bind]
        rw [hk1v] at eh'; exact eh'
    · obtain ⟨h', hh', eh', hl', ht'⟩ := ih k1 h (by omega) (by omega) hk2 (by omega)
      refine ⟨h', ?_, ?_, hl', by omega⟩
      · unfold sim.step.acc_challenge_loop0_loop0; rw [loop_unfold]; dsimp only
        rw [show sim.step.acc_challenge_loop0_loop0.body c t rp lf std n h k = ok (.cont (h, k1)) by
          by_cases hstd : ac.standard = std
          · have hlt : ¬ n < ac.min_acc := by simpa [hstd] using hc
            simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hlt, hk1]
          · simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hk1]]
        simp only [bind_ok]
        unfold sim.step.acc_challenge_loop0_loop0 at hh'; exact hh'
      · have hc' : ¬ ((abs ac : F64 × Bool).2 == std && decide (n < (abs ac : F64 × Bool).1)) = true := hc
        simp only [hc', ite_false, Bool.false_eq_true]
        rw [hk1v] at eh'; exact eh'

end
section
open OsuImpl OsuModel.Net

theorem sim_cfg_rebuild (c : sim.mods.Config) :
    ({ policy := c.policy, classic_head_block := c.classic_head_block, legacy_health := c.legacy_health,
       fail_overrides := c.fail_overrides, easy_retries := c.easy_retries, fail_conds := c.fail_conds,
       acc_challenges := c.acc_challenges, rank_adjust := c.rank_adjust, rate_sources := c.rate_sources,
       dyn_rates := c.dyn_rates, score_multiplier := c.score_multiplier, updatables := c.updatables,
       input_blockers := c.input_blockers, spun_out := c.spun_out, strict_tracking := c.strict_tracking,
       lazer_replay := c.lazer_replay, rate_mods := c.rate_mods, vis_mods := c.vis_mods, depth_max := c.depth_max,
       magnet_strength := c.magnet_strength, repel_strength := c.repel_strength, barrel_roll := c.barrel_roll } :
      sim.mods.Config) = c := rfl

/-- one AC pass (`std`): the Rust inner loop from 0 and the spec inner `forIn` (any body equal to the spec's) -/
theorem sim_acc_pass (c : sim.mods.Config) (t : F64) (rp : Bool) (lf : Option F64) (std : Bool) (n : F64)
    (h : sim.scoring.HealthSt)
    (hk : ∀ e, sim.mods.FailOverride.Easy e ∈ c.fail_overrides.val → e.val < h.retries.val.length)
    (ht : h.fail_triggers.val + c.acc_challenges.val.length ≤ U64.max) :
    ∃ h', sim.step.acc_challenge_loop0_loop0 c t rp lf h std n 0#usize = ok (simCfgT c h') ∧
      (∀ (F : (F64 × Bool) → OsuModel.Sim.HealthSt → Except String (ForInStep OsuModel.Sim.HealthSt)),
        (∀ x b, F x b = if (x.2 == std && decide (n < x.1)) = true then
          (OsuModel.Sim.Sim.triggerFailure (abs c) b t rp (abs lf)).bind (fun y => .ok (.yield y)) else .ok (.yield b)) →
        forIn (abs c : OsuModel.Sim.Config).accChallenges (abs h) F = .ok (abs h')) ∧
      h'.retries.val.length = h.retries.val.length ∧
      h'.fail_triggers.val ≤ h.fail_triggers.val + c.acc_challenges.val.length := by
  obtain ⟨h', e1, e2, e3, e4⟩ := sim_acc_inner c t rp lf std n (fun x (b : OsuModel.Sim.HealthSt) =>
        if (x.2 == std && decide (n < x.1)) = true then
          (OsuModel.Sim.Sim.triggerFailure (abs c) b t rp (abs lf)).bind (fun y => .ok (.yield y)) else .ok (.yield b))
      (fun x b => rfl) c.acc_challenges.val.length 0#usize h (by simp) (by simp) hk ht
  refine ⟨h', e1, fun F hF => ?_, e3, e4⟩
  have : F = (fun x (b : OsuModel.Sim.HealthSt) =>
        if (x.2 == std && decide (n < x.1)) = true then
          (OsuModel.Sim.Sim.triggerFailure (abs c) b t rp (abs lf)).bind (fun y => .ok (.yield y)) else .ok (.yield b)) := by
    funext x b; exact hF x b
  subst this
  rw [show (abs c : OsuModel.Sim.Config).accChallenges = (c.acc_challenges.val.map (fun a => (abs a : F64 × Bool))).toArray
    from rfl, List.forIn_toArray]
  simpa using e2

end
section
open OsuImpl OsuModel.Net

theorem sim_usize_succ_lit (a b : Usize) (h : b.val = a.val + 1) (hb : b.val ≤ Usize.max) : a + 1#usize = ok b := by
  obtain ⟨j, hj, hjv⟩ := usize_add_one a (by omega)
  rw [hj]; congr 1; exact UScalar.eq_of_val_eq (by rw [hjv, h])
theorem sim_usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  rw [Usize.max_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
theorem sim_a01 : (0#usize + 1#usize : Result Usize) = ok 1#usize :=
  sim_usize_succ_lit _ _ (by simp) (by have := sim_usize_max_ge; simp; omega)
theorem sim_a12 : (1#usize + 1#usize : Result Usize) = ok 2#usize :=
  sim_usize_succ_lit _ _ (by simp) (by have := sim_usize_max_ge; simp; omega)

theorem sim.step.acc_challenge_refines (c : sim.mods.Config) (h : sim.scoring.HealthSt) (old new : sim.scoring.ScoreSt)
    (t : F64) (rp : Bool) (lf : Option F64)
    (hk : ∀ e, sim.mods.FailOverride.Easy e ∈ c.fail_overrides.val → e.val < h.retries.val.length)
    (ht : h.fail_triggers.val + 2 * c.acc_challenges.val.length ≤ U64.max) :
    ∃ r, sim.step.acc_challenge c h old new t rp lf = ok r ∧
      OsuModel.Sim.Sim.accChallenge (abs c) (abs h) (abs old) (abs new) t rp (abs lf) = .ok (abs r) := by
  -- pass 0 (Standard: `Accuracy`)
  obtain ⟨h1, e1, s1, l1, t1⟩ := sim_acc_pass c t rp lf true new.accuracy h hk (by omega)
  obtain ⟨h2, e2, s2, l2, t2⟩ := sim_acc_pass c t rp lf false new.maximum_accuracy
    (if Framework.Bindable.equalsD old.accuracy new.accuracy then h else h1)
    (by split <;> [exact hk; (rw [l1]; exact hk)]) (by split <;> omega)
  set hm := (if Framework.Bindable.equalsD old.accuracy new.accuracy then h else h1) with hhm
  refine ⟨if Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy then hm else h2, ?_, ?_⟩
  · unfold sim.step.acc_challenge sim.step.acc_challenge_loop0
    rw [loop_unfold]
    have p0 : sim.step.acc_challenge_loop0.body old new t rp lf c h 0#usize = ok (.cont (c, hm, 1#usize)) := by
      cases he : Framework.Bindable.equalsD old.accuracy new.accuracy <;>
        simp [sim.step.acc_challenge_loop0.body, sim.netx.equals_d_refines, he, hhm, e1, simCfgT, sim_a01]
    simp only [p0, bind_ok]
    rw [loop_unfold]
    have p1 : sim.step.acc_challenge_loop0.body old new t rp lf c hm 1#usize =
        ok (.cont (c, (if Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy then hm else h2), 2#usize)) := by
      cases he : Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy <;>
        simp [sim.step.acc_challenge_loop0.body, sim.netx.equals_d_refines, he, e2, simCfgT, sim_a12]
    simp only [p1, bind_ok]
    rw [loop_unfold]
    simp [sim.step.acc_challenge_loop0.body]
  · unfold OsuModel.Sim.Sim.accChallenge
    simp only [sim_except_forIn_cons, ite_true, Bool.false_eq_true, ite_false, if_true]
    have hacc : (abs old : OsuModel.Sim.ScoreSt).accuracy = old.accuracy := rfl
    have hacc2 : (abs new : OsuModel.Sim.ScoreSt).accuracy = new.accuracy := rfl
    have hm1 : (abs old : OsuModel.Sim.ScoreSt).maximumAccuracy = old.maximum_accuracy := rfl
    have hm2 : (abs new : OsuModel.Sim.ScoreSt).maximumAccuracy = new.maximum_accuracy := rfl
    simp only [hacc, hacc2, hm1, hm2]
    cases he1 : Framework.Bindable.equalsD old.accuracy new.accuracy <;>
      cases he2 : Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy <;>
      simp only [he1, he2, hhm, ite_true, ite_false, Bool.false_eq_true] at s2 ⊢
    · rw [s1 _ ?a1]
      · simp only [Except.bind, pure, Except.pure, Bind.bind]
        rw [s2 _ ?a2]
        · rfl
        · intro x b; rfl
      · intro x b; rfl
    · rw [s1 _ ?b1]
      · rfl
      · intro x b; rfl
    · simp only [Except.bind, pure, Except.pure, Bind.bind]
      rw [s2 _ ?c2]
      · rfl
      · intro x b; rfl
    · rfl

end

end OsuProofs
