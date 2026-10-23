/-
proc (D73): the judgement writes keep the drain-period cursor. `trigger_failure`, `health_apply`, `acc_challenge`,
`emit_one` and `emit` never write `HealthSt.nearest_index` (only `sim::scoring::drain` in `processors_phase` does), so
`emit` keeps `health.nearest_index` and `health_rp.nearest_index`. Used by `SimQOk.emit` (Sim/ApplyFrame.lean), whence
every frame built on `simKeepS` carries both indices.
-/
import OsuProofs.Sim.EmitProps
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

theorem pr_tf_ni (c : sim.mods.Config) (h : sim.scoring.HealthSt) (t : F64) (rp : Bool) (lf : Option F64)
    (r : sim.scoring.HealthSt) (hr : sim.step.trigger_failure c h t rp lf = ok r) :
    r.nearest_index = h.nearest_index := by
  unfold sim.step.trigger_failure at hr
  cases hf : h.has_failed
  · simp only [hf, sim_health_clone, bind_ok, Bool.false_eq_true, ite_false] at hr
    cases hi : h.fail_triggers + 1#u64 with
    | vis i0 k0 => rw [hi] at hr; simp at hr
    | div => rw [hi] at hr; simp at hr
    | ret i =>
      rw [hi] at hr; simp only [bind_ok] at hr
      cases rp
      · simp only [Bool.false_eq_true, ite_false] at hr
        cases hl : sim.step.trigger_failure_loop1 c h.health h.retries false 0#usize with
        | vis i0 k0 => rw [hl] at hr; simp at hr
        | div => rw [hl] at hr; simp at hr
        | ret x =>
          rw [hl] at hr; obtain ⟨f, v, st⟩ := x
          cases st <;> simp at hr <;> subst hr <;> rfl
      · simp only [ite_true] at hr
        cases lf with
        | none => simp at hr; subst hr; rfl
        | some lf =>
          simp only [float.F64.le] at hr
          by_cases hle : lf ≤ t
          · simp only [hle, decide_true, ite_true, bind_ok] at hr
            cases hl : sim.step.trigger_failure_loop0 c h.health h.retries false 0#usize with
            | vis i0 k0 => rw [hl] at hr; simp at hr
            | div => rw [hl] at hr; simp at hr
            | ret x =>
              rw [hl] at hr; obtain ⟨f, v, st⟩ := x
              cases st <;> simp at hr <;> subst hr <;> rfl
          · simp [hle] at hr; subst hr; rfl
  · simp [hf] at hr; subst hr; rfl

theorem pr_happly_ni (h0 : sim.scoring.HealthSt) (hc : sim.scoring.HealthCfg) (c : sim.mods.Config)
    (j : sim.scoring.JInfo) (t : F64) (rp : Bool) (lf : Option F64) (r : sim.scoring.HealthSt × Bool)
    (hr : sim.step.health_apply h0 hc c j t rp lf = ok r) : r.1.nearest_index = h0.nearest_index := by
  cases hf : h0.has_failed
  · obtain ⟨cr, inc, hif, -⟩ := sim.scoring.increase_for_refines h0 hc j false
    rcases h0 with ⟨hh, hfl, crr, ni, ft, fld, fti, rts⟩
    simp only at hf; subst hf
    let h1 : sim.scoring.HealthSt := ⟨OsuModel.Sim.clamp01 (hh + inc), false, cr, ni, ft, fld, fti, rts⟩
    unfold sim.step.health_apply at hr
    simp only [hif, sim_health_clone, float.F64.add, sim_clamp01_eq, bind_ok, Bool.false_eq_true, ite_false,
      sim_default_fail_condition_eq, sim_any_fail_condition_eq, uncurry_apply_pair] at hr
    rw [show (⟨OsuModel.Sim.clamp01 (hh + inc), false, cr, ni, ft, fld, fti, rts⟩ : sim.scoring.HealthSt) = h1
      from rfl] at hr
    split at hr
    · cases htf : sim.step.trigger_failure c h1 t rp lf with
      | vis i0 k0 => rw [htf] at hr; simp at hr
      | div => rw [htf] at hr; simp at hr
      | ret tf =>
        have := pr_tf_ni c h1 t rp lf tf htf
        rw [htf] at hr; simp at hr; subst hr; exact this
    · split at hr
      · cases htf : sim.step.trigger_failure c h1 t rp lf with
        | vis i0 k0 => rw [htf] at hr; simp at hr
        | div => rw [htf] at hr; simp at hr
        | ret tf =>
          have := pr_tf_ni c h1 t rp lf tf htf
          rw [htf] at hr; simp at hr; subst hr; exact this
      · simp at hr; subst hr; rfl
  · simp [sim.step.health_apply, hf] at hr; subst hr; rfl

/-- the inner AC loop keeps the cursor (any start `k`, any number of trigger_failure calls) -/
theorem pr_acc_inner_ni (c : sim.mods.Config) (t : F64) (rp : Bool) (lf : Option F64) (std : Bool) (n : F64) :
    ∀ m (k : Usize) (h h' : sim.scoring.HealthSt), c.acc_challenges.val.length - k.val = m →
      sim.step.acc_challenge_loop0_loop0 c t rp lf h std n k = ok (simCfgT c h') →
      h'.nearest_index = h.nearest_index := by
  intro m
  induction m with
  | zero =>
    intro k h h' hm hr
    have : ¬ k < alloc.vec.Vec.len c.acc_challenges := by rw [vec_lt_len_iff]; omega
    unfold sim.step.acc_challenge_loop0_loop0 at hr; rw [loop_unfold] at hr; dsimp only at hr
    simp [sim.step.acc_challenge_loop0_loop0.body, this, simCfgT] at hr
    rw [hr]
  | succ m ih =>
    intro k h h' hm hr
    have hkl : k.val < c.acc_challenges.val.length := by omega
    have hkv : k < alloc.vec.Vec.len c.acc_challenges := by rw [vec_lt_len_iff]; exact hkl
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := c.acc_challenges.property; omega)
    set ac := c.acc_challenges.val[k.val]'hkl with hac
    unfold sim.step.acc_challenge_loop0_loop0 at hr; rw [loop_unfold] at hr; dsimp only at hr
    have hstep : ∀ h1, h1.nearest_index = h.nearest_index →
        sim.step.acc_challenge_loop0_loop0.body c t rp lf std n h k = ok (.cont (h1, k1)) →
        h'.nearest_index = h.nearest_index := by
      intro h1 e1 hb
      rw [hb] at hr; simp only [bind_ok] at hr
      rw [← e1]; exact ih k1 h1 h' (by omega) hr
    by_cases hstd : ac.standard = std
    · by_cases hlt : n < ac.min_acc
      · cases htf : sim.step.trigger_failure c h t rp lf with
        | vis i0 k0 =>
          simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hlt, htf,
            float.F64.lt] at hr
        | div =>
          simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hlt, htf,
            float.F64.lt] at hr
        | ret tf =>
          exact hstep tf (pr_tf_ni c h t rp lf tf htf) (by
            simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hlt, htf, hk1,
              float.F64.lt])
      · exact hstep h rfl (by
          simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hlt, hk1,
            float.F64.lt])
    · exact hstep h rfl (by
        simp [sim.step.acc_challenge_loop0_loop0.body, hkv, vec_index_usize_ok _ _ hkl, ← hac, hstd, hk1])

theorem pr_acc_ni (c : sim.mods.Config) (h : sim.scoring.HealthSt) (old new : sim.scoring.ScoreSt)
    (t : F64) (rp : Bool) (lf : Option F64)
    (hk : ∀ e, sim.mods.FailOverride.Easy e ∈ c.fail_overrides.val → e.val < h.retries.val.length)
    (ht : h.fail_triggers.val + 2 * c.acc_challenges.val.length ≤ U64.max) (r : sim.scoring.HealthSt)
    (hr : sim.step.acc_challenge c h old new t rp lf = ok r) :
    r.nearest_index = h.nearest_index := by
  obtain ⟨h1, e1, s1, l1, t1⟩ := sim_acc_pass c t rp lf true new.accuracy h hk (by omega)
  obtain ⟨h2, e2, s2, l2, t2⟩ := sim_acc_pass c t rp lf false new.maximum_accuracy
    (if Framework.Bindable.equalsD old.accuracy new.accuracy then h else h1)
    (by split <;> [exact hk; (rw [l1]; exact hk)]) (by split <;> omega)
  set hm := (if Framework.Bindable.equalsD old.accuracy new.accuracy then h else h1) with hhm
  have hres : sim.step.acc_challenge c h old new t rp lf =
      ok (if Framework.Bindable.equalsD old.maximum_accuracy new.maximum_accuracy then hm else h2) := by
    unfold sim.step.acc_challenge sim.step.acc_challenge_loop0
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
  rw [hres] at hr
  cases Result.ok_injective hr
  have n1 : h1.nearest_index = h.nearest_index := pr_acc_inner_ni c t rp lf true new.accuracy _ 0#usize h h1 rfl e1
  have nm : hm.nearest_index = h.nearest_index := by rw [hhm]; split <;> [rfl; exact n1]
  have n2 : h2.nearest_index = hm.nearest_index :=
    pr_acc_inner_ni c t rp lf false new.maximum_accuracy _ 0#usize hm h2 rfl e2
  split <;> [exact nm; (rw [n2]; exact nm)]

theorem pr_emit_one_ni (c : sim.state.Ctx) (j : sim.scoring.JInfo) (t : F64) (hs : sim.scoring.HealthSt)
    (ss : sim.scoring.ScoreSt) (rp : Bool) (hok : simEmitOk c hs ss) (r : sim.scoring.HealthSt × sim.scoring.ScoreSt × Bool × U64)
    (hr : sim.step.emit_one c j t hs ss rp = ok r) : r.1.nearest_index = hs.nearest_index := by
  obtain ⟨hk, ht, h3, h4, h5, h6⟩ := hok
  obtain ⟨⟨h1, fl⟩, e1, -⟩ := sim.step.health_apply_refines hs c.hcfg c.cfg j t rp c.last_frame_time hk (by omega)
  obtain ⟨p1, p2⟩ := sim.step.health_apply_props hs c.hcfg c.cfg j t rp c.last_frame_time hk (by omega) _ e1
  have n1 := pr_happly_ni hs c.hcfg c.cfg j t rp c.last_frame_time _ e1
  simp only at p1 p2 n1
  obtain ⟨⟨ss2, combo⟩, e2, -⟩ := sim.scoring.score_apply_refines ss c.smax j fl false h3 h4 h5 h6
  obtain ⟨h2, e3, -⟩ := sim.step.acc_challenge_refines c.cfg h1 ss ss2 t rp c.last_frame_time
    (by rw [p1]; exact hk) (by omega)
  have n2 := pr_acc_ni c.cfg h1 ss ss2 t rp c.last_frame_time (by rw [p1]; exact hk) (by omega) h2 e3
  have : r = (h2, ss2, fl, combo) := by
    have e : sim.step.emit_one c j t hs ss rp = ok (h2, ss2, fl, combo) := by simp [sim.step.emit_one, e1, e2, e3]
    rw [e] at hr; exact (Result.ok_injective hr).symm
  subst this
  simp only; rw [n2, n1]

/-- `emit` keeps both drain-period cursors -/
theorem pr_emit_ni (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref) (ty : sim.basic.HitResult) (t : F64)
    (hr : simRefOk c r) (hl : simEmitOk c s.health s.score) (hrp : simEmitOk c s.health_rp s.score_rp)
    (hout : s.out.val.length < Usize.max)
    (s' : sim.state.St) (he : sim.step.emit c s r ty t = ok s') :
    s'.health.nearest_index = s.health.nearest_index ∧ s'.health_rp.nearest_index = s.health_rp.nearest_index := by
  obtain ⟨hh, _⟩ := sim_hobj_of_eq (fun _ => "") (alloc.vec.Vec.new Usize) c r hr
  unfold sim.step.emit at he
  simp only [hh, bind_ok, float.F64.add, net.min_refines, float.F64.sub] at he
  generalize hj : (⟨(simHobj c r).kind, (simHobj c r).max_result, (simHobj c r).min_result, ty,
    F64.min t ((simHobj c r).end_time + (simHobj c r).max_judgement_offset), (simHobj c r).end_time,
    F64.min (t - (simHobj c r).end_time) (simHobj c r).max_judgement_offset, (simHobj c r).new_combo,
    (simHobj c r).last_in_combo⟩ : sim.scoring.JInfo) = j at he
  obtain ⟨r1, h1, -⟩ := sim.step.emit_one_refines c j t s.health s.score false hl
  obtain ⟨r2, h2, -⟩ := sim.step.emit_one_refines c j t s.health_rp s.score_rp true hrp
  have a := pr_emit_one_ni c j t s.health s.score false hl r1 h1
  have b := pr_emit_one_ni c j t s.health_rp s.score_rp true hrp r2 h2
  obtain ⟨x1, x2, x3, x4⟩ := r1
  obtain ⟨y1, y2, y3, y4⟩ := r2
  rw [h1, h2] at he
  simp only [bind_ok, vec_push_ok _ _ hout, ok.injEq] at he
  obtain rfl := Result.ok_injective he
  exact ⟨a, b⟩
end OsuProofs
