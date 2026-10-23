/-
sim6 (D64): the input press chain of `sim::step` against `OsuModel.Sim.Sim`: `intercept_press` (AL/SG interceptor),
`propagate_press` (interceptor loop + receptor loop with `circle_update_result` and the `hit_action` write),
`trigger_pressed`, and `legacy_blocked_by_earlier` (FRAGMENT of the legacy `checkHittable` loop).
Results are stated in sim core's style: `SimARInv .. e 0 0` and `simLP` preserved, frame `s6PFr` (judgement fields,
`hit_action`, `pressed`, the block trackers with the same lengths), block-tracker invariant `s6Blk`.
-/
import OsuProofs.Sim.OnKilled
import OsuProofs.Sim.LegacyHit
import OsuProofs.Sim3.SB_Upd2
import OsuProofs.Sim3.SC_Misc
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net
/-- the input-blocker trackers of the state are in range (AL/SG: `block_last`/`block_idx` per blocker, stored period
indices valid) -/
def s6Blk (c : sim.state.Ctx) (s : sim.state.St) : Prop :=
  c.cfg.input_blockers.val.length ≤ s.block_last.val.length ∧
  c.cfg.input_blockers.val.length ≤ s.block_idx.val.length ∧
  (c.block_periods.val.length ≠ 0 → ∀ x ∈ s.block_idx.val, x.val < c.block_periods.val.length)

/-- `s'` differs from `s` only in the input-blocker trackers (same lengths) -/
def s6BF (s s' : sim.state.St) : Prop := ∃ x y, s' = { s with block_last := x, block_idx := y } ∧
  x.val.length = s.block_last.val.length ∧ y.val.length = s.block_idx.val.length

theorem s6BF_refl (s : sim.state.St) : s6BF s s := ⟨_, _, rfl, rfl, rfl⟩
theorem s6BF_trans {s1 s2 s3 : sim.state.St} (h1 : s6BF s1 s2) (h2 : s6BF s2 s3) : s6BF s1 s3 := by
  obtain ⟨_, _, rfl, a1, b1⟩ := h1; obtain ⟨_, _, rfl, a2, b2⟩ := h2; exact ⟨_, _, rfl, a2.trans a1, b2.trans b1⟩

theorem s6_pia (ps : Slice sim.playable.Period) (idx : Usize) (time : F64)
    (hidx : ps.val.length ≠ 0 → idx.val < ps.val.length) :
    ∃ r, sim.scoring.period_is_in_any ps idx time = ok r ∧
      OsuModel.Sim.periodIsInAny (simPS ps).toArray idx.val time = .ok (r.1, r.2.val) ∧
      (ps.val.length ≠ 0 → r.2.val < ps.val.length) := by
  obtain ⟨r, hr, er⟩ := sim.scoring.period_is_in_any_refines ps idx time hidx
  refine ⟨r, hr, er, fun h0 => ?_⟩
  have hlen : (simPS ps).length = ps.val.length := by simp [simPS]
  have hi' : idx.val < (simPS ps).length := by rw [hlen]; exact hidx h0
  rw [simS_periodIsInAny (simPS ps) idx.val time hi'] at er
  dsimp only at er
  simp only [Except.ok.injEq, Prod.mk.injEq] at er
  rw [← er.2, ← hlen]
  split
  · exact sim_fwd_lt _ _ _ _ hi'
  · exact sim_bwd_lt _ _ _ _ hi'

theorem s6_blk_set (c : sim.state.Ctx) (s : sim.state.St) (hB : s6Blk c s) (k : Usize) (idx : Usize)
    (hk : k.val < s.block_idx.val.length)
    (hidx : c.block_periods.val.length ≠ 0 → idx.val < c.block_periods.val.length)
    (bl : alloc.vec.Vec (Option replay.frames.Action)) (hbl : bl.val.length = s.block_last.val.length) :
    s6Blk c { s with block_last := bl, block_idx := s.block_idx.set k idx } := by
  obtain ⟨h1, h2, h3⟩ := hB
  refine ⟨by simp only; omega, by simp [vec_set_val']; omega, fun h0 x hx => ?_⟩
  simp only [vec_set_val'] at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact h3 h0 x hx
  · subst hx; exact hidx h0

/-- closed form of the Rust `intercept_press` after `period_is_in_any` returned `(ia, idx)` -/
def s6IP (c : sim.state.Ctx) (s : sim.state.St) (k : Usize) (a : replay.frames.Action) (ia : Bool) (idx : Usize)
    (last : Option replay.frames.Action) (alt : Bool) : Bool × sim.state.St :=
  if ia then (false, { s with block_idx := s.block_idx.set k idx })
  else if !(actS a == .left || actS a == .right) then (false, { s with block_idx := s.block_idx.set k idx })
  else if (if alt then !(last.map actS == some (actS a)) else (last.isNone || last.map actS == some (actS a))) then
    (false, { s with block_last := s.block_last.set k (some a), block_idx := s.block_idx.set k idx })
  else (true, { s with block_idx := s.block_idx.set k idx })

theorem s6_ip_rust (c : sim.state.Ctx) (s : sim.state.St) (k : Usize) (a : replay.frames.Action)
    (hk1 : k.val < s.block_last.val.length) (hk2 : k.val < s.block_idx.val.length)
    (hk : k.val < c.cfg.input_blockers.val.length) (ia : Bool) (idx : Usize)
    (hr : sim.scoring.period_is_in_any (alloc.vec.Vec.deref c.block_periods) (s.block_idx.val[k.val]'hk2) s.t = ok (ia, idx)) :
    sim.step.intercept_press c s k a =
      ok (s6IP c s k a ia idx (s.block_last.val[k.val]'hk1) (c.cfg.input_blockers.val[k.val]'hk)) := by
  unfold sim.step.intercept_press
  simp only [vec_index_eq _ _ hk2, bind_ok, hr, vec_index_mut_eq _ _ hk2, vec_index_eq _ _ hk1, vec_index_eq _ _ hk,
    vec_index_mut_eq _ _ hk1, sim.step.is_left_or_right_refines]
  generalize s.block_last.val[k.val]'hk1 = last
  generalize c.cfg.input_blockers.val[k.val]'hk = alt
  cases ia <;> cases a <;> cases alt <;> rcases last with _ | l <;> (try cases l) <;>
    simp [s6IP, actS, s2_actS, core.option.Option.is_none]

theorem sim.step.intercept_press_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (k : Usize)
    (a : replay.frames.Action) (hB : s6Blk c s) (hk : k.val < c.cfg.input_blockers.val.length) :
    ∃ b s', sim.step.intercept_press c s k a = ok (b, s') ∧
      OsuModel.Sim.Sim.interceptPress k.val (abs a) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s') ∧
      s6BF s s' ∧ s6Blk c s' := by
  have hk1 : k.val < s.block_last.val.length := by have := hB.1; omega
  have hk2 : k.val < s.block_idx.val.length := by have := hB.2.1; omega
  obtain ⟨⟨ia, idx⟩, hr, er, hlt⟩ := s6_pia (alloc.vec.Vec.deref c.block_periods) (s.block_idx.val[k.val]'hk2) s.t
    (fun h0 => by simpa using hB.2.2 (by simpa using h0) _ (List.getElem_mem hk2))
  have hk1' : k.val < (simStS tn s).blockLast.size := by simpa [simStS] using hk1
  have hk2' : k.val < (simStS tn s).blockIdx.size := by simpa [simStS, abs] using hk2
  have hk3' : k.val < (simCtxS tn fo c).cfg.inputBlockers.size := by simpa [simCtxS, abs, configS] using hk
  have e1 : (simStS tn s).blockLast[k.val]'hk1' = (s.block_last.val[k.val]'hk1).map actS := by simp [simStS]
  have e2 : (simStS tn s).blockIdx[k.val]'hk2' = (s.block_idx.val[k.val]'hk2).val := by simp [simStS, abs]
  have e3 : (simCtxS tn fo c).cfg.inputBlockers[k.val]'hk3' = c.cfg.input_blockers.val[k.val]'hk := by
    simp [simCtxS, abs, configS]
  have hbp : (simCtxS tn fo c).blockPeriods = (simPS (alloc.vec.Vec.deref c.block_periods)).toArray := by
    simp [simCtxS, simPS, abs]
  have er' : OsuModel.Sim.periodIsInAny (simCtxS tn fo c).blockPeriods (s.block_idx.val[k.val]'hk2).val (simStS tn s).t =
      .ok (ia, idx.val) := by rw [hbp]; exact er
  have hB1 := s6_blk_set c s hB k idx hk2 (fun h0 => by simpa using hlt (by simpa using h0)) s.block_last rfl
  have hI : (simStS tn s).blockIdx.set k.val idx.val hk2' =
      (simStS tn { s with block_idx := s.block_idx.set k idx }).blockIdx := by
    simp [simStS, abs, alloc.vec.Vec.set, List.map_set]
  have hR := s6_ip_rust c s k a hk1 hk2 hk ia idx hr
  have hL2 : ∀ x h, (simStS tn s).blockLast.set k.val (some (abs x)) h =
      (simStS tn { s with block_last := s.block_last.set k (some x) }).blockLast := by
    intro x h; simp [simStS, abs, alloc.vec.Vec.set, List.map_set]
  generalize s.block_last.val[k.val]'hk1 = L at hR e1
  generalize c.cfg.input_blockers.val[k.val]'hk = A at hR e3
  obtain ⟨b, s', hbs⟩ : ∃ b s', s6IP c s k a ia idx L A = (b, s') := ⟨_, _, rfl⟩
  rw [hbs] at hR
  refine ⟨b, s', hR, ?_, ?_, ?_⟩
  all_goals unfold s6IP at hbs
  · unfold OsuModel.Sim.Sim.interceptPress
    simp only [simM_bind, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_read, simM_get, Except.bind,
      OsuModel.Sim.Sim.getA, dif_pos hk2', e2, er', OsuModel.Sim.Sim.liftExcept, simM_pure, OsuModel.Sim.Sim.setA,
      simM_set, dif_pos hk1', dif_pos hk3', e1, e3]
    cases ia <;> cases a <;> cases A <;> rcases L with _ | l <;> (try cases l) <;>
      simp [actS, abs, hk1'] at hbs ⊢ <;> obtain ⟨rfl, rfl⟩ := hbs
    all_goals (simp [simStS, abs, alloc.vec.Vec.set, List.map_set, actS]; try rfl)
  · split_ifs at hbs <;> (simp only [Prod.mk.injEq] at hbs; obtain ⟨rfl, rfl⟩ := hbs; exact ⟨_, _, rfl, by simp [vec_set_val'], by simp [vec_set_val']⟩)
  · split_ifs at hbs <;> (simp only [Prod.mk.injEq] at hbs; obtain ⟨rfl, rfl⟩ := hbs)
    all_goals first | exact hB1 | exact s6_blk_set c s hB k idx hk2 (fun h0 => by simpa using hlt (by simpa using h0)) _ (by simp [vec_set_val'])

/-! ## `legacy_blocked_by_earlier` -/
-- FRAGMENT-OF: checkHittable (.legacy) `for p in alive` loop, as `simLegScan` (= the spec loop by sim_legG_foldr); parent sim.step.check_hittable_legacy_refines
theorem sim.step.legacy_blocked_by_earlier_refines (c : sim.state.Ctx) (s : sim.state.St) (alive : Slice Usize)
    (r : sim.step.Ref) (h : sim.playable.HObj) (aj : Nat → Bool)
    (hj : ∀ p ∈ alive.val, sim.step.all_judged s p = ok (aj p.val))
    (hE : ∀ p ∈ alive.val, p.val < c.pb.objects.val.length) :
    sim.step.legacy_blocked_by_earlier c s alive r h =
      ok (simLegScan aj (simEndOf c.pb.objects) (r.top.val, r.nested.val) h.start (alive.val.map (·.val))) := by
  have := sim_leg_loop c s alive r h aj hj hE _ 0#usize rfl (by simp)
  simpa using this

/-! ## the interceptor loop of `propagate_press` -/
@[reducible] def s6L0 (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (nb kk : Usize) (b : Bool) :=
  sim.step.propagate_press_loop0 c.env c.cfg.policy c.cfg.classic_head_block
      c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries
      c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust
      c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier
      c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out
      c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods
      c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength
      c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax
      c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
      c.block_periods c.first_obj s a nb kk b

@[reducible] def s6B0 (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (nb kk : Usize) (b : Bool) :=
  sim.step.propagate_press_loop0.body c.env c.cfg.policy c.cfg.classic_head_block
      c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries
      c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust
      c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier
      c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out
      c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods
      c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength
      c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax
      c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
      c.block_periods c.first_obj a nb s kk b

theorem s6_l0_step (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (nb kk : Usize) (b : Bool) (r)
    (hb : s6B0 c s a nb kk b = ok r) :
    s6L0 c s a nb kk b = (match r with
      | .cont (s1, k1, b1) => s6L0 c s1 a nb k1 b1
      | .done y => ok y) := by
  unfold s6L0 sim.step.propagate_press_loop0
  rw [loop_unfold]; dsimp only
  simp only [s6B0] at hb; rw [hb]; simp only [bind_ok]
  rcases r with ⟨s1, k1, b1⟩ | y <;> rfl

theorem s6_l0_blocked (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (nb kk : Usize) :
    s6L0 c s a nb kk true = ok (s, true) := by
  rw [s6_l0_step c s a nb kk true (.done (s, true)) (by
    unfold s6B0 sim.step.propagate_press_loop0.body; by_cases h : kk < nb <;> simp [h])]

theorem s6_ctx_eta (c : sim.state.Ctx) :
    ({ env := c.env,
       cfg := { policy := c.cfg.policy, classic_head_block := c.cfg.classic_head_block,
                legacy_health := c.cfg.legacy_health, fail_overrides := c.cfg.fail_overrides,
                easy_retries := c.cfg.easy_retries, fail_conds := c.cfg.fail_conds,
                acc_challenges := c.cfg.acc_challenges, rank_adjust := c.cfg.rank_adjust,
                rate_sources := c.cfg.rate_sources, dyn_rates := c.cfg.dyn_rates,
                score_multiplier := c.cfg.score_multiplier, updatables := c.cfg.updatables,
                input_blockers := c.cfg.input_blockers, spun_out := c.cfg.spun_out,
                strict_tracking := c.cfg.strict_tracking, lazer_replay := c.cfg.lazer_replay,
                rate_mods := c.cfg.rate_mods, vis_mods := c.cfg.vis_mods, depth_max := c.cfg.depth_max,
                magnet_strength := c.cfg.magnet_strength, repel_strength := c.cfg.repel_strength,
                barrel_roll := c.cfg.barrel_roll },
       pb := c.pb, frames := c.frames, steps := c.steps, head_idx := c.head_idx, tail_idx := c.tail_idx,
       smax := c.smax, hcfg := c.hcfg, last_frame_time := c.last_frame_time, corner_pow := c.corner_pow,
       prec_end := c.prec_end, ap_frames := c.ap_frames, block_periods := c.block_periods,
       first_obj := c.first_obj } : sim.state.Ctx) = c := rfl

theorem s6_loop0 (tn fo) (c : sim.state.Ctx) (a : replay.frames.Action) (N : Nat)
    (hN : N = c.cfg.input_blockers.val.length)
    (F : Nat → Option Unit × Unit → OsuModel.Sim.SimM (ForInStep (Option Unit × Unit)))
    (hF : ∀ k' x, F k' x = (do
      let b ← OsuModel.Sim.Sim.interceptPress (N - 1 - k') (abs a)
      if b = true then pure (ForInStep.done (some (), ())) else pure (ForInStep.yield (none, ())))) :
    ∀ m (kk : Usize) (s : sim.state.St), N - kk.val = m → kk.val ≤ N → s6Blk c s →
      ∃ s' b, s6L0 c s a (alloc.vec.Vec.len c.cfg.input_blockers) kk false = ok (s', b) ∧
        forIn (m := OsuModel.Sim.SimM) (List.range' kk.val m) ((none : Option Unit), ()) F (simCtxS tn fo c) (simStS tn s) =
          .ok ((if b then some () else none, ()), simStS tn s') ∧ s6BF s s' ∧ s6Blk c s' := by
  intro m
  induction m with
  | zero =>
    intro kk s hm hk hB
    refine ⟨s, false, ?_, by simp, s6BF_refl s, hB⟩
    rw [s6_l0_step c s a _ kk false (.done (s, false)) (by
      have : ¬ kk < alloc.vec.Vec.len c.cfg.input_blockers := by rw [vec_lt_len_iff]; omega
      unfold s6B0 sim.step.propagate_press_loop0.body; simp [this])]
  | succ m ih =>
    intro kk s hm hk hB
    have hlt : kk.val < c.cfg.input_blockers.val.length := by omega
    have hlt' : kk < alloc.vec.Vec.len c.cfg.input_blockers := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one kk (by have := c.cfg.input_blockers.property; omega)
    obtain ⟨i0, hi0, hi0v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len c.cfg.input_blockers)
      (y := 1#usize) (by simp; omega))
    obtain ⟨i1, hi1, hi1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i0) (y := kk) (by simp at hi0v ⊢; omega))
    have hiv : i1.val = N - 1 - kk.val := by simp at hi0v hi1v; omega
    have hil : i1.val < c.cfg.input_blockers.val.length := by omega
    obtain ⟨b, s1, eR, eS, hF1, hB1⟩ := sim.step.intercept_press_refines tn fo c s i1 a hB hil
    rw [List.range'_succ, List.forIn_cons, simM_bind, hF, simM_bind, ← hiv, eS]
    simp only [Except.bind]
    cases b with
    | true =>
      refine ⟨s1, true, ?_, by simp, hF1, hB1⟩
      rw [s6_l0_step c s a _ kk false (.cont (s1, k1, true)) (by
        unfold s6B0 sim.step.propagate_press_loop0.body
        simp only [hlt', if_true, Bool.false_eq_true, if_false, hi0, hi1, bind_ok, eR, hk1]; simp)]
      exact s6_l0_blocked c s1 a _ k1
    | false =>
      obtain ⟨s2, b2, eR2, eS2, hF2, hB2⟩ := ih k1 s1 (by omega) (by omega) hB1
      refine ⟨s2, b2, ?_, ?_, s6BF_trans hF1 hF2, hB2⟩
      · rw [s6_l0_step c s a _ kk false (.cont (s1, k1, false)) (by
          unfold s6B0 sim.step.propagate_press_loop0.body
          simp only [hlt', if_true, Bool.false_eq_true, if_false, hi0, hi1, bind_ok, eR, hk1]; simp)]
        exact eR2
      · simp only [Bool.false_eq_true, if_false, simM_pure]
        rw [hk1v] at eS2; exact eS2

/-! ## frames of the press chain -/
/-- the object fields the press chain never writes (`simKeepJ` without `hit_action`) -/
def s6KeepO (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.child_id, o.hovered, o.head_alive, o.inst, o.head_inst,
   o.tick_insts, o.tick_live, o.slider_mouse, o.spin_tracking, o.spin_mouse, o.last_angle, o.total_accumulated,
   o.accumulated_at_last_completion, o.current_spin_max, o.completed_spins, o.last_report_time, o.completed_full_spins)

/-- the state fields the press chain never writes (`simKeepS` without `pressed`, `block_last`, `block_idx`) -/
def s6KeepT (s : sim.state.St) :=
  (s.k, s.t, s.first_lifetime_update, s.next_future, s.future_order, s.active, s.dict_slots, s.free_list,
   s.child_counter, s.mouse_valid, s.mouse, s.last_replay, s.speed, s.clock_rate, s.relax_down,
   s.relax_was_left, s.relax_last, s.ap_frame, s.pools, s.br_rot, s.cursor_pos,
   s.health.nearest_index, s.health_rp.nearest_index)  -- proc (D73): drain cursors, appended last

/-- the frame of `trigger_pressed` / `propagate_press`: judgement processing (`simJFr`), `hit_action` writes,
`pressed` and the input-blocker trackers (same lengths) -/
structure s6PFr (s s' : sim.state.St) : Prop where
  keep : s6KeepT s' = s6KeepT s
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), s6KeepO (s'.objs.val[j]'h') = s6KeepO (s.objs.val[j]'h)
  bl : s'.block_last.val.length = s.block_last.val.length
  bi : s'.block_idx.val.length = s.block_idx.val.length
  il : s'.insts.val.length = s.insts.val.length

theorem s6PFr_refl (s : sim.state.St) : s6PFr s s := ⟨rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem s6PFr_trans {s1 s2 s3 : sim.state.St} (h1 : s6PFr s1 s2) (h2 : s6PFr s2 s3) : s6PFr s1 s3 :=
  ⟨h2.keep.trans h1.keep, h2.len.trans h1.len, fun j h h' => (h2.ow j (by rw [h1.len]; exact h) h').trans (h1.ow j h _),
   h2.bl.trans h1.bl, h2.bi.trans h1.bi, h2.il.trans h1.il⟩

/-- the hit-phase frame inside the receptor loop (results, insts, score, `hit_action`; block trackers untouched) -/
structure s6HFr (s s' : sim.state.St) : Prop where
  keep : simKeepS s' = simKeepS s
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), s6KeepO (s'.objs.val[j]'h') = s6KeepO (s.objs.val[j]'h)
  il : s'.insts.val.length = s.insts.val.length

theorem s6HFr_refl (s : sim.state.St) : s6HFr s s := ⟨rfl, rfl, fun _ _ _ => rfl, rfl⟩
theorem s6HFr_trans {s1 s2 s3 : sim.state.St} (h1 : s6HFr s1 s2) (h2 : s6HFr s2 s3) : s6HFr s1 s3 :=
  ⟨h2.keep.trans h1.keep, h2.len.trans h1.len, fun j h h' => (h2.ow j (by rw [h1.len]; exact h) h').trans (h1.ow j h _),
   h2.il.trans h1.il⟩

theorem s6HFr_of_jfr {s s' : sim.state.St} (h : simJFr s s') : s6HFr s s' := by
  refine ⟨h.keep, h.len, fun j hj hj' => ?_, h.il⟩
  have e := h.ow j hj hj'
  simp only [simKeepJ, Prod.mk.injEq] at e
  simp only [s6KeepO, e]

theorem s6HFr_set (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) (o' : sim.state.OState)
    (ho : s6KeepO o' = s6KeepO (s.objs.val[i.val]'hi)) : s6HFr s { s with objs := s.objs.set i o' } := by
  refine ⟨rfl, by simp [vec_set_val'], fun j hj hj' => ?_, rfl⟩
  simp only [vec_set_val', List.getElem_set]
  split
  · subst_vars; exact ho
  · rfl

theorem s6PFr_of_hfr {s s' : sim.state.St} (h : s6HFr s s') : s6PFr s s' := by
  have k := h.keep
  simp only [simKeepS, Prod.mk.injEq] at k
  refine ⟨?_, h.len, h.ow, ?_, ?_, h.il⟩
  · simp only [s6KeepT, k]
  · rw [k.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [k.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]


theorem s6_pressed_of_hfr {s s' : sim.state.St} (h : s6HFr s s') : s'.pressed = s.pressed := by
  have k := h.keep; simp only [simKeepS, Prod.mk.injEq] at k; exact k.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s6_blk_of_hfr {c : sim.state.Ctx} {s s' : sim.state.St} (h : s6HFr s s') (hb : s6Blk c s) : s6Blk c s' := by
  have k := h.keep; simp only [simKeepS, Prod.mk.injEq] at k
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e1, e2, _⟩ := k
  unfold s6Blk; rw [e1, e2]; exact hb

/-! ## the receptor loop of `propagate_press` -/
@[reducible] def s6L1 (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (order : alloc.vec.Vec Usize)
    (k : Usize) (d : Bool) :=
  sim.step.propagate_press_loop1 c.env c.cfg.policy c.cfg.classic_head_block
      c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries
      c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust
      c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier
      c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out
      c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods
      c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength
      c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax
      c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
      c.block_periods c.first_obj s a order k d

@[reducible] def s6B1 (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (order : alloc.vec.Vec Usize)
    (k : Usize) (d : Bool) :=
  sim.step.propagate_press_loop1.body c.env c.cfg.policy c.cfg.classic_head_block
      c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries
      c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust
      c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier
      c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out
      c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods
      c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength
      c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax
      c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
      c.block_periods c.first_obj a order s k d

theorem s6_l1_step (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (order : alloc.vec.Vec Usize)
    (k : Usize) (d : Bool) (r) (hb : s6B1 c s a order k d = ok r) :
    s6L1 c s a order k d = (match r with
      | .cont (s1, k1, d1) => s6L1 c s1 a order k1 d1
      | .done y => ok y) := by
  unfold s6L1 sim.step.propagate_press_loop1
  rw [loop_unfold]; dsimp only
  simp only [s6B1] at hb; rw [hb]; simp only [bind_ok]
  rcases r with ⟨s1, k1, d1⟩ | y <;> rfl

theorem s6_l1_done (c : sim.state.Ctx) (s : sim.state.St) (a : replay.frames.Action) (order : alloc.vec.Vec Usize)
    (k : Usize) : s6L1 c s a order k true = ok (.Ok (), s) := by
  rw [s6_l1_step c s a order k true (.done (.Ok (), s)) (by
    unfold s6B1 sim.step.propagate_press_loop1.body; by_cases h : k < alloc.vec.Vec.len order <;> simp [h])]

/-- one step of the receptor loop: Rust body result vs the spec body's result -/
def s6StepRel (Inv : sim.state.St → Prop) (A : sim.state.St → OsuModel.Sim.St) (k1 : Usize) :
    ControlFlow (sim.state.St × Usize × Bool) (core.result.Result Unit sim.err.SimErr × sim.state.St) →
    Except String (ForInStep (Option Unit × Unit) × OsuModel.Sim.St) → Prop
  | .cont (s1, k', d), sp => k' = k1 ∧ Inv s1 ∧
      sp = .ok ((if d then ForInStep.done (some (), ()) else ForInStep.yield (none, ())), A s1)
  | .done (.Err _, _), sp => ∃ m, sp = .error m
  | .done (.Ok _, _), _ => False

theorem s6_loop1 (c : sim.state.Ctx) (a : replay.frames.Action) (order : alloc.vec.Vec Usize) (C : OsuModel.Sim.Ctx)
    (A : sim.state.St → OsuModel.Sim.St) (Inv : sim.state.St → Prop)
    (F : Nat → Option Unit × Unit → OsuModel.Sim.SimM (ForInStep (Option Unit × Unit)))
    (hstep : ∀ s (k : Usize) (hk : k.val < order.val.length), Inv s → ∀ k1 : Usize, k1.val = k.val + 1 →
      ∃ r, s6B1 c s a order k false = ok r ∧ s6StepRel Inv A k1 r (F (order.val[k.val]'hk).val (none, ()) C (A s))) :
    ∀ m (k : Usize) s, order.val.length - k.val = m → k.val ≤ order.val.length → Inv s →
      ∃ res s', s6L1 c s a order k false = ok (res, s') ∧
        (res = .Ok () → Inv s' ∧ ∃ x, forIn (m := OsuModel.Sim.SimM) ((order.val.drop k.val).map (·.val))
          ((none : Option Unit), ()) F C (A s) = .ok ((x, ()), A s')) ∧
        (∀ e, res = .Err e → ∃ m, forIn (m := OsuModel.Sim.SimM) ((order.val.drop k.val).map (·.val))
          ((none : Option Unit), ()) F C (A s) = .error m) := by
  intro m
  induction m with
  | zero =>
    intro k s hm hk hI
    have hge : ¬ k < alloc.vec.Vec.len order := by rw [vec_lt_len_iff]; omega
    refine ⟨.Ok (), s, ?_, fun _ => ⟨hI, none, ?_⟩, fun e h => (by cases h)⟩
    · rw [s6_l1_step c s a order k false (.done (.Ok (), s)) (by
        unfold s6B1 sim.step.propagate_press_loop1.body; simp [hge])]
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    intro k s hm hk hI
    have hlt : k.val < order.val.length := by omega
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := order.property; omega)
    obtain ⟨r, hb, hr⟩ := hstep s k hlt hI k1 hk1v
    rw [s6_l1_step c s a order k false r hb, List.drop_eq_getElem_cons hlt, List.map_cons, List.forIn_cons]
    rcases r with ⟨s1, k', d⟩ | ⟨res, s1⟩
    · obtain ⟨rfl, hI1, hF⟩ := hr
      cases d with
      | true =>
        refine ⟨.Ok (), s1, s6_l1_done c s1 a order k', fun _ => ⟨hI1, some (), ?_⟩, fun e h => (by cases h)⟩
        simp only [simM_bind, hF, Except.bind, if_true]; rfl
      | false =>
        obtain ⟨res, s', e1, h1, h2⟩ := ih k' s1 (by omega) (by omega) hI1
        refine ⟨res, s', e1, fun h => ?_, fun e h => ?_⟩
        · obtain ⟨hI', x, hx⟩ := h1 h
          refine ⟨hI', x, ?_⟩
          simp only [simM_bind, hF, Except.bind, Bool.false_eq_true, if_false]
          rw [hk1v] at hx; exact hx
        · obtain ⟨m', hm'⟩ := h2 e h
          refine ⟨m', ?_⟩
          simp only [simM_bind, hF, Except.bind, Bool.false_eq_true, if_false]
          rw [hk1v] at hm'; exact hm'
    · cases res with
      | Ok u => exact hr.elim
      | Err er =>
        obtain ⟨m', hm'⟩ := hr
        refine ⟨.Err er, s1, rfl, fun h => (by cases h), fun e _ => ⟨m', ?_⟩⟩
        simp only [simM_bind, hm', Except.bind]

theorem s6_loop1' (c : sim.state.Ctx) (a : replay.frames.Action) (order : alloc.vec.Vec Usize) (C : OsuModel.Sim.Ctx)
    (A : sim.state.St → OsuModel.Sim.St) (Inv : sim.state.St → Prop)
    (F : Nat → Option Unit × Unit → OsuModel.Sim.SimM (ForInStep (Option Unit × Unit)))
    (hstep : ∀ s (k : Usize) (hk : k.val < order.val.length), Inv s → ∀ k1 : Usize, k1.val = k.val + 1 →
      ∃ r, s6B1 c s a order k false = ok r ∧ s6StepRel Inv A k1 r (F (order.val[k.val]'hk).val (none, ()) C (A s)))
    (s : sim.state.St) (hI : Inv s) (X : Except String ((Option Unit × Unit) × OsuModel.Sim.St))
    (hX : forIn (m := OsuModel.Sim.SimM) ((order.val.drop (0#usize).val).map (·.val)) ((none : Option Unit), ()) F C (A s) = X) :
    ∃ res s', s6L1 c s a order 0#usize false = ok (res, s') ∧
      (res = .Ok () → Inv s' ∧ ∃ x, X = .ok ((x, ()), A s')) ∧ (∀ e, res = .Err e → ∃ m, X = .error m) := by
  subst hX
  exact s6_loop1 c a order C A Inv F hstep _ 0#usize s rfl (by simp) hI

/-! ## the `hit_action` write of `propagate_press` -/
/-- `os.hitAction <|> some a` on the Rust side -/
def s6Hit (o : sim.state.OState) (a : replay.frames.Action) : sim.state.OState :=
  { o with hit_action := o.hit_action <|> some a }

theorem s6_hit_rust (v : alloc.vec.Vec sim.state.OState) (i : Usize) (hi : i.val < v.val.length) (a : replay.frames.Action) :
    (if core.option.Option.is_none (v.val[i.val]'hi).hit_action = true
      then alloc.vec.Vec.set v i { (v.val[i.val]'hi) with hit_action := some a } else v) =
      alloc.vec.Vec.set v i (s6Hit (v.val[i.val]'hi) a) := by
  unfold s6Hit
  cases h : (v.val[i.val]'hi).hit_action with
  | none => simp [core.option.Option.is_none, h]
  | some x =>
    simp only [core.option.Option.is_none, h, Option.isNone_some, Bool.false_eq_true, if_false]
    have e : ({ (v.val[i.val]'hi) with hit_action := (some x <|> some a) } : sim.state.OState) = v.val[i.val]'hi := by
      rw [show (some x <|> some a) = some x from rfl, ← h]
    rw [e]; unfold alloc.vec.Vec.set; simp

theorem s6_hit_spec (o : sim.state.OState) (a : replay.frames.Action) :
    (fun os : OsuModel.Sim.OState => { os with hitAction := os.hitAction <|> some (abs a) }) (ostateS o) = ostateS (s6Hit o a) := by
  unfold s6Hit
  cases h : o.hit_action <;> simp [ostateS, h] <;> rfl

theorem s6_lp_set {s : sim.state.St} (h : simLP s) (i : Usize) (hi : i.val < s.objs.val.length) (a : replay.frames.Action) :
    simLP { s with objs := s.objs.set i (s6Hit (s.objs.val[i.val]'hi) a) } := by
  refine ⟨h.1, fun j hj => ?_⟩
  have hj0 : j < s.objs.val.length := by simpa [vec_set_val'] using hj
  simp only [vec_set_val', List.getElem_set]
  split
  · subst_vars; exact h.2 _ hi
  · exact h.2 j hj0

/-! ## `propagate_press` -/
theorem s6_ar_bf (tn fo) {P : Nat → sim.transforms.TObj → Prop} (b0 n : Nat) (c : sim.state.Ctx) (s s' : sim.state.St) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (h : s6BF s s') : SimARInv tn fo P b0 n c s' e 0 0 := by
  obtain ⟨x, y, rfl, _, _⟩ := h
  exact sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hI _ (s3b_inv_of hI.inv rfl rfl) (s3b_objFrame_of_eq rfl) rfl hI.tf
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem s6PFr_of_bf {s s' : sim.state.St} (h : s6BF s s') : s6PFr s s' := by
  obtain ⟨x, y, rfl, h1, h2⟩ := h
  exact ⟨rfl, rfl, fun _ _ _ => rfl, h1, h2, rfl⟩

set_option hygiene false in
/-- the receptor tail of `propagate_press` (`receptorCanBeHit` .. `hitAction`), shared by the circle and slider-head
cases; expects `rr` (Rust ref), `hsr`, `hcr`, `habs`, `htop`, `hkk` in scope -/
macro "s6_tail" : tactic => `(tactic| (
  obtain ⟨bc, hbc, ebc⟩ := sim.step.receptor_can_be_hit_refines tn fo c t rr hsr
  rw [habs] at ebc
  simp only [simM_pure, simM_bind, Except.bind]
  simp only [hbc, bind_ok, simM_bind, ebc, Except.bind]
  cases bc
  · refine ⟨.cont (t, k1, false), by simp [hkk], rfl, ⟨hIt', hLt, hHt⟩, by simp⟩
  · simp only [sim.step.is_left_or_right_refines, bind_ok, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    have hlrS : (abs a != OsuModel.Replay.Action.left && abs a != OsuModel.Replay.Action.right) =
        !(actS a == OsuModel.Replay.Action.left || actS a == OsuModel.Replay.Action.right) := by cases a <;> rfl
    rw [hlrS]
    cases hlr : (actS a == OsuModel.Replay.Action.left || actS a == OsuModel.Replay.Action.right)
    · exact ⟨.cont (t, k1, false), by simp [hkk, hlr], rfl, ⟨hIt', hLt, hHt⟩, by simp⟩
    · (
      rw [show (ostateS (t.objs.val[i.val]'hos)).hovered = (t.objs.val[i.val]'hos).hovered from rfl]
      cases hh : (t.objs.val[i.val]'hos).hovered
      · exact ⟨.cont (t, k1, false), by simp [hkk, hlr, hh], rfl, ⟨hIt', hLt, hHt⟩, by simp⟩
      · obtain ⟨res, s2, e2, r2, i2⟩ := sim.step.circle_update_result_refines h64 tn fo E b0 n c hC hCS hlen t rr true e
          hIt' hcr (htop ▸ hIt'.ik i hiD) (htop ▸ hp _ hio) hLt
        rw [habs] at r2
        cases res with
        | Err er =>
          obtain ⟨m, hm⟩ := r2
          refine ⟨.done (.Err er, s2), ?_, m, ?_⟩
          · simp [hlr, hh, e2, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
          · simp [hm, Except.bind]
        | Ok u =>
          cases u
          obtain ⟨hI2, hJ2, hL2⟩ := i2 rfl
          have hos2 : i.val < s2.objs.val.length := by rw [hJ2.len]; exact hos
          refine ⟨.cont ({ s2 with objs := s2.objs.set i (s6Hit (s2.objs.val[i.val]'hos2) a) }, k1, true), ?_, rfl,
            ⟨sim_ar_inv_objw tn fo P b0 n c s2 e hI2 i hos2 _ rfl rfl rfl rfl rfl
              (s3a_inv_set c s2 i _ hI2.inv hos2 rfl), s6_lp_set hL2 i hos2 _,
             s6HFr_trans hHt (s6HFr_trans (s6HFr_of_jfr hJ2) (s6HFr_set s2 i hos2 _ rfl))⟩, ?_⟩
          · simp only [hlr, hh, e2, bind_ok, if_true]
            simp only [uncurry_apply_pair]
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, vec_index_eq _ _ hos2, hkk]
            rw [← s6_hit_rust s2.objs i hos2 a]
            cases (core.option.Option.is_none (s2.objs.val[i.val]'hos2).hit_action) <;>
              simp [vec_index_mut_eq _ _ hos2]
          · simp only [simRelM] at r2
            simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, ite_true, simM_bind, r2, Except.bind]
            rw [s3a_modifyObj tn fo c s2 i hos2 (fun os => { os with hitAction := os.hitAction <|> some (abs a) }) _
              (s6_hit_spec (s2.objs.val[i.val]'hos2) a)]
            simp)))

theorem sim.step.propagate_press_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (s : sim.state.St) (a : replay.frames.Action) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hLP : simLP s) (hB : s6Blk c s)
    (hA : ∀ x ∈ s.active.val, x.val < c.pb.objects.val.length) (hAl : s.active.val.length < Usize.max)
    (hAD : ∀ x ∈ s.active.val, some x ∈ s.dict_slots.val) :
    ∃ res s', sim.step.propagate_press c s a = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.propagatePress (abs a) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simLP s' ∧ s6Blk c s' ∧ s6PFr s s' ∧ s'.pressed = s.pressed) := by
  have hsz : (simCtxS tn fo c).cfg.inputBlockers.size = c.cfg.input_blockers.val.length := by
    simp [simCtxS, abs, configS]
  unfold sim.step.propagate_press OsuModel.Sim.Sim.propagatePress
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
  obtain ⟨s1, b, e0, f0, hbf, hB1⟩ := s6_loop0 tn fo c a _ hsz _ (fun _ _ => rfl) (simCtxS tn fo c).cfg.inputBlockers.size 0#usize s (by simp) (by simp) hB
  simp only [s6L0] at e0
  simp only [e0, bind_ok]
  have h00 : (0#usize).val = 0 := rfl
  rw [h00] at f0
  rw [f0]
  have hI1 := s6_ar_bf tn fo b0 n c s s1 e hI hbf
  have hLP1 : simLP s1 := by obtain ⟨x, y, rfl, _, _⟩ := hbf; exact hLP
  have hpr1 : s1.pressed = s.pressed := by obtain ⟨x, y, rfl, _, _⟩ := hbf; rfl
  have hact1 : s1.active = s.active := by obtain ⟨x, y, rfl, _, _⟩ := hbf; rfl
  cases b with
  | true =>
    refine ⟨.Ok (), s1, by simp, by simp [simRelM], fun _ => ⟨hI1, hLP1, hB1, s6PFr_of_bf hbf, hpr1⟩⟩
  | false =>
    have hA1 : ∀ x ∈ s1.active.val, x.val < c.pb.objects.val.length := by rw [hact1]; exact hA
    obtain ⟨order, ho, hov⟩ := sim.step.input_order_refines_list c s1 hI1.inv hA1 (by rw [hact1]; exact hAl)
    obtain ⟨order', ho', eo⟩ := sim.step.input_order_refines tn fo c s1 hI1.inv hA1 (by rw [hact1]; exact hAl)
    rw [ho] at ho'; simp at ho'; subst ho'
    have hordE : ∀ x ∈ order.val, x.val < c.pb.objects.val.length := by
      intro x hx
      have h1 : x.val ∈ order.val.map (·.val) := List.mem_map_of_mem hx
      rw [hov] at h1
      have h2 := sim_simSortL_mem _ _ _ h1
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h2
      rw [← hyx]; exact hA1 y hy
    have hordD : ∀ x ∈ order.val, some x ∈ s1.dict_slots.val := by
      intro x hx
      have h1 : x.val ∈ order.val.map (·.val) := List.mem_map_of_mem hx
      rw [hov] at h1
      have h2 := sim_simSortL_mem _ _ _ h1
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h2
      have hxy : y = x := UScalar.eq_of_val_eq hyx
      subst hxy
      have hd1 : s1.dict_slots = s.dict_slots := by obtain ⟨u, w, rfl, _, _⟩ := hbf; rfl
      rw [hd1]; rw [hact1] at hy; exact hAD _ hy
    simp only [ho, bind_ok, Bool.false_eq_true, if_false, eo, Except.bind, simM_bind]
    rw [← Array.forIn_toList]
    have hab : (abs order : _root_.Array Nat).toList = (order.val.drop (0#usize).val).map (·.val) := by
      simp [abs]
    rw [hab]
    generalize hX : forIn (m := OsuModel.Sim.SimM) (List.map (fun x => x.val) (List.drop (0#usize).val order.val)) ((none : Option Unit), ()) _
      (simCtxS tn fo c) (simStS tn s1) = X
    have key := s6_loop1' c a order (simCtxS tn fo c) (simStS tn)
      (fun t => SimARInv tn fo P b0 n c t e 0 0 ∧ simLP t ∧ s6HFr s1 t) _ ?_ s1 ⟨hI1, hLP1, s6HFr_refl s1⟩ X hX
    rotate_left
    · intro t k hk hIt k1 hk1
      obtain ⟨hIt', hLt, hHt⟩ := hIt
      have hlt' : k < alloc.vec.Vec.len order := by rw [vec_lt_len_iff]; exact hk
      have hio : (order.val[k.val]'hk).val < c.pb.objects.val.length := hordE _ (List.getElem_mem hk)
      have hos : (order.val[k.val]'hk).val < t.objs.val.length := by rw [hIt'.inv.objs_len]; exact hio
      unfold s6B1 sim.step.propagate_press_loop1.body
      simp only [hlt', if_true, Bool.false_eq_true, if_false, vec_index_eq _ _ hk, bind_ok]
      have hiD : some (order.val[k.val]'hk) ∈ t.dict_slots.val := by
        rw [sim_keepS_dict hHt.keep]; exact hordD _ (List.getElem_mem hk)
      generalize order.val[k.val]'hk = i at hio hos hiD ⊢
      obtain ⟨k1', hkk, hk1'⟩ := usize_add_one k (by have := order.property; omega)
      have : k1 = k1' := UScalar.eq_of_val_eq (by rw [hk1', hk1])
      subst this
      simp only [vec_index_eq _ _ hos, vec_index_eq _ _ hio, bind_ok,
        simM_bind, s3b_topObj tn fo c _ _ hio, Except.bind, s3a_ostate tn fo c t _ hos]
      have hkS : (topS tn (c.pb.objects.val[i.val]'hio)).h.kind = kindS (c.pb.objects.val[i.val]'hio).h.kind := rfl
      rw [hkS]
      unfold sim.step.receptor_ref
      simp only [vec_index_eq _ _ hio, bind_ok]
      cases hK : (c.pb.objects.val[i.val]'hio).h.kind <;> simp only [kindS, simM_pure, bind_ok]
      case Circle =>
        have hsr0 : simSRefOk t ⟨i, (-1)#i64⟩ := ⟨hos, fun h => by simp at h⟩
        have hcr0 : simRefOk c ⟨i, (-1)#i64⟩ := ⟨hio, fun h => by simp at h⟩
        have habs0 : (abs (⟨i, (-1)#i64⟩ : sim.step.Ref) : Nat × Int) = (i.val, -1) := by simp [abs]
        have htop0 : (⟨i, (-1)#i64⟩ : sim.step.Ref).top = i := rfl
        generalize (⟨i, (-1)#i64⟩ : sim.step.Ref) = rr at hsr0 hcr0 habs0 htop0 ⊢
        have hsr := hsr0; have hcr := hcr0; have habs := habs0; have htop := htop0
        s6_tail
      case Slider =>
        simp only [vec_index_eq _ _ hos, bind_ok]
        rw [show (ostateS (t.objs.val[i.val]'hos)).headAlive = (t.objs.val[i.val]'hos).head_alive from rfl]
        cases hha : (t.objs.val[i.val]'hos).head_alive
        · exact ⟨.cont (t, k1, false), by simp [hkk, hha], rfl, ⟨hIt', hLt, hHt⟩, by simp⟩
        · obtain ⟨hhi, hh63, hhb⟩ := hC.hd i.val hio
          have hhl := hhb (Or.inl hK)
          have hnl := hIt'.inv.nested_len _ hos hio
          have hch : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) :=
            sim_usize_to_i64 _ hh63
          have ehead : OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) (simStS tn t) =
              .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn t) := by
            have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
            simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi',
              Except.bind, simCtxS, abs, hhi]
          simp only [hha, if_true, vec_index_eq _ _ hhi, bind_ok, lift, ehead, simM_bind, Except.bind]
          have hsr0 : simSRefOk t ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := ⟨hos, fun _ => by
            show (UScalar.hcast .I64 _).val.toNat < _; rw [hch, hnl]; simpa using hhl⟩
          have hcr0 : simRefOk c ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := ⟨hio, fun _ => by
            show (UScalar.hcast .I64 _).val.toNat < _; rw [hch]; simpa using hhl⟩
          have habs0 : (abs (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
              (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) := by simp [abs, hch]
          have htop0 : (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref).top = i := rfl
          generalize (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref) = rr at hsr0 hcr0 habs0 htop0 ⊢
          have hsr := hsr0; have hcr := hcr0; have habs := habs0; have htop := htop0
          s6_tail
      all_goals exact ⟨.cont (t, k1, false), by simp [hkk], rfl, ⟨hIt', hLt, hHt⟩, by simp⟩
    obtain ⟨res, s', e1, h1, h2⟩ := key
    simp only [s6L1] at e1
    refine ⟨res, s', by simp [ho, e1], ?_, ?_⟩
    · cases res with
      | Ok u =>
        cases u
        obtain ⟨_, x, hx⟩ := h1 rfl
        simp only [simRelM, hx]
        cases x <;> rfl
      | Err er =>
        obtain ⟨m, hm⟩ := h2 er rfl
        exact ⟨m, by simp only [hm]⟩
    · intro hr
      obtain ⟨⟨hI', hL', hF'⟩, _⟩ := h1 hr
      exact ⟨hI', hL', s6_blk_of_hfr hF' hB1, s6PFr_trans (s6PFr_of_bf hbf) (s6PFr_of_hfr hF'),
        (s6_pressed_of_hfr hF').trans hpr1⟩

/-! ## `trigger_pressed` -/
theorem s6_len_lt3 (l : replay.frames.ActList) (a : replay.frames.Action) (hl : l.len.val ≤ 3)
    (hND : (actListS l).Nodup) (hc : (actListS l).contains (actS a) = false) : l.len.val < 3 := by
  have hlen : (actListS l).length = l.len.val := by
    have := s2_items_len l
    simp [actListS, this]; omega
  have hsub : (actListS l).Subperm ([OsuModel.Replay.Action.left, .right, .smoke].erase (actS a)) := by
    apply hND.subperm
    intro x hx
    have hxa : x ≠ actS a := by
      intro h; subst h; simp [List.contains_iff_mem] at hc; exact hc hx
    cases x <;> cases a <;> simp [actS] at hxa ⊢
  have := hsub.length_le
  have h2 : ([OsuModel.Replay.Action.left, .right, .smoke].erase (actS a)).length = 2 := by cases a <;> rfl
  omega

-- NOT-CONDITIONAL: SimARCtx/simCSH/s3aPathOk are context premises (ev_ctxWF; simCSH via sim_ar_cs); SimARInv, simLP, s6Blk, the Nodup of `pressed` and the active-index facts are state invariants the step loop carries
theorem sim.step.trigger_pressed_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (s : sim.state.St) (a : replay.frames.Action) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hLP : simLP s) (hB : s6Blk c s) (hND : (actListS s.pressed).Nodup)
    (hA : ∀ x ∈ s.active.val, x.val < c.pb.objects.val.length) (hAl : s.active.val.length < Usize.max)
    (hAD : ∀ x ∈ s.active.val, some x ∈ s.dict_slots.val) :
    ∃ res s', sim.step.trigger_pressed c s a = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.triggerPressed (abs a) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ simLP s' ∧ s6Blk c s' ∧ s6PFr s s' ∧
        (actListS s'.pressed).Nodup) := by
  have hcon : (simStS tn s).pressed.contains (abs a) = (actListS s.pressed).contains (actS a) := by
    simp [simStS, abs]
  unfold sim.step.trigger_pressed OsuModel.Sim.Sim.triggerPressed
  simp only [replay.frames.act_contains_refines _ _ hLP.1, bind_ok, simM_bind, OsuModel.Sim.Sim.st, simM_get,
    Except.bind, hcon]
  change (∃ res s', (if (actListS s.pressed).contains (actS a) = true then _ else _) = _ ∧ _) 
  cases hc : (actListS s.pressed).contains (actS a)
  · simp only [Bool.false_eq_true, if_false]
    have hl3 := s6_len_lt3 s.pressed a hLP.1 hND hc
    obtain ⟨al, hal, hal1, hal2, _⟩ := replay.frames.act_push_refines s.pressed a hl3
    simp only [hal, bind_ok, simM_modify]
    have hS : ({ (simStS tn s) with pressed := (simStS tn s).pressed.push (abs a) } : OsuModel.Sim.St) =
        simStS tn { s with pressed := al } := by
      simp only [simStS]; congr 1
      show (actListS s.pressed).toArray.push (actS a) = (actListS al).toArray
      rw [show actListS al = (abs al : List OsuModel.Replay.Action) from rfl, hal1]; simp [abs]
    have hI' : SimARInv tn fo P b0 n c { s with pressed := al } e 0 0 :=
      sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hI _ (s3b_inv_of hI.inv rfl rfl) (s3b_objFrame_of_eq rfl) rfl hI.tf
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hLP' : simLP { s with pressed := al } := ⟨by show al.len.val ≤ 3; omega, hLP.2⟩
    obtain ⟨res, s', e1, r1, i1⟩ := sim.step.propagate_press_refines h64 tn fo E b0 n c hC hCS hlen hp
      { s with pressed := al } a e hI' hLP' hB hA hAl hAD
    refine ⟨res, s', e1, ?_, fun h => ?_⟩
    · rw [← hS] at r1
      simp only [simM_bind, simM_modify, Except.bind]
      exact r1
    · obtain ⟨j1, j2, j3, j4, j5⟩ := i1 h
      refine ⟨j1, j2, j3, s6PFr_trans (show s6PFr s { s with pressed := al } from ⟨rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩) j4, ?_⟩
      rw [j5, show actListS al = (abs al : List OsuModel.Replay.Action) from rfl, hal1]
      refine List.nodup_append.mpr ⟨hND, by simp, ?_⟩
      intro x hx y hy; simp at hy; subst hy; intro hxa; subst hxa
      simp [List.contains_iff_mem] at hc; exact hc hx
  · simp only [if_true]
    exact ⟨.Ok (), s, rfl, rfl, fun _ => ⟨hI, hLP, hB, s6PFr_refl s, hND⟩⟩

end OsuProofs
