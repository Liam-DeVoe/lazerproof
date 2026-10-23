import OsuProofs.Sim.Lifetime

/-
  sim8: the lifetime chain, loop layer. Generated `lifetime_first_update_loop`, `lifetime_future_update_loop`,
  `lifetime_update_loop{0,1}` (newly-dead scan) and `lifetime_update_loop{0,1}_loop0` (active filter) against the spec
  `Sim.lifetimeUpdate`, split by `s8_lu_splitS` (rfl) into s8LUFirstK / s8LUFutK / s8LUTail. The loops are generic over
  the per-object contracts of `became_alive` / `became_dead` (invariant families A, B, D); `s8_lu_gen` composes them.
-/
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result
namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s8_life_eq (a : sim.state.Life) :
    sim.state.Life.Insts.CoreCmpPartialEqLife.eq a sim.state.Life.Alive = ok (lifeS a == OsuModel.Sim.Life.alive) := by
  cases a <;> simp [sim.state.Life.Insts.CoreCmpPartialEqLife.eq, sim.state.Life.read_discriminant, lifeS] <;> decide

theorem s8_simm_loop_unfold {β} (F : Unit → β → OsuModel.Sim.SimM (ForInStep β)) (b : β) :
    forIn Lean.Loop.mk b F = (do let r ← F () b; match r with | .done c => pure c | .yield c => forIn Lean.Loop.mk c F) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

/-- liveness filter predicate (out-of-range entries are dropped; never happens under the invariant) -/
def s8Alive (s : sim.state.St) (x : Usize) : Bool :=
  match s.objs.val[x.val]? with | some o => lifeS o.life == .alive | none => false

/-- the active-list filter `lifetime_update_loop{0,1}_loop0` result tuple -/
@[reducible] def s8FT (s : sim.state.St) (kept : alloc.vec.Vec Usize) :=
  (s.k, s.t, s.objs, s.first_lifetime_update, s.next_future,
      s.future_order, s.dict_slots, s.free_list, s.child_counter,
      s.mouse_valid, s.mouse, s.last_replay, s.pressed, s.score, s.health,
      s.score_rp, s.health_rp, s.out, s.speed, s.as_target, s.as_recent,
      s.as_seen, s.clock_rate, s.relax_down, s.relax_was_left, s.relax_last,
      s.ap_frame, s.block_last, s.block_idx, s.insts, s.pools, s.br_rot,
      s.theta, s.cursor_pos, kept)

theorem s8_lbe1 : (OsuModel.Sim.Life.future == OsuModel.Sim.Life.alive) = false := rfl
theorem s8_lbe2 : (OsuModel.Sim.Life.alive == OsuModel.Sim.Life.alive) = true := rfl
theorem s8_lbe3 : (OsuModel.Sim.Life.past == OsuModel.Sim.Life.alive) = false := rfl

-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (active filter, s8LUFilt via s8_filt_spec; parent sim.step.lifetime_update_refines, bridge s8_lu_splitS by rfl)
theorem sim.step.lifetime_update_loop0_loop0_refines (s : sim.state.St) (hact : ∀ x ∈ s.active.val, x.val < s.objs.val.length) :
    ∀ m (j : Usize) (kept : alloc.vec.Vec Usize), s.active.val.length - j.val = m → j.val ≤ s.active.val.length →
      kept.val.length ≤ j.val →
      ∃ KF : alloc.vec.Vec Usize, sim.step.lifetime_update_loop0_loop0 s kept j = ok (s8FT s KF) ∧
        KF.val = kept.val ++ (s.active.val.drop j.val).filter (s8Alive s) := by
  intro m
  induction m with
  | zero =>
    intro j kept hm hj hk
    refine ⟨kept, ?_, by simp [show s.active.val.length ≤ j.val by omega]⟩
    unfold sim.step.lifetime_update_loop0_loop0
    rw [loop_unfold]
    have hge : ¬ j < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; omega
    simp [sim.step.lifetime_update_loop0_loop0.body, hge]
  | succ m ih =>
    intro j kept hm hj hk
    have hjl : j.val < s.active.val.length := by omega
    have hlt : j < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; exact hjl
    have hx := hact _ (List.getElem_mem hjl)
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := s.active.property; omega)
    have hkm : kept.val.length < Usize.max := by have := s.active.property; omega
    obtain ⟨k1, ek1, vk1⟩ : ∃ k1 : alloc.vec.Vec Usize,
        (if lifeS (s.objs.val[(s.active.val[j.val]'hjl).val]'hx).life == OsuModel.Sim.Life.alive
          then alloc.vec.Vec.push kept (s.active.val[j.val]'hjl) else ok kept) = ok k1 ∧
        k1.val = kept.val ++ (if s8Alive s (s.active.val[j.val]'hjl) then [s.active.val[j.val]'hjl] else []) := by
      have hA : s8Alive s (s.active.val[j.val]'hjl) =
          (lifeS (s.objs.val[(s.active.val[j.val]'hjl).val]'hx).life == OsuModel.Sim.Life.alive) := by
        simp [s8Alive, hx]
      rw [hA]
      cases hl : (s.objs.val[(s.active.val[j.val]'hjl).val]'hx).life <;>
        simp [lifeS, vec_push_ok _ _ hkm, s8_lbe1, s8_lbe2, s8_lbe3]
    have hb : sim.step.lifetime_update_loop0_loop0.body s kept j = ok (.cont (k1, j1)) := by
      simp only [sim.step.lifetime_update_loop0_loop0.body, hlt, ite_true, vec_index_eq _ _ hjl, bind_ok,
        vec_index_eq _ _ hx, s8_life_eq, ek1, hj1]
    obtain ⟨KF, e, v⟩ := ih j1 k1 (by omega) (by omega) (by rw [vk1]; split <;> simp <;> omega)
    refine ⟨KF, ?_, ?_⟩
    · unfold sim.step.lifetime_update_loop0_loop0
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      unfold sim.step.lifetime_update_loop0_loop0 at e
      exact e
    · rw [v, vk1, hj1v, List.drop_eq_getElem_cons hjl, List.filter_cons]
      split <;> simp
theorem s8_filterM_aux (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (f : Nat → OsuModel.Sim.SimM Bool) (g : Nat → Bool) :
    ∀ (l : List Nat), (∀ x ∈ l, f x C S = .ok (g x, S)) → ∀ (acc : Array Nat),
      List.foldlM (m := OsuModel.Sim.SimM) (fun acc a => do if (← f a) then pure (acc.push a) else pure acc) acc l C S =
        .ok (acc ++ (l.filter g).toArray, S) := by
  intro l
  induction l with
  | nil => intro _ acc; simp
  | cons a t ih =>
    intro hl acc
    simp only [List.foldlM_cons, simM_bind, hl a (by simp), Except.bind]
    cases hg : g a
    · simp only [Bool.false_eq_true, ite_false, simM_pure, List.filter_cons, hg]
      exact ih (fun x hx => hl x (by simp [hx])) acc
    · simp only [ite_true, simM_pure, List.filter_cons, hg]
      rw [ih (fun x hx => hl x (by simp [hx])) (acc.push a)]
      simp
theorem s8_filterM (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (f : Nat → OsuModel.Sim.SimM Bool) (g : Nat → Bool) (l : List Nat)
    (hl : ∀ x ∈ l, f x C S = .ok (g x, S)) :
    Array.filterM f l.toArray 0 l.toArray.size C S = .ok ((l.filter g).toArray, S) := by
  simp only [Array.filterM]
  rw [List.size_toArray, List.foldlM_toArray']
  have := s8_filterM_aux C S f g l hl #[]
  simp only [Array.empty_append] at this
  exact this
  simp

/-- spec: the newly-dead scan body of `lifetimeUpdate` -/
def s8DG (t : F64) (i : Nat) (_ : PUnit.{1}) : OsuModel.Sim.SimM (ForInStep PUnit.{1}) := do
  let os ← OsuModel.Sim.Sim.ostate i
  if os.lifetimeEnd ≤ t || t < os.lifetimeStart then
    OsuModel.Sim.Sim.becameDead i
    pure (ForInStep.yield PUnit.unit)
  else pure (ForInStep.yield PUnit.unit)

/-- spec: the active filter of `lifetimeUpdate` -/
def s8LUFilt : OsuModel.Sim.SimM Unit := do
  let s ← OsuModel.Sim.Sim.st
  let keep ← s.active.filterM fun i => do return (← OsuModel.Sim.Sim.ostate i).life == .alive
  modify fun s => { s with active := keep }

theorem s8_filt_spec (tn : Nat → String) (C : OsuModel.Sim.Ctx) (s : sim.state.St)
    (hact : ∀ x ∈ s.active.val, x.val < s.objs.val.length) (KF : alloc.vec.Vec Usize)
    (hKF : KF.val = s.active.val.filter (s8Alive s)) :
    s8LUFilt C (simStS tn s) = .ok ((), simStS tn { s with active := KF }) := by
  unfold s8LUFilt
  have hl : ∀ x ∈ (s.active.val.map (·.val)), (fun i => do return (← OsuModel.Sim.Sim.ostate i).life == .alive :
      Nat → OsuModel.Sim.SimM Bool) x C (simStS tn s) =
      .ok ((fun i => ((simStS tn s).objs[i]?.map (fun o => o.life == .alive)).getD false) x, simStS tn s) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hy' : y.val < (simStS tn s).objs.size := by simpa using hact y hy
    simp only [simM_bind, simS_ostate _ _ _ hy', Except.bind, simM_pure]
    rw [Array.getElem?_eq_getElem hy']; rfl
  have hA : (simStS tn s).active = (s.active.val.map (·.val)).toArray := by simp [simStS, abs]
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind]
  rw [hA, s8_filterM C _ _ _ _ hl]
  simp only [simM_modify]
  congr 2
  simp only [simStS, abs, OsuModel.Sim.St.mk.injEq]
  rw [hKF, List.filter_map]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_, by simp⟩
  congr 2
  apply List.filter_congr
  intro x hx
  have hx' := hact x hx
  simp only [Function.comp, s8Alive, List.getElem?_eq_getElem hx']
  rw [Array.getElem?_eq_getElem (by simpa using hx')]
  simp
  rfl


theorem s8_DG_dead (tn : Nat → String) (C : OsuModel.Sim.Ctx) (t : F64) (s : sim.state.St) (x : Nat)
    (ho : x < s.objs.val.length)
    (hc : (s.objs.val[x]'ho).lifetime_end ≤ t ∨ t < (s.objs.val[x]'ho).lifetime_start) :
    s8DG t x PUnit.unit C (simStS tn s) =
      (OsuModel.Sim.Sim.becameDead x C (simStS tn s)).bind (fun p => .ok (ForInStep.yield PUnit.unit, p.2)) := by
  have hos : x < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s x hos
  have hc' : (decide ((ostateS (s.objs.val[x]'ho)).lifetimeEnd ≤ t) ||
      decide (t < (ostateS (s.objs.val[x]'ho)).lifetimeStart)) = true := by
    rcases hc with h | h <;> simp [ostateS, h]
  unfold s8DG
  simp only [simM_bind, simS_ostate _ _ _ hos, hO, Except.bind, hc', ite_true, simM_pure]

theorem s8_DG_skip (tn : Nat → String) (C : OsuModel.Sim.Ctx) (t : F64) (s : sim.state.St) (x : Nat)
    (ho : x < s.objs.val.length)
    (hc : ¬ ((s.objs.val[x]'ho).lifetime_end ≤ t ∨ t < (s.objs.val[x]'ho).lifetime_start)) :
    s8DG t x PUnit.unit C (simStS tn s) = .ok (ForInStep.yield PUnit.unit, simStS tn s) := by
  have hos : x < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s x hos
  have hc' : (decide ((ostateS (s.objs.val[x]'ho)).lifetimeEnd ≤ t) ||
      decide (t < (ostateS (s.objs.val[x]'ho)).lifetimeStart)) = false := by
    simp only [not_or] at hc; simp [ostateS, hc.1, hc.2]
  unfold s8DG
  simp only [simM_bind, simS_ostate _ _ _ hos, hO, Except.bind, hc', Bool.false_eq_true, ite_false, simM_pure]

-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (newly-dead scan s8DG + s8LUFilt, generic over the became_dead contract; parent sim.step.lifetime_update_refines)
theorem sim.step.lifetime_update_loop0_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (t : float.F64)
    (snap : alloc.vec.Vec Usize) (D : Nat → sim.state.St → Prop)
    (hb : ∀ k s, D k s → ∀ hk : k < snap.val.length, (snap.val[k]'hk).val < s.objs.val.length)
    (hd : ∀ k s (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < s.objs.val.length), D k s →
      ((s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ t ∨ t < (s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      ∃ res s', sim.step.became_dead c s (snap.val[k]'hk) = ok (res, s') ∧
        simRelM tn s' res (OsuModel.Sim.Sim.becameDead (snap.val[k]'hk).val (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → D (k + 1) s'))
    (hs : ∀ k s (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < s.objs.val.length), D k s →
      ¬ ((s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ t ∨ t < (s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      D (k + 1) s)
    (he : ∀ s, D snap.val.length s → ∀ x ∈ s.active.val, x.val < s.objs.val.length) :
    ∀ m (k : Usize) (s : sim.state.St), snap.val.length - k.val = m → k.val ≤ snap.val.length → D k.val s →
      ∃ res s', sim.step.lifetime_update_loop0 c s t snap k = ok (res, s') ∧
        simRelM tn s' res ((do forIn ((snap.val.drop k.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt)
          (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → ∃ sE KF, D snap.val.length sE ∧ s' = { sE with active := KF } ∧
          KF.val = sE.active.val.filter (s8Alive sE)) := by
  intro m
  induction m with
  | zero =>
    intro k s hm hk hD
    have hkl : snap.val.length = k.val := by omega
    have hD' : D snap.val.length s := by rw [hkl]; exact hD
    obtain ⟨KF, eF, vF⟩ := sim.step.lifetime_update_loop0_loop0_refines s (he s hD') s.active.val.length 0#usize (alloc.vec.Vec.new Usize)
      (by simp) (by simp) (by simp)
    have vF' : KF.val = s.active.val.filter (s8Alive s) := by simpa using vF
    refine ⟨.Ok (), { s with active := KF }, ?_, ?_, fun _ => ⟨s, KF, hD', rfl, vF'⟩⟩
    · unfold sim.step.lifetime_update_loop0
      rw [loop_unfold]
      have hge : ¬ k < alloc.vec.Vec.len snap := by rw [vec_lt_len_iff]; omega
      simp only [sim.step.lifetime_update_loop0.body, hge, ite_false, eF, bind_ok]
      simp
    · show _ = _
      have hdr : snap.val.drop k.val = [] := by simp; omega
      simp only [hdr, List.map_nil, List.forIn_nil, simM_bind, simM_pure, Except.bind]
      exact s8_filt_spec tn _ s (he s hD') KF vF'
  | succ m ih =>
    intro k s hm hk hD
    have hkl : k.val < snap.val.length := by omega
    have ho := hb k.val s hD hkl
    have hlt : k < alloc.vec.Vec.len snap := by rw [vec_lt_len_iff]; exact hkl
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := snap.property; omega)
    have hdrop : (snap.val.drop k.val).map (·.val) =
        (snap.val[k.val]'hkl).val :: (snap.val.drop k1.val).map (·.val) := by
      rw [List.drop_eq_getElem_cons hkl, hk1v]; rfl
    have hstep : ∀ s1, sim.step.lifetime_update_loop0.body c t snap s k = ok (.cont (s1, k1)) →
        sim.step.lifetime_update_loop0 c s t snap k = sim.step.lifetime_update_loop0 c s1 t snap k1 := by
      intro s1 hb1
      conv_lhs => unfold sim.step.lifetime_update_loop0
      rw [loop_unfold]; dsimp only; rw [hb1]; simp only [bind_ok]
      rfl
    by_cases hc : (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t ∨
        t < (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_start
    · obtain ⟨res, s1, e1, r1, i1⟩ := hd k.val s hkl ho hD hc
      have hbody : ∀ R, (∀ (hle : (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t),
            sim.step.lifetime_update_loop0.body c t snap s k = R) →
          (∀ (hle : ¬ (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t)
            (hls : t < (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_start),
            sim.step.lifetime_update_loop0.body c t snap s k = R) →
          sim.step.lifetime_update_loop0.body c t snap s k = R := by
        intro R h1 h2
        by_cases hle : (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t
        · exact h1 hle
        · exact h2 hle (hc.resolve_left hle)
      have hS := s8_DG_dead tn (simCtxS tn fo c) t s _ ho hc
      cases res with
      | Err e =>
        refine ⟨.Err e, s1, ?_, ?_, fun h => by cases h⟩
        · have hb1 : sim.step.lifetime_update_loop0.body c t snap s k = ok (.done (.Err e, s1)) := by
            apply hbody
            · intro hle
              simp only [sim.step.lifetime_update_loop0.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
              simp [float.F64.le,
                hle, e1, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            · intro hle hls
              simp only [sim.step.lifetime_update_loop0.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
              simp [float.F64.le,
                hle, float.F64.lt, hls, e1, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          unfold sim.step.lifetime_update_loop0
          rw [loop_unfold]; dsimp only
          rw [hb1]; simp only [bind_ok]
        · obtain ⟨mm, hmm⟩ := r1
          refine ⟨mm, ?_⟩
          rw [hdrop]
          simp only [List.forIn_cons, simM_bind, hS, hmm, Except.bind]
      | Ok u =>
        cases u
        have hb1 : sim.step.lifetime_update_loop0.body c t snap s k = ok (.cont (s1, k1)) := by
          apply hbody
          · intro hle
            simp only [sim.step.lifetime_update_loop0.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
            simp [float.F64.le,
              hle, e1, core.result.Result.Insts.CoreOpsTry.branch, hk1]
          · intro hle hls
            simp only [sim.step.lifetime_update_loop0.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
            simp [float.F64.le,
              hle, float.F64.lt, hls, e1, core.result.Result.Insts.CoreOpsTry.branch, hk1]
        obtain ⟨res', s', e', r', i'⟩ := ih k1 s1 (by omega) (by omega) (by rw [hk1v]; exact i1 rfl)
        refine ⟨res', s', by rw [hstep s1 hb1]; exact e', ?_, i'⟩
        have r1' : OsuModel.Sim.Sim.becameDead (snap.val[k.val]'hkl).val (simCtxS tn fo c) (simStS tn s) =
          .ok ((), simStS tn s1) := r1
        have : ((do forIn ((snap.val.drop k.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
            OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s)) =
            ((do forIn ((snap.val.drop k1.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
            OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s1)) := by
          rw [hdrop]
          simp only [List.forIn_cons, simM_bind, hS, r1', Except.bind]
        rw [this]; exact r'
    · have hb1 : sim.step.lifetime_update_loop0.body c t snap s k = ok (.cont (s, k1)) := by
        simp only [not_or] at hc
        simp only [sim.step.lifetime_update_loop0.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok,
          vec_index_eq _ _ ho, float.F64.le, hc.1, decide_false, Bool.false_eq_true, ite_false, float.F64.lt, hc.2, hk1]
      have hS := s8_DG_skip tn (simCtxS tn fo c) t s _ ho hc
      obtain ⟨res', s', e', r', i'⟩ := ih k1 s (by omega) (by omega) (by rw [hk1v]; exact hs k.val s hkl ho hD hc)
      refine ⟨res', s', by rw [hstep s hb1]; exact e', ?_, i'⟩
      have : ((do forIn ((snap.val.drop k.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
          OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s)) =
          ((do forIn ((snap.val.drop k1.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
          OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s)) := by
        rw [hdrop]
        simp only [List.forIn_cons, simM_bind, hS, Except.bind]
      rw [this]; exact r'

-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (active filter, s8LUFilt via s8_filt_spec; parent sim.step.lifetime_update_refines, bridge s8_lu_splitS by rfl)
theorem sim.step.lifetime_update_loop1_loop0_refines (s : sim.state.St) (hact : ∀ x ∈ s.active.val, x.val < s.objs.val.length) :
    ∀ m (j : Usize) (kept : alloc.vec.Vec Usize), s.active.val.length - j.val = m → j.val ≤ s.active.val.length →
      kept.val.length ≤ j.val →
      ∃ KF : alloc.vec.Vec Usize, sim.step.lifetime_update_loop1_loop0 s kept j = ok (s8FT s KF) ∧
        KF.val = kept.val ++ (s.active.val.drop j.val).filter (s8Alive s) := by
  intro m
  induction m with
  | zero =>
    intro j kept hm hj hk
    refine ⟨kept, ?_, by simp [show s.active.val.length ≤ j.val by omega]⟩
    unfold sim.step.lifetime_update_loop1_loop0
    rw [loop_unfold]
    have hge : ¬ j < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; omega
    simp [sim.step.lifetime_update_loop1_loop0.body, hge]
  | succ m ih =>
    intro j kept hm hj hk
    have hjl : j.val < s.active.val.length := by omega
    have hlt : j < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; exact hjl
    have hx := hact _ (List.getElem_mem hjl)
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := s.active.property; omega)
    have hkm : kept.val.length < Usize.max := by have := s.active.property; omega
    obtain ⟨k1, ek1, vk1⟩ : ∃ k1 : alloc.vec.Vec Usize,
        (if lifeS (s.objs.val[(s.active.val[j.val]'hjl).val]'hx).life == OsuModel.Sim.Life.alive
          then alloc.vec.Vec.push kept (s.active.val[j.val]'hjl) else ok kept) = ok k1 ∧
        k1.val = kept.val ++ (if s8Alive s (s.active.val[j.val]'hjl) then [s.active.val[j.val]'hjl] else []) := by
      have hA : s8Alive s (s.active.val[j.val]'hjl) =
          (lifeS (s.objs.val[(s.active.val[j.val]'hjl).val]'hx).life == OsuModel.Sim.Life.alive) := by
        simp [s8Alive, hx]
      rw [hA]
      cases hl : (s.objs.val[(s.active.val[j.val]'hjl).val]'hx).life <;>
        simp [lifeS, vec_push_ok _ _ hkm, s8_lbe1, s8_lbe2, s8_lbe3]
    have hb : sim.step.lifetime_update_loop1_loop0.body s kept j = ok (.cont (k1, j1)) := by
      simp only [sim.step.lifetime_update_loop1_loop0.body, hlt, ite_true, vec_index_eq _ _ hjl, bind_ok,
        vec_index_eq _ _ hx, s8_life_eq, ek1, hj1]
    obtain ⟨KF, e, v⟩ := ih j1 k1 (by omega) (by omega) (by rw [vk1]; split <;> simp <;> omega)
    refine ⟨KF, ?_, ?_⟩
    · unfold sim.step.lifetime_update_loop1_loop0
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      unfold sim.step.lifetime_update_loop1_loop0 at e
      exact e
    · rw [v, vk1, hj1v, List.drop_eq_getElem_cons hjl, List.filter_cons]
      split <;> simp
-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (newly-dead scan s8DG + s8LUFilt, generic over the became_dead contract; parent sim.step.lifetime_update_refines)
theorem sim.step.lifetime_update_loop1_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (t : float.F64)
    (snap : alloc.vec.Vec Usize) (D : Nat → sim.state.St → Prop)
    (hb : ∀ k s, D k s → ∀ hk : k < snap.val.length, (snap.val[k]'hk).val < s.objs.val.length)
    (hd : ∀ k s (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < s.objs.val.length), D k s →
      ((s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ t ∨ t < (s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      ∃ res s', sim.step.became_dead c s (snap.val[k]'hk) = ok (res, s') ∧
        simRelM tn s' res (OsuModel.Sim.Sim.becameDead (snap.val[k]'hk).val (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → D (k + 1) s'))
    (hs : ∀ k s (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < s.objs.val.length), D k s →
      ¬ ((s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ t ∨ t < (s.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      D (k + 1) s)
    (he : ∀ s, D snap.val.length s → ∀ x ∈ s.active.val, x.val < s.objs.val.length) :
    ∀ m (k : Usize) (s : sim.state.St), snap.val.length - k.val = m → k.val ≤ snap.val.length → D k.val s →
      ∃ res s', sim.step.lifetime_update_loop1 c s t snap k = ok (res, s') ∧
        simRelM tn s' res ((do forIn ((snap.val.drop k.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt)
          (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → ∃ sE KF, D snap.val.length sE ∧ s' = { sE with active := KF } ∧
          KF.val = sE.active.val.filter (s8Alive sE)) := by
  intro m
  induction m with
  | zero =>
    intro k s hm hk hD
    have hkl : snap.val.length = k.val := by omega
    have hD' : D snap.val.length s := by rw [hkl]; exact hD
    obtain ⟨KF, eF, vF⟩ := sim.step.lifetime_update_loop1_loop0_refines s (he s hD') s.active.val.length 0#usize (alloc.vec.Vec.new Usize)
      (by simp) (by simp) (by simp)
    have vF' : KF.val = s.active.val.filter (s8Alive s) := by simpa using vF
    refine ⟨.Ok (), { s with active := KF }, ?_, ?_, fun _ => ⟨s, KF, hD', rfl, vF'⟩⟩
    · unfold sim.step.lifetime_update_loop1
      rw [loop_unfold]
      have hge : ¬ k < alloc.vec.Vec.len snap := by rw [vec_lt_len_iff]; omega
      simp only [sim.step.lifetime_update_loop1.body, hge, ite_false, eF, bind_ok]
      simp
    · show _ = _
      have hdr : snap.val.drop k.val = [] := by simp; omega
      simp only [hdr, List.map_nil, List.forIn_nil, simM_bind, simM_pure, Except.bind]
      exact s8_filt_spec tn _ s (he s hD') KF vF'
  | succ m ih =>
    intro k s hm hk hD
    have hkl : k.val < snap.val.length := by omega
    have ho := hb k.val s hD hkl
    have hlt : k < alloc.vec.Vec.len snap := by rw [vec_lt_len_iff]; exact hkl
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := snap.property; omega)
    have hdrop : (snap.val.drop k.val).map (·.val) =
        (snap.val[k.val]'hkl).val :: (snap.val.drop k1.val).map (·.val) := by
      rw [List.drop_eq_getElem_cons hkl, hk1v]; rfl
    have hstep : ∀ s1, sim.step.lifetime_update_loop1.body c t snap s k = ok (.cont (s1, k1)) →
        sim.step.lifetime_update_loop1 c s t snap k = sim.step.lifetime_update_loop1 c s1 t snap k1 := by
      intro s1 hb1
      conv_lhs => unfold sim.step.lifetime_update_loop1
      rw [loop_unfold]; dsimp only; rw [hb1]; simp only [bind_ok]
      rfl
    by_cases hc : (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t ∨
        t < (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_start
    · obtain ⟨res, s1, e1, r1, i1⟩ := hd k.val s hkl ho hD hc
      have hbody : ∀ R, (∀ (hle : (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t),
            sim.step.lifetime_update_loop1.body c t snap s k = R) →
          (∀ (hle : ¬ (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t)
            (hls : t < (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_start),
            sim.step.lifetime_update_loop1.body c t snap s k = R) →
          sim.step.lifetime_update_loop1.body c t snap s k = R := by
        intro R h1 h2
        by_cases hle : (s.objs.val[(snap.val[k.val]'hkl).val]'ho).lifetime_end ≤ t
        · exact h1 hle
        · exact h2 hle (hc.resolve_left hle)
      have hS := s8_DG_dead tn (simCtxS tn fo c) t s _ ho hc
      cases res with
      | Err e =>
        refine ⟨.Err e, s1, ?_, ?_, fun h => by cases h⟩
        · have hb1 : sim.step.lifetime_update_loop1.body c t snap s k = ok (.done (.Err e, s1)) := by
            apply hbody
            · intro hle
              simp only [sim.step.lifetime_update_loop1.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
              simp [float.F64.le,
                hle, e1, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            · intro hle hls
              simp only [sim.step.lifetime_update_loop1.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
              simp [float.F64.le,
                hle, float.F64.lt, hls, e1, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          unfold sim.step.lifetime_update_loop1
          rw [loop_unfold]; dsimp only
          rw [hb1]; simp only [bind_ok]
        · obtain ⟨mm, hmm⟩ := r1
          refine ⟨mm, ?_⟩
          rw [hdrop]
          simp only [List.forIn_cons, simM_bind, hS, hmm, Except.bind]
      | Ok u =>
        cases u
        have hb1 : sim.step.lifetime_update_loop1.body c t snap s k = ok (.cont (s1, k1)) := by
          apply hbody
          · intro hle
            simp only [sim.step.lifetime_update_loop1.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
            simp [float.F64.le,
              hle, e1, core.result.Result.Insts.CoreOpsTry.branch, hk1]
          · intro hle hls
            simp only [sim.step.lifetime_update_loop1.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok, vec_index_eq _ _ ho]
            simp [float.F64.le,
              hle, float.F64.lt, hls, e1, core.result.Result.Insts.CoreOpsTry.branch, hk1]
        obtain ⟨res', s', e', r', i'⟩ := ih k1 s1 (by omega) (by omega) (by rw [hk1v]; exact i1 rfl)
        refine ⟨res', s', by rw [hstep s1 hb1]; exact e', ?_, i'⟩
        have r1' : OsuModel.Sim.Sim.becameDead (snap.val[k.val]'hkl).val (simCtxS tn fo c) (simStS tn s) =
          .ok ((), simStS tn s1) := r1
        have : ((do forIn ((snap.val.drop k.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
            OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s)) =
            ((do forIn ((snap.val.drop k1.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
            OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s1)) := by
          rw [hdrop]
          simp only [List.forIn_cons, simM_bind, hS, r1', Except.bind]
        rw [this]; exact r'
    · have hb1 : sim.step.lifetime_update_loop1.body c t snap s k = ok (.cont (s, k1)) := by
        simp only [not_or] at hc
        simp only [sim.step.lifetime_update_loop1.body, hlt, ite_true, vec_index_eq _ _ hkl, bind_ok,
          vec_index_eq _ _ ho, float.F64.le, hc.1, decide_false, Bool.false_eq_true, ite_false, float.F64.lt, hc.2, hk1]
      have hS := s8_DG_skip tn (simCtxS tn fo c) t s _ ho hc
      obtain ⟨res', s', e', r', i'⟩ := ih k1 s (by omega) (by omega) (by rw [hk1v]; exact hs k.val s hkl ho hD hc)
      refine ⟨res', s', by rw [hstep s hb1]; exact e', ?_, i'⟩
      have : ((do forIn ((snap.val.drop k.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
          OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s)) =
          ((do forIn ((snap.val.drop k1.val).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
          OsuModel.Sim.SimM Unit) (simCtxS tn fo c) (simStS tn s)) := by
        rw [hdrop]
        simp only [List.forIn_cons, simM_bind, hS, Except.bind]
      rw [this]; exact r'

/-- spec: the first-update scan body (future list accumulator) -/
def s8FG (t : F64) (i : Nat) (fut : Array Nat) : OsuModel.Sim.SimM (ForInStep (Array Nat)) := do
  let os ← OsuModel.Sim.Sim.ostate i
  if t < os.lifetimeStart then pure (ForInStep.yield (fut.push i))
  else if os.lifetimeEnd ≤ t then do
    OsuModel.Sim.Sim.modifyObj i fun os => { os with life := .past }
    pure (ForInStep.yield fut)
  else do
    OsuModel.Sim.Sim.becameAlive i
    pure (ForInStep.yield fut)

/-- spec: `lifetimeUpdate`'s first-update branch, continuation `K` (the newly-dead scan) -/
def s8LUFirstK (t : F64) (c : OsuModel.Sim.Ctx) (K : Unit → OsuModel.Sim.SimM Unit) : OsuModel.Sim.SimM Unit := do
  modify fun s => { s with firstLifetimeUpdate := false }
  let fut ← forIn [0:c.pb.objects.size] (#[] : Array Nat) (s8FG t)
  let keyed ← fut.mapM fun i => do return (i, (← OsuModel.Sim.Sim.ostate i).lifetimeStart)
  let sorted := (OsuModel.Sim.stableSortBy keyed fun a b => a.2 < b.2).map (·.1)
  let r ← modify fun s => { s with futureOrder := sorted, nextFuture := 0 }
  K r

/-- spec: the later-update fuel-loop body -/
def s8WG (t : F64) (_ : Unit) (fuel : Nat) : OsuModel.Sim.SimM (ForInStep Nat) :=
  if fuel > 0 then do
    let s ← OsuModel.Sim.Sim.st
    if h : s.nextFuture < s.futureOrder.size then do
      let os ← OsuModel.Sim.Sim.ostate (s.futureOrder[s.nextFuture]'h)
      if t < os.lifetimeStart then pure (ForInStep.done (fuel - 1))
      else do
        modify fun s => { s with nextFuture := s.nextFuture + 1 }
        if os.lifetimeEnd ≤ t then do
          OsuModel.Sim.Sim.modifyObj (s.futureOrder[s.nextFuture]'h) fun os => { os with life := .past }
          pure (ForInStep.yield (fuel - 1))
        else do
          OsuModel.Sim.Sim.becameAlive (s.futureOrder[s.nextFuture]'h)
          pure (ForInStep.yield (fuel - 1))
    else pure (ForInStep.done (fuel - 1))
  else pure (ForInStep.done fuel)

/-- spec: `lifetimeUpdate`'s later-update branch (fuel loop), continuation `K` -/
def s8LUFutK (t : F64) (c : OsuModel.Sim.Ctx) (K : Unit → OsuModel.Sim.SimM Unit) : OsuModel.Sim.SimM Unit := do
  let _ ← forIn Lean.Loop.mk (c.pb.objects.size + 1) (s8WG t)
  K ()

/-- spec: the newly-dead scan and active filter -/
def s8LUTail (t : F64) : OsuModel.Sim.SimM Unit := do
  let s ← OsuModel.Sim.Sim.st
  forIn s.active PUnit.unit (s8DG t)
  s8LUFilt

def s8LUS : OsuModel.Sim.SimM Unit := do
  let t := (← OsuModel.Sim.Sim.st).t
  let c ← OsuModel.Sim.Sim.ctx
  if (← OsuModel.Sim.Sim.st).firstLifetimeUpdate then s8LUFirstK t c (fun _ => s8LUTail t)
  else s8LUFutK t c (fun _ => s8LUTail t)

theorem s8_lu_splitS : OsuModel.Sim.Sim.lifetimeUpdate = s8LUS := rfl


/-- spec: the first-update tail after the scan (sort + store), continuation `K` -/
def s8FirstRest (K : Unit → OsuModel.Sim.SimM Unit) (fut : Array Nat) : OsuModel.Sim.SimM Unit := do
  let keyed ← fut.mapM fun i => do return (i, (← OsuModel.Sim.Sim.ostate i).lifetimeStart)
  let sorted := (OsuModel.Sim.stableSortBy keyed fun a b => a.2 < b.2).map (·.1)
  let r ← modify fun s => { s with futureOrder := sorted, nextFuture := 0 }
  K r

theorem s8_first_eq (t : F64) (c : OsuModel.Sim.Ctx) (K : Unit → OsuModel.Sim.SimM Unit) :
    s8LUFirstK t c K = (do
      modify fun s => { s with firstLifetimeUpdate := false }
      let fut ← forIn [0:c.pb.objects.size] (#[] : Array Nat) (s8FG t)
      s8FirstRest K fut) := rfl

theorem s8_FG_fut (tn : Nat → String) (C : OsuModel.Sim.Ctx) (t : F64) (s : sim.state.St) (i : Nat)
    (ho : i < s.objs.val.length) (fut : Array Nat) (h1 : t < (s.objs.val[i]'ho).lifetime_start) :
    s8FG t i fut C (simStS tn s) = .ok (ForInStep.yield (fut.push i), simStS tn s) := by
  have hos : i < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s i hos
  have h1' : t < (ostateS (s.objs.val[i]'ho)).lifetimeStart := h1
  unfold s8FG
  simp only [simM_bind, simS_ostate _ _ _ hos, hO, Except.bind, h1', ite_true, simM_pure]

theorem s8_FG_past (tn : Nat → String) (C : OsuModel.Sim.Ctx) (t : F64) (s : sim.state.St) (i : Usize)
    (ho : i.val < s.objs.val.length) (fut : Array Nat) (h1 : ¬ t < (s.objs.val[i.val]'ho).lifetime_start)
    (h2 : (s.objs.val[i.val]'ho).lifetime_end ≤ t) :
    s8FG t i.val fut C (simStS tn s) = .ok (ForInStep.yield fut,
      simStS tn { s with objs := s.objs.set i { (s.objs.val[i.val]'ho) with life := .Past } }) := by
  have hos : i.val < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s i.val hos
  have h1' : ¬ t < (ostateS (s.objs.val[i.val]'ho)).lifetimeStart := h1
  have h2' : (ostateS (s.objs.val[i.val]'ho)).lifetimeEnd ≤ t := h2
  have hm := sim_modifyObj_stS tn C s i ho { (s.objs.val[i.val]'ho) with life := .Past }
    (fun os => { os with life := .past }) rfl i.val rfl
  unfold s8FG
  simp only [simM_bind, simS_ostate _ _ _ hos, hO, Except.bind, h1', h2', ite_true, ite_false, simM_pure, hm]

theorem s8_FG_alive (tn : Nat → String) (C : OsuModel.Sim.Ctx) (t : F64) (s : sim.state.St) (i : Nat)
    (ho : i < s.objs.val.length) (fut : Array Nat) (h1 : ¬ t < (s.objs.val[i]'ho).lifetime_start)
    (h2 : ¬ (s.objs.val[i]'ho).lifetime_end ≤ t) :
    s8FG t i fut C (simStS tn s) =
      (OsuModel.Sim.Sim.becameAlive i C (simStS tn s)).bind (fun p => .ok (ForInStep.yield fut, p.2)) := by
  have hos : i < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s i hos
  have h1' : ¬ t < (ostateS (s.objs.val[i]'ho)).lifetimeStart := h1
  have h2' : ¬ (ostateS (s.objs.val[i]'ho)).lifetimeEnd ≤ t := h2
  unfold s8FG
  simp only [simM_bind, simS_ostate _ _ _ hos, hO, Except.bind, h1', h2', ite_false, simM_pure]

-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (first-update scan s8FG + s8FirstRest, generic over the became_alive contract; parent sim.step.lifetime_update_refines)
theorem sim.step.lifetime_first_update_loop_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (t : F64)
    (A : Nat → sim.state.St → List Usize → Prop) (hcl : c.pb.objects.val.length < Usize.max)
    (hlen : ∀ i s F, A i s F → s.objs.val.length = c.pb.objects.val.length)
    (hF : ∀ (i : Usize) s F (ho : i.val < s.objs.val.length), A i.val s F →
      t < (s.objs.val[i.val]'ho).lifetime_start → A (i.val + 1) s (F ++ [i]))
    (hP : ∀ (i : Usize) s F (ho : i.val < s.objs.val.length), A i.val s F →
      ¬ t < (s.objs.val[i.val]'ho).lifetime_start → (s.objs.val[i.val]'ho).lifetime_end ≤ t →
      A (i.val + 1) { s with objs := s.objs.set i { (s.objs.val[i.val]'ho) with life := .Past } } F)
    (hA : ∀ (i : Usize) s F (ho : i.val < s.objs.val.length), A i.val s F →
      ¬ t < (s.objs.val[i.val]'ho).lifetime_start → ¬ (s.objs.val[i.val]'ho).lifetime_end ≤ t →
      ∃ res s', sim.step.became_alive c s i = ok (res, s') ∧
        simRelM tn s' res (OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn s)) ∧
        (res = .Ok () → A (i.val + 1) s' F)) :
    ∀ m (i : Usize) (s : sim.state.St) (fut : alloc.vec.Vec Usize),
      c.pb.objects.val.length - i.val = m → i.val ≤ c.pb.objects.val.length → A i.val s fut.val →
      fut.val.length ≤ i.val → (∀ e ∈ fut.val, e.val < i.val) →
      ∃ res s', sim.step.lifetime_first_update_loop c s t fut i = ok (res, s') ∧
        (∀ K, res = .Ok () → (forIn (List.range' i.val m) (fut.val.map (·.val)).toArray (s8FG t) >>= s8FirstRest K)
          (simCtxS tn fo c) (simStS tn s) = K () (simCtxS tn fo c) (simStS tn s')) ∧
        (∀ K e, res = .Err e → ∃ msg, (forIn (List.range' i.val m) (fut.val.map (·.val)).toArray (s8FG t) >>=
          s8FirstRest K) (simCtxS tn fo c) (simStS tn s) = .error msg) ∧
        (res = .Ok () → ∃ sE FUT sorted, A c.pb.objects.val.length sE FUT.val ∧
          sim.step.sort_by_lifetime_start sE (alloc.vec.Vec.deref FUT) = ok sorted ∧
          s' = { sE with next_future := 0#usize, future_order := sorted }) := by
  intro m
  induction m with
  | zero =>
    intro i s fut hm hi hA0 hfl hfe
    have hil : i.val = c.pb.objects.val.length := by omega
    have hdv : (alloc.vec.Vec.deref fut).val = fut.val := by simp [alloc.vec.Vec.deref, Slice.from_val]
    have hx : ∀ e ∈ (alloc.vec.Vec.deref fut).val, e.val < s.objs.val.length := by
      intro e he; rw [hdv] at he; rw [hlen _ _ _ hA0, ← hil]; exact hfe e he
    obtain ⟨out, hout, hspec⟩ := sim.step.sort_by_lifetime_start_refines tn s (alloc.vec.Vec.deref fut) hx
      (by rw [hdv]; omega)
    refine ⟨.Ok (), { s with next_future := 0#usize, future_order := out }, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · intro K e h; cases h
    · intro _; exact ⟨s, fut, out, by rw [← hil]; exact hA0, hout, rfl⟩
    · unfold sim.step.lifetime_first_update_loop
      rw [loop_unfold]
      have hge : ¬ i < alloc.vec.Vec.len c.pb.objects := by rw [vec_lt_len_iff]; omega
      simp only [sim.step.lifetime_first_update_loop.body, hge, ite_false, hout, bind_ok]
    · intro K _
      have hsp := hspec (simCtxS tn fo c)
      simp only [simM_bind, simM_pure] at hsp
      simp only [List.range'_zero, List.forIn_nil, simM_bind, simM_pure, Except.bind, s8FirstRest]
      rw [hdv] at hsp
      have hsp' := hsp
      revert hsp'
      cases hk : (Array.mapM (fun i => do return (i, (← OsuModel.Sim.Sim.ostate i).lifetimeStart) :
          Nat → OsuModel.Sim.SimM (Nat × F64)) (fut.val.map (·.val)).toArray)
          (simCtxS tn fo c) (simStS tn s) with
      | error e => intro h; simp [Except.bind] at h
      | ok p =>
        obtain ⟨kp, sp⟩ := p
        intro h
        simp only [Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        simp only [simM_modify]
        first | (rw [h1]; rfl) | (simp only [h1]; rfl)
  | succ m ih =>
    intro i s fut hm hi hA0 hfl hfe
    have hic : i.val < c.pb.objects.val.length := by omega
    have ho : i.val < s.objs.val.length := by rw [hlen _ _ _ hA0]; exact hic
    have hlt : i < alloc.vec.Vec.len c.pb.objects := by rw [vec_lt_len_iff]; exact hic
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hR : List.range' i.val (m + 1) = i.val :: List.range' i1.val m := by rw [hi1v]; rfl
    have hstep : ∀ X, sim.step.lifetime_first_update_loop.body c t s fut i = ok (.cont X) →
        sim.step.lifetime_first_update_loop c s t fut i = sim.step.lifetime_first_update_loop c X.1 t X.2.1 X.2.2 := by
      intro X hb1
      conv_lhs => unfold sim.step.lifetime_first_update_loop
      rw [loop_unfold]; dsimp only; rw [hb1]; simp only [bind_ok]
      rfl
    by_cases h1 : t < (s.objs.val[i.val]'ho).lifetime_start
    · have hpl : fut.val.length < Usize.max := by omega
      have hb1 : sim.step.lifetime_first_update_loop.body c t s fut i = ok (.cont (s, vpush fut i hpl, i1)) := by
        simp only [sim.step.lifetime_first_update_loop.body, hlt, ite_true, vec_index_eq _ _ ho, bind_ok,
          float.F64.lt, h1, decide_true, vec_push_ok _ _ hpl, hi1]
      obtain ⟨res, s', e', r1, r2, r3⟩ := ih i1 s (vpush fut i hpl) (by omega) (by omega)
        (by rw [hi1v, vpush_val]; exact hF i s fut.val ho hA0 h1) (by simp; omega)
        (by intro e he; simp at he; rcases he with he | he
            · have := hfe e he; omega
            · subst he; omega)
      have hS := s8_FG_fut tn (simCtxS tn fo c) t s i.val ho ((fut.val.map (·.val)).toArray) h1
      have hpush : ((fut.val.map (·.val)).toArray.push i.val) = ((vpush fut i hpl).val.map (·.val)).toArray := by
        simp
      refine ⟨res, s', by rw [hstep _ hb1]; exact e', fun K h => ?_, fun K e h => ?_, r3⟩
      · rw [hR]; simp only [List.forIn_cons, simM_bind, hS, Except.bind, hpush]
        have := r1 K h; simp only [simM_bind] at this; exact this
      · rw [hR]; simp only [List.forIn_cons, simM_bind, hS, Except.bind, hpush]
        have := r2 K e h; simp only [simM_bind] at this; exact this
    · by_cases h2 : (s.objs.val[i.val]'ho).lifetime_end ≤ t
      · have hb1 : sim.step.lifetime_first_update_loop.body c t s fut i = ok (.cont
            ({ s with objs := s.objs.set i { (s.objs.val[i.val]'ho) with life := .Past } }, fut, i1)) := by
          simp only [sim.step.lifetime_first_update_loop.body, hlt, ite_true, vec_index_eq _ _ ho, bind_ok,
            float.F64.lt, h1, decide_false, Bool.false_eq_true, ite_false, float.F64.le, h2, decide_true,
            vec_index_mut_eq _ _ ho, hi1]
          rfl
        have hlen' : ({ s with objs := s.objs.set i { (s.objs.val[i.val]'ho) with life := .Past } } : sim.state.St).objs.val.length
            = s.objs.val.length := by simp [alloc.vec.Vec.set]
        obtain ⟨res, s', e', r1, r2, r3⟩ := ih i1 _ fut (by omega) (by omega)
          (by rw [hi1v]; exact hP i s fut.val ho hA0 h1 h2) (by omega) (by intro e he; have := hfe e he; omega)
        have hS := s8_FG_past tn (simCtxS tn fo c) t s i ho ((fut.val.map (·.val)).toArray) h1 h2
        refine ⟨res, s', by rw [hstep _ hb1]; exact e', fun K h => ?_, fun K e h => ?_, r3⟩
        · rw [hR]; simp only [List.forIn_cons, simM_bind, hS, Except.bind]
          have := r1 K h; simp only [simM_bind] at this; exact this
        · rw [hR]; simp only [List.forIn_cons, simM_bind, hS, Except.bind]
          have := r2 K e h; simp only [simM_bind] at this; exact this
      · obtain ⟨res, s1, e1, rr, i1'⟩ := hA i s fut.val ho hA0 h1 h2
        have hS := s8_FG_alive tn (simCtxS tn fo c) t s i.val ho ((fut.val.map (·.val)).toArray) h1 h2
        cases res with
        | Err e =>
          have hb1 : sim.step.lifetime_first_update_loop.body c t s fut i = ok (.done (.Err e, s1)) := by
            simp only [sim.step.lifetime_first_update_loop.body, hlt, ite_true, vec_index_eq _ _ ho, bind_ok,
              float.F64.lt, h1, decide_false, Bool.false_eq_true, ite_false, float.F64.le, h2]
            simp [e1, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          refine ⟨.Err e, s1, ?_, ?_, ?_, ?_⟩
          rotate_left 1
          · intro K h; cases h
          rotate_left 1
          · intro h; cases h
          · unfold sim.step.lifetime_first_update_loop
            rw [loop_unfold]; dsimp only; rw [hb1]; simp only [bind_ok]
          · intro K e' _
            obtain ⟨mm, hmm⟩ := rr
            refine ⟨mm, ?_⟩
            rw [hR]; simp only [List.forIn_cons, simM_bind, hS, hmm, Except.bind]
        | Ok u =>
          cases u
          have hb1 : sim.step.lifetime_first_update_loop.body c t s fut i = ok (.cont (s1, fut, i1)) := by
            simp only [sim.step.lifetime_first_update_loop.body, hlt, ite_true, vec_index_eq _ _ ho, bind_ok,
              float.F64.lt, h1, decide_false, Bool.false_eq_true, ite_false, float.F64.le, h2]
            simp [e1, core.result.Result.Insts.CoreOpsTry.branch, hi1]
          have rr' : OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s1) := rr
          obtain ⟨res, s', e', r1, r2, r3⟩ := ih i1 s1 fut (by omega) (by omega)
            (by rw [hi1v]; exact i1' rfl) (by omega) (by intro e he; have := hfe e he; omega)
          refine ⟨res, s', by rw [hstep _ hb1]; exact e', fun K h => ?_, fun K e h => ?_, r3⟩
          · rw [hR]; simp only [List.forIn_cons, simM_bind, hS, rr', Except.bind]
            have := r1 K h; simp only [simM_bind] at this; exact this
          · rw [hR]; simp only [List.forIn_cons, simM_bind, hS, rr', Except.bind]
            have := r2 K e h; simp only [simM_bind] at this; exact this


/-- the later-update fuel loop with the context exploded as in the generated code -/
@[reducible] def s8FL (c : sim.state.Ctx) (s : sim.state.St) (t : float.F64) (fuel : Usize) (stop : Bool) :=
  sim.step.lifetime_future_update_loop c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s t fuel stop

@[reducible] def s8FB (c : sim.state.Ctx) (t : float.F64) (s : sim.state.St) (fuel : Usize) (stop : Bool) :=
  sim.step.lifetime_future_update_loop.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj t s fuel stop

theorem s8_FL_unfold (c : sim.state.Ctx) (s : sim.state.St) (t : float.F64) (fuel : Usize) (stop : Bool) :
    s8FL c s t fuel stop = (do
      let r ← s8FB c t s fuel stop
      match r with
      | .cont (s1, f1, b1) => s8FL c s1 t f1 b1
      | .done y => ok y) := by
  unfold s8FL sim.step.lifetime_future_update_loop
  rw [loop_unfold]
  simp only [s8FB]
  congr 1; funext r; cases r with
  | cont x => obtain ⟨a, b, d⟩ := x; rfl
  | done y => rfl

theorem s8_WG_zero (t : F64) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) :
    s8WG t () 0 C S = .ok (ForInStep.done 0, S) := by
  unfold s8WG; simp

theorem s8_WG_end (tn : Nat → String) (t : F64) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (m : Nat)
    (h : ¬ s.next_future.val < s.future_order.val.length) :
    s8WG t () (m + 1) C (simStS tn s) = .ok (ForInStep.done m, simStS tn s) := by
  have h' : ¬ (simStS tn s).nextFuture < (simStS tn s).futureOrder.size := by simpa [simStS, abs] using h
  unfold s8WG
  simp [OsuModel.Sim.Sim.st, h']

theorem s8_WG_fo (tn : Nat → String) (s : sim.state.St) (h : s.next_future.val < s.future_order.val.length)
    (h' : (simStS tn s).nextFuture < (simStS tn s).futureOrder.size) :
    (simStS tn s).futureOrder[(simStS tn s).nextFuture]'h' = (s.future_order.val[s.next_future.val]'h).val := by
  simp [simStS, abs]

theorem s8_WG_brk (tn : Nat → String) (t : F64) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (m : Nat)
    (h : s.next_future.val < s.future_order.val.length)
    (ho : (s.future_order.val[s.next_future.val]'h).val < s.objs.val.length)
    (h1 : t < (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_start) :
    s8WG t () (m + 1) C (simStS tn s) = .ok (ForInStep.done m, simStS tn s) := by
  have h' : (simStS tn s).nextFuture < (simStS tn s).futureOrder.size := by simpa [simStS, abs] using h
  have hos : (s.future_order.val[s.next_future.val]'h).val < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s _ hos
  have h1' : t < (ostateS (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho)).lifetimeStart := h1
  unfold s8WG
  simp only [show (m + 1 > 0) = True by simp, ite_true, simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind,
    dif_pos h', s8_WG_fo tn s h h', simS_ostate _ _ _ hos, hO, h1', simM_pure, Nat.add_sub_cancel]

theorem s8_nf_stS (tn : Nat → String) (s : sim.state.St) (i3 : Usize) (hi3 : i3.val = s.next_future.val + 1) :
    ({ simStS tn s with nextFuture := (simStS tn s).nextFuture + 1 } : OsuModel.Sim.St) =
      simStS tn { s with next_future := i3 } := by
  simp only [simStS, hi3]

theorem s8_WG_past (tn : Nat → String) (t : F64) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (m : Nat)
    (h : s.next_future.val < s.future_order.val.length)
    (ho : (s.future_order.val[s.next_future.val]'h).val < s.objs.val.length)
    (h1 : ¬ t < (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_start)
    (h2 : (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_end ≤ t)
    (i3 : Usize) (hi3 : i3.val = s.next_future.val + 1) :
    s8WG t () (m + 1) C (simStS tn s) = .ok (ForInStep.yield m, simStS tn { s with
      objs := s.objs.set (s.future_order.val[s.next_future.val]'h)
        { (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho) with life := .Past },
      next_future := i3 }) := by
  have h' : (simStS tn s).nextFuture < (simStS tn s).futureOrder.size := by simpa [simStS, abs] using h
  have hos : (s.future_order.val[s.next_future.val]'h).val < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s _ hos
  have h1' : ¬ t < (ostateS (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho)).lifetimeStart := h1
  have h2' : (ostateS (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho)).lifetimeEnd ≤ t := h2
  have hm := sim_modifyObj_stS tn C { s with next_future := i3 } (s.future_order.val[s.next_future.val]'h) ho
    { (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho) with life := .Past }
    (fun os => { os with life := .past }) rfl _ rfl
  unfold s8WG
  simp only [show (m + 1 > 0) = True by simp, ite_true, simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind,
    dif_pos h', s8_WG_fo tn s h h', simS_ostate _ _ _ hos, hO, h1', ite_false, simM_modify, s8_nf_stS tn s i3 hi3,
    h2', hm, simM_pure, Nat.add_sub_cancel]

theorem s8_WG_alive (tn : Nat → String) (t : F64) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (m : Nat)
    (h : s.next_future.val < s.future_order.val.length)
    (ho : (s.future_order.val[s.next_future.val]'h).val < s.objs.val.length)
    (h1 : ¬ t < (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_start)
    (h2 : ¬ (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_end ≤ t)
    (i3 : Usize) (hi3 : i3.val = s.next_future.val + 1) :
    s8WG t () (m + 1) C (simStS tn s) =
      (OsuModel.Sim.Sim.becameAlive (s.future_order.val[s.next_future.val]'h).val C
        (simStS tn { s with next_future := i3 })).bind (fun p => .ok (ForInStep.yield m, p.2)) := by
  have h' : (simStS tn s).nextFuture < (simStS tn s).futureOrder.size := by simpa [simStS, abs] using h
  have hos : (s.future_order.val[s.next_future.val]'h).val < (simStS tn s).objs.size := by simpa using ho
  have hO := sim_stS_obj tn s _ hos
  have h1' : ¬ t < (ostateS (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho)).lifetimeStart := h1
  have h2' : ¬ (ostateS (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho)).lifetimeEnd ≤ t := h2
  unfold s8WG
  simp only [show (m + 1 > 0) = True by simp, ite_true, simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind,
    dif_pos h', s8_WG_fo tn s h h', simS_ostate _ _ _ hos, hO, h1', ite_false, simM_modify, s8_nf_stS tn s i3 hi3,
    h2', simM_pure, Nat.add_sub_cancel]


theorem s8_FB_zero (c : sim.state.Ctx) (t : float.F64) (s : sim.state.St) (fuel : Usize) (stop : Bool)
    (h : fuel.val = 0) : s8FB c t s fuel stop = ok (.done (.Ok (), s)) := by
  have : ¬ fuel > 0#usize := by
    show ¬ (0#usize : Usize).val < fuel.val; simp [h]
  simp only [s8FB, sim.step.lifetime_future_update_loop.body, this, ite_false]

theorem s8_FB_stop (c : sim.state.Ctx) (t : float.F64) (s : sim.state.St) (fuel : Usize) :
    s8FB c t s fuel true = ok (.done (.Ok (), s)) := by
  by_cases h : fuel > 0#usize <;> simp only [s8FB, sim.step.lifetime_future_update_loop.body, h, ite_true, ite_false]

theorem s8_FL_stop (c : sim.state.Ctx) (t : float.F64) (s : sim.state.St) (fuel : Usize) :
    s8FL c s t fuel true = ok (.Ok (), s) := by
  rw [s8_FL_unfold, s8_FB_stop]; simp only [bind_ok]

/-- the state after the later-update loop marks a skipped object past -/
def s8SP (s : sim.state.St) (x : Usize) (o : sim.state.OState) (i3 : Usize) : sim.state.St :=
  { s with objs := s.objs.set x { o with life := .Past }, next_future := i3 }

-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (fuel loop s8WG, generic over the became_alive contract; parent sim.step.lifetime_update_refines)
theorem sim.step.lifetime_future_update_loop_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (t : F64)
    (B : sim.state.St → Prop)
    (hfo : ∀ s, B s → ∀ x ∈ s.future_order.val, x.val < s.objs.val.length)
    (hP : ∀ s (h : s.next_future.val < s.future_order.val.length)
      (ho : (s.future_order.val[s.next_future.val]'h).val < s.objs.val.length), B s →
      ¬ t < (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_start →
      (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_end ≤ t →
      ∀ i3 : Usize, i3.val = s.next_future.val + 1 →
      B (s8SP s (s.future_order.val[s.next_future.val]'h) (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho) i3))
    (hA : ∀ s (h : s.next_future.val < s.future_order.val.length)
      (ho : (s.future_order.val[s.next_future.val]'h).val < s.objs.val.length), B s →
      ¬ t < (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_start →
      ¬ (s.objs.val[(s.future_order.val[s.next_future.val]'h).val]'ho).lifetime_end ≤ t →
      ∀ i3 : Usize, i3.val = s.next_future.val + 1 →
      ∃ res s', sim.step.became_alive c { s with next_future := i3 } (s.future_order.val[s.next_future.val]'h) =
          ok (res, s') ∧
        simRelM tn s' res (OsuModel.Sim.Sim.becameAlive (s.future_order.val[s.next_future.val]'h).val
          (simCtxS tn fo c) (simStS tn { s with next_future := i3 })) ∧
        (res = .Ok () → B s')) :
    ∀ m (fuel : Usize) (s : sim.state.St), fuel.val = m → B s →
      ∃ res s', s8FL c s t fuel false = ok (res, s') ∧
        (res = .Ok () → ∃ r : Nat, forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk fuel.val (s8WG t) (simCtxS tn fo c)
          (simStS tn s) = .ok (r, simStS tn s') ∧ B s') ∧
        (∀ e, res = .Err e → ∃ msg, forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk fuel.val (s8WG t) (simCtxS tn fo c)
          (simStS tn s) = .error msg) := by
  intro m
  induction m with
  | zero =>
    intro fuel s hf hB
    refine ⟨.Ok (), s, by rw [s8_FL_unfold, s8_FB_zero c t s fuel false hf]; simp only [bind_ok],
      fun _ => ⟨0, ?_, hB⟩, fun e h => by cases h⟩
    rw [s8_simm_loop_unfold, hf]
    simp only [simM_bind, s8_WG_zero, Except.bind, simM_pure]
  | succ m ih =>
    intro fuel s hf hB
    have hpos : fuel > 0#usize := by show (0#usize : Usize).val < fuel.val; simp [hf]
    obtain ⟨f1, hf1, hf1v⟩ : ∃ z, fuel - 1#usize = ok z ∧ z.val = m := by
      obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp [hf]))
      exact ⟨z, hz, by simp at hv; omega⟩
    by_cases hnf : s.next_future.val < s.future_order.val.length
    · have hnl : s.next_future < alloc.vec.Vec.len s.future_order := by rw [vec_lt_len_iff]; exact hnf
      have ho := hfo s hB _ (List.getElem_mem hnf)
      obtain ⟨i3, hi3, hi3v⟩ := usize_add_one s.next_future (by have := s.future_order.property; omega)
      by_cases h1 : t < (s.objs.val[(s.future_order.val[s.next_future.val]'hnf).val]'ho).lifetime_start
      · have hb : s8FB c t s fuel false = ok (.cont (s, f1, true)) := by
          simp only [s8FB, sim.step.lifetime_future_update_loop.body, hpos, ite_true, Bool.false_eq_true,
            ite_false, hf1, bind_ok, hnl, vec_index_eq _ _ hnf, vec_index_eq _ _ ho, float.F64.lt, h1, decide_true]
        refine ⟨.Ok (), s, by rw [s8_FL_unfold, hb]; simp only [bind_ok]; exact s8_FL_stop c t s f1,
          fun _ => ⟨m, ?_, hB⟩, fun e h => by cases h⟩
        rw [s8_simm_loop_unfold, hf]; simp only [simM_bind]
        simp only [s8_WG_brk tn t _ s m hnf ho h1, Except.bind, simM_pure]
      · by_cases h2 : (s.objs.val[(s.future_order.val[s.next_future.val]'hnf).val]'ho).lifetime_end ≤ t
        · have hb : s8FB c t s fuel false = ok (.cont (s8SP s (s.future_order.val[s.next_future.val]'hnf) (s.objs.val[(s.future_order.val[s.next_future.val]'hnf).val]'ho) i3, f1, false)) := by
            simp only [s8FB, sim.step.lifetime_future_update_loop.body, hpos, ite_true, Bool.false_eq_true,
              ite_false, hf1, bind_ok, hnl, vec_index_eq _ _ hnf, vec_index_eq _ _ ho, float.F64.lt, h1, decide_false,
              hi3, float.F64.le, h2, decide_true, vec_index_mut_eq _ _ ho]
            rfl
          obtain ⟨res, s', e', r1, r2⟩ := ih f1 _ hf1v (hP s hnf ho hB h1 h2 i3 hi3v)
          refine ⟨res, s', by rw [s8_FL_unfold, hb]; simp only [bind_ok]; exact e', fun h => ?_, fun e h => ?_⟩
          · obtain ⟨r, er, hB'⟩ := r1 h
            refine ⟨r, ?_, hB'⟩
            rw [s8_simm_loop_unfold, hf]; simp only [simM_bind]
            simp only [s8_WG_past tn t _ s m hnf ho h1 h2 i3 hi3v, Except.bind]
            rw [← hf1v]; exact er
          · obtain ⟨msg, em⟩ := r2 e h
            refine ⟨msg, ?_⟩
            rw [s8_simm_loop_unfold, hf]; simp only [simM_bind]
            simp only [s8_WG_past tn t _ s m hnf ho h1 h2 i3 hi3v, Except.bind]
            rw [← hf1v]; exact em
        · obtain ⟨res, s1, e1, rr, i1⟩ := hA s hnf ho hB h1 h2 i3 hi3v
          have hS := s8_WG_alive tn t (simCtxS tn fo c) s m hnf ho h1 h2 i3 hi3v
          have hb0 : s8FB c t s fuel false = (do
              let (r, s1) ← sim.step.became_alive c { s with next_future := i3 } (s.future_order.val[s.next_future.val]'hnf)
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue _ => ok (ControlFlow.cont (s1, f1, false))
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame sim.err.SimErr) residual
                ok (ControlFlow.done (r1, s1))) := by
            simp only [s8FB, sim.step.lifetime_future_update_loop.body, hpos, ite_true, Bool.false_eq_true,
              ite_false, hf1, bind_ok, hnl, vec_index_eq _ _ hnf, vec_index_eq _ _ ho, float.F64.lt, h1, decide_false,
              hi3, float.F64.le, h2]
            rfl
          cases res with
          | Err e =>
            refine ⟨.Err e, s1, ?_, ?_, ?_⟩
            rotate_left 1
            · intro h; cases h
            · intro e' _
              obtain ⟨mm, hmm⟩ := rr
              refine ⟨mm, ?_⟩
              rw [s8_simm_loop_unfold, hf]; simp only [simM_bind, hS, hmm, Except.bind]
            · rw [s8_FL_unfold, hb0, e1]
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
            cases u
            have hb : s8FB c t s fuel false = ok (.cont (s1, f1, false)) := by
              rw [hb0, e1]; simp [core.result.Result.Insts.CoreOpsTry.branch]
            have rr' : OsuModel.Sim.Sim.becameAlive (s.future_order.val[s.next_future.val]'hnf).val (simCtxS tn fo c)
                (simStS tn { s with next_future := i3 }) = .ok ((), simStS tn s1) := rr
            obtain ⟨res, s', e', r1, r2⟩ := ih f1 s1 hf1v (i1 rfl)
            refine ⟨res, s', by rw [s8_FL_unfold, hb]; simp only [bind_ok]; exact e', fun h => ?_, fun e h => ?_⟩
            · obtain ⟨r, er, hB'⟩ := r1 h
              refine ⟨r, ?_, hB'⟩
              rw [s8_simm_loop_unfold, hf]; simp only [simM_bind, hS, rr', Except.bind]
              rw [← hf1v]; exact er
            · obtain ⟨msg, em⟩ := r2 e h
              refine ⟨msg, ?_⟩
              rw [s8_simm_loop_unfold, hf]; simp only [simM_bind, hS, rr', Except.bind]
              rw [← hf1v]; exact em
    · have hnl : ¬ s.next_future < alloc.vec.Vec.len s.future_order := by rw [vec_lt_len_iff]; exact hnf
      have hb : s8FB c t s fuel false = ok (.cont (s, f1, true)) := by
        simp only [s8FB, sim.step.lifetime_future_update_loop.body, hpos, ite_true, Bool.false_eq_true,
          ite_false, hf1, bind_ok, hnl]
      refine ⟨.Ok (), s, by rw [s8_FL_unfold, hb]; simp only [bind_ok]; exact s8_FL_stop c t s f1,
        fun _ => ⟨m, ?_, hB⟩, fun e h => by cases h⟩
      rw [s8_simm_loop_unfold, hf]; simp only [simM_bind]
      simp only [s8_WG_end tn t _ s m hnf, Except.bind, simM_pure]


theorem s8_clone_usize (v : alloc.vec.Vec Usize) : alloc.vec.CloneVec.clone core.clone.CloneUsize v = ok v := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := core.clone.CloneUsize.clone) (s := v.slice)
    (by intro x _; rfl))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp

theorem s8_tail_spec (tn : Nat → String) (C : OsuModel.Sim.Ctx) (t : F64) (s : sim.state.St) :
    s8LUTail t C (simStS tn s) =
      (do forIn ((s.active.val.drop 0).map (fun x : Usize => x.val)) PUnit.unit (s8DG t); s8LUFilt :
        OsuModel.Sim.SimM Unit) C (simStS tn s) := by
  have hA : (simStS tn s).active = (s.active.val.map (fun x : Usize => x.val)).toArray := by simp [simStS, abs]
  unfold s8LUTail
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind, hA, List.forIn_toArray, List.drop_zero]

-- FRAGMENT-OF: OsuModel.Sim.Sim.lifetimeUpdate (generic over the per-phase contracts; instantiated by sim.step.lifetime_update_refines)
/-- `lifetime_update` refines `Sim.lifetimeUpdate`, generic over the per-phase contracts: `A` (first-update scan),
`B` (later-update fuel loop) and `D snap` (newly-dead scan over the snapshot `snap`). -/
theorem s8_lu_gen (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (hcl : c.pb.objects.val.length < Usize.max)
    (A : Nat → sim.state.St → List Usize → Prop)
    (hlen : ∀ i s F, A i s F → s.objs.val.length = c.pb.objects.val.length)
    (hF : ∀ (i : Usize) s' F (ho : i.val < s'.objs.val.length), A i.val s' F →
      s.t < (s'.objs.val[i.val]'ho).lifetime_start → A (i.val + 1) s' (F ++ [i]))
    (hPa : ∀ (i : Usize) s' F (ho : i.val < s'.objs.val.length), A i.val s' F →
      ¬ s.t < (s'.objs.val[i.val]'ho).lifetime_start → (s'.objs.val[i.val]'ho).lifetime_end ≤ s.t →
      A (i.val + 1) { s' with objs := s'.objs.set i { (s'.objs.val[i.val]'ho) with life := .Past } } F)
    (hAa : ∀ (i : Usize) s' F (ho : i.val < s'.objs.val.length), A i.val s' F →
      ¬ s.t < (s'.objs.val[i.val]'ho).lifetime_start → ¬ (s'.objs.val[i.val]'ho).lifetime_end ≤ s.t →
      ∃ res s'', sim.step.became_alive c s' i = ok (res, s'') ∧
        simRelM tn s'' res (OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn s')) ∧
        (res = .Ok () → A (i.val + 1) s'' F))
    (hA0 : s.first_lifetime_update = true → A 0 { s with first_lifetime_update := false } [])
    (B : sim.state.St → Prop)
    (hfo : ∀ s, B s → ∀ x ∈ s.future_order.val, x.val < s.objs.val.length)
    (hPb : ∀ s' (h : s'.next_future.val < s'.future_order.val.length)
      (ho : (s'.future_order.val[s'.next_future.val]'h).val < s'.objs.val.length), B s' →
      ¬ s.t < (s'.objs.val[(s'.future_order.val[s'.next_future.val]'h).val]'ho).lifetime_start →
      (s'.objs.val[(s'.future_order.val[s'.next_future.val]'h).val]'ho).lifetime_end ≤ s.t →
      ∀ i3 : Usize, i3.val = s'.next_future.val + 1 →
      B (s8SP s' (s'.future_order.val[s'.next_future.val]'h) (s'.objs.val[(s'.future_order.val[s'.next_future.val]'h).val]'ho) i3))
    (hAb : ∀ s' (h : s'.next_future.val < s'.future_order.val.length)
      (ho : (s'.future_order.val[s'.next_future.val]'h).val < s'.objs.val.length), B s' →
      ¬ s.t < (s'.objs.val[(s'.future_order.val[s'.next_future.val]'h).val]'ho).lifetime_start →
      ¬ (s'.objs.val[(s'.future_order.val[s'.next_future.val]'h).val]'ho).lifetime_end ≤ s.t →
      ∀ i3 : Usize, i3.val = s'.next_future.val + 1 →
      ∃ res s'', sim.step.became_alive c { s' with next_future := i3 } (s'.future_order.val[s'.next_future.val]'h) =
          ok (res, s'') ∧
        simRelM tn s'' res (OsuModel.Sim.Sim.becameAlive (s'.future_order.val[s'.next_future.val]'h).val
          (simCtxS tn fo c) (simStS tn { s' with next_future := i3 })) ∧
        (res = .Ok () → B s''))
    (hB0 : s.first_lifetime_update = false → B s)
    (D : alloc.vec.Vec Usize → Nat → sim.state.St → Prop)
    (hb : ∀ snap k s, D snap k s → ∀ hk : k < snap.val.length, (snap.val[k]'hk).val < s.objs.val.length)
    (hd : ∀ snap k s' (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < s'.objs.val.length), D snap k s' →
      ((s'.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ s.t ∨ s.t < (s'.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      ∃ res s'', sim.step.became_dead c s' (snap.val[k]'hk) = ok (res, s'') ∧
        simRelM tn s'' res (OsuModel.Sim.Sim.becameDead (snap.val[k]'hk).val (simCtxS tn fo c) (simStS tn s')) ∧
        (res = .Ok () → D snap (k + 1) s''))
    (hs : ∀ snap k s' (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < s'.objs.val.length), D snap k s' →
      ¬ ((s'.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ s.t ∨ s.t < (s'.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      D snap (k + 1) s')
    (he : ∀ snap s', D snap snap.val.length s' → ∀ x ∈ s'.active.val, x.val < s'.objs.val.length)
    (hAD : ∀ sE FUT sorted, A c.pb.objects.val.length sE FUT.val →
      sim.step.sort_by_lifetime_start sE (alloc.vec.Vec.deref FUT) = ok sorted →
      D sE.active 0 { sE with next_future := 0#usize, future_order := sorted })
    (hBD : ∀ s', B s' → D s'.active 0 s') :
    ∃ res s', sim.step.lifetime_update c s = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.lifetimeUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → ∃ snap sE KF, D snap snap.val.length sE ∧ s' = { sE with active := KF } ∧
        KF.val = sE.active.val.filter (s8Alive sE)) := by
  have hsz : (simCtxS tn fo c).pb.objects.size = c.pb.objects.val.length := by simp [simCtxS, playableS, abs]
  rw [s8_lu_splitS]
  unfold s8LUS
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, OsuModel.Sim.Sim.ctx, simM_read, Except.bind]
  have hfS : (simStS tn s).firstLifetimeUpdate = s.first_lifetime_update := rfl
  cases hf : s.first_lifetime_update with
  | true =>
    obtain ⟨res1, s1, e1, r1, r2, r3⟩ := sim.step.lifetime_first_update_loop_refines tn fo c s.t A hcl hlen hF hPa hAa
      c.pb.objects.val.length 0#usize { s with first_lifetime_update := false } (alloc.vec.Vec.new Usize)
      (by simp) (by simp) (hA0 hf) (by simp) (by simp)
    have hsp0 : ∀ K, s8LUFirstK (simStS tn s).t (simCtxS tn fo c) K (simCtxS tn fo c) (simStS tn s) =
        (forIn (List.range' (0#usize : Usize).val c.pb.objects.val.length)
          (((alloc.vec.Vec.new Usize).val.map (·.val)).toArray) (s8FG s.t) >>= s8FirstRest K)
          (simCtxS tn fo c) (simStS tn { s with first_lifetime_update := false }) := by
      intro K
      rw [s8_first_eq]
      have h1 : [:c.pb.objects.val.length].size = c.pb.objects.val.length := by simp [Std.Legacy.Range.size]
      have h2 : ((alloc.vec.Vec.new Usize).val.map (·.val)).toArray = (#[] : Array Nat) := by simp
      simp only [simM_bind, simM_modify, Except.bind, Std.Legacy.Range.forIn_eq_forIn_range', hsz, h1, h2]
      rfl
    simp only [hfS, hf, ite_true]
    rw [hsp0]
    cases res1 with
    | Err e =>
      refine ⟨.Err e, s1, ?_, ?_, fun h => by cases h⟩
      · simp only [sim.step.lifetime_update, hf, ite_true, sim.step.lifetime_first_update, e1, bind_ok]
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · exact r2 _ e rfl
    | Ok u =>
      cases u
      obtain ⟨sE, FUT, sorted, hAE, hsort, hs1⟩ := r3 rfl
      have hD0 : D s1.active 0 s1 := by rw [hs1]; exact hAD sE FUT sorted hAE hsort
      obtain ⟨res, s', e', r', i'⟩ := sim.step.lifetime_update_loop0_refines tn fo c s.t s1.active (D s1.active) (hb _) (hd _) (hs _) (he _)
        _ 0#usize s1 rfl (by simp) hD0
      refine ⟨res, s', ?_, ?_, fun h => ⟨s1.active, i' h⟩⟩
      · simp only [sim.step.lifetime_update, hf, ite_true, sim.step.lifetime_first_update, e1, bind_ok]
        simp [core.result.Result.Insts.CoreOpsTry.branch, s8_clone_usize, e']
      · rw [r1 _ rfl, s8_tail_spec]; exact r'
  | false =>
    obtain ⟨fu, hfu, hfuv⟩ := usize_add_one (alloc.vec.Vec.len c.pb.objects) (by simp; omega)
    obtain ⟨res1, s1, e1, r1, r2⟩ := sim.step.lifetime_future_update_loop_refines tn fo c s.t B hfo hPb hAb fu.val fu s rfl (hB0 hf)
    have hsp0 : ∀ K, s8LUFutK (simStS tn s).t (simCtxS tn fo c) K (simCtxS tn fo c) (simStS tn s) =
        ((forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk fu.val (s8WG s.t)) >>= fun _ => K ())
          (simCtxS tn fo c) (simStS tn s) := by
      intro K
      have : (simCtxS tn fo c).pb.objects.size + 1 = fu.val := by rw [hsz, hfuv]; simp
      unfold s8LUFutK; rw [this]; rfl
    simp only [hfS, hf, Bool.false_eq_true, ite_false]
    rw [hsp0]
    cases res1 with
    | Err e =>
      refine ⟨.Err e, s1, ?_, ?_, fun h => by cases h⟩
      · simp only [sim.step.lifetime_update, hf, Bool.false_eq_true, ite_false, sim.step.lifetime_future_update,
          hfu, bind_ok]
        have e1' := e1; simp only [s8FL] at e1'
        rw [e1']
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · obtain ⟨msg, hm⟩ := r2 e rfl
        exact ⟨msg, by simp only [simM_bind, hm, Except.bind]⟩
    | Ok u =>
      cases u
      obtain ⟨r, er, hB1⟩ := r1 rfl
      obtain ⟨res, s', e', r', i'⟩ := sim.step.lifetime_update_loop1_refines tn fo c s.t s1.active (D s1.active) (hb _) (hd _) (hs _) (he _)
        _ 0#usize s1 rfl (by simp) (hBD s1 hB1)
      refine ⟨res, s', ?_, ?_, fun h => ⟨s1.active, i' h⟩⟩
      · simp only [sim.step.lifetime_update, hf, Bool.false_eq_true, ite_false, sim.step.lifetime_future_update,
          hfu, bind_ok]
        have e1' := e1; simp only [s8FL] at e1'
        rw [e1']
        simp [core.result.Result.Insts.CoreOpsTry.branch, s8_clone_usize, e']
      · simp only [simM_bind, er, Except.bind]
        rw [s8_tail_spec]; exact r'

end OsuProofs
