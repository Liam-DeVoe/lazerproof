/-
sim3d (D59): Relax (`relax_update` / `relaxUpdate`) and its helpers. The spec inlines the requirements loop and the
local `changeState`; `s3d_reqS` / `s3d_csS` are verbatim copies (`s3d_relax_eq : relaxUpdate = s3d_relaxS := rfl`).
`relax_change_state` and `relax_update` are CONDITIONAL on `trigger_pressed` (sim core) via `s3d_TPOk`.
`s3d_loopStop` relates the Rust stop-flag loop to the spec `forIn` with `break`.
-/
import OsuProofs.Sim3.SD_Upd
import OsuProofs.Sim3.SB_Upd2
import OsuProofs.Sim.ReplayDiff
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

section
open OsuModel.Sim OsuModel.Sim.Sim OsuModel.Net OsuModel.Replay

/-- the local `changeState` of `Sim.relaxUpdate` (verbatim, `time` as a parameter); `s3d_relax_eq` bridges by `rfl` -/
def s3d_csS (time : F64) (down : Bool) : SimM Unit := do
    let s ← st
    if s.relaxDown == down then return
    set { s with relaxDown := down, relaxLast := time }
    if (← ctx).cfg.traceObj.isSome then
      modify fun s => { s with dbg := s.dbg.push s!"relax t={time} down={down} wasLeft={s.relaxWasLeft}" }
    if down then
      triggerPressed (if s.relaxWasLeft then .left else .right)
      modify fun s => { s with relaxWasLeft := !s.relaxWasLeft }
    else
      triggerReleased (if s.relaxWasLeft then .right else .left)

/-- `Sim.relaxUpdate` with its local `changeState` named (`s3d_csS`) -/
def s3d_relaxS : SimM Unit := do
  let c ← ctx
  if c.cfg.lazerReplay then return
  let time := (← st).t
  let mut requiresHold := false
  let mut requiresHit := false
  for i in ← aliveObjects do
    let o := (← topObj i)
    -- `RELAX_LENIENCY = 12` (float)
    if time < o.h.start - 12 then break
    let os ← ostate i
    if (← isHitRef (i, -1)) || ((o.h.kind == .slider || o.h.kind == .spinner) && o.h.endTime < time) then continue
    -- handleHitCircle: `HitArea.IsHovered && HitWindows.CanBeHit(time - StartTime)`
    let hitCircle (h : HObj) : Bool := match h.hitWindows with
      | some hw => os.hovered && hw.canBeHit (time - h.start)
      | none => false
    match o.h.kind with
    | .circle => requiresHit := requiresHit || hitCircle o.h
    | .slider =>
      let hj := (← headIdxOf i)
      if !(← isHitRef (i, hj)) then requiresHit := requiresHit || hitCircle (← nestedOf o hj)
      requiresHold := requiresHold || (← mouseInFollowArea i (← instOf os.inst).drawableTracking)
    | .spinner =>
      requiresHold := requiresHold || (match o.spinner with | some sp => sp.spinsRequired > 0 | none => false)
    | _ => pure ()
  let changeState (down : Bool) : SimM Unit := s3d_csS time down
  if requiresHit then
    changeState false
    changeState true
  if requiresHold then changeState true
  else if (← st).relaxDown && 50 < time - (← st).relaxLast then changeState false

theorem s3d_relax_eq : OsuModel.Sim.Sim.relaxUpdate = s3d_relaxS := rfl
end
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `trigger_released` only replaces `pressed` (`sim.step.trigger_released_refines` with the state made explicit) -/
theorem s3d_tr (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (a : replay.frames.Action) (hp : s.pressed.len.val ≤ 3) :
    ∃ p : replay.frames.ActList, sim.step.trigger_released s a = ok { s with pressed := p } ∧ p.len.val ≤ 3 ∧
      OsuModel.Sim.Sim.triggerReleased (abs a) (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn { s with pressed := p }) ∧ (actListS p).Sublist (actListS s.pressed) := by
  obtain ⟨s', h1, h2, h3⟩ := sim.step.trigger_released_refines tn fo c s a hp
  obtain ⟨r, hr, -, hf⟩ := replay.frames.act_remove_refines s.pressed a hp
  have e : s' = { s with pressed := r } :=
    Result.ok_injective (h1.symm.trans (by simp [sim.step.trigger_released, hr]))
  subst e
  have hf' : actListS r = (actListS s.pressed).filter (· != abs a) := hf
  exact ⟨r, h1, h2, h3, by rw [hf']; exact List.filter_sublist⟩

/-- `trigger_released` only shrinks `pressed` (filter): frame and `Nodup` preservation (for `input_phase`) -/
theorem s3d_trigger_released_frame (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (a : replay.frames.Action) (hp : s.pressed.len.val ≤ 3) :
    ∃ p : replay.frames.ActList, sim.step.trigger_released s a = ok { s with pressed := p } ∧ p.len.val ≤ 3 ∧
      OsuModel.Sim.Sim.triggerReleased (abs a) (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn { s with pressed := p }) ∧ (actListS p).Sublist (actListS s.pressed) ∧
      ((actListS s.pressed).Nodup → (actListS p).Nodup) := by
  obtain ⟨p, h1, h2, h3, h4⟩ := s3d_tr tn fo c s a hp
  exact ⟨p, h1, h2, h3, h4, fun h => List.Nodup.sublist h4 h⟩

/-- the `trigger_pressed` refinement that `relax_update` needs, under a caller invariant `I` (CONDITIONAL input:
`trigger_pressed` belongs to the sim core) -/
def s3d_TPOk (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : sim.state.St → Prop) : Prop :=
  ∀ s a, I s → ∃ r s', sim.step.trigger_pressed c s a = ok (r, s') ∧
    s3b_rrel (fun _ => ()) (simStS tn s') r
      (OsuModel.Sim.Sim.triggerPressed (abs a) (simCtxS tn fo c) (simStS tn s)) ∧ (r = .Ok () → I s')

/-- the closure that `relax_change_state` needs of the caller invariant: the relax fields may change and `pressed`
may shrink to a sublist (`trigger_released` filters it) -/
def s3d_RelaxCl (I : sim.state.St → Prop) : Prop :=
  (∀ s, I s → s.pressed.len.val ≤ 3) ∧
  ∀ s d l w (p : replay.frames.ActList), I s → p.len.val ≤ 3 → (actListS p).Sublist (actListS s.pressed) →
    I { s with relax_down := d, relax_last := l, relax_was_left := w, pressed := p }

@[simp] theorem s3d_st_relaxDown (tn) (s : sim.state.St) : (simStS tn s).relaxDown = s.relax_down := rfl
@[simp] theorem s3d_st_relaxWasLeft (tn) (s : sim.state.St) : (simStS tn s).relaxWasLeft = s.relax_was_left := rfl
@[simp] theorem s3d_st_relaxLast (tn) (s : sim.state.St) : (simStS tn s).relaxLast = s.relax_last := rfl
@[simp] theorem s3d_ctx_traceObj (tn fo) (c : sim.state.Ctx) : (simCtxS tn fo c).cfg.traceObj = none := rfl

theorem s3d_stS_relax (tn) (s : sim.state.St) (d : Bool) (t : F64) (S : OsuModel.Sim.St) (h : S = simStS tn s) :
    ({ S with relaxDown := d, relaxLast := t } : OsuModel.Sim.St) =
      simStS tn { s with relax_down := d, relax_last := t } := by subst h; rfl

theorem s3d_stS_wasLeft (tn) (s : sim.state.St) (S : OsuModel.Sim.St) (h : S = simStS tn s) :
    ({ S with relaxWasLeft := !S.relaxWasLeft } : OsuModel.Sim.St) =
      simStS tn { s with relax_was_left := !s.relax_was_left } := by subst h; rfl

theorem s3d_csS_noop (t : F64) (d : Bool) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (h : S.relaxDown = d) :
    s3d_csS t d C S = .ok ((), S) := by
  unfold s3d_csS
  simp only [OsuModel.Sim.Sim.st, simM_bind, simM_get, Except.bind]
  rw [if_pos (by simp [h])]; rfl

theorem s3d_csS_rel (t : F64) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (h : S.relaxDown = true)
    (hc : C.cfg.traceObj = none) :
    s3d_csS t false C S = OsuModel.Sim.Sim.triggerReleased (if S.relaxWasLeft then .right else .left) C
      { S with relaxDown := false, relaxLast := t } := by
  unfold s3d_csS
  simp only [OsuModel.Sim.Sim.st, OsuModel.Sim.Sim.ctx, simM_bind, simM_get, Except.bind]
  rw [if_neg (by simp [h])]
  simp only [simM_bind, simM_set, simM_read, Except.bind, hc, Option.isSome_none]
  rfl

theorem s3d_csS_press (t : F64) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (h : S.relaxDown = false)
    (hc : C.cfg.traceObj = none) :
    s3d_csS t true C S = (do
        OsuModel.Sim.Sim.triggerPressed (if S.relaxWasLeft then .left else .right)
        modify fun s => { s with relaxWasLeft := !s.relaxWasLeft } : OsuModel.Sim.SimM Unit) C
      { S with relaxDown := true, relaxLast := t } := by
  unfold s3d_csS
  simp only [OsuModel.Sim.Sim.st, OsuModel.Sim.Sim.ctx, simM_bind, simM_get, Except.bind]
  rw [if_neg (by simp [h])]
  simp only [simM_bind, simM_set, simM_read, Except.bind, hc, Option.isSome_none]
  rfl

theorem s3d_rcs (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (down : Bool)
    (time : F64) (I : sim.state.St → Prop) (hI : I s) (hcl : s3d_RelaxCl I) (htp : s3d_TPOk tn fo c I) :
    ∃ r s', sim.step.relax_change_state c s down time = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (s3d_csS time down (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → I s') := by
  have hI1 : I { s with relax_down := down, relax_last := time } :=
    hcl.2 s down time s.relax_was_left s.pressed hI (hcl.1 s hI) (List.Sublist.refl _)
  have hp1 := hcl.1 _ hI1
  by_cases hd : s.relax_down = down
  · refine ⟨.Ok (), s, by simp [sim.step.relax_change_state, hd], ?_, fun _ => hI⟩
    rw [s3d_csS_noop _ _ _ _ hd]; rfl
  unfold sim.step.relax_change_state
  simp only [hd, if_false]
  cases down
  · -- release
    have hrd : s.relax_down = true := by simpa using hd
    rw [s3d_csS_rel _ _ _ hrd rfl, s3d_stS_relax tn s false time (simStS tn s) rfl]
    by_cases hw : s.relax_was_left = true
    · obtain ⟨p, hr, hpl, he, hsl⟩ := s3d_tr tn fo c { s with relax_down := false, relax_last := time } .Right hp1
      refine ⟨.Ok (), { ({ s with relax_down := false, relax_last := time } : sim.state.St) with pressed := p },
        ?_, ?_, fun _ => hcl.2 s false time s.relax_was_left p hI hpl hsl⟩
      · simp only [Bool.false_eq_true, if_false]; rw [if_pos hw, hr]; simp only [bind_ok]
      · rw [if_pos (show (simStS tn s).relaxWasLeft = true from hw)]; exact he
    · obtain ⟨p, hr, hpl, he, hsl⟩ := s3d_tr tn fo c { s with relax_down := false, relax_last := time } .Left hp1
      refine ⟨.Ok (), { ({ s with relax_down := false, relax_last := time } : sim.state.St) with pressed := p },
        ?_, ?_, fun _ => hcl.2 s false time s.relax_was_left p hI hpl hsl⟩
      · simp only [Bool.false_eq_true, if_false]; rw [if_neg hw, hr]; simp only [bind_ok]
      · rw [if_neg (show ¬ (simStS tn s).relaxWasLeft = true from hw)]; exact he
  · -- press
    have hrd : s.relax_down = false := by simpa using hd
    rw [s3d_csS_press _ _ _ hrd rfl, s3d_stS_relax tn s true time (simStS tn s) rfl]
    by_cases hw : s.relax_was_left = true
    · obtain ⟨r, s2, hr, er, hI2⟩ := htp { s with relax_down := true, relax_last := time } .Left hI1
      rw [if_pos (show (simStS tn s).relaxWasLeft = true from hw)]
      simp only [if_pos hw, if_true]
      rw [hr]
      simp only [bind_ok]
      rcases r with _ | e
      · have er' : OsuModel.Sim.Sim.triggerPressed (abs replay.frames.Action.Left) (simCtxS tn fo c)
            (simStS tn { s with relax_down := true, relax_last := time }) = .ok ((), simStS tn s2) := er
        have hI2' := hI2 rfl
        refine ⟨.Ok (), { s2 with relax_was_left := !s2.relax_was_left }, ?_, ?_, fun _ =>
          hcl.2 s2 s2.relax_down s2.relax_last (!s2.relax_was_left) s2.pressed hI2' (hcl.1 s2 hI2') (List.Sublist.refl _)⟩
        · simp [core.result.Result.Insts.CoreOpsTry.branch]
        · simp only [simM_bind]
          rw [show OsuModel.Replay.Action.left = abs replay.frames.Action.Left from rfl, er']
          simp only [Except.bind, simM_modify, s3b_rrel]
          rw [s3d_stS_wasLeft tn s2 (simStS tn s2) rfl]
      · obtain ⟨m, hm⟩ := er
        refine ⟨.Err e, s2, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · simp only [simM_bind]
          rw [show OsuModel.Replay.Action.left = abs replay.frames.Action.Left from rfl, hm]; rfl
    · obtain ⟨r, s2, hr, er, hI2⟩ := htp { s with relax_down := true, relax_last := time } .Right hI1
      rw [if_neg (show ¬ (simStS tn s).relaxWasLeft = true from hw)]
      simp only [if_neg hw, if_true]
      rw [hr]
      simp only [bind_ok]
      rcases r with _ | e
      · have er' : OsuModel.Sim.Sim.triggerPressed (abs replay.frames.Action.Right) (simCtxS tn fo c)
            (simStS tn { s with relax_down := true, relax_last := time }) = .ok ((), simStS tn s2) := er
        have hI2' := hI2 rfl
        refine ⟨.Ok (), { s2 with relax_was_left := !s2.relax_was_left }, ?_, ?_, fun _ =>
          hcl.2 s2 s2.relax_down s2.relax_last (!s2.relax_was_left) s2.pressed hI2' (hcl.1 s2 hI2') (List.Sublist.refl _)⟩
        · simp [core.result.Result.Insts.CoreOpsTry.branch]
        · simp only [simM_bind]
          rw [show OsuModel.Replay.Action.right = abs replay.frames.Action.Right from rfl, er']
          simp only [Except.bind, simM_modify, s3b_rrel]
          rw [s3d_stS_wasLeft tn s2 (simStS tn s2) rfl]
      · obtain ⟨m, hm⟩ := er
        refine ⟨.Err e, s2, ?_, ⟨m, ?_⟩, fun h => by cases h⟩
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · simp only [simM_bind]
          rw [show OsuModel.Replay.Action.right = abs replay.frames.Action.Right from rfl, hm]; rfl
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net
theorem s3d_sortL_mem {α} (lt : α → α → Bool) (xs : List α) (y : α) (hy : y ∈ simSortL lt xs) : y ∈ xs := by
  unfold simSortL at hy
  suffices h : ∀ (acc : List α), y ∈ xs.foldl (fun out x => out.insertIdx (simInsPos lt out x out.length) x) acc →
      y ∈ acc ∨ y ∈ xs by
    rcases h [] hy with h | h
    · simp at h
    · exact h
  clear hy
  induction xs with
  | nil => intro acc h; exact Or.inl h
  | cons x t ih =>
    intro acc h
    rw [List.foldl_cons] at h
    rcases ih _ h with h | h
    · rw [List.mem_insertIdx (sim_simInsPos_le lt acc x acc.length)] at h
      rcases h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self)
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem s3d_alive_mem (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (hinv : SimInv c s) (v : alloc.vec.Vec Usize)
    (hv : OsuModel.Sim.Sim.aliveObjects (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s)) :
    ∀ x ∈ v.val, x.val < c.pb.objects.val.length := by
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hinv.dict_in _ ha a rfl
  rw [simS_aliveObjects _ _ hS] at hv
  simp only [Except.ok.injEq, Prod.mk.injEq] at hv
  intro x hx
  have h1 : x.val ∈ (abs v : Array Nat).toList := by simp [abs]; exact ⟨x, hx, rfl⟩
  rw [← hv.1] at h1
  simp only [List.toList_toArray] at h1
  have h2 := s3d_sortL_mem _ _ _ h1
  have h3 := hS _ (by simpa using h2)
  simpa [simCtxS, playableS, abs] using h3

/-- the alive list enumerates alive-dictionary entries -/
theorem s3d_alive_dict (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (hinv : SimInv c s) (v : alloc.vec.Vec Usize)
    (hv : OsuModel.Sim.Sim.aliveObjects (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s)) :
    ∀ x ∈ v.val, ∃ y, some y ∈ s.dict_slots.val ∧ y.val = x.val := by
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hinv.dict_in _ ha a rfl
  rw [simS_aliveObjects _ _ hS] at hv
  simp only [Except.ok.injEq, Prod.mk.injEq] at hv
  intro x hx
  have h1 : x.val ∈ (abs v : Array Nat).toList := by simp [abs]; exact ⟨x, hx, rfl⟩
  rw [← hv.1] at h1
  simp only [List.toList_toArray] at h1
  have h2 := s3d_sortL_mem _ _ _ h1
  simp [simStS, abs] at h2
  obtain ⟨a, ha, hai⟩ := h2
  exact ⟨a, ha, hai⟩
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net

/-- lockstep for `relax_requirements`' loop (a `stop` flag loop: the spec `break` takes one extra Rust iteration)
against the spec `forIn` over the alive list with accumulator `(requiresHold, requiresHit)`; read-only body -/
theorem s3d_loopStop
    (B : Bool → Bool → Usize → Bool → Result (ControlFlow (Bool × Bool × Usize × Bool)
      (core.result.Result (Bool × Bool) sim.err.SimErr)))
    (l : List Nat) (F : Nat → Bool × Bool → OsuModel.Sim.SimM (ForInStep (Bool × Bool)))
    (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St)
    (hstep : ∀ (k : Usize) (hk : k.val < l.length) hold hit,
      (∃ hold' hit', ∃ k1 : Usize, k1.val = k.val + 1 ∧ B hold hit k false = ok (.cont (hold', hit', k1, false)) ∧
        F (l[k.val]'hk) (hold, hit) C S = .ok (.yield (hold', hit'), S)) ∨
      (B hold hit k false = ok (.cont (hold, hit, k, true)) ∧
        F (l[k.val]'hk) (hold, hit) C S = .ok (.done (hold, hit), S)) ∨
      (∃ e, B hold hit k false = ok (.done (.Err e)) ∧ ∃ m, F (l[k.val]'hk) (hold, hit) C S = .error m))
    (hstop : ∀ hold hit (k : Usize), k.val < l.length → B hold hit k true = ok (.done (.Ok (hit, hold))))
    (hend : ∀ hold hit (k : Usize) st, l.length ≤ k.val → B hold hit k st = ok (.done (.Ok (hit, hold)))) :
    ∀ m (k : Usize) hold hit, l.length - k.val = m → k.val ≤ l.length →
      ∃ r, loop (fun x => B x.1 x.2.1 x.2.2.1 x.2.2.2) (hold, hit, k, false) = ok r ∧
        s3aR (fun p => (p.2, p.1)) S r (forIn (l.drop k.val) (hold, hit) F C S) := by
  intro m
  induction m with
  | zero =>
    intro k hold hit hm hk
    refine ⟨.Ok (hit, hold), by rw [loop_unfold, hend hold hit k false (by omega)]; simp only [bind_ok], ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    intro k hold hit hm hk
    have hlt : k.val < l.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.forIn_cons]
    rcases hstep k hlt hold hit with ⟨hold', hit', k1, hk1, hb, hF⟩ | ⟨hb, hF⟩ | ⟨e, hb, m', hF⟩
    · obtain ⟨r, hl, hr⟩ := ih k1 hold' hit' (by omega) (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
      simp only [simM_bind, hF, Except.bind]
      rw [hk1] at hr; exact hr
    · refine ⟨.Ok (hit, hold), ?_, ?_⟩
      · rw [loop_unfold, hb]; simp only [bind_ok]
        rw [loop_unfold, hstop hold hit k hlt]; simp only [bind_ok]
      · simp only [simM_bind, hF, Except.bind]; rfl
    · refine ⟨.Err e, by rw [loop_unfold, hb]; simp only [bind_ok], m', ?_⟩
      simp only [simM_bind, hF, Except.bind]

theorem s3d_loopStop0
    (B : Bool → Bool → Usize → Bool → Result (ControlFlow (Bool × Bool × Usize × Bool)
      (core.result.Result (Bool × Bool) sim.err.SimErr)))
    (v : alloc.vec.Vec Usize) (F : Nat → Bool × Bool → OsuModel.Sim.SimM (ForInStep (Bool × Bool)))
    (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St)
    (hstep : ∀ (k : Usize) (hk : k.val < v.val.length) hold hit,
      (∃ hold' hit', ∃ k1 : Usize, k1.val = k.val + 1 ∧ B hold hit k false = ok (.cont (hold', hit', k1, false)) ∧
        F (v.val[k.val]'hk).val (hold, hit) C S = .ok (.yield (hold', hit'), S)) ∨
      (B hold hit k false = ok (.cont (hold, hit, k, true)) ∧
        F (v.val[k.val]'hk).val (hold, hit) C S = .ok (.done (hold, hit), S)) ∨
      (∃ e, B hold hit k false = ok (.done (.Err e)) ∧ ∃ m, F (v.val[k.val]'hk).val (hold, hit) C S = .error m))
    (hstop : ∀ hold hit (k : Usize), k.val < v.val.length → B hold hit k true = ok (.done (.Ok (hit, hold))))
    (hend : ∀ hold hit (k : Usize) st, v.val.length ≤ k.val → B hold hit k st = ok (.done (.Ok (hit, hold))))
    (X : Except String ((Bool × Bool) × OsuModel.Sim.St))
    (hX : forIn (m := OsuModel.Sim.SimM) (abs v : Array Nat) (false, false) F C S = X) :
    ∃ r, loop (fun x => B x.1 x.2.1 x.2.2.1 x.2.2.2) (false, false, 0#usize, false) = ok r ∧
      s3aR (fun p => (p.2, p.1)) S r X := by
  have hl : (abs v : Array Nat).toList = v.val.map (·.val) := by simp [abs]
  obtain ⟨r, h1, h2⟩ := s3d_loopStop B (v.val.map (·.val)) F C S
    (fun k hk hold hit => by
      have hk' : k.val < v.val.length := by simpa using hk
      simpa using hstep k hk' hold hit)
    (fun hold hit k hk => hstop hold hit k (by simpa using hk))
    (fun hold hit k st hk => hend hold hit k st (by simpa using hk))
    v.val.length 0#usize false false (by simp) (by simp)
  refine ⟨r, h1, ?_⟩
  rw [← hX, ← Array.forIn_toList, hl]; simpa using h2
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Net

/-- what `relax_requirements` needs of the context: head indices in range for sliders, slider paths bounded -/
def s3d_RCtx (c : sim.state.Ctx) : Prop :=
  (∀ i (hi : i < c.pb.objects.val.length), ∃ hhi : i < c.head_idx.val.length,
    (c.head_idx.val[i]'hhi).val < 2 ^ 63 ∧
    ((c.pb.objects.val[i]'hi).h.kind = .Slider → (c.head_idx.val[i]'hhi).val < (c.pb.objects.val[i]'hi).nested.val.length)) ∧
  ∀ i, s3aPathOk c i

/-- the spec's `hitCircle` at a Rust object (`relax_hit_circle`) -/
def s3d_hc (tn : Nat → String) (h : sim.playable.HObj) (hov : Bool) (t : F64) : Bool :=
  match (hobjS tn h).hitWindows with
  | some hw => hov && hw.canBeHit (t - (hobjS tn h).start)
  | none => false

theorem s3d_rhc (tn : Nat → String) (h : sim.playable.HObj) (hov : Bool) (t : F64) :
    sim.step.relax_hit_circle h hov t = ok (s3d_hc tn h hov t) := by
  unfold sim.step.relax_hit_circle s3d_hc
  cases hw : h.hit_windows <;> cases hov <;>
    simp [hobjS, hw, sim.playable.can_be_hit, OsuModel.Sim.HitWindows.canBeHit, abs, float.F64.sub, float.F64.le]

theorem s3d_kbeq (a b : OsuModel.Sim.Kind) : (a == b) = decide (a = b) := by cases a <;> cases b <;> rfl

theorem s3d_headIdxOf (tn fo) (c : sim.state.Ctx) (S : OsuModel.Sim.St) (i : Nat) (h : i < c.head_idx.val.length) :
    OsuModel.Sim.Sim.headIdxOf i (simCtxS tn fo c) S = .ok ((c.head_idx.val[i]'h).val, S) := by
  have h' : i < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using h
  simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, h', Except.bind]
  simp [simCtxS, abs]

theorem s3d_nestedOf (tn fo) (c : sim.state.Ctx) (S : OsuModel.Sim.St) (o : sim.playable.TopObj) (j : Nat)
    (h : j < o.nested.val.length) :
    OsuModel.Sim.Sim.nestedOf (topS tn o) j (simCtxS tn fo c) S = .ok (hobjS tn (o.nested.val[j]'h), S) := by
  simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, h]

set_option hygiene false in
/-- relax tail, `requiresHold` branch at state `X` -/
macro "s3d_rhold" X:term "," hX:term "," hR:term : tactic => `(tactic| (
  have hRR := $hR
  obtain ⟨r3, s3, h3, e3, i3⟩ := s3d_rcs tn fo c $X true s.t I $hX hcl htp
  have e3' : s3b_rrel (fun _ => ()) (simStS tn s3) r3
      (s3d_csS (simStS tn s).t true (simCtxS tn fo c) (simStS tn $X)) := e3
  cases r3 with
  | Ok u =>
    exact ⟨.Ok (), s3, by simp [hRR, h3, core.result.Result.Insts.CoreOpsTry.branch], e3', fun _ => i3 rfl⟩
  | Err e =>
    exact ⟨.Err e, s3, by simp [hRR, h3, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], e3', by simp⟩))

set_option hygiene false in
/-- relax tail, decay branch at state `X` -/
macro "s3d_rdecay" X:term "," hX:term "," hR:term : tactic => `(tactic| (
  have hRR := $hR
  simp only [simM_bind, simM_get, Except.bind]
  generalize hcond : ((simStS tn $X).relaxDown && decide ((50 : F64) < (simStS tn s).t - (simStS tn $X).relaxLast)) = cb
  cases cb
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hcond
    refine ⟨.Ok (), $X, ?_, rfl, fun _ => $hX⟩
    by_cases hd : ($X).relax_down = true
    · have hl : ¬ (50 : F64) < s.t - ($X).relax_last := hcond.resolve_left (by simp [hRR, hd])
      simp [hRR, hd, hl, float.F64.sub, float.F64.lt]
    · simp [hRR, hd]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hd : ($X).relax_down = true := hcond.1
    have hl : (50 : F64) < s.t - ($X).relax_last := hcond.2
    obtain ⟨r3, s3, h3, e3, i3⟩ := s3d_rcs tn fo c $X false s.t I $hX hcl htp
    have e3' : s3b_rrel (fun _ => ()) (simStS tn s3) r3
        (s3d_csS (simStS tn s).t false (simCtxS tn fo c) (simStS tn $X)) := e3
    cases r3 with
    | Ok u =>
      exact ⟨.Ok (), s3, by simp [hRR, hd, hl, float.F64.sub, float.F64.lt, h3,
        core.result.Result.Insts.CoreOpsTry.branch], e3', fun _ => i3 rfl⟩
    | Err e =>
      exact ⟨.Err e, s3, by simp [hRR, hd, hl, float.F64.sub, float.F64.lt, h3,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], e3', by simp⟩))

theorem s3d_relax_update_gen (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (I : sim.state.St → Prop) (hI : I s)
    (hcl : s3d_RelaxCl I) (htp : s3d_TPOk tn fo c I) (hinv : SimInv c s) (hik : s3d_IK s) (hrc : s3d_RCtx c) :
    ∃ r s', sim.step.relax_update c s = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (OsuModel.Sim.Sim.relaxUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → I s') := by
  rw [s3d_relax_eq]
  unfold sim.step.relax_update s3d_relaxS
  simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind]
  have hlzS : (simCtxS tn fo c).cfg.lazerReplay = c.cfg.lazer_replay := rfl
  rw [hlzS]
  by_cases hlz : c.cfg.lazer_replay = true
  · refine ⟨.Ok (), s, by simp [hlz], by simp [hlz, s3b_rrel], fun _ => hI⟩
  rw [if_neg hlz, if_neg hlz]
  obtain ⟨v, hv, ev⟩ := sim.step.alive_objects_refines tn fo c s hinv.dict_in hinv.dict_small
  have hvm := s3d_alive_mem tn fo c s hinv v ev
  have hvd := s3d_alive_dict tn fo c s hinv v ev
  unfold sim.step.relax_requirements
  simp only [hv, bind_ok, simM_bind, simM_get, Except.bind]
  simp only [ev]
  generalize hX : forIn (m := OsuModel.Sim.SimM) (abs v : Array Nat) (false, false) _ (simCtxS tn fo c) (simStS tn s) = X
  have hK := s3d_loopStop0 (fun hold hit k st => sim.step.relax_requirements_loop.body c s s.t v hold hit k st)
    v _ (simCtxS tn fo c) (simStS tn s) ?hs ?hstop ?hend X hX
  case hs =>
    intro k hk hold hit
    have hi : (v.val[k.val]'hk).val < c.pb.objects.val.length := hvm _ (List.getElem_mem hk)
    have hio : (v.val[k.val]'hk).val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
    simp only [s3a_topObj _ _ _ _ _ hi, simM_bind, Except.bind]
    have hmem : v.val[k.val]'hk ∈ v.val := List.getElem_mem hk
    generalize hiv : v.val[k.val]'hk = i at *
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := v.property; omega)
    simp only [sim.step.relax_requirements_loop.body, vec_lt_len_iff, hk, if_true, Bool.false_eq_true, if_false,
      vec_index_eq _ _ hk, hiv, bind_ok, vec_index_eq _ _ hi, sim.step.RELAX_LENIENCY, fb64_4622945017495814144,
      float.F64.sub, float.F64.lt]
    by_cases hc : s.t < (c.pb.objects.val[i.val]'hi).h.start - 12
    · refine Or.inr (Or.inl ⟨by simp [hc], ?_⟩)
      rw [if_pos (show (simStS tn s).t < (topS tn (c.pb.objects.val[i.val]'hi)).h.start - 12 from hc)]; rfl
    rw [if_neg (show ¬ (simStS tn s).t < (topS tn (c.pb.objects.val[i.val]'hi)).h.start - 12 from hc)]
    simp only [hc, decide_false, Bool.false_eq_true, if_false]
    obtain ⟨b1, hb1, eb1⟩ := sim.step.is_hit_ref_refines tn fo c s ⟨i, (-1)#i64⟩ ⟨hio, fun h => by simp at h⟩
    simp only [simM_bind, s3a_ostate tn fo c s _ hio, Except.bind]
    rw [show ((i.val, -1) : Nat × Int) = abs (sim.step.Ref.mk i ((-1)#i64)) from rfl, eb1]
    simp only [hb1, bind_ok]
    obtain ⟨hhi, hh63, hhn⟩ := hrc.1 i.val hi
    have hpo := hrc.2 i.val
    have hnl := hinv.nested_len _ hio hi
    have hiok : s3aInstOk s i.val := by
      obtain ⟨y, hy, hyv⟩ := hvd i hmem
      exact hik.1 i ((UScalar.eq_of_val_eq hyv : y = i) ▸ hy)
    have hinst : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length := hiok.2.1
    have edt : ∀ q : sim.state.Inst, (abs q : OsuModel.Sim.Inst).drawableTracking = q.drawable_tracking := fun _ => rfl
    by_cases hb : b1 = true
    · subst hb
      refine Or.inl ⟨hold, hit, k1, hk1v, by simp [hk1], ?_⟩
      split
      · rfl
      · rename_i h; simp [s3d_kbeq] at h
    have hb' : b1 = false := by simpa using hb
    subst hb'
    cases hkd : (c.pb.objects.val[i.val]'hi).h.kind
    case Circle =>
      refine Or.inl ⟨hold, hit || s3d_hc tn (c.pb.objects.val[i.val]'hi).h (s.objs.val[i.val]'hio).hovered s.t,
        k1, hk1v, ?_, ?_⟩
      · cases hit <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, vec_index_eq _ _ hio, s3d_rhc tn, hk1]
      · split
        · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS] at h
        · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
          rfl
    case Slider =>
      by_cases he : (c.pb.objects.val[i.val]'hi).h.end_time < s.t
      · refine Or.inl ⟨hold, hit, k1, hk1v, by simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, hk1], ?_⟩
        split
        · rfl
        · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
      have hhn' := hhn hkd
      obtain ⟨hj, hhj⟩ : ∃ hj, c.head_idx.val[i.val]'hhi = hj := ⟨_, rfl⟩
      rw [hhj] at hh63 hhn'
      have hcj : (UScalar.hcast .I64 hj).val = (hj.val : Int) := sim_usize_to_i64 hj hh63
      obtain ⟨b4, hb4, eb4⟩ := sim.step.is_hit_ref_refines tn fo c s ⟨i, UScalar.hcast .I64 hj⟩
        ⟨hio, fun _ => by show (UScalar.hcast .I64 hj).val.toNat < _; rw [hcj, hnl]; simpa using hhn'⟩
      have eabs : (abs (⟨i, UScalar.hcast .I64 hj⟩ : sim.step.Ref) : Nat × Int) = (i.val, (hj.val : Int)) := by
        simp [abs, hcj]
      rw [eabs] at eb4
      obtain ⟨r, hr, er⟩ := sim.step.mouse_in_follow_area_refines h64 tn fo c s i
        ((s.insts.val[(s.objs.val[i.val]'hio).inst.val]'hinst).drawable_tracking) hinv hiok hpo
      have ehd := s3d_headIdxOf tn fo c (simStS tn s) i.val hhi
      rw [hhj] at ehd
      have enj := s3d_nestedOf tn fo c (simStS tn s) (c.pb.objects.val[i.val]'hi) hj.val hhn'
      have ein := s3a_instOf tn fo c s _ hinst
      cases r with
      | Ok val =>
        have er' : OsuModel.Sim.Sim.mouseInFollowArea i.val
            (s.insts.val[(s.objs.val[i.val]'hio).inst.val]'hinst).drawable_tracking (simCtxS tn fo c) (simStS tn s) =
            .ok (val, simStS tn s) := er
        cases b4
        · refine Or.inl ⟨hold || val, hit || s3d_hc tn ((c.pb.objects.val[i.val]'hi).nested.val[hj.val]'hhn')
            (s.objs.val[i.val]'hio).hovered s.t, k1, hk1v, ?_, ?_⟩
          · cases hold <;> cases hit <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, vec_index_eq _ _ hhi, hhj,
              lift, hb4, vec_index_eq _ _ hhn', vec_index_usize_ok _ _ hhn', vec_index_usize_ok _ _ hhi, vec_index_usize_ok _ _ hinst, s3d_rhc tn, vec_index_eq _ _ hinst, hr,
              core.result.Result.Insts.CoreOpsTry.branch, hk1]
          · split
            · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
            · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS, simM_bind, ehd, Except.bind, eb4, enj,
                s3a_ostateS_inst, ein, edt, er', Bool.not_false, Bool.false_eq_true, ↓reduceIte]
              rfl
        · refine Or.inl ⟨hold || val, hit, k1, hk1v, ?_, ?_⟩
          · cases hold <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, vec_index_eq _ _ hhi, hhj,
              lift, hb4, vec_index_eq _ _ hinst, vec_index_usize_ok _ _ hinst, hr, core.result.Result.Insts.CoreOpsTry.branch, hk1]
          · split
            · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
            · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS, simM_bind, ehd, Except.bind, eb4,
                s3a_ostateS_inst, ein, edt, er', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rfl
      | Err e =>
        obtain ⟨m, hm⟩ := er
        refine Or.inr (Or.inr ⟨e, ?_, m, ?_⟩)
        · cases b4 <;> cases hit <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, vec_index_eq _ _ hhi, hhj,
              lift, hb4, vec_index_eq _ _ hhn', vec_index_usize_ok _ _ hhn', vec_index_usize_ok _ _ hhi, vec_index_usize_ok _ _ hinst, s3d_rhc tn, vec_index_eq _ _ hinst, hr,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · split
          · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
          · cases b4 <;> simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS, simM_bind, ehd, Except.bind, eb4, enj,
                s3a_ostateS_inst, ein, edt, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> rfl
    case Spinner =>
      by_cases he : (c.pb.objects.val[i.val]'hi).h.end_time < s.t
      · refine Or.inl ⟨hold, hit, k1, hk1v, by simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, hk1], ?_⟩
        split
        · rfl
        · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
      cases hsp : (c.pb.objects.val[i.val]'hi).spinner with
      | none =>
        refine Or.inl ⟨hold, hit, k1, hk1v, ?_, ?_⟩
        · cases hold <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, hsp, hk1]
        · split
          · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
          · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
            simp [topS, hsp]
            try rfl
      | some sp =>
        refine Or.inl ⟨hold || decide (sp.spins_required.val > 0), hit, k1, hk1v, ?_, ?_⟩
        · cases hold <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, hsp, hk1]
        · split
          · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
          · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
            simp [topS, hsp, abs]
            try rfl
    all_goals
      refine Or.inl ⟨hold, hit, k1, hk1v, by simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, vec_index_eq _ _ hio, hk1], ?_⟩
      split
      · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS] at h
      · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
        rfl
  case hstop =>
    intro hold hit k hk
    simp [sim.step.relax_requirements_loop.body, vec_lt_len_iff, hk]
  case hend =>
    intro hold hit k st hk
    have : ¬ k < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; omega
    simp [sim.step.relax_requirements_loop.body, this]
  obtain ⟨r, hr, hrX⟩ := hK
  have hloop : sim.step.relax_requirements_loop c s s.t v false false 0#usize false = ok r := by
    unfold sim.step.relax_requirements_loop; exact hr
  simp only [hloop, bind_ok]
  rcases r with p | e
  · obtain ⟨hit, hold⟩ := p
    have hX' : X = .ok ((hold, hit), simStS tn s) := hrX
    subst hX'
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    cases hit
    · cases hold
      · simp only [Bool.false_eq_true, ↓reduceIte]
        s3d_rdecay s, hI, hI
      · simp only [Bool.false_eq_true, ↓reduceIte]
        s3d_rhold s, hI, hI
    · obtain ⟨r1, s1, h1, e1, i1⟩ := s3d_rcs tn fo c s false s.t I hI hcl htp
      have e1' : s3b_rrel (fun _ => ()) (simStS tn s1) r1
          (s3d_csS (simStS tn s).t false (simCtxS tn fo c) (simStS tn s)) := e1
      simp only [↓reduceIte, h1, bind_ok, simM_bind]
      cases r1 with
      | Err e =>
        obtain ⟨m, hm⟩ := e1'
        exact ⟨.Err e, s1, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨m, by rw [hm] <;> rfl⟩, by simp⟩
      | Ok u =>
        have hI1 := i1 rfl
        have e1'' : s3d_csS (simStS tn s).t false (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s1) := e1'
        obtain ⟨r2, s2, h2, e2, i2⟩ := s3d_rcs tn fo c s1 true s.t I hI1 hcl htp
        have e2' : s3b_rrel (fun _ => ()) (simStS tn s2) r2
            (s3d_csS (simStS tn s).t true (simCtxS tn fo c) (simStS tn s1)) := e2
        simp only [core.result.Result.Insts.CoreOpsTry.branch, e1'', Except.bind, h2, bind_ok]
        cases r2 with
        | Err e =>
          obtain ⟨m, hm⟩ := e2'
          exact ⟨.Err e, s2, by simp [h2, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
            ⟨m, by rw [hm] <;> rfl⟩, by simp⟩
        | Ok u2 =>
          have hI2 := i2 rfl
          have e2'' : s3d_csS (simStS tn s).t true (simCtxS tn fo c) (simStS tn s1) = .ok ((), simStS tn s2) := e2'
          simp only [e2'']
          cases hold
          · simp only [Bool.false_eq_true, ↓reduceIte]
            s3d_rdecay s2, hI2, h2
          · simp only [↓reduceIte]
            s3d_rhold s2, hI2, h2
  · obtain ⟨m, hm⟩ := hrX
    subst hm
    exact ⟨.Err e, s, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨m, rfl⟩, by simp⟩
end OsuProofs
namespace OsuProofs
open OsuImpl

section
open OsuModel.Sim OsuModel.Sim.Sim OsuModel.Net OsuModel.Replay

/-- the requirements loop of `Sim.relaxUpdate` (verbatim; the spec inlines it), returning `(requiresHold, requiresHit)` -/
def s3d_reqS (time : F64) : SimM (Bool × Bool) := do
  let mut requiresHold := false
  let mut requiresHit := false
  for i in ← aliveObjects do
    let o := (← topObj i)
    -- `RELAX_LENIENCY = 12` (float)
    if time < o.h.start - 12 then break
    let os ← ostate i
    if (← isHitRef (i, -1)) || ((o.h.kind == .slider || o.h.kind == .spinner) && o.h.endTime < time) then continue
    -- handleHitCircle: `HitArea.IsHovered && HitWindows.CanBeHit(time - StartTime)`
    let hitCircle (h : HObj) : Bool := match h.hitWindows with
      | some hw => os.hovered && hw.canBeHit (time - h.start)
      | none => false
    match o.h.kind with
    | .circle => requiresHit := requiresHit || hitCircle o.h
    | .slider =>
      let hj := (← headIdxOf i)
      if !(← isHitRef (i, hj)) then requiresHit := requiresHit || hitCircle (← nestedOf o hj)
      requiresHold := requiresHold || (← mouseInFollowArea i (← instOf os.inst).drawableTracking)
    | .spinner =>
      requiresHold := requiresHold || (match o.spinner with | some sp => sp.spinsRequired > 0 | none => false)
    | _ => pure ()
  return (requiresHold, requiresHit)
end

theorem sim.step.relax_hit_circle_refines (tn : Nat → String) (h : sim.playable.HObj) (hov : Bool) (t : F64) :
    sim.step.relax_hit_circle h hov t = ok (s3d_hc tn h hov t) := s3d_rhc tn h hov t

/-- generic in the caller invariant `I` (needs `trigger_pressed` through `htp`); the named instance is in SD_Play2 -/
theorem s3d_relax_change_state_gen (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (down : Bool) (time : F64) (I : sim.state.St → Prop) (hI : I s) (hcl : s3d_RelaxCl I)
    (htp : s3d_TPOk tn fo c I) :
    ∃ r s', sim.step.relax_change_state c s down time = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (s3d_csS time down (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → I s') := s3d_rcs tn fo c s down time I hI hcl htp

theorem sim.step.relax_requirements_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (hinv : SimInv c s) (hik : s3d_IK s) (hrc : s3d_RCtx c) :
    ∃ r, sim.step.relax_requirements c s s.t = ok r ∧
      s3aR (fun p => (p.2, p.1)) (simStS tn s) r (s3d_reqS (simStS tn s).t (simCtxS tn fo c) (simStS tn s)) := by
  obtain ⟨v, hv, ev⟩ := sim.step.alive_objects_refines tn fo c s hinv.dict_in hinv.dict_small
  have hvm := s3d_alive_mem tn fo c s hinv v ev
  have hvd := s3d_alive_dict tn fo c s hinv v ev
  unfold sim.step.relax_requirements s3d_reqS
  simp only [hv, bind_ok, simM_bind, simM_get, Except.bind]
  simp only [ev]
  generalize hX : forIn (m := OsuModel.Sim.SimM) (abs v : Array Nat) (false, false) _ (simCtxS tn fo c) (simStS tn s) = X
  have hK := s3d_loopStop0 (fun hold hit k st => sim.step.relax_requirements_loop.body c s s.t v hold hit k st)
    v _ (simCtxS tn fo c) (simStS tn s) ?hs ?hstop ?hend X hX
  case hs =>
    intro k hk hold hit
    have hi : (v.val[k.val]'hk).val < c.pb.objects.val.length := hvm _ (List.getElem_mem hk)
    have hio : (v.val[k.val]'hk).val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
    simp only [s3a_topObj _ _ _ _ _ hi, simM_bind, Except.bind]
    have hmem : v.val[k.val]'hk ∈ v.val := List.getElem_mem hk
    generalize hiv : v.val[k.val]'hk = i at *
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := v.property; omega)
    simp only [sim.step.relax_requirements_loop.body, vec_lt_len_iff, hk, if_true, Bool.false_eq_true, if_false,
      vec_index_eq _ _ hk, hiv, bind_ok, vec_index_eq _ _ hi, sim.step.RELAX_LENIENCY, fb64_4622945017495814144,
      float.F64.sub, float.F64.lt]
    by_cases hc : s.t < (c.pb.objects.val[i.val]'hi).h.start - 12
    · refine Or.inr (Or.inl ⟨by simp [hc], ?_⟩)
      rw [if_pos (show (simStS tn s).t < (topS tn (c.pb.objects.val[i.val]'hi)).h.start - 12 from hc)]; rfl
    rw [if_neg (show ¬ (simStS tn s).t < (topS tn (c.pb.objects.val[i.val]'hi)).h.start - 12 from hc)]
    simp only [hc, decide_false, Bool.false_eq_true, if_false]
    obtain ⟨b1, hb1, eb1⟩ := sim.step.is_hit_ref_refines tn fo c s ⟨i, (-1)#i64⟩ ⟨hio, fun h => by simp at h⟩
    simp only [simM_bind, s3a_ostate tn fo c s _ hio, Except.bind]
    rw [show ((i.val, -1) : Nat × Int) = abs (sim.step.Ref.mk i ((-1)#i64)) from rfl, eb1]
    simp only [hb1, bind_ok]
    obtain ⟨hhi, hh63, hhn⟩ := hrc.1 i.val hi
    have hpo := hrc.2 i.val
    have hnl := hinv.nested_len _ hio hi
    have hiok : s3aInstOk s i.val := by
      obtain ⟨y, hy, hyv⟩ := hvd i hmem
      exact hik.1 i ((UScalar.eq_of_val_eq hyv : y = i) ▸ hy)
    have hinst : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length := hiok.2.1
    have edt : ∀ q : sim.state.Inst, (abs q : OsuModel.Sim.Inst).drawableTracking = q.drawable_tracking := fun _ => rfl
    by_cases hb : b1 = true
    · subst hb
      refine Or.inl ⟨hold, hit, k1, hk1v, by simp [hk1], ?_⟩
      split
      · rfl
      · rename_i h; simp [s3d_kbeq] at h
    have hb' : b1 = false := by simpa using hb
    subst hb'
    cases hkd : (c.pb.objects.val[i.val]'hi).h.kind
    case Circle =>
      refine Or.inl ⟨hold, hit || s3d_hc tn (c.pb.objects.val[i.val]'hi).h (s.objs.val[i.val]'hio).hovered s.t,
        k1, hk1v, ?_, ?_⟩
      · cases hit <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, vec_index_eq _ _ hio, s3d_rhc tn, hk1]
      · split
        · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS] at h
        · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
          rfl
    case Slider =>
      by_cases he : (c.pb.objects.val[i.val]'hi).h.end_time < s.t
      · refine Or.inl ⟨hold, hit, k1, hk1v, by simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, hk1], ?_⟩
        split
        · rfl
        · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
      have hhn' := hhn hkd
      obtain ⟨hj, hhj⟩ : ∃ hj, c.head_idx.val[i.val]'hhi = hj := ⟨_, rfl⟩
      rw [hhj] at hh63 hhn'
      have hcj : (UScalar.hcast .I64 hj).val = (hj.val : Int) := sim_usize_to_i64 hj hh63
      obtain ⟨b4, hb4, eb4⟩ := sim.step.is_hit_ref_refines tn fo c s ⟨i, UScalar.hcast .I64 hj⟩
        ⟨hio, fun _ => by show (UScalar.hcast .I64 hj).val.toNat < _; rw [hcj, hnl]; simpa using hhn'⟩
      have eabs : (abs (⟨i, UScalar.hcast .I64 hj⟩ : sim.step.Ref) : Nat × Int) = (i.val, (hj.val : Int)) := by
        simp [abs, hcj]
      rw [eabs] at eb4
      obtain ⟨r, hr, er⟩ := sim.step.mouse_in_follow_area_refines h64 tn fo c s i
        ((s.insts.val[(s.objs.val[i.val]'hio).inst.val]'hinst).drawable_tracking) hinv hiok hpo
      have ehd := s3d_headIdxOf tn fo c (simStS tn s) i.val hhi
      rw [hhj] at ehd
      have enj := s3d_nestedOf tn fo c (simStS tn s) (c.pb.objects.val[i.val]'hi) hj.val hhn'
      have ein := s3a_instOf tn fo c s _ hinst
      cases r with
      | Ok val =>
        have er' : OsuModel.Sim.Sim.mouseInFollowArea i.val
            (s.insts.val[(s.objs.val[i.val]'hio).inst.val]'hinst).drawable_tracking (simCtxS tn fo c) (simStS tn s) =
            .ok (val, simStS tn s) := er
        cases b4
        · refine Or.inl ⟨hold || val, hit || s3d_hc tn ((c.pb.objects.val[i.val]'hi).nested.val[hj.val]'hhn')
            (s.objs.val[i.val]'hio).hovered s.t, k1, hk1v, ?_, ?_⟩
          · cases hold <;> cases hit <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, vec_index_eq _ _ hhi, hhj,
              lift, hb4, vec_index_eq _ _ hhn', vec_index_usize_ok _ _ hhn', vec_index_usize_ok _ _ hhi, vec_index_usize_ok _ _ hinst, s3d_rhc tn, vec_index_eq _ _ hinst, hr,
              core.result.Result.Insts.CoreOpsTry.branch, hk1]
          · split
            · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
            · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS, simM_bind, ehd, Except.bind, eb4, enj,
                s3a_ostateS_inst, ein, edt, er', Bool.not_false, Bool.false_eq_true, ↓reduceIte]
              rfl
        · refine Or.inl ⟨hold || val, hit, k1, hk1v, ?_, ?_⟩
          · cases hold <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, vec_index_eq _ _ hhi, hhj,
              lift, hb4, vec_index_eq _ _ hinst, vec_index_usize_ok _ _ hinst, hr, core.result.Result.Insts.CoreOpsTry.branch, hk1]
          · split
            · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
            · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS, simM_bind, ehd, Except.bind, eb4,
                s3a_ostateS_inst, ein, edt, er', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rfl
      | Err e =>
        obtain ⟨m, hm⟩ := er
        refine Or.inr (Or.inr ⟨e, ?_, m, ?_⟩)
        · cases b4 <;> cases hit <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, vec_index_eq _ _ hhi, hhj,
              lift, hb4, vec_index_eq _ _ hhn', vec_index_usize_ok _ _ hhn', vec_index_usize_ok _ _ hhi, vec_index_usize_ok _ _ hinst, s3d_rhc tn, vec_index_eq _ _ hinst, hr,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · split
          · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
          · cases b4 <;> simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS, simM_bind, ehd, Except.bind, eb4, enj,
                s3a_ostateS_inst, ein, edt, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> rfl
    case Spinner =>
      by_cases he : (c.pb.objects.val[i.val]'hi).h.end_time < s.t
      · refine Or.inl ⟨hold, hit, k1, hk1v, by simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, hk1], ?_⟩
        split
        · rfl
        · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
      cases hsp : (c.pb.objects.val[i.val]'hi).spinner with
      | none =>
        refine Or.inl ⟨hold, hit, k1, hk1v, ?_, ?_⟩
        · cases hold <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, hsp, hk1]
        · split
          · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
          · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
            simp [topS, hsp]
            try rfl
      | some sp =>
        refine Or.inl ⟨hold || decide (sp.spins_required.val > 0), hit, k1, hk1v, ?_, ?_⟩
        · cases hold <;> simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, float.F64.lt, he, vec_index_eq _ _ hio, hsp, hk1]
        · split
          · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS, he] at h
          · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
            simp [topS, hsp, abs]
            try rfl
    all_goals
      refine Or.inl ⟨hold, hit, k1, hk1v, by simp [kindS, s3d_kbeq, vec_index_usize_ok _ _ hio, vec_index_eq _ _ hio, hk1], ?_⟩
      split
      · rename_i h; simp [hkd, kindS, s3d_kbeq, hobjS, simStS] at h
      · simp only [s3a_topS_h, s3a_hobjS_kind, hkd, kindS]
        rfl
  case hstop =>
    intro hold hit k hk
    simp [sim.step.relax_requirements_loop.body, vec_lt_len_iff, hk]
  case hend =>
    intro hold hit k st hk
    have : ¬ k < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; omega
    simp [sim.step.relax_requirements_loop.body, this]
  obtain ⟨r, hr, hrX⟩ := hK
  refine ⟨r, by unfold sim.step.relax_requirements_loop; exact hr, ?_⟩
  rcases r with p | e
  · obtain ⟨hit, hold⟩ := p
    have hX' : X = .ok ((hold, hit), simStS tn s) := hrX
    subst hX'
    rfl
  · obtain ⟨m, hm⟩ := hrX
    subst hm
    exact ⟨m, rfl⟩
end OsuProofs
