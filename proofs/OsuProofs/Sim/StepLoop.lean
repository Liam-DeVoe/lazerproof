/-
`sim::step::run` / `run_with` (simcore2, D67): the step loop, generic over a per-step contract `sc2StepC tn fo c I`
(`I k s`: the loop invariant before step `k`; the concrete one is `simStepInv` with a budget decreasing in `k`, see
Sim/StepInv.lean). `sc2_run`: Rust `run_loop` against the spec's zipped `for stp in steps, k in [0:steps.size]` (with
`cfg.traceObj = none`, which `configS` fixes); `sc2_run_with`: `init_state` then `run`, given `init_state_refines` and
the invariant of the initial state.
-/
import OsuProofs.Sim.InitState
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `k`-th position stream of `[0:n]` -/
def sc2_rg (k n : Nat) : Std.Legacy.Range := { start := k, stop := n, step := 1, step_pos := by omega }

theorem sc2_rg_next (k n : Nat) (h : k < n) : Std.Stream.next? (sc2_rg k n) = some (k, sc2_rg (k + 1) n) := by
  simp [Std.Stream.next?, sc2_rg, h]

/-- Rust loop result vs a spec `forIn` result (the loop state of the spec is ignored) -/
def sc2R {β : Type} (tn : Nat → String) :
    core.result.Result Unit sim.err.SimErr × sim.state.St → Except String (β × OsuModel.Sim.St) → Prop
  | (.Ok _, s'), .ok (_, S') => S' = simStS tn s'
  | (.Err _, _), .error _ => True
  | _, _ => False

/-- the per-step contract of the `run` loop: from `I k s`, `step_once` on the state with `k, t` set refines
`stepOnce` and re-establishes `I (k+1)` -/
def sc2StepC (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (I : Nat → sim.state.St → Prop) : Prop :=
  ∀ (k : Usize) (hk : k.val < c.steps.val.length) (s : sim.state.St), I k.val s →
    ∃ r s', sim.step.step_once c { s with k := k, t := (c.steps.val[k.val]'hk).time } = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.stepOnce (simCtxS tn fo c)
        (simStS tn { s with k := k, t := (c.steps.val[k.val]'hk).time })) ∧
      (r = .Ok () → I (k.val + 1) s')

theorem sc2_run_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I : Nat → sim.state.St → Prop) (hS : sc2StepC tn fo c I)
    (F : OsuModel.Sim.Step → Std.Legacy.Range → OsuModel.Sim.SimM (ForInStep Std.Legacy.Range))
    (hF : ∀ k (hk : k < c.steps.val.length) S,
      F (abs (c.steps.val[k]'hk)) (sc2_rg k c.steps.val.length) (simCtxS tn fo c) S =
        (OsuModel.Sim.Sim.stepOnce (simCtxS tn fo c) { S with k := k, t := (c.steps.val[k]'hk).time }).bind
          (fun p => .ok (.yield (sc2_rg (k + 1) c.steps.val.length), p.2))) :
    ∀ m (k : Usize) (s : sim.state.St), c.steps.val.length - k.val = m → k.val ≤ c.steps.val.length → I k.val s →
      ∃ r s', sim.step.run_loop c.env c.cfg c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg
          c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj s
          (alloc.vec.Vec.len c.steps) k = ok (r, s') ∧
        sc2R tn (r, s') (forIn (m := OsuModel.Sim.SimM) ((c.steps.val.map (fun x => (abs x : OsuModel.Sim.Step))).drop k.val)
          (sc2_rg k.val c.steps.val.length) F (simCtxS tn fo c) (simStS tn s)) := by
  intro m
  induction m with
  | zero =>
    intro k s hm hk _
    have hge : ¬ k < alloc.vec.Vec.len c.steps := by rw [vec_lt_len_iff]; omega
    refine ⟨.Ok (), s, ?_, ?_⟩
    · unfold sim.step.run_loop; rw [loop_unfold]
      simp [sim.step.run_loop.body, hge]
    · rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl
  | succ m ih =>
    intro k s hm hk hI
    have hkl : k.val < c.steps.val.length := by omega
    have hlt : k < alloc.vec.Vec.len c.steps := by rw [vec_lt_len_iff]; exact hkl
    have hnp := c.steps.property
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    obtain ⟨r, s2, e2, r2, i2⟩ := hS k hkl s hI
    have hb : sim.step.run_loop.body c.env c.cfg c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg
        c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj
        (alloc.vec.Vec.len c.steps) s k =
        (match r with
          | .Ok _ => ok (ControlFlow.cont (s2, k1))
          | .Err e => ok (ControlFlow.done (.Err e, s2))) := by
      simp only [sim.step.run_loop.body, hlt, if_true, vec_index_eq _ _ hkl, bind_ok]
      have hc : sim.step.step_once (⟨c.env, c.cfg, c.pb, c.frames, c.steps, c.head_idx, c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods, c.first_obj⟩ : sim.state.Ctx) _ = ok (r, s2) := e2
      simp only [hc]
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, hk1,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
    rw [List.drop_eq_getElem_cons (by simp; exact hkl), List.forIn_cons]
    simp only [List.getElem_map, simM_bind, hF k.val hkl]
    have eS : simStS tn { s with k := k, t := (c.steps.val[k.val]'hkl).time } =
        { simStS tn s with k := k.val, t := (c.steps.val[k.val]'hkl).time } := rfl
    cases r with
    | Ok u =>
      simp only [simRelM] at r2
      rw [← eS, r2]
      obtain ⟨r', s', e', h'⟩ := ih k1 s2 (by omega) (by omega) (by rw [hk1v]; exact i2 rfl)
      refine ⟨r', s', ?_, ?_⟩
      · unfold sim.step.run_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.step.run_loop at e'; exact e'
      · show sc2R tn (r', s') ((Except.ok _).bind _); simp only [Except.bind]
        rw [hk1v] at h'; exact h'
    | Err er =>
      obtain ⟨msg, hmsg⟩ := r2
      rw [← eS, hmsg]
      refine ⟨.Err er, s2, ?_, trivial⟩
      unfold sim.step.run_loop; rw [loop_unfold]; dsimp only; rw [hb]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

@[simp] theorem sc2_ebok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a).bind f = f a := rfl

theorem sc2_traceObj (tn fo) (c : sim.state.Ctx) : (simCtxS tn fo c).cfg.traceObj = none := rfl

theorem sc2_run_core (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I : Nat → sim.state.St → Prop) (hS : sc2StepC tn fo c I)
    (F : OsuModel.Sim.Step → Std.Legacy.Range → OsuModel.Sim.SimM (ForInStep Std.Legacy.Range))
    (hF : ∀ k (hk : k < c.steps.val.length) S,
      F (abs (c.steps.val[k]'hk)) (sc2_rg k c.steps.val.length) (simCtxS tn fo c) S =
        (OsuModel.Sim.Sim.stepOnce (simCtxS tn fo c) { S with k := k, t := (c.steps.val[k]'hk).time }).bind
          (fun p => .ok (.yield (sc2_rg (k + 1) c.steps.val.length), p.2)))
    (s : sim.state.St) (h0 : I 0 s) :
    ∃ r s', sim.step.run_loop c.env c.cfg c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg
          c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj s
          (alloc.vec.Vec.len c.steps) 0#usize = ok (r, s') ∧
      simRelM tn s' r ((forIn (m := OsuModel.Sim.SimM) (c.steps.val.map (fun x => (abs x : OsuModel.Sim.Step)))
          (sc2_rg 0 c.steps.val.length) F (simCtxS tn fo c) (simStS tn s)).bind
        (fun p => (pure () : OsuModel.Sim.SimM Unit) (simCtxS tn fo c) p.2)) := by
  obtain ⟨r, s', e, h⟩ := sc2_run_loop tn fo c I hS F hF _ 0#usize s rfl (by simp) h0
  refine ⟨r, s', e, ?_⟩
  rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at h
  revert h
  generalize forIn (m := OsuModel.Sim.SimM) (c.steps.val.map (fun x => (abs x : OsuModel.Sim.Step)))
    (sc2_rg 0 c.steps.val.length) F (simCtxS tn fo c) (simStS tn s) = X
  intro h
  rcases r with _ | _ <;> rcases X with _ | ⟨_, _⟩ <;> simp_all [sc2R, simRelM, Except.bind]

theorem sc2_run (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I : Nat → sim.state.St → Prop) (hS : sc2StepC tn fo c I) (s : sim.state.St) (h0 : I 0 s) :
    ∃ r s', sim.step.run c s = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.run (simCtxS tn fo c) (simStS tn s)) := by
  unfold sim.step.run OsuModel.Sim.Sim.run
  simp only [OsuModel.Sim.Sim.ctx, simM_bind, simM_read, sc2_ebok]
  rw [← Array.forIn_toList]
  have hl : (simCtxS tn fo c).steps.toList = c.steps.val.map (fun x => (abs x : OsuModel.Sim.Step)) := by
    simp [simCtxS, abs]
  have hsz : (simCtxS tn fo c).steps.size = c.steps.val.length := by simp [simCtxS, abs]
  have hrg : (Std.toStream [:(simCtxS tn fo c).steps.size] : Std.Legacy.Range) = sc2_rg 0 c.steps.val.length := by
    rw [hsz]; rfl
  rw [hl, hrg]
  refine sc2_run_core tn fo c I hS _ (fun k hk S => ?_) s h0
  simp only [sc2_rg_next k _ hk, simM_bind, simM_modify, sc2_ebok, simM_read, sc2_traceObj]
  rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sc2_run_with (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I : Nat → sim.state.St → Prop) (hS : sc2StepC tn fo c I)
    (hIS : ∃ R, sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok R ∧
      simRel (simStS tn) R (OsuModel.Sim.initState (abs c.cfg) (playableS tn c.pb) c.smax.init_without_mods.val))
    (hinit : ∀ s0, sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0) → I 0 s0) :
    ∃ R, sim.step.run_with c = ok R ∧
      simRel (simStS tn) R (OsuModel.Sim.runWith (simCtxS tn fo c) (abs c.cfg) (playableS tn c.pb)) := by
  obtain ⟨R, eR, hR⟩ := hIS
  unfold sim.step.run_with OsuModel.Sim.runWith
  have hw : (simCtxS tn fo c).smax.initWithoutMods = c.smax.init_without_mods.val := rfl
  rw [hw]
  rw [eR]; simp only [bind_ok]
  cases R with
  | Err e =>
    obtain ⟨m, hm⟩ := hR
    refine ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame], ?_⟩
    simp only [hm]; exact ⟨m, rfl⟩
  | Ok s0 =>
    simp only [simRel] at hR
    rw [hR]
    obtain ⟨r, s', e1, h1⟩ := sc2_run tn fo c I hS s0 (hinit s0 eR)
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [e1]; simp only [bind_ok]
    cases r with
    | Ok u =>
      simp only [simRelM] at h1
      refine ⟨.Ok s', by simp [core.result.Result.Insts.CoreOpsTry.branch], ?_⟩
      simp only [simRel]
      simp [ReaderT.run, StateT.run, h1, Except.bind, Bind.bind, pure, Except.pure]
    | Err er =>
      obtain ⟨m, hm⟩ := h1
      refine ⟨.Err er, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame], m, ?_⟩
      simp [ReaderT.run, StateT.run, hm, Except.bind, Bind.bind]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sc2_life_eq (a : sim.state.Life) :
    sim.state.Life.Insts.CoreCmpPartialEqLife.eq a sim.state.Life.Alive = ok (lifeS a == OsuModel.Sim.Life.alive) := by
  cases a <;> simp [sim.state.Life.Insts.CoreCmpPartialEqLife.eq, sim.state.Life.read_discriminant, lifeS] <;> decide

/-- per-object contract of the `step_once` update loop: `J b` with `b` update budget units left -/
def sc2UpdC (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (J : Nat → sim.state.St → Prop) : Prop :=
  ∀ b (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length), J (b + 1) s →
    (s.objs.val[i.val]'hi).life = .Alive →
    ∃ r s', sim.step.update_dho c s i = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.updateDho i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → J b s' ∧ s'.objs.val.length = s.objs.val.length)

theorem sc2_upd_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (J : Nat → sim.state.St → Prop) (hU : sc2UpdC tn fo c J)
    (hJm : ∀ b s, J (b + 1) s → J b s)
    (G : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hG : ∀ (i : Usize) (s : sim.state.St) (h : i.val < s.objs.val.length), G i.val PUnit.unit (simCtxS tn fo c) (simStS tn s) =
      if (lifeS (s.objs.val[i.val]'h).life == OsuModel.Sim.Life.alive) = true then
        (OsuModel.Sim.Sim.updateDho i.val (simCtxS tn fo c) (simStS tn s)).bind (fun p => .ok (.yield PUnit.unit, p.2))
      else .ok (.yield PUnit.unit, simStS tn s))
    (order : alloc.vec.Vec Usize) :
    ∀ m (k : Usize) b (s : sim.state.St), order.val.length - k.val = m → k.val ≤ order.val.length →
      (∀ x ∈ order.val, x.val < s.objs.val.length) → J (b + m) s →
      ∃ r s', sim.step.step_once_loop c s order k = ok (r, s') ∧
        sc2R tn (r, s') (forIn (m := OsuModel.Sim.SimM) ((order.val.map (·.val)).drop k.val) PUnit.unit G
          (simCtxS tn fo c) (simStS tn s)) ∧
        (r = .Ok () → J b s') := by
  intro m
  induction m with
  | zero =>
    intro k b s hm hk _ hJ
    have hge : ¬ k < alloc.vec.Vec.len order := by rw [vec_lt_len_iff]; omega
    refine ⟨.Ok (), s, ?_, ?_, fun _ => hJ⟩
    · unfold sim.step.step_once_loop; rw [loop_unfold]
      simp [sim.step.step_once_loop.body, hge]
    · rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl
  | succ m ih =>
    intro k b s hm hk hx hJ
    have hkl : k.val < order.val.length := by omega
    have hlt : k < alloc.vec.Vec.len order := by rw [vec_lt_len_iff]; exact hkl
    have hnp := order.property
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    have hxi : (order.val[k.val]'hkl).val < s.objs.val.length := hx _ (List.getElem_mem hkl)
    rw [List.drop_eq_getElem_cons (by simp; exact hkl), List.forIn_cons]
    simp only [List.getElem_map, simM_bind, hG _ s hxi]
    by_cases hal : (s.objs.val[(order.val[k.val]'hkl).val]'hxi).life = .Alive
    · have hb : (lifeS (s.objs.val[(order.val[k.val]'hkl).val]'hxi).life == OsuModel.Sim.Life.alive) = true := by
        rw [hal]; rfl
      rw [if_pos hb]
      obtain ⟨r, s2, e2, r2, i2⟩ := hU (b + m) s _ hxi (by rw [show b + m + 1 = b + (m + 1) by omega]; exact hJ) hal
      have hbody : sim.step.step_once_loop.body c order s k =
          (match r with
            | .Ok _ => ok (ControlFlow.cont (s2, k1))
            | .Err e => ok (ControlFlow.done (.Err e, s2))) := by
        simp only [sim.step.step_once_loop.body, hlt, if_true, vec_index_eq _ _ hkl, vec_index_eq _ _ hxi, bind_ok,
          sc2_life_eq, hb, e2]
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, hk1,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
      cases r with
      | Ok u =>
        simp only [simRelM] at r2
        rw [r2]
        obtain ⟨hJ2, hl2⟩ := i2 rfl
        obtain ⟨r', s', e', h', i'⟩ := ih k1 b s2 (by omega) (by omega) (by rw [hl2]; exact hx) hJ2
        refine ⟨r', s', ?_, ?_, i'⟩
        · unfold sim.step.step_once_loop; rw [loop_unfold]; dsimp only; rw [hbody]; simp only [bind_ok]
          unfold sim.step.step_once_loop at e'; exact e'
        · show sc2R tn (r', s') ((Except.ok _).bind _); simp only [Except.bind]
          rw [hk1v] at h'; exact h'
      | Err er =>
        obtain ⟨msg, hmsg⟩ := r2
        rw [hmsg]
        refine ⟨.Err er, s2, ?_, trivial, fun h => by cases h⟩
        unfold sim.step.step_once_loop; rw [loop_unfold]; dsimp only; rw [hbody]; simp
    · have hb : (lifeS (s.objs.val[(order.val[k.val]'hkl).val]'hxi).life == OsuModel.Sim.Life.alive) = false := by
        revert hal; cases (s.objs.val[(order.val[k.val]'hkl).val]'hxi).life <;> simp [lifeS] <;> decide
      rw [if_neg (by rw [hb]; simp)]
      have hbody : sim.step.step_once_loop.body c order s k = ok (ControlFlow.cont (s, k1)) := by
        simp only [sim.step.step_once_loop.body, hlt, if_true, vec_index_eq _ _ hkl, vec_index_eq _ _ hxi, bind_ok,
          sc2_life_eq, hb]
        simp [hk1]
      obtain ⟨r', s', e', h', i'⟩ := ih k1 (b + 1) s (by omega) (by omega) hx
        (by rw [show b + 1 + m = b + (m + 1) by omega]; exact hJ)
      refine ⟨r', s', ?_, ?_, fun h => hJm _ _ (i' h)⟩
      · unfold sim.step.step_once_loop; rw [loop_unfold]; dsimp only; rw [hbody]; simp only [bind_ok]
        unfold sim.step.step_once_loop at e'; exact e'
      · show sc2R tn (r', s') ((Except.ok _).bind _); simp only [Except.bind]
        rw [hk1v] at h'; exact h'
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- a phase contract: from `A`, the Rust phase `f` refines the spec phase `F` and establishes `B` on `Ok` -/
def sc2PhC (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (f : sim.state.Ctx → sim.state.St → Result (core.result.Result Unit sim.err.SimErr × sim.state.St))
    (F : OsuModel.Sim.SimM Unit) (A B : sim.state.St → Prop) : Prop :=
  ∀ s, A s → ∃ r s', f c s = ok (r, s') ∧ simRelM tn s' r (F (simCtxS tn fo c) (simStS tn s)) ∧ (r = .Ok () → B s')

theorem sc2_upd_core (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (J : Nat → sim.state.St → Prop) (hU : sc2UpdC tn fo c J) (hJm : ∀ b s, J (b + 1) s → J b s) (b : Nat)
    (v : alloc.vec.Vec Usize) (s4 : sim.state.St) (hvx : ∀ x ∈ v.val, x.val < s4.objs.val.length)
    (hJ : J (b + v.val.length) s4)
    (G : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hG : ∀ (i : Usize) (s : sim.state.St) (h : i.val < s.objs.val.length), G i.val PUnit.unit (simCtxS tn fo c) (simStS tn s) =
      if (lifeS (s.objs.val[i.val]'h).life == OsuModel.Sim.Life.alive) = true then
        (OsuModel.Sim.Sim.updateDho i.val (simCtxS tn fo c) (simStS tn s)).bind (fun p => .ok (.yield PUnit.unit, p.2))
      else .ok (.yield PUnit.unit, simStS tn s)) :
    ∃ r s', sim.step.step_once_loop c s4 v 0#usize = ok (r, s') ∧
      simRelM tn s' r ((forIn (m := OsuModel.Sim.SimM) (abs v : Array Nat) PUnit.unit G (simCtxS tn fo c) (simStS tn s4)).bind
        (fun p => (pure () : OsuModel.Sim.SimM Unit) (simCtxS tn fo c) p.2)) ∧ (r = .Ok () → J b s') := by
  obtain ⟨r, s', e, h, i⟩ := sc2_upd_loop tn fo c J hU hJm G hG v _ 0#usize b s4 rfl (by simp) hvx hJ
  refine ⟨r, s', e, ?_, i⟩
  rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at h
  have hv : (abs v : Array Nat) = (v.val.map (·.val)).toArray := rfl
  rw [hv, ← Array.forIn_toList]
  revert h
  generalize forIn (m := OsuModel.Sim.SimM) (v.val.map (·.val)) PUnit.unit G (simCtxS tn fo c) (simStS tn s4) = X
  intro h
  rcases r with _ | _ <;> rcases X with _ | ⟨_, _⟩ <;> simp_all [sc2R, simRelM, Except.bind]

theorem sc2_step_once (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (I0 I1 I2 I3 I4 : sim.state.St → Prop) (J : Nat → sim.state.St → Prop) (b : Nat)
    (h1 : sc2PhC tn fo c sim.step.processors_phase OsuModel.Sim.Sim.processorsPhase I0 I1)
    (h2 : sc2PhC tn fo c sim.step.input_phase OsuModel.Sim.Sim.inputPhase I1 I2)
    (h3 : sc2PhC tn fo c sim.step.playfield_update OsuModel.Sim.Sim.playfieldUpdate I2 I3)
    (h4 : sc2PhC tn fo c sim.step.lifetime_update OsuModel.Sim.Sim.lifetimeUpdate I3 I4)
    (hO : ∀ s, I4 s → ∃ v, sim.step.update_order c s = ok v ∧
      OsuModel.Sim.Sim.updateOrder (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) ∧
      (∀ x ∈ v.val, x.val < s.objs.val.length) ∧ J (b + v.val.length) s)
    (hU : sc2UpdC tn fo c J) (hJm : ∀ b s, J (b + 1) s → J b s) :
    sc2PhC tn fo c sim.step.step_once OsuModel.Sim.Sim.stepOnce I0 (J b) := by
  intro s hs
  unfold sim.step.step_once OsuModel.Sim.Sim.stepOnce
  simp only [simM_bind]
  obtain ⟨r1, s1, e1, q1, i1⟩ := h1 s hs
  rw [e1]; simp only [bind_ok, uncurry_apply_pair]
  cases r1 with
  | Err er =>
    obtain ⟨m, hm⟩ := q1; rw [hm]
    exact ⟨.Err er, s1, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame],
      ⟨m, rfl⟩, fun h => by cases h⟩
  | Ok u1 =>
  simp only [simRelM] at q1; rw [q1]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, sc2_ebok]
  obtain ⟨r2, s2, e2, q2, i2⟩ := h2 s1 (i1 rfl)
  rw [e2]; simp only [bind_ok, uncurry_apply_pair]
  cases r2 with
  | Err er =>
    obtain ⟨m, hm⟩ := q2; rw [hm]
    exact ⟨.Err er, s2, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame],
      ⟨m, rfl⟩, fun h => by cases h⟩
  | Ok u2 =>
  simp only [simRelM] at q2; rw [q2]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, sc2_ebok]
  obtain ⟨r3, s3, e3, q3, i3⟩ := h3 s2 (i2 rfl)
  rw [e3]; simp only [bind_ok, uncurry_apply_pair]
  cases r3 with
  | Err er =>
    obtain ⟨m, hm⟩ := q3; rw [hm]
    exact ⟨.Err er, s3, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame],
      ⟨m, rfl⟩, fun h => by cases h⟩
  | Ok u3 =>
  simp only [simRelM] at q3; rw [q3]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, sc2_ebok]
  obtain ⟨r4, s4, e4, q4, i4⟩ := h4 s3 (i3 rfl)
  rw [e4]; simp only [bind_ok, uncurry_apply_pair]
  cases r4 with
  | Err er =>
    obtain ⟨m, hm⟩ := q4; rw [hm]
    exact ⟨.Err er, s4, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame],
      ⟨m, rfl⟩, fun h => by cases h⟩
  | Ok u4 =>
  simp only [simRelM] at q4; rw [q4]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, sc2_ebok]
  obtain ⟨v, ev, eV, hvx, hJ⟩ := hO s4 (i4 rfl)
  rw [ev, eV]; simp only [bind_ok, sc2_ebok]
  refine sc2_upd_core tn fo c J hU hJm b v s4 hvx hJ _ (fun i s h => ?_)
  have eo : OsuModel.Sim.Sim.ostate i.val (simCtxS tn fo c) (simStS tn s) =
      .ok (abs (s.objs.val[i.val]'h), simStS tn s) := by
    simp [OsuModel.Sim.Sim.ostate, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.st, simStS, abs, h]
  simp only [simM_bind, eo, sc2_ebok]
  have hl : (abs (s.objs.val[i.val]'h) : OsuModel.Sim.OState).life = lifeS (s.objs.val[i.val]'h).life := rfl
  rw [hl]
  split <;> simp [simM_bind]
end OsuProofs
