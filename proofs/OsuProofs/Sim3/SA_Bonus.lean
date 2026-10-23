/-
sim3a (D37): spinner bonus spins (`DrawableSpinner.updateBonusScore`, `DrawableSpinner.cs:335-366`):
`os_first_unjudged_nested` / `first_unjudged_nested` (the "first unjudged tick" inner loop, spec body `s3aTickF`),
`bonus_spin` and `bonus_spins` (the fuel loop). `hit_forcefully` (sim core agent) enters as a hypothesis `s3aHF`
(its refinement at the states the loop visits), so these theorems compose once it is proved.
-/
import OsuProofs.Sim3.SA_Spin
import OsuProofs.Sim3.SA_Track
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

/-- first index of a `none` -/
def s3aFirstNone {α : Type} : List (Option α) → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: t => (s3aFirstNone t).map (· + 1)

theorem s3a_fun_found (os : sim.state.OState) (j x : Usize) :
    sim.step.os_first_unjudged_nested_loop.body os j (some x) = ok (.done (some x)) := by
  unfold sim.step.os_first_unjudged_nested_loop.body
  by_cases h : j < alloc.vec.Vec.len os.nested
  · rw [if_pos h]; rfl
  · rw [if_neg h]

theorem s3a_fun_loop (os : sim.state.OState) :
    ∀ k (j : Usize), os.nested.val.length - j.val = k → j.val ≤ os.nested.val.length →
      ∃ r, loop (fun x => sim.step.os_first_unjudged_nested_loop.body os x.1 x.2) (j, none) = ok r ∧
        r.map (·.val) = (s3aFirstNone (os.nested.val.drop j.val)).map (· + j.val) := by
  intro k
  induction k with
  | zero =>
    intro j hk hj
    have hge : ¬ j < alloc.vec.Vec.len os.nested := by rw [vec_lt_len_iff]; omega
    refine ⟨none, ?_, ?_⟩
    · rw [loop_unfold]; simp [sim.step.os_first_unjudged_nested_loop.body, hge]
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro j hk hj
    have hjl : j.val < os.nested.val.length := by omega
    have hlt : j < alloc.vec.Vec.len os.nested := by rw [vec_lt_len_iff]; exact hjl
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := os.nested.property; omega)
    rw [List.drop_eq_getElem_cons hjl]
    cases hx : os.nested.val[j.val]'hjl with
    | none =>
      have hb : sim.step.os_first_unjudged_nested_loop.body os j none = ok (.cont (j1, some j)) := by
        simp only [sim.step.os_first_unjudged_nested_loop.body, if_pos hlt, core.option.Option.is_none,
          Option.isNone_none, if_true, vec_index_eq _ _ hjl, hx, bind_ok, hj1]
      refine ⟨some j, ?_, by simp [s3aFirstNone]⟩
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      rw [loop_unfold]; dsimp only; rw [s3a_fun_found]; simp only [bind_ok]
    | some v =>
      obtain ⟨r, hr, er⟩ := ih j1 (by omega) (by omega)
      have hb : sim.step.os_first_unjudged_nested_loop.body os j none = ok (.cont (j1, none)) := by
        simp only [sim.step.os_first_unjudged_nested_loop.body, if_pos hlt, core.option.Option.is_none,
          Option.isNone_none, if_true, vec_index_eq _ _ hjl, hx, bind_ok, hj1, Option.isNone_some,
          Bool.false_eq_true, if_false]
      refine ⟨r, ?_, ?_⟩
      · rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        exact hr
      · rw [er, hj1v]; simp only [s3aFirstNone, Option.map_map]; congr 1; funext x; simp; omega

theorem sim.step.os_first_unjudged_nested_refines (os : sim.state.OState) :
    ∃ r, sim.step.os_first_unjudged_nested os = ok r ∧ r.map (·.val) = s3aFirstNone os.nested.val := by
  obtain ⟨r, hr, er⟩ := s3a_fun_loop os _ 0#usize rfl (by simp)
  exact ⟨r, hr, by simpa using er⟩

theorem sim.step.first_unjudged_nested_refines (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) :
    ∃ r, sim.step.first_unjudged_nested s i = ok r ∧ r.map (·.val) = s3aFirstNone (s.objs.val[i.val]'hi).nested.val := by
  obtain ⟨r, hr, er⟩ := sim.step.os_first_unjudged_nested_refines (s.objs.val[i.val]'hi)
  exact ⟨r, by simp only [sim.step.first_unjudged_nested, vec_index_eq _ _ hi, bind_ok]; exact hr, er⟩

/-- the inner "first unjudged tick" loop body of `updateBonusScore` (as elaborated) -/
def s3aTickF (i : Nat) : Nat → Option Nat → OsuModel.Sim.SimM (ForInStep (Option Nat)) := fun j __s => do
  let tick := __s
  let jd ← OsuModel.Sim.Sim.judged (i, (j : Int))
  if (!jd) = true then pure (ForInStep.done (some j)) else pure (ForInStep.yield tick)

theorem s3a_judged_obj (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i j : Nat) (hi : i < s.objs.val.length)
    (hj : j < (s.objs.val[i]'hi).nested.val.length) :
    OsuModel.Sim.Sim.judged (i, (j : Int)) (simCtxS tn fo c) (simStS tn s) =
      .ok (((s.objs.val[i]'hi).nested.val[j]'hj).isSome, simStS tn s) := by
  have hi' : i < (simStS tn s).objs.size := by simpa using hi
  rw [simS_judged _ _ _ hi' (fun _ => by rw [sim_stS_obj]; simpa [ostateS] using hj), sim_stS_obj]
  have hn : ¬ ((j : Int) < 0) := by omega
  simp [ostateS, hj, hn]

theorem s3a_tick_loop (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Nat) (hi : i < s.objs.val.length) :
    ∀ k j, j + k = (s.objs.val[i]'hi).nested.val.length →
      forIn (m := OsuModel.Sim.SimM) (List.range' j k) none (s3aTickF i) (simCtxS tn fo c) (simStS tn s) =
        .ok ((s3aFirstNone ((s.objs.val[i]'hi).nested.val.drop j)).map (· + j), simStS tn s) := by
  intro k
  induction k with
  | zero =>
    intro j hk
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    intro j hk
    have hj : j < (s.objs.val[i]'hi).nested.val.length := by omega
    rw [List.range'_succ, List.forIn_cons, List.drop_eq_getElem_cons hj]
    simp only [simM_bind, s3aTickF, s3a_judged_obj tn fo c s i j hi hj, Except.bind]
    cases hx : (s.objs.val[i]'hi).nested.val[j]'hj with
    | none => simp [s3aFirstNone]
    | some v =>
      simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false, simM_pure]
      rw [ih (j + 1) (by omega)]
      simp only [s3aFirstNone, Option.map_map]; congr 2; congr 1; funext x; simp; omega

/-! ## one bonus spin -/
/-- one iteration of the bonus-spin loop of `updateBonusScore` (after the `completedFullSpins == spins` test):
hit the first unjudged tick, then count the spin -/
def s3aBonusStep (i N : Nat) : OsuModel.Sim.SimM Unit := do
  let tick ← forIn [:N] none (s3aTickF i)
  match tick with
  | some j => OsuModel.Sim.Sim.hitForcefully (i, (j : Int))
  | none => pure ()
  OsuModel.Sim.Sim.modifyObj i fun os => { os with completedFullSpins := os.completedFullSpins + 1 }

/-- the refinement of `hit_forcefully` (sim core) at the states `Q` the loop visits, for the ticks of object `i` -/
def s3aHF (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize) (Q : sim.state.St → Prop) : Prop :=
  ∀ s, Q s → ∀ (hi : i.val < s.objs.val.length) (j : Usize), j.val < (s.objs.val[i.val]'hi).nested.val.length →
    ∃ res s1, sim.step.hit_forcefully c s ⟨i, UScalar.hcast .I64 j⟩ = ok (res, s1) ∧
      match res with
      | .Ok _ => OsuModel.Sim.Sim.hitForcefully (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s1) ∧
          Q s1 ∧ ∃ hi1 : i.val < s1.objs.val.length,
            (s1.objs.val[i.val]'hi1).completed_full_spins = (s.objs.val[i.val]'hi).completed_full_spins
      | .Err _ => ∃ m, OsuModel.Sim.Sim.hitForcefully (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) = .error m

theorem s3a_ostateS_cfs (o : sim.state.OState) (x : I64) :
    ostateS { o with completed_full_spins := x } = { ostateS o with completedFullSpins := x.val } := rfl

theorem s3a_cfs_upd (o : sim.state.OState) (x : I64) (hx : x.val = o.completed_full_spins.val + 1) :
    (fun os : OsuModel.Sim.OState => { os with completedFullSpins := os.completedFullSpins + 1 }) (ostateS o) =
      ostateS { o with completed_full_spins := x } := by
  show _ = { ostateS o with completedFullSpins := x.val }
  rw [hx]; rfl

theorem s3a_inc_cfs (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length)
    (hb : (s.objs.val[i.val]'hi).completed_full_spins.val < I64.max) :
    ∃ x : I64, (s.objs.val[i.val]'hi).completed_full_spins + 1#i64 = ok x ∧
      x.val = (s.objs.val[i.val]'hi).completed_full_spins.val + 1 ∧
      OsuModel.Sim.Sim.modifyObj i.val (fun os => { os with completedFullSpins := os.completedFullSpins + 1 })
        (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn { s with objs := (alloc.vec.Vec.set s.objs i
          { s.objs.val[i.val]'hi with completed_full_spins := x }) }) := by
  obtain ⟨x, hx, hxv⟩ := eq_ok_of_spec (I64.add_spec (x := (s.objs.val[i.val]'hi).completed_full_spins) (y := 1#i64)
    (by simp [I64.min, I64.numBits]; have := (s.objs.val[i.val]'hi).completed_full_spins.hmin; simp [I64.min, IScalar.min] at this ⊢; omega)
    (by simp; omega))
  have hxv' : x.val = (s.objs.val[i.val]'hi).completed_full_spins.val + 1 := by simpa using hxv
  refine ⟨x, hx, hxv', ?_⟩
  rw [s3a_modifyObj tn fo c s i hi _ _ (s3a_cfs_upd _ x hxv')]

theorem s3a_firstNone_lt {α : Type} : ∀ (l : List (Option α)) j, s3aFirstNone l = some j → j < l.length := by
  intro l
  induction l with
  | nil => intro j h; simp [s3aFirstNone] at h
  | cons x t ih =>
    intro j h
    cases x with
    | none => simp [s3aFirstNone] at h; simp; omega
    | some v =>
      simp only [s3aFirstNone, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      have := ih a ha; simp; omega

theorem s3a_tick_range (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Nat) (hi : i < s.objs.val.length) :
    forIn (m := OsuModel.Sim.SimM) [:(s.objs.val[i]'hi).nested.val.length] none (s3aTickF i) (simCtxS tn fo c) (simStS tn s) =
      .ok (s3aFirstNone (s.objs.val[i]'hi).nested.val, simStS tn s) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
  rw [s3a_tick_loop tn fo c s i hi _ 0 (by simp)]
  simp

theorem sim.step.bonus_spin_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (Q : sim.state.St → Prop) (hHF : s3aHF tn fo c i Q) (hQ : Q s) (hi : i.val < s.objs.val.length)
    (hb : (s.objs.val[i.val]'hi).completed_full_spins.val < I64.max) :
    ∃ r s', sim.step.bonus_spin c s i = ok (r, s') ∧
      s3aR (fun _ => ()) (simStS tn s') r
        (s3aBonusStep i.val (s.objs.val[i.val]'hi).nested.val.length (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → ∃ s1, Q s1 ∧ ∃ (hi1 : i.val < s1.objs.val.length) (x : I64),
        x.val = (s.objs.val[i.val]'hi).completed_full_spins.val + 1 ∧
        s' = { s1 with objs := alloc.vec.Vec.set s1.objs i { s1.objs.val[i.val]'hi1 with completed_full_spins := x } }) := by
  obtain ⟨fr, hfr, efr⟩ := sim.step.os_first_unjudged_nested_refines (s.objs.val[i.val]'hi)
  have hfu : sim.step.first_unjudged_nested s i = ok fr := by
    simp only [sim.step.first_unjudged_nested, vec_index_eq _ _ hi, bind_ok]; exact hfr
  unfold sim.step.bonus_spin s3aBonusStep
  simp only [hfu, bind_ok, simM_bind, s3a_tick_range tn fo c s i.val hi, Except.bind]
  cases fr with
  | none =>
    simp only [Option.map_none] at efr
    obtain ⟨x, hx, hxv, hm⟩ := s3a_inc_cfs tn fo c s i hi hb
    refine ⟨.Ok (), _, by simp only [vec_index_mut_eq _ _ hi, bind_ok]; first | (split; simp only [hx, bind_ok]; rfl) | (simp [hx]),
      ?_, fun _ => ⟨s, hQ, hi, x, hxv, rfl⟩⟩
    simp only [← efr, simM_pure, s3aR]
    exact hm
  | some j =>
    simp only [Option.map_some] at efr
    have hj : j.val < (s.objs.val[i.val]'hi).nested.val.length := s3a_firstNone_lt _ _ efr.symm
    obtain ⟨res, s1, hh, eh⟩ := hHF s hQ hi j hj
    simp only [← efr, lift, bind_ok, hh]
    cases res with
    | Err e =>
      obtain ⟨m, hm⟩ := eh
      refine ⟨.Err e, s1, by simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ?_, fun h => by cases h⟩
      simp only [s3aR, simM_bind, hm, Except.bind]
      exact ⟨m, rfl⟩
    | Ok u =>
      obtain ⟨hm, hQ1, hi1, hcfs⟩ := eh
      have hb1 : (s1.objs.val[i.val]'hi1).completed_full_spins.val < I64.max := by rw [hcfs]; exact hb
      obtain ⟨x, hx, hxv, hm2⟩ := s3a_inc_cfs tn fo c s1 i hi1 hb1
      refine ⟨.Ok (), _, by simp [core.result.Result.Insts.CoreOpsTry.branch, vec_index_mut_eq _ _ hi1,
          vec_index_mut_usize_ok _ _ hi1, hx],
        ?_, fun _ => ⟨s1, hQ1, hi1, x, by rw [hxv, hcfs], rfl⟩⟩
      simp only [s3aR, hm, Except.bind, simM_bind]
      exact hm2

/-! ## the bonus-spin fuel loop -/
@[simp] theorem s3a_ostateS_cfsv (o : sim.state.OState) : (ostateS o).completedFullSpins = o.completed_full_spins.val := rfl

/-- the spec `while fuel > 0` loop body of `updateBonusScore`, characterised at the spec states of the loop
(`F` is the elaborated body; the sim core agent discharges `hF` from Step.lean by unfolding). -/
def s3aBonusLoopF (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize) (N : Nat)
    (spins : Int) (F : Unit → Nat → OsuModel.Sim.SimM (ForInStep Nat)) : Prop :=
  ∀ (s : sim.state.St) n,
    (n = 0 → F () n (simCtxS tn fo c) (simStS tn s) = .ok (.done 0, simStS tn s)) ∧
    (n > 0 → F () n (simCtxS tn fo c) (simStS tn s) = (do
      let os ← OsuModel.Sim.Sim.ostate i.val
      if (os.completedFullSpins == spins) = true then pure (ForInStep.done (n - 1))
      else do
        s3aBonusStep i.val N
        pure (ForInStep.yield (n - 1))) (simCtxS tn fo c) (simStS tn s))

/-- what the loop keeps: the hit-forcefully invariant, object `i` in range with `nested` length `N`, and
`completedFullSpins ≤ spins` -/
def s3aBI (Q : sim.state.St → Prop) (i : Usize) (spins : I64) (s : sim.state.St) : Prop :=
  Q s ∧ ∃ hi : i.val < s.objs.val.length, (s.objs.val[i.val]'hi).completed_full_spins.val ≤ spins.val

theorem s3a_bonus_loop (tn fo) (c : sim.state.Ctx) (i : Usize) (Q : sim.state.St → Prop) (N : Nat) (spins : I64)
    (hHF : s3aHF tn fo c i Q)
    (hQset : ∀ s (hi : i.val < s.objs.val.length) (x : I64), Q s →
      Q { s with objs := alloc.vec.Vec.set s.objs i { s.objs.val[i.val]'hi with completed_full_spins := x } })
    (hQN : ∀ s, Q s → ∀ hi : i.val < s.objs.val.length, (s.objs.val[i.val]'hi).nested.val.length = N)
    (hsp : spins.val < I64.max)
    (F : Unit → Nat → OsuModel.Sim.SimM (ForInStep Nat)) (hF : s3aBonusLoopF tn fo c i N spins.val F) :
    ∀ n (fuel : U32) (s : sim.state.St), fuel.val = n → s3aBI Q i spins s →
      ∃ r s', loop (fun x => sim.step.bonus_spins_loop.body c i spins x.1 x.2) (s, fuel) = ok (r, s') ∧
        match r with
        | .Ok f => forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk n F (simCtxS tn fo c) (simStS tn s) =
            .ok (f.val - 1, simStS tn s') ∧ s3aBI Q i spins s' ∧
            (f.val > 0 → ∃ hi : i.val < s'.objs.val.length, (s'.objs.val[i.val]'hi).completed_full_spins = spins)
        | .Err _ => ∃ m, forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk n F (simCtxS tn fo c) (simStS tn s) = .error m := by
  intro n
  induction n with
  | zero =>
    intro fuel s hf hBI
    have hf0 : fuel = 0#u32 := UScalar.eq_of_val_eq (by simp [hf])
    subst hf0
    refine ⟨.Ok 0#u32, s, ?_, ?_⟩
    · rw [loop_unfold]; simp [sim.step.bonus_spins_loop.body]
    · refine ⟨?_, hBI, fun h => by simp at h⟩
      show (Lean.Loop.forIn Lean.Loop.mk 0 F : OsuModel.Sim.SimM Nat) _ _ = _
      rw [Lean.Loop.forIn_eq_of_monadTail]
      simp only [simM_bind, (hF s 0).1 rfl, Except.bind]
      rfl
  | succ n ih =>
    intro fuel s hf hBI
    obtain ⟨hQ, hi, hle⟩ := hBI
    have hpos : fuel > 0#u32 := by scalar_tac
    obtain ⟨f1, hf1, hf1v⟩ : ∃ f1 : U32, fuel - 1#u32 = ok f1 ∧ f1.val = n := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U32.sub_spec (x := fuel) (y := 1#u32) (by scalar_tac))
      exact ⟨z, hz, by simp at hzv; omega⟩
    have hF1 := (hF s (n + 1)).2 (by omega)
    by_cases heq : (s.objs.val[i.val]'hi).completed_full_spins = spins
    · refine ⟨.Ok fuel, s, ?_, ?_⟩
      · rw [loop_unfold]
        simp [sim.step.bonus_spins_loop.body, hpos, vec_index_eq _ _ hi, heq]
      · refine ⟨?_, ⟨hQ, hi, hle⟩, fun _ => ⟨hi, heq⟩⟩
        show (Lean.Loop.forIn Lean.Loop.mk (n + 1) F : OsuModel.Sim.SimM Nat) _ _ = _
        rw [Lean.Loop.forIn_eq_of_monadTail]
        simp only [simM_bind, hF1, s3a_ostate tn fo c s _ hi, Except.bind, s3a_ostateS_cfsv, heq, beq_self_eq_true,
          if_true, simM_pure]
        rw [hf]
    · have hlt : (s.objs.val[i.val]'hi).completed_full_spins.val < I64.max := by
        have : (s.objs.val[i.val]'hi).completed_full_spins.val ≠ spins.val := fun e => heq (IScalar.eq_of_val_eq e)
        omega
      obtain ⟨r, s', hr, er, eok⟩ := sim.step.bonus_spin_refines tn fo c s i Q hHF hQ hi hlt
      have hval : ¬ ((s.objs.val[i.val]'hi).completed_full_spins.val = spins.val) := fun e => heq (IScalar.eq_of_val_eq e)
      have hne : ((s.objs.val[i.val]'hi).completed_full_spins.val == spins.val) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => heq (IScalar.eq_of_val_eq e)
      cases r with
      | Err e =>
        refine ⟨.Err e, s', ?_, ?_⟩
        · rw [loop_unfold]
          simp [sim.step.bonus_spins_loop.body, hpos, vec_index_eq _ _ hi, heq, hval, hf1, hr,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · obtain ⟨m, hm⟩ := er
          refine ⟨m, ?_⟩
          show (Lean.Loop.forIn Lean.Loop.mk (n + 1) F : OsuModel.Sim.SimM Nat) _ _ = _
          rw [Lean.Loop.forIn_eq_of_monadTail]
          simp only [simM_bind, hF1, s3a_ostate tn fo c s _ hi, Except.bind, s3a_ostateS_cfsv, hne, Bool.false_eq_true,
            if_false]
          rw [hQN s hQ hi] at hm
          rw [hm]
      | Ok u =>
        obtain ⟨s1, hQ1, hi1, x, hxv, hs'⟩ := eok rfl
        have hBI' : s3aBI Q i spins s' := by
          subst hs'
          refine ⟨hQset s1 hi1 x hQ1, by simp [vec_set_val']; exact hi1, ?_⟩
          simp only [vec_set_val', List.getElem_set_self]
          have : (s.objs.val[i.val]'hi).completed_full_spins.val ≠ spins.val := fun e => heq (IScalar.eq_of_val_eq e)
          omega
        obtain ⟨r2, s2, hr2, er2⟩ := ih f1 s' hf1v hBI'
        refine ⟨r2, s2, ?_, ?_⟩
        · rw [loop_unfold]
          have hb : sim.step.bonus_spins_loop.body c i spins s fuel = ok (.cont (s', f1)) := by
            simp [sim.step.bonus_spins_loop.body, hpos, vec_index_eq _ _ hi, heq, hval, hf1, hr,
              core.result.Result.Insts.CoreOpsTry.branch]
          dsimp only; rw [hb]; simp only [bind_ok]; exact hr2
        · have er' : s3aBonusStep i.val N (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') := by
            rw [← hQN s hQ hi]; exact er
          cases r2 with
          | Ok f =>
            obtain ⟨e1, e2, e3⟩ := er2
            refine ⟨?_, e2, e3⟩
            show (Lean.Loop.forIn Lean.Loop.mk (n + 1) F : OsuModel.Sim.SimM Nat) _ _ = _
            rw [Lean.Loop.forIn_eq_of_monadTail]
            simp only [simM_bind, hF1, s3a_ostate tn fo c s _ hi, Except.bind, s3a_ostateS_cfsv, hne,
              Bool.false_eq_true, if_false, er', simM_pure, Nat.add_sub_cancel]
            exact e1
          | Err e =>
            obtain ⟨m, hm⟩ := er2
            refine ⟨m, ?_⟩
            show (Lean.Loop.forIn Lean.Loop.mk (n + 1) F : OsuModel.Sim.SimM Nat) _ _ = _
            rw [Lean.Loop.forIn_eq_of_monadTail]
            simp only [simM_bind, hF1, s3a_ostate tn fo c s _ hi, Except.bind, s3a_ostateS_cfsv, hne,
              Bool.false_eq_true, if_false, er', simM_pure, Nat.add_sub_cancel]
            exact hm

/-- `bonus_spins` (the `while fuel > 0` loop of `updateBonusScore`, fuel 10^7; Rust returns the fuel left `f`, the
spec loop `f - 1` (it decrements before the `completedFullSpins == spins` break); either way the final
"fuel exhausted" test agrees: `f = 0 ∧ cfs ≠ spins`). -/
theorem sim.step.bonus_spins_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (Q : sim.state.St → Prop) (N : Nat) (spins : I64) (hHF : s3aHF tn fo c i Q)
    (hQset : ∀ s (hi : i.val < s.objs.val.length) (x : I64), Q s →
      Q { s with objs := alloc.vec.Vec.set s.objs i { s.objs.val[i.val]'hi with completed_full_spins := x } })
    (hQN : ∀ s, Q s → ∀ hi : i.val < s.objs.val.length, (s.objs.val[i.val]'hi).nested.val.length = N)
    (hsp : spins.val < I64.max)
    (F : Unit → Nat → OsuModel.Sim.SimM (ForInStep Nat)) (hF : s3aBonusLoopF tn fo c i N spins.val F)
    (hBI : s3aBI Q i spins s) :
    ∃ r s', sim.step.bonus_spins c s i spins = ok (r, s') ∧
      match r with
      | .Ok f => forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk 10000000 F (simCtxS tn fo c) (simStS tn s) =
          .ok (f.val - 1, simStS tn s') ∧ s3aBI Q i spins s' ∧
          (f.val > 0 → ∃ hi : i.val < s'.objs.val.length, (s'.objs.val[i.val]'hi).completed_full_spins = spins)
      | .Err _ => ∃ m, forIn (m := OsuModel.Sim.SimM) Lean.Loop.mk 10000000 F (simCtxS tn fo c) (simStS tn s) = .error m := by
  obtain ⟨r, s', h, e⟩ := s3a_bonus_loop tn fo c i Q N spins hHF hQset hQN hsp F hF 10000000 10000000#u32 s rfl hBI
  exact ⟨r, s', by unfold sim.step.bonus_spins sim.step.bonus_spins_loop; exact h, e⟩

end OsuProofs
