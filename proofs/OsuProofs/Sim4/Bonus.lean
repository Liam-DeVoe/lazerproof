/-
sim4 (D62): `update_bonus_score` (`DrawableSpinner.updateBonusScore`, `DrawableSpinner.cs:335-366`) against
`OsuModel.Sim.Sim.updateBonusScore`. Closes the sim3a FRAGMENT bridge (docs/proof-status.md "OPEN BRIDGES" (2)):
sim3a's `bonus_spin`/`bonus_spins` lemmas assume `s3aHF` (hit_forcefully at every tick index). The loop only hits
the FIRST UNJUDGED tick, so `s4HF` adds the premise `nested[j] = none` (needed by `hit_forcefully_frame`); `s4_bonus_spin`
/ `s4_bonus_loop` are sim3a's proofs re-run under `s4HF`, which `s4_hf` discharges from `hit_forcefully_frame`. The
spec `while` body is matched against `s3aBonusLoopF` by unfolding inside `update_bonus_score_refines`.
-/
import OsuProofs.Sim.Circle
import OsuProofs.Sim3.SA_Bonus
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-! ## frame -/

/-- per-step frame of an object update at object `i`: the state fields of `simKeepS` are kept, objects `j ≠ i` keep
`KO`, object `i` keeps `KI` -/
structure s4Fr {α β : Type} (KO : sim.state.OState → α) (KI : sim.state.OState → β) (i : Nat)
    (s s' : sim.state.St) : Prop where
  keep : simKeepS s' = simKeepS s
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), j ≠ i →
    KO (s'.objs.val[j]'h') = KO (s.objs.val[j]'h)
  oi : ∀ (h : i < s.objs.val.length) (h' : i < s'.objs.val.length), KI (s'.objs.val[i]'h') = KI (s.objs.val[i]'h)
  il : s'.insts.val.length = s.insts.val.length

theorem s4Fr_refl {α β : Type} (KO : sim.state.OState → α) (KI : sim.state.OState → β) (i : Nat) (s : sim.state.St) :
    s4Fr KO KI i s s := ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem s4Fr_trans {α β : Type} {KO : sim.state.OState → α} {KI : sim.state.OState → β} {i : Nat}
    {s1 s2 s3 : sim.state.St} (h1 : s4Fr KO KI i s1 s2) (h2 : s4Fr KO KI i s2 s3) : s4Fr KO KI i s1 s3 :=
  ⟨h2.keep.trans h1.keep, h2.len.trans h1.len,
   fun j h h' hj => (h2.ow j (by rw [h1.len]; exact h) h' hj).trans (h1.ow j h _ hj),
   fun h h' => (h2.oi (by rw [h1.len]; exact h) h').trans (h1.oi h _), h2.il.trans h1.il⟩

/-- the `apply_result` frame is an `s4Fr` frame whenever `KO`, `KI` only read `simKeepO` fields -/
theorem s4Fr_of_ar {α β : Type} {KO : sim.state.OState → α} {KI : sim.state.OState → β} (i : Nat)
    (hO : ∀ o o', simKeepO o = simKeepO o' → KO o = KO o') (hI : ∀ o o', simKeepO o = simKeepO o' → KI o = KI o')
    {s s' : sim.state.St} (h : simARFr s s') : s4Fr KO KI i s s' :=
  ⟨h.keep, h.len, fun j hj hj' _ => hO _ _ (h.ow j hj hj'), fun hj hj' => hI _ _ (h.ow i hj hj'), h.il⟩

/-- writing object `i` with an object that keeps `KI` -/
theorem s4Fr_set {α β : Type} {KO : sim.state.OState → α} {KI : sim.state.OState → β} (s0 s : sim.state.St)
    (i : Usize) (h : s4Fr KO KI i.val s0 s) (hi : i.val < s.objs.val.length) (o' : sim.state.OState)
    (ho : KI o' = KI (s.objs.val[i.val]'hi)) :
    s4Fr KO KI i.val s0 { s with objs := s.objs.set i o' } := by
  refine ⟨h.keep, by simp [alloc.vec.Vec.set, h.len], fun j hj hj' hji => ?_, fun hj hj' => ?_, h.il⟩
  · have hj2 : j < s.objs.val.length := by rw [h.len]; exact hj
    rw [← h.ow j hj hj2 hji]
    simp only [vec_set_val', List.getElem_set]
    rw [if_neg (fun e => hji e.symm)]
  · have hj2 : i.val < s.objs.val.length := by rw [h.len]; exact hj
    rw [← h.oi hj hj2]
    simp only [vec_set_val', List.getElem_set_self]
    exact ho

/-- `simKeepO` without `completed_full_spins` (what the bonus loop keeps of the spinner) -/
def s4KeepB (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.child_id, o.hit_action, o.hovered, o.head_alive, o.tracking, o.inst, o.head_inst,
   o.tick_insts, o.tick_live, o.accept_any_after, o.last_pressed, o.slider_mouse, o.spin_tracking, o.spin_mouse,
   o.last_angle, o.total_accumulated, o.accumulated_at_last_completion, o.current_spin_max, o.completed_spins,
   o.last_report_time)

theorem s4_keepB_of (o o' : sim.state.OState) (h : simKeepO o = simKeepO o') : s4KeepB o = s4KeepB o' := by
  simp only [simKeepO, Prod.mk.injEq] at h
  simp only [s4KeepB, h]

theorem s4_cfs_of (o o' : sim.state.OState) (h : simKeepO o = simKeepO o') :
    o.completed_full_spins = o'.completed_full_spins := by
  simp only [simKeepO, Prod.mk.injEq] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## the bonus loop under the first-unjudged premise -/

theorem s4_firstNone_get {α : Type} : ∀ (l : List (Option α)) j, s3aFirstNone l = some j →
    ∃ h : j < l.length, l[j]'h = none := by
  intro l
  induction l with
  | nil => intro j h; simp [s3aFirstNone] at h
  | cons x t ih =>
    intro j h
    cases x with
    | none => simp [s3aFirstNone] at h; subst h; exact ⟨by simp, rfl⟩
    | some v =>
      simp only [s3aFirstNone, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      obtain ⟨h1, h2⟩ := ih a ha
      exact ⟨by simp; omega, by simpa using h2⟩

/-- `s3aHF` restricted to unjudged ticks (the only ones the loop hits) -/
def s4HF (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize) (Q : sim.state.St → Prop) : Prop :=
  ∀ s, Q s → ∀ (hi : i.val < s.objs.val.length) (j : Usize) (hj : j.val < (s.objs.val[i.val]'hi).nested.val.length),
    (s.objs.val[i.val]'hi).nested.val[j.val]'hj = none →
    ∃ res s1, sim.step.hit_forcefully c s ⟨i, UScalar.hcast .I64 j⟩ = ok (res, s1) ∧
      match res with
      | .Ok _ => OsuModel.Sim.Sim.hitForcefully (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s1) ∧
          Q s1 ∧ ∃ hi1 : i.val < s1.objs.val.length,
            (s1.objs.val[i.val]'hi1).completed_full_spins = (s.objs.val[i.val]'hi).completed_full_spins
      | .Err _ => ∃ m, OsuModel.Sim.Sim.hitForcefully (i.val, (j.val : Int)) (simCtxS tn fo c) (simStS tn s) = .error m

/-- sim3a's `bonus_spin_refines` under `s4HF` -/
theorem s4_bonus_spin (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (Q : sim.state.St → Prop) (hHF : s4HF tn fo c i Q) (hQ : Q s) (hi : i.val < s.objs.val.length)
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
    obtain ⟨hj, hjn⟩ := s4_firstNone_get _ _ efr.symm
    obtain ⟨res, s1, hh, eh⟩ := hHF s hQ hi j hj hjn
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

/-- sim3a's `s3a_bonus_loop` under `s4HF` -/
theorem s4_bonus_loop (tn fo) (c : sim.state.Ctx) (i : Usize) (Q : sim.state.St → Prop) (N : Nat) (spins : I64)
    (hHF : s4HF tn fo c i Q)
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
      obtain ⟨r, s', hr, er, eok⟩ := s4_bonus_spin tn fo c s i Q hHF hQ hi hlt
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

/-! ## discharging `s4HF` from `hit_forcefully_frame` -/

/-- the loop invariant: the `apply_result` invariant and the bonus frame from the entry state -/
def s4BQ (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b0 n : Nat)
    (c : sim.state.Ctx) (e : Nat) (i : Nat) (s0 s : sim.state.St) : Prop :=
  SimARInv tn fo P b0 n c s e 0 0 ∧ s4Fr simKeepO s4KeepB i s0 s

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs
theorem s4_hf (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (e : Nat) (i : Usize) (s0 : sim.state.St)
    (hD : some i ∈ s0.dict_slots.val) :
    s4HF tn fo c i (s4BQ tn fo P b0 n c e i.val s0) := by
  intro s hQ hi j hj hjn
  obtain ⟨hI, hF0⟩ := hQ
  have hic : i.val < c.pb.objects.val.length := by rw [← hI.inv.objs_len]; exact hi
  have hnl := hI.inv.nested_len _ hi hic
  have hsm := hI.inv.nested_small _ (List.getElem_mem hic)
  have hcj : (UScalar.hcast .I64 j).val = (j.val : Int) := sim_usize_to_i64 j (by omega)
  have hrj : simRefOk c ⟨i, UScalar.hcast .I64 j⟩ := ⟨hic, fun _ => by
    show (UScalar.hcast .I64 j).val.toNat < (c.pb.objects.val[i.val]'hic).nested.val.length
    rw [hcj, Int.toNat_natCast]; omega⟩
  have hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none := by
    have hn : ¬ (UScalar.hcast .I64 j : I64) < 0#i64 := by
      intro h; have : (UScalar.hcast .I64 j : I64).val < 0 := h; omega
    have hu : (lift (IScalar.hcast .Usize (UScalar.hcast .I64 j : I64)) : Result Usize) = ok j := by
      simp only [lift]; congr 1; apply UScalar.eq_of_val_eq
      rw [sim_i64_cast_usize _ (by rw [hcj]; omega) (by rw [hcj, Int.toNat_natCast]; scalar_tac), hcj,
        Int.toNat_natCast]
    simp only [sim.step.res_of, vec_index_eq _ _ hi, bind_ok, hn, if_false, hu, vec_index_eq _ _ hj, hjn]
  obtain ⟨res, s1, e1, r1, i1⟩ := sim.step.hit_forcefully_frame tn fo E b0 n c hC hCS hlen (simARFr s)
    (fun _ => True) (fun _ _ _ => trivial) (simARFr_qok c s _) s _ e hI (simARFr_refl s) trivial hrj
    (hI.ik i (by rw [sim_keepS_dict hF0.keep]; exact hD)) hres
  have eabs : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
    simp [abs, hcj]
  rw [eabs] at r1
  refine ⟨res, s1, e1, ?_⟩
  cases res with
  | Err er => exact r1
  | Ok u =>
    obtain ⟨hI1, hF1⟩ := i1 rfl
    have hi1 : i.val < s1.objs.val.length := by rw [hF1.len]; exact hi
    exact ⟨r1, ⟨hI1, s4Fr_trans hF0 (s4Fr_of_ar i.val (fun _ _ h => h) s4_keepB_of hF1)⟩, hi1,
      s4_cfs_of _ _ (hF1.ow i.val hi hi1)⟩

theorem s4_bq_set (tn fo P b0 n c e) (i : Usize) (s0 s : sim.state.St) (hi : i.val < s.objs.val.length) (x : I64)
    (hQ : s4BQ tn fo P b0 n c e i.val s0 s) :
    s4BQ tn fo P b0 n c e i.val s0
      { s with objs := alloc.vec.Vec.set s.objs i { s.objs.val[i.val]'hi with completed_full_spins := x } } := by
  obtain ⟨hI, hF⟩ := hQ
  refine ⟨sim_ar_inv_objw tn fo P b0 n c s e hI i hi _ rfl rfl rfl rfl rfl
    (s3a_inv_set c s i _ hI.inv hi rfl), s4Fr_set s0 s i hF hi _ rfl⟩

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the elaborated `while fuel > 0` body of `Sim.updateBonusScore` (`N` = nested count, `T` = `spins`) -/
def s4BonusBody (i N : Nat) (T : Int) : Unit → Nat → OsuModel.Sim.SimM (ForInStep Nat) := fun _ __s =>
  if __s > 0 then do
    let __do_lift ← OsuModel.Sim.Sim.ostate i
    if (__do_lift.completedFullSpins == T) = true then pure (ForInStep.done (__s - 1))
    else do
      let __s_1 ← forIn [:N] none (s3aTickF i)
      match __s_1 with
      | some j => do
        OsuModel.Sim.Sim.hitForcefully (i, (j : Int))
        OsuModel.Sim.Sim.modifyObj i fun os => { os with completedFullSpins := os.completedFullSpins + 1 }
        pure (ForInStep.yield (__s - 1))
      | _ => do
        OsuModel.Sim.Sim.modifyObj i fun os => { os with completedFullSpins := os.completedFullSpins + 1 }
        pure (ForInStep.yield (__s - 1))
  else pure (ForInStep.done __s)

theorem s4_forIn_congrL {β : Type} (b : β) (F G : Unit → β → OsuModel.Sim.SimM (ForInStep β))
    (h : ∀ a x, G a x = F a x) : forIn Lean.Loop.mk b G = forIn Lean.Loop.mk b F := by
  rw [show G = F from funext fun a => funext fun x => h a x]

theorem s4_bonus_body_ok (tn fo) (c : sim.state.Ctx) (i : Usize) (N : Nat) (T : Int) :
    s3aBonusLoopF tn fo c i N T (s4BonusBody i.val N T) := by
  intro s m
  refine ⟨fun h => by subst h; rfl, fun hm => ?_⟩
  have e : s4BonusBody i.val N T () m = (do
      let os ← OsuModel.Sim.Sim.ostate i.val
      if (os.completedFullSpins == T) = true then pure (ForInStep.done (m - 1))
      else do
        s3aBonusStep i.val N
        pure (ForInStep.yield (m - 1))) := by
    simp only [s4BonusBody, if_pos hm, s3aBonusStep, bind_assoc]
    congr 1; funext os
    split
    · rfl
    · congr 1; funext t; cases t <;> simp
  rw [e]


/-- `update_bonus_score` (Rust) refines `Sim.updateBonusScore`; closes sim3a's FRAGMENT bridge (2). Frame: everything of
`simARFr` except object `i`'s `completed_full_spins`. -/
-- CONDITIONAL: hcs (completed_spins * 360 < 2^63 for object i, as in on_killed_refines; total_rotation overflow-freedom, to be carried by the step invariant); simCSH via sim_ar_cs
theorem sim.step.update_bonus_score_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (s : sim.state.St) (i : Usize) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hD : some i ∈ s.dict_slots.val) (hi : i.val < c.pb.objects.val.length)
    (hcs : ∀ h : i.val < s.objs.val.length, (s.objs.val[i.val]'h).completed_spins.val * 360 < 2 ^ 63) :
    ∃ res s', sim.step.update_bonus_score c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.updateBonusScore i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ s4Fr simKeepO s4KeepB i.val s s') := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hnl := hI.inv.nested_len _ ho hi
  unfold sim.step.update_bonus_score OsuModel.Sim.Sim.updateBonusScore
  simp only [vec_index_eq _ _ hi, bind_ok, simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind]
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  rw [hsz]
  by_cases hz : (c.pb.objects.val[i.val]'hi).nested.val.length = 0
  · have hz' : alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [hz]
    simp only [hz', ite_true, hz, beq_self_eq_true, simM_pure]
    exact ⟨.Ok (), s, rfl, rfl, fun _ => ⟨hI, s4Fr_refl _ _ _ s⟩⟩
  have hz' : ¬ alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested = 0#usize := by
    intro h; apply hz; have := congrArg UScalar.val h; simpa using this
  have hzb : ((c.pb.objects.val[i.val]'hi).nested.val.length == 0) = false := by simpa using hz
  simp only [hz', ite_false, hzb, Bool.false_eq_true, vec_index_eq _ _ ho, s3a_ostate tn fo c s _ ho,
    sim.step.total_rotation_refines _ (hcs ho), s3a_step_F32_360, float.F32.div, float.F32.to_i32_sat, lift, bind_ok,
    simM_bind, s3a_ostate tn fo c s _ ho, Except.bind, s3a_abs_os]
  generalize hv : F32.toInt32 (OsuModel.Sim.Sim.totalRotation (ostateS (s.objs.val[i.val]'ho)) / 360) = v
  have hspv : (IScalar.cast .I64 (i32I v)).val = v.toInt := s3a_cast_i32I v
  have hcI : ((v.toBitVec)#iscalar : IScalar .I32) = i32I v := rfl
  rw [hcI]
  generalize IScalar.cast .I64 (i32I v) = spins at hspv ⊢
  rw [← hspv]
  have hsm : spins.val < I64.max := by
    rw [hspv]; have := Int32.toInt_lt v; simp [I64.max, I64.numBits] at this ⊢; omega
  by_cases hlt : spins < (s.objs.val[i.val]'ho).completed_full_spins
  · have hlt' : spins.val < (ostateS (s.objs.val[i.val]'ho)).completedFullSpins := hlt
    rw [if_pos hlt, if_pos hlt']
    have hm := s3a_modifyObj tn fo c s i ho
      (fun os : OsuModel.Sim.OState => { os with completedFullSpins := spins.val })
      { s.objs.val[i.val]'ho with completed_full_spins := spins } rfl
    refine ⟨.Ok (), _, by simp only [vec_index_mut_eq _ _ ho, bind_ok]; rfl, ?_, fun _ => ⟨?_, ?_⟩⟩
    · simp only [simM_bind, hm, Except.bind, simM_pure]; rfl
    · exact (s4_bq_set tn fo P b0 n c e i s s ho spins ⟨hI, s4Fr_refl _ _ _ s⟩).1
    · exact (s4_bq_set tn fo P b0 n c e i s s ho spins ⟨hI, s4Fr_refl _ _ _ s⟩).2
  · have hlt' : ¬ spins.val < (ostateS (s.objs.val[i.val]'ho)).completedFullSpins := hlt
    rw [if_neg hlt, if_neg hlt']
    rw [s4_forIn_congrL _ (s4BonusBody i.val (c.pb.objects.val[i.val]'hi).nested.val.length spins.val) _ ?hF]
    case hF => intro a x; rfl
    have hBI : s3aBI (s4BQ tn fo P b0 n c e i.val s) i spins s := ⟨⟨hI, s4Fr_refl _ _ _ s⟩, ho, by
      have : ¬ spins.val < (s.objs.val[i.val]'ho).completed_full_spins.val := hlt
      omega⟩
    obtain ⟨r, s', hr, er⟩ := s4_bonus_loop tn fo c i (s4BQ tn fo P b0 n c e i.val s)
      (c.pb.objects.val[i.val]'hi).nested.val.length spins
      (s4_hf tn fo E b0 n c hC hCS hlen e i s hD) (fun s1 hi1 x hQ => s4_bq_set tn fo P b0 n c e i s s1 hi1 x hQ)
      (fun s1 hQ hi1 => hQ.1.inv.nested_len _ hi1 hi) hsm _ (s4_bonus_body_ok tn fo c i _ _)
      10000000 10000000#u32 s rfl hBI
    have hbs : sim.step.bonus_spins c s i spins = ok (r, s') := by
      unfold sim.step.bonus_spins sim.step.bonus_spins_loop; exact hr
    simp only [hbs, bind_ok, simM_bind, uncurry_apply_pair]
    cases r with
    | Err er' =>
      obtain ⟨m, hm⟩ := er
      refine ⟨.Err er', s', by simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame], ⟨m, ?_⟩,
        fun h => by cases h⟩
      simp only [hm, Except.bind]
    | Ok f =>
      obtain ⟨e1, ⟨⟨hI', hF'⟩, ho', hle'⟩, e3⟩ := er
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, e1, Except.bind, s3a_ostate tn fo c s' _ ho']
      by_cases hf0 : f = 0#u32
      · subst hf0
        rw [if_pos rfl]
        simp only [vec_index_eq _ _ ho', bind_ok]
        by_cases hc : (s'.objs.val[i.val]'ho').completed_full_spins = spins
        · have hc1 : ((s'.objs.val[i.val]'ho').completed_full_spins != spins) = false := by simp [hc]
          have hcv : (s'.objs.val[i.val]'ho').completed_full_spins.val = spins.val := by rw [hc]
          rw [hc1]; simp only [Bool.false_eq_true, ite_false]
          split
          · rename_i hcond; simp [hcv] at hcond
          · exact ⟨.Ok (), s', rfl, rfl, fun _ => ⟨hI', hF'⟩⟩
        · have hc1 : ((s'.objs.val[i.val]'ho').completed_full_spins != spins) = true := by simpa using hc
          have hcv : (s'.objs.val[i.val]'ho').completed_full_spins.val ≠ spins.val :=
            fun h => hc (IScalar.eq_of_val_eq h)
          rw [hc1]; simp only [ite_true]
          split
          · exact ⟨_, s', rfl, ⟨_, rfl⟩, fun h => by cases h⟩
          · rename_i hcond; exfalso; apply hcond; simp [hcv]
      · have hfp : f.val > 0 := by
          have : f.val ≠ 0 := fun h => hf0 (UScalar.eq_of_val_eq (by simpa using h)); omega
        obtain ⟨ho2, hc⟩ := e3 hfp
        rw [if_neg hf0]
        have hcv : (s'.objs.val[i.val]'ho').completed_full_spins.val = spins.val := by rw [hc]
        split
        · rename_i hcond; simp [hcv] at hcond
        · exact ⟨.Ok (), s', rfl, rfl, fun _ => ⟨hI', hF'⟩⟩

end OsuProofs
