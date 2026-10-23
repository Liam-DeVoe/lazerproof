/-
`apply_result` with frame conditions: the fuel induction of Sim/ApplyResult.lean generalised to an extra state predicate
`Q` that every write of the `apply_result` chain preserves (`SimQOk`), and a target predicate `A` (the refs the chain
may judge: the top-level target, and circle-like refs judged by the StartTimeOrdered `HandleHit`).
-/
import OsuProofs.Sim.ApplyResult
import OsuProofs.Sim.ProcEmit
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `simAROk` restricted to targets satisfying `A` -/
def simAROkA (tn : Nat → String) (fo : alloc.vec.Vec Usize) (I : sim.state.St → Nat → Prop)
    (A : sim.step.Ref → Prop) (c : sim.state.Ctx) (f : U64) : Prop :=
  ∀ s r ty e, I s e → simRefOk c r → A r → simInstOk c s r.top.val → sim.step.res_of s r = ok none →
    ∃ res s', sim.step.apply_result c s f r ty = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyResult f.val (abs r) (abs ty) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → I s' e ∧ s'.dict_slots = s.dict_slots)

/-- the writes of the `apply_result` chain preserve `Q` (result writes only at targets satisfying `A`) -/
structure SimQOk (c : sim.state.Ctx) (Q : sim.state.St → Prop) (A : sim.step.Ref → Prop) : Prop where
  setTop : ∀ s (r : sim.step.Ref) (ht : r.top.val < s.objs.val.length) (ty : sim.basic.HitResult),
    r.nested.val < 0 → A r → Q s →
    Q { s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ } }
  setNested : ∀ s (r : sim.step.Ref) (ht : r.top.val < s.objs.val.length) (j : Usize) (ty : sim.basic.HitResult),
    0 ≤ r.nested.val → j.val = r.nested.val.toNat → A r → Q s →
    Q { s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set j (some ⟨ty, s.t⟩) } }
  us : ∀ s s' (i : Usize), Q s → s3c_usFrame i s s' → Q s'
  tick : ∀ s ins th, ins.val.length = s.insts.val.length → Q s → Q { s with insts := ins, theta := th }
  asp : ∀ s a b d, Q s → Q { s with as_target := a, as_recent := b, as_seen := d }
  -- proc (D73): `emit` keeps both drain-period cursors (`pr_emit_ni`), so `Q` may mention them
  emit : ∀ s hl hr sl sr v, hl.nearest_index = s.health.nearest_index → hr.nearest_index = s.health_rp.nearest_index →
    Q s → Q { s with score := sl, health := hl, score_rp := sr, health_rp := hr, out := v }

theorem sim_sto_from_loopA (tn : Nat → String) (fo : alloc.vec.Vec Usize) (I : sim.state.St → Nat → Prop)
    (A : sim.step.Ref → Prop) (c : sim.state.Ctx) (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r)
    (hI : ∀ s e, I s e → SimInv c s) (hD : ∀ s e, I s e → simIK c s) (f : U64) (hAR : simAROkA tn fo I A c f)
    (D : alloc.vec.Vec (Option Usize))
    (objs : Slice sim.step.Ref) (hv : ∀ o ∈ objs.val, simRefOk c o ∧ some o.top ∈ D.val)
    (F : OsuModel.Sim.Ref → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hF : ∀ (o : sim.step.Ref) S, F (abs o) PUnit.unit (simCtxS tn fo c) S =
      ((OsuModel.Sim.Sim.judged (abs o)) >>= fun b => if b = true then pure (ForInStep.yield PUnit.unit) else
        (OsuModel.Sim.Sim.circleLike (abs o)) >>= fun b2 => if b2 = true then
          (OsuModel.Sim.Sim.hobjOf (abs o)) >>= fun oh => (OsuModel.Sim.Sim.applyResult f.val (abs o) oh.minResult) >>=
            fun _ => pure (ForInStep.yield PUnit.unit)
        else pure (ForInStep.yield PUnit.unit)) (simCtxS tn fo c) S) :
    ∀ m (k : Usize) s e, objs.val.length - k.val = m → k.val ≤ objs.val.length → I s e → s.dict_slots = D →
      ∃ res s', sim.step.handle_hit_sto_from c s f objs k = ok (res, s') ∧
        simRelM tn s' res (forIn ((objs.val.drop k.val).map (fun o => (abs o : Nat × Int))) PUnit.unit F
          (simCtxS tn fo c) (simStS tn s)) ∧ (res = .Ok () → I s' e ∧ s'.dict_slots = D) := by
  intro m
  induction m with
  | zero =>
    intro k s e hm hk hs hsd
    have hk' : k.val = objs.val.length := by omega
    refine ⟨.Ok (), s, ?_, ?_, fun _ => ⟨hs, hsd⟩⟩
    · rw [sim.step.handle_hit_sto_from.eq_def]
      have : ¬ (k < Slice.len objs) := by rw [slice_lt_len_iff]; omega
      simp only [this, if_false]
    · simp only [hk', List.drop_length, List.map_nil, simRelM]; rfl
  | succ m ih =>
    intro k s e hm hk hs hsd
    have hlt : k.val < objs.val.length := by omega
    have hinv := hI s e hs
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := objs.property; omega)
    have hdrop : objs.val.drop k.val = objs.val[k.val]'hlt :: objs.val.drop k1.val := by
      rw [hk1v]; exact List.drop_eq_getElem_cons hlt
    generalize ho : objs.val[k.val]'hlt = o at hdrop
    have hor : simRefOk c o := (hv o (by rw [← ho]; exact List.getElem_mem hlt)).1
    have hoL : simInstOk c s o.top.val :=
      hD s e hs o.top (by rw [hsd]; exact (hv o (by rw [← ho]; exact List.getElem_mem hlt)).2)
    have hos := sim_sRefOk_of c s hinv o hor
    obtain ⟨b, hb, hbS⟩ := sim.step.judged_refines tn fo c s o hos
    obtain ⟨b2, hb2, hb2S⟩ := sim.step.circle_like_refines tn fo c o hor
    obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c o hor
    rw [hdrop, List.map_cons, sim_forIn_cons_simM, hF]
    rw [sim.step.handle_hit_sto_from.eq_def]
    have hlt' : k < Slice.len objs := by rw [slice_lt_len_iff]; exact hlt
    simp only [hlt', if_true, slice_index_ok _ _ hlt, ho, bind_ok, hb]
    simp only [simM_bind, hbS, s3b_ebok]
    cases b
    · simp only [Bool.false_eq_true, if_false, hb2, bind_ok, simM_bind, hb2S, s3b_ebok]
      cases b2
      · simp only [Bool.false_eq_true, if_false, hk1, bind_ok, simM_ite, simM_pure, s3b_ebok]
        exact ih k1 s e (by omega) (by omega) hs hsd
      · simp only [if_true, hh, bind_ok, simM_ite, simM_bind, hhS, s3b_ebok]
        have hres : sim.step.res_of s o = ok none := by
          obtain ⟨ro, hro, _⟩ := sim.step.res_of_refines tn fo c s o hos
          have hj : sim.step.judged s o = ok ro.isSome := by
            simp [sim.step.judged, hro, core.option.Option.is_some]
          rw [hj] at hb
          cases ro with
          | none => exact hro
          | some x => simp at hb
        obtain ⟨res, s1, e1, r1, i1⟩ := hAR s o (simHobj c o).min_result e hs hor (hA o hor hb2) hoL hres
        have hmin : (hobjS tn (simHobj c o)).minResult = abs (simHobj c o).min_result := rfl
        rw [e1, hmin]
        simp only [bind_ok, uncurry_apply_pair]
        cases res with
        | Ok u =>
          simp only [simRelM] at r1
          rw [r1]
          simp only [s3b_ebok, simM_pure, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hk1]
          exact ih k1 s1 e (by omega) (by omega) (i1 rfl).1 (by rw [(i1 rfl).2]; exact hsd)
        | Err er =>
          obtain ⟨msg, hmsg⟩ := r1
          rw [hmsg]
          refine ⟨.Err er, s1, ?_, ⟨msg, rfl⟩, fun h => by cases h⟩
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
    · simp only [if_true, hk1, bind_ok, simM_ite, simM_pure, s3b_ebok]
      exact ih k1 s e (by omega) (by omega) hs hsd

theorem sim_handle_hitA (tn : Nat → String) (fo : alloc.vec.Vec Usize) (I : sim.state.St → Nat → Prop)
    (A : sim.step.Ref → Prop) (c : sim.state.Ctx) (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r) (hI : ∀ s e, I s e → SimInv c s)
    (hD : ∀ s e, I s e → simIK c s)
    (hcap : ∀ s e, I s e → ∀ target v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) =
      .ok (v, simStS tn s) → v.size < Usize.max)
    (f : U64) (hAR : simAROkA tn fo I A c f) (s : sim.state.St) (r : sim.step.Ref) (e : Nat) (hs : I s e)
    (hr : simRefOk c r) :
    ∃ res s', sim.step.handle_hit c s f r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.handleHit f.val (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → I s' e ∧ s'.dict_slots = s.dict_slots) := by
  have hinv := hI s e hs
  rw [sim.step.handle_hit.eq_def, OsuModel.Sim.Sim.handleHit.eq_def]
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok]
  cases hp : c.cfg.policy with
  | Legacy range =>
    have hpS : (simCtxS tn fo c).cfg.policy = .legacy (abs range) := by simp [simCtxS, abs, configS, hp]
    simp only [hpS]
    exact ⟨.Ok (), s, rfl, rfl, fun _ => ⟨hs, rfl⟩⟩
  | StartTimeOrdered =>
    have hpS : (simCtxS tn fo c).cfg.policy = .startTimeOrdered := by simp [simCtxS, abs, configS, hp]
    simp only [hpS]
    obtain ⟨b, hb, hbS⟩ := sim.step.circle_like_refines tn fo c r hr
    simp only [hb, bind_ok, simM_bind, hbS, s3b_ebok]
    cases b
    · exact ⟨.Ok (), s, by simp, by simp [simRelM], fun _ => ⟨hs, rfl⟩⟩
    · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
      obtain ⟨hh, eh⟩ := sim_hobj_of_eq tn fo c r hr
      obtain ⟨objs, ho, eo⟩ := sim.step.enumerate_up_to_refines tn fo c s (simHobj c r).start hinv.dict_in
        hinv.dict_small hinv.nested_small (hcap s e hs _)
      have hv := sim_enum_refs_valid tn fo c s _ hinv objs eo
      have hvd := sim_enum_refs_dict tn fo c s _ hinv objs eo
      simp only [simM_bind, eh, s3b_ebok]
      have eo' : OsuModel.Sim.Sim.enumerateUpTo (hobjS tn (simHobj c r)).start (simCtxS tn fo c) (simStS tn s) =
          .ok (abs objs, simStS tn s) := eo
      rw [eo', s3b_ebok]
      simp only [simM_bind]
      unfold sim.step.handle_hit_sto
      simp only [hh, ho, bind_ok]
      have hl : (abs objs : _root_.Array OsuModel.Sim.Ref).toList =
          ((alloc.vec.Vec.deref objs).val.drop (0#usize).val).map (fun r => (abs r : OsuModel.Sim.Ref)) := by
        simp [abs, alloc.vec.Vec.deref]
      rw [← Array.forIn_toList, hl]
      obtain ⟨res, s', e1, r1, i1⟩ := sim_sto_from_loopA tn fo I A c hA hI hD f hAR s.dict_slots (alloc.vec.Vec.deref objs)
        (fun o h => ⟨(hv o (by simpa [alloc.vec.Vec.deref] using h)).1, hvd o (by simpa [alloc.vec.Vec.deref] using h)⟩)
        (fun o __s => do
          let __do_lift ← OsuModel.Sim.Sim.judged o
          if __do_lift = true then pure (ForInStep.yield PUnit.unit)
          else do
            let __do_lift ← OsuModel.Sim.Sim.circleLike o
            if __do_lift = true then do
              let oh ← OsuModel.Sim.Sim.hobjOf o
              OsuModel.Sim.Sim.applyResult f.val o oh.minResult
              pure (ForInStep.yield PUnit.unit)
            else pure (ForInStep.yield PUnit.unit)) (fun o S => rfl)
        _ 0#usize s e rfl (by simp) hs rfl
      refine ⟨res, s', e1, ?_, i1⟩
      cases res with
      | Ok u =>
        simp only [simRelM] at r1 ⊢
        rw [r1]; rfl
      | Err er =>
        obtain ⟨m, hm⟩ := r1
        exact ⟨m, by rw [hm]; rfl⟩

set_option hygiene false in
/-- the part of `apply_result` after the state hook: adaptive speed, the handle-hit recursion and `emit` -/
macro "sim_arA_cont" : tactic => `(tactic| (
  try simp only [simM_bind]
  obtain ⟨res, s2, eAS, rAS, ⟨a2, b2, d2, hs2⟩, hinv2, _⟩ := sim.step.adaptive_speed_on_result_refines tn fo c s1 r ty s.t
    hI1.inv (fun _ => hr) (hC.pre r hr) hI1.sp hI1.cnt (fun l hl => by have := hI1.seen l hl; omega)
  obtain ⟨l1, l2, l3, l4⟩ := sim.step.adaptive_speed_on_result_grow c s1 r ty s.t hI1.inv (fun _ => hr) (hC.pre r hr)
    hI1.sp hI1.cnt (fun l hl => by have := hI1.seen l hl; omega) _ _ eAS
  simp only [eAS, bind_ok, uncurry_apply_pair]
  have htS : (simStS tn s).t = s.t := rfl
  rw [htS]
  cases res with
  | Err er =>
    obtain ⟨m, hm⟩ := rAS
    refine ⟨.Err er, s2, ?_, ⟨m, by rw [hm]; rfl⟩, fun h => by cases h⟩
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
  | Ok u =>
    simp only [s3b_rrel] at rAS
    rw [rAS, s3b_ebok]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    subst hs2
    have hI2 := sim_ar_inv_as tn fo P b0 n c s1 (e + 1) hI1 a2 b2 d2 hinv2 l1 l2 l3 l4
    have hQ2 := hQ.asp s1 a2 b2 d2 hQ1
    by_cases hf : fuel = 0#u64
    · have hf0 : fuel.val = 0 := by rw [hf]; rfl
      refine ⟨.Err (sim.err.SimErr.Internal sim.err.Internal.HandleHitDepth), _, by simp only [hf, if_true]; rfl, ?_,
        fun h => by cases h⟩
      rw [hf0]; exact ⟨_, rfl⟩
    · have hf1 : 1 ≤ fuel.val := by
        have : fuel.val ≠ 0 := fun h0 => hf (UScalar.eq_of_val_eq (by simpa using h0))
        omega
      obtain ⟨i, hi, hiv, _⟩ := eq_ok_of_spec (U64.sub_spec (x := fuel) (y := 1#u64) (by simp; omega))
      have hfi : fuel.val = i.val + 1 := by simp at hiv; omega
      simp only [hf, if_false, hi, bind_ok]
      rw [hfi]
      obtain ⟨res3, s3, e3, r3, i3⟩ := sim_handle_hitA tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0 ∧ Q s) A c hA
        (fun _ _ h => h.1.inv) (fun _ _ h => h.1.ik) (fun _ _ h => h.1.enum) i (hAR i (by omega)) _ r (e + 1) ⟨hI2, hQ2⟩ hr
      simp only [e3, bind_ok, uncurry_apply_pair, simM_bind]
      cases res3 with
      | Err er =>
        obtain ⟨m, hm⟩ := r3
        refine ⟨.Err er, s3, ?_, ⟨m, by rw [hm]; rfl⟩, fun h => by cases h⟩
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]
      | Ok u3 =>
        simp only [simRelM] at r3
        rw [r3, s3b_ebok]
        obtain ⟨⟨hI3, hQ3⟩, hd3⟩ := i3 rfl
        obtain ⟨o1, o2, o3⟩ := sim_emitOk_of_bud c s3 (simUnj s3 + e) (by exact hI3.em)
        obtain ⟨s4, e4, eS4⟩ := sim.step.emit_refines tn fo c s3 r ty s.t hr o1 o2 o3
        obtain ⟨hl', hr', sl, sr, v, hs4, -⟩ := sim.step.emit_props c s3 r ty s.t hr o1 o2 o3 s4 e4
        have pn := pr_emit_ni c s3 r ty s.t hr o1 o2 o3 s4 e4
        rw [hs4] at pn
        refine ⟨.Ok (), s4, by simp [core.result.Result.Insts.CoreOpsTry.branch, e4], ?_,
          fun _ => ⟨⟨sim_ar_inv_emit tn fo P b0 n c s3 e hI3 r ty s.t hr s4 e4, by
            rw [hs4]; exact hQ.emit s3 hl' hr' sl sr v pn.1 pn.2 hQ3⟩, by rw [hs4]; exact hd3.trans (hd1.trans hd0)⟩⟩
        simp only [simRelM]; exact eS4))

set_option hygiene false in
/-- `apply_result` after the result write (state `s0`, invariant `hI0`) -/
macro "sim_arA_tail" : tactic => `(tactic| (
  obtain ⟨b, hb, hbS⟩ := sim.basic.is_hit_refines ty
  have hbS' : (abs ty : OsuModel.Sim.HitResult).isHit = b := hbS
  simp only [hb, bind_ok, sim_ns_ok, hbS', sim_hobjS_kind]
  have hio : r.top.val < s0.objs.val.length := by rw [hI0.inv.objs_len]; exact hr.1
  have htf0 : s3b_TfInv P (b0 + simUnj s0 * (n + n + 4) + n + n + 4) s0 := by
    have := hI0.tf
    have e' : b0 + (simUnj s0 + 1) * (n + n + 4) = b0 + simUnj s0 * (n + n + 4) + n + n + 4 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [e'] at this; exact this
  cases hk : (simHobj c r).kind <;> simp only [kindS]
  case Circle =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1, us1⟩ := s3c_update_state_strong tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Top (if b = true then .Hit else .Miss) false 1#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun h => by cases h)) hio hk1 hk2 hhi hhb (fun h => h.elim (fun h' => by cases h') (fun h' => hhn (Or.inl h')))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .top (if b = true then .hit else .miss) false 1
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hQ1 := hQ.us s0 s1 r.top hQ0 us1
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_arA_cont
  case Slider =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1, us1⟩ := s3c_update_state_strong tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Top (if b = true then .Hit else .Miss) false 1#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun h => by cases h)) hio hk1 hk2 hhi hhb (fun h => h.elim (fun h' => by cases h') (fun h' => hhn (Or.inl h')))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .top (if b = true then .hit else .miss) false 1
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hQ1 := hQ.us s0 s1 r.top hQ0 us1
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_arA_cont
  case Spinner =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1, us1⟩ := s3c_update_state_strong tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Top (if b = true then .Hit else .Miss) false 1#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun h => by cases h)) hio hk1 hk2 hhi hhb (fun h => h.elim (fun h' => by cases h') (fun h' => hhn (Or.inl h')))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .top (if b = true then .hit else .miss) false 1
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hQ1 := hQ.us s0 s1 r.top hQ0 us1
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_arA_cont
  case Head =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1, us1⟩ := s3c_update_state_strong tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Head (if b = true then .Hit else .Miss) false 2#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun _ => hhn (Or.inr ⟨r, hr, rfl, hk⟩))) hio hk1 hk2 hhi hhb (fun _ => hhn (Or.inr ⟨r, hr, rfl, hk⟩))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .head (if b = true then .hit else .miss) false 2
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hQ1 := hQ.us s0 s1 r.top hQ0 us1
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_arA_cont
  case Tick =>
    simp only [bind_ok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s0 hI0.inv (s3b_objFrame_of_eq rfl) rfl
      (sim_tfInv_mono E _ _ s0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hI0.tf)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hd1 : s0.dict_slots = s0.dict_slots := rfl
    generalize s0 = s1 at hI1 hQ0 hd0 hd1 ⊢
    have hQ1 := hQ0
    sim_arA_cont
  case Repeat =>
    simp only [bind_ok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s0 hI0.inv (s3b_objFrame_of_eq rfl) rfl
      (sim_tfInv_mono E _ _ s0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hI0.tf)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hd1 : s0.dict_slots = s0.dict_slots := rfl
    generalize s0 = s1 at hI1 hQ0 hd0 hd1 ⊢
    have hQ1 := hQ0
    sim_arA_cont
  case Tail =>
    simp only [bind_ok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s0 hI0.inv (s3b_objFrame_of_eq rfl) rfl
      (sim_tfInv_mono E _ _ s0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hI0.tf)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hd1 : s0.dict_slots = s0.dict_slots := rfl
    generalize s0 = s1 at hI1 hQ0 hd0 hd1 ⊢
    have hQ1 := hQ0
    sim_arA_cont
  case SpinnerTick =>
    have h0 := hC.tkn r hr (Or.inl hk)
    obtain ⟨hio', _, _, htkA, htkR⟩ := hL0
    have htj := htkR r hr rfl (Or.inl hk)
    have hcv : (IScalar.hcast .Usize r.nested).val = r.nested.val.toNat :=
      sim_ref_cast r h0 _ htj (by have := ((s0.objs.val[r.top.val]'hio').tick_insts).property; omega)
    have hj : (IScalar.hcast .Usize r.nested).val < (c.pb.objects.val[r.top.val]'hr.1).nested.val.length := by
      rw [hcv]; exact hr.2 h0
    have htj' : (IScalar.hcast .Usize r.nested).val < (s0.objs.val[r.top.val]'hio).tick_insts.val.length := by
      rw [hcv]; exact htj
    have htk := htkA _ htj'
    obtain ⟨s1, e1, eS1, ⟨ins, th, hs1⟩, il1, inv1, fo1, ob1, fr1⟩ := sim.step.tick_state_refines tn fo c s0 r.top
      (IScalar.hcast .Usize r.nested) 2#u64 (if b = true then .Hit else .Miss) false hI0.inv hr.1 hj hio htj' htk
    have eS1' : OsuModel.Sim.Sim.tickState (abs r : Nat × Int).1 (abs r : Nat × Int).2.toNat 2
        (if b = true then .hit else .miss) false (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by
      rw [← sim_armedS_ite, show (abs r : Nat × Int).2.toNat = (IScalar.hcast .Usize r.nested).val from hcv.symm]
      exact eS1
    simp only [lift, e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 (s3b_objFrame_of_eq ob1) il1
      (sim_tfInv_mono E _ _ s1 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) (sim.step.tick_state_tfinv c s0 r.top _ 2#u64 _ false hI0.inv hr.1 hj hio htj' htk s1 e1 P _ hI0.tf))
      fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 (by rw [hs1])
    have hQ1 : Q s1 := by rw [hs1] at il1 ⊢; exact hQ.tick s0 ins th il1 hQ0
    have hd1 : s1.dict_slots = s0.dict_slots := by rw [hs1]
    sim_arA_cont
  case SpinnerBonusTick =>
    have h0 := hC.tkn r hr (Or.inr hk)
    obtain ⟨hio', _, _, htkA, htkR⟩ := hL0
    have htj := htkR r hr rfl (Or.inr hk)
    have hcv : (IScalar.hcast .Usize r.nested).val = r.nested.val.toNat :=
      sim_ref_cast r h0 _ htj (by have := ((s0.objs.val[r.top.val]'hio').tick_insts).property; omega)
    have hj : (IScalar.hcast .Usize r.nested).val < (c.pb.objects.val[r.top.val]'hr.1).nested.val.length := by
      rw [hcv]; exact hr.2 h0
    have htj' : (IScalar.hcast .Usize r.nested).val < (s0.objs.val[r.top.val]'hio).tick_insts.val.length := by
      rw [hcv]; exact htj
    have htk := htkA _ htj'
    obtain ⟨s1, e1, eS1, ⟨ins, th, hs1⟩, il1, inv1, fo1, ob1, fr1⟩ := sim.step.tick_state_refines tn fo c s0 r.top
      (IScalar.hcast .Usize r.nested) 2#u64 (if b = true then .Hit else .Miss) false hI0.inv hr.1 hj hio htj' htk
    have eS1' : OsuModel.Sim.Sim.tickState (abs r : Nat × Int).1 (abs r : Nat × Int).2.toNat 2
        (if b = true then .hit else .miss) false (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by
      rw [← sim_armedS_ite, show (abs r : Nat × Int).2.toNat = (IScalar.hcast .Usize r.nested).val from hcv.symm]
      exact eS1
    simp only [lift, e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 (s3b_objFrame_of_eq ob1) il1
      (sim_tfInv_mono E _ _ s1 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) (sim.step.tick_state_tfinv c s0 r.top _ 2#u64 _ false hI0.inv hr.1 hj hio htj' htk s1 e1 P _ hI0.tf))
      fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 (by rw [hs1])
    have hQ1 : Q s1 := by rw [hs1] at il1 ⊢; exact hQ.tick s0 ins th il1 hQ0
    have hd1 : s1.dict_slots = s0.dict_slots := by rw [hs1]
    sim_arA_cont))

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim_ar_stepA (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (Q : sim.state.St → Prop) (A : sim.step.Ref → Prop)
    (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r) (hQ : SimQOk c Q A)
    (fuel : U64) (hAR : ∀ f : U64, f.val < fuel.val →
      simAROkA tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0 ∧ Q s) A c f) :
    simAROkA tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0 ∧ Q s) A c fuel := by
  intro s r ty e hIQ hr hAr hL hres
  obtain ⟨hI, hQs⟩ := hIQ
  have hinv := hI.inv
  obtain ⟨ht, hn⟩ := sim_sRefOk_of c s hinv r hr
  obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c r hr
  rw [sim.step.apply_result.eq_def, OsuModel.Sim.Sim.applyResult.eq_def]
  simp only [hh, bind_ok]
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok, hhS]
  by_cases hneg : r.nested < 0#i64
  · have hneg' : (abs r : Nat × Int).2 < 0 := by show r.nested.val < 0; scalar_tac
    simp only [hneg, if_true, vec_index_mut_eq _ _ ht, bind_ok, uncurry_apply_pair, hneg', simM_bind, simM_ite]
    rw [sim_modifyObj_stS tn _ s r.top ht { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ } _ ?hf
      (abs r : Nat × Int).1 rfl, s3b_ebok]
    case hf => rfl
    have hro : (s.objs.val[r.top.val]'ht).result = none := by
      have h0 : r.nested.val < 0 := by scalar_tac
      simp [sim.step.res_of, vec_index_eq _ _ ht, hneg] at hres; exact hres
    have hI0 := sim_ar_inv_set tn fo P b0 n c s e r.top ht { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ }
      hI rfl rfl rfl rfl (sim_unjO_result _ hro _)
    have hQ0 := hQ.setTop s r ht ty (by scalar_tac) hAr hQs
    have hL0 := sim_instOk_keep (sim_keep_set s r.top ht { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ }
      rfl rfl rfl) (Nat.le_refl _) hL
    have hd0 : ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ } } :
      sim.state.St).dict_slots = s.dict_slots := rfl
    generalize ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ } } :
      sim.state.St) = s0 at hI0 hQ0 hL0 hd0 ⊢
    sim_arA_tail
  · have h0 : 0 ≤ r.nested.val := by scalar_tac
    have hneg' : ¬ (abs r : Nat × Int).2 < 0 := by show ¬ r.nested.val < 0; omega
    have hnl := hn h0
    have hcv : (IScalar.hcast .Usize r.nested).val = r.nested.val.toNat :=
      sim_ref_cast r h0 _ hnl (by have := ((s.objs.val[r.top.val]'ht).nested).property; omega)
    have hnl' : (IScalar.hcast .Usize r.nested).val < (s.objs.val[r.top.val]'ht).nested.val.length := by rw [hcv]; exact hnl
    have hnone : (s.objs.val[r.top.val]'ht).nested.val[(IScalar.hcast .Usize r.nested).val]'hnl' = none := by
      simp [sim.step.res_of, vec_index_eq _ _ ht, hneg, lift] at hres
      rw [vec_index_usize_eq _ _ hnl'] at hres; simpa using hres
    simp only [hneg, if_false, vec_index_mut_eq _ _ ht, bind_ok, uncurry_apply_pair, lift, vec_index_mut_eq _ _ hnl',
      hneg', simM_bind, simM_ite]
    have hS : (abs r : Nat × Int).1 < (simStS tn s).objs.size := by simpa [abs] using ht
    have hsz : (abs r : Nat × Int).2.toNat < ((simStS tn s).objs[(abs r : Nat × Int).1]'hS).nested.size := by
      rw [sim_stS_obj]; simpa [ostateS, abs] using hnl
    simp only [simS_ostate _ _ _ hS, s3b_ebok, OsuModel.Sim.Sim.setA, simM_dite, dif_pos hsz, simM_pure]
    rw [sim_modifyObj_stS tn _ s r.top ht { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) } _ ?hf
      (abs r : Nat × Int).1 rfl, s3b_ebok]
    case hf =>
      simp only [sim_stS_obj]
      simp [ostateS, alloc.vec.Vec.set, List.map_set, hcv, abs]; try rfl
    have hI0 := sim_ar_inv_set tn fo P b0 n c s e r.top ht { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) }
      hI rfl rfl rfl (by simp [alloc.vec.Vec.set]) (sim_unjO_nested _ _ hnl' hnone _)
    have hQ0 := hQ.setNested s r ht (IScalar.hcast .Usize r.nested) ty h0 hcv hAr hQs
    have hL0 := sim_instOk_keep (sim_keep_set s r.top ht { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) }
      rfl rfl rfl) (Nat.le_refl _) hL
    have hd0 : ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) } } :
      sim.state.St).dict_slots = s.dict_slots := rfl
    generalize ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) } } :
      sim.state.St) = s0 at hI0 hQ0 hL0 hd0 ⊢
    sim_arA_tail

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim_ar_allA (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (Q : sim.state.St → Prop) (A : sim.step.Ref → Prop)
    (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r) (hQ : SimQOk c Q A) :
    ∀ N (fuel : U64), fuel.val ≤ N →
      simAROkA tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0 ∧ Q s) A c fuel := by
  intro N
  induction N with
  | zero =>
    intro fuel hf
    exact sim_ar_stepA tn fo E b0 n c hC hCS Q A hA hQ fuel (fun f hlt => absurd hlt (by omega))
  | succ N ih =>
    intro fuel hf
    exact sim_ar_stepA tn fo E b0 n c hC hCS Q A hA hQ fuel (fun f hlt => ih f (by omega))

theorem SimQOk.and {c : sim.state.Ctx} {Q1 Q2 : sim.state.St → Prop} {A1 A2 : sim.step.Ref → Prop}
    (h1 : SimQOk c Q1 A1) (h2 : SimQOk c Q2 A2) : SimQOk c (fun s => Q1 s ∧ Q2 s) (fun r => A1 r ∧ A2 r) where
  setTop s r ht ty hn hA hQ := ⟨h1.setTop s r ht ty hn hA.1 hQ.1, h2.setTop s r ht ty hn hA.2 hQ.2⟩
  setNested s r ht j ty h0 hj hA hQ := ⟨h1.setNested s r ht j ty h0 hj hA.1 hQ.1, h2.setNested s r ht j ty h0 hj hA.2 hQ.2⟩
  us s s' i hQ hf := ⟨h1.us s s' i hQ.1 hf, h2.us s s' i hQ.2 hf⟩
  tick s ins th hl hQ := ⟨h1.tick s ins th hl hQ.1, h2.tick s ins th hl hQ.2⟩
  asp s a b d hQ := ⟨h1.asp s a b d hQ.1, h2.asp s a b d hQ.2⟩
  emit s hl hr sl sr v e1 e2 hQ := ⟨h1.emit s hl hr sl sr v e1 e2 hQ.1, h2.emit s hl hr sl sr v e1 e2 hQ.2⟩

/-- the object-state fields the `apply_result` chain never writes (all but result, nested, armed, head_armed,
lifetime_end, head_lifetime_end) -/
def simKeepO (o : sim.state.OState) :=
  (o.life, o.lifetime_start, o.child_id, o.hit_action, o.hovered, o.head_alive, o.tracking, o.inst, o.head_inst,
   o.tick_insts, o.tick_live, o.accept_any_after, o.last_pressed, o.slider_mouse, o.spin_tracking, o.spin_mouse,
   o.last_angle, o.total_accumulated, o.accumulated_at_last_completion, o.current_spin_max, o.completed_spins,
   o.last_report_time, o.completed_full_spins)

/-- the state fields the `apply_result` chain never writes (all but objs, insts, theta, score, health, score_rp,
health_rp, out, as_target, as_recent, as_seen), plus the drain-period cursors `health.nearest_index` /
`health_rp.nearest_index` (proc, D73: only `drain` in `processors_phase` writes them; kept LAST so the positional
projections of the earlier fields are unchanged) -/
def simKeepS (s : sim.state.St) :=
  (s.k, s.t, s.first_lifetime_update, s.next_future, s.future_order, s.active, s.dict_slots, s.free_list,
   s.child_counter, s.mouse_valid, s.mouse, s.last_replay, s.pressed, s.speed, s.clock_rate, s.relax_down,
   s.relax_was_left, s.relax_last, s.ap_frame, s.block_last, s.block_idx, s.pools, s.br_rot, s.cursor_pos,
   s.health.nearest_index, s.health_rp.nearest_index)

/-- the field frame of the `apply_result` chain -/
structure simARFr (s s' : sim.state.St) : Prop where
  keep : simKeepS s' = simKeepS s
  len : s'.objs.val.length = s.objs.val.length
  ow : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), simKeepO (s'.objs.val[j]'h') = simKeepO (s.objs.val[j]'h)
  il : s'.insts.val.length = s.insts.val.length

theorem simARFr_refl (s : sim.state.St) : simARFr s s := ⟨rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem simARFr_trans {s1 s2 s3 : sim.state.St} (h1 : simARFr s1 s2) (h2 : simARFr s2 s3) : simARFr s1 s3 :=
  ⟨h2.keep.trans h1.keep, h2.len.trans h1.len, fun j h h' => (h2.ow j (by rw [h1.len]; exact h) h').trans (h1.ow j h _),
    h2.il.trans h1.il⟩

theorem simARFr_set (s0 s : sim.state.St) (h : simARFr s0 s) (i : Usize) (hi : i.val < s.objs.val.length)
    (o' : sim.state.OState) (ho : simKeepO o' = simKeepO (s.objs.val[i.val]'hi)) :
    simARFr s0 { s with objs := s.objs.set i o' } := by
  refine ⟨h.keep, by simp [alloc.vec.Vec.set, h.len], fun j hj hj' => ?_, h.il⟩
  have hj2 : j < s.objs.val.length := by rw [h.len]; exact hj
  rw [← h.ow j hj hj2]
  simp only [vec_set_val', List.getElem_set]
  split
  · subst_vars; exact ho
  · rfl

theorem simARFr_qok (c : sim.state.Ctx) (s0 : sim.state.St) (A : sim.step.Ref → Prop) :
    SimQOk c (simARFr s0) A where
  setTop s r ht ty _ _ hQ := simARFr_set s0 s hQ r.top ht _ rfl
  setNested s r ht j ty _ _ _ hQ := simARFr_set s0 s hQ r.top ht _ rfl
  us s s' i hQ hf := by
    obtain ⟨hio, a, ha, le, hle, e, hl⟩ := hf
    rw [e]
    exact simARFr_set s0 { s with insts := s'.insts, theta := s'.theta } ⟨hQ.keep, hQ.len, hQ.ow, hl.trans hQ.il⟩ i hio _ rfl
  tick s ins th hl hQ := ⟨hQ.keep, hQ.len, hQ.ow, hl.trans hQ.il⟩
  asp s a b d hQ := ⟨hQ.keep, hQ.len, hQ.ow, hQ.il⟩
  emit s hl hr sl sr v e1 e2 hQ := ⟨by rw [← hQ.keep]; simp only [simKeepS, e1, e2], hQ.len, hQ.ow, hQ.il⟩

/-- proc (D73): the drain-period cursors of a `simKeepS` frame -/
theorem pr_keepS_ni {s s' : sim.state.St} (h : simKeepS s' = simKeepS s) :
    s'.health.nearest_index = s.health.nearest_index ∧ s'.health_rp.nearest_index = s.health_rp.nearest_index := by
  simp only [simKeepS, Prod.mk.injEq] at h
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem sim_keepS_dict {s s' : sim.state.St} (h : simKeepS s' = simKeepS s) : s'.dict_slots = s.dict_slots :=
  congrArg (fun x => x.2.2.2.2.2.2.1) h

/-- the old (unrestricted) `simIK` shape for an alive-dictionary entry -/
theorem simIK.old {c : sim.state.Ctx} {s : sim.state.St} (hik : simIK c s) {i : Usize} (hD : some i ∈ s.dict_slots.val)
    (ho : i.val < s.objs.val.length) :
    (s.objs.val[i.val]'ho).inst.val < s.insts.val.length ∧ (s.objs.val[i.val]'ho).head_inst.val < s.insts.val.length ∧
    ∀ j (hj : j < (s.objs.val[i.val]'ho).tick_insts.val.length),
      ((s.objs.val[i.val]'ho).tick_insts.val[j]'hj).val < s.insts.val.length := by
  obtain ⟨_, a, b, d, _⟩ := hik i hD; exact ⟨a, b, d⟩

theorem simInstOk.old {c : sim.state.Ctx} {s : sim.state.St} {i : Nat} (h : simInstOk c s i)
    (ho : i < s.objs.val.length) :
    (s.objs.val[i]'ho).inst.val < s.insts.val.length ∧ (s.objs.val[i]'ho).head_inst.val < s.insts.val.length ∧
    ∀ j (hj : j < (s.objs.val[i]'ho).tick_insts.val.length),
      ((s.objs.val[i]'ho).tick_insts.val[j]'hj).val < s.insts.val.length := by
  obtain ⟨_, a, b, d, _⟩ := h; exact ⟨a, b, d⟩

/-- the instances of an object survive the `apply_result` chain -/
theorem simInstOk_of_fr {c : sim.state.Ctx} {s s' : sim.state.St} (h : simARFr s s') {i : Nat}
    (hL : simInstOk c s i) : simInstOk c s' i := by
  refine sim_instOk_keep ⟨h.len, fun j hj hj' => ?_⟩ (by rw [h.il]) hL
  have e := h.ow j hj hj'
  simp only [simKeepO, Prod.mk.injEq] at e
  exact ⟨e.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.1⟩

/-- the top-level result of object `i` is never written by a chain whose targets avoid it -/
def simTopRes (i : Nat) (R : Option sim.state.Res) (s : sim.state.St) : Prop :=
  ∀ h : i < s.objs.val.length, (s.objs.val[i]'h).result = R

theorem simTopRes_qok (c : sim.state.Ctx) (i : Nat) (R : Option sim.state.Res) :
    SimQOk c (simTopRes i R) (fun r => ¬ (r.top.val = i ∧ r.nested.val < 0)) where
  setTop s r ht ty hn hA hQ := by
    intro h
    have hne : r.top.val ≠ i := fun e => hA ⟨e, hn⟩
    simp only [vec_set_val', List.getElem_set]
    rw [if_neg hne]; exact hQ _
  setNested s r ht j ty _ _ _ hQ := by
    intro h
    simp only [vec_set_val', List.getElem_set]
    split
    · subst_vars; exact hQ _
    · exact hQ _
  us s s' i' hQ hf := by
    obtain ⟨hio, a, ha, le, hle, e, _⟩ := hf
    rw [e]; intro h
    simp only [vec_set_val', List.getElem_set]
    split
    · subst_vars; exact hQ _
    · exact hQ _
  tick s ins th _ hQ := hQ
  asp s a b d hQ := hQ
  emit s hl hr sl sr v _ _ hQ := hQ

/-- `apply_result` with a preserved state predicate `Q` (e.g. `simARFr s₀`, `simTopRes i R`) -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.apply_result_frame (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (Q : sim.state.St → Prop) (A : sim.step.Ref → Prop)
    (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r) (hQ : SimQOk c Q A)
    (s : sim.state.St) (fuel : U64) (r : sim.step.Ref) (ty : sim.basic.HitResult) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hQs : Q s) (hAr : A r) (hr : simRefOk c r)
    (hL : simInstOk c s r.top.val) (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.apply_result c s fuel r ty = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyResult fuel.val (abs r) (abs ty) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ Q s') := by
  obtain ⟨res, s', e1, r1, i1⟩ :=
    sim_ar_allA tn fo E b0 n c hC hCS Q A hA hQ fuel.val fuel (Nat.le_refl _) s r ty e ⟨hI, hQs⟩ hr hAr hL hres
  exact ⟨res, s', e1, r1, fun h => (i1 h).1⟩

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.hit_forcefully_frame (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (Q : sim.state.St → Prop) (A : sim.step.Ref → Prop)
    (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r) (hQ : SimQOk c Q A)
    (s : sim.state.St) (r : sim.step.Ref) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hQs : Q s) (hAr : A r) (hr : simRefOk c r)
    (hL : simInstOk c s r.top.val) (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.hit_forcefully c s r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.hitForcefully (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ Q s') := by
  obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c r hr
  obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
  obtain ⟨res, s', e1, r1, i1⟩ := sim.step.apply_result_frame tn fo E b0 n c hC hCS Q A hA hQ s f r
    (simHobj c r).max_result e hI hQs hAr hr hL hres
  refine ⟨res, s', by simp [sim.step.hit_forcefully, hh, hf, e1], ?_, i1⟩
  simp only [OsuModel.Sim.Sim.hitForcefully, simM_bind, hfS, s3b_ebok, hhS]
  exact r1

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.miss_forcefully_frame (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (Q : sim.state.St → Prop) (A : sim.step.Ref → Prop)
    (hA : ∀ r, simRefOk c r → sim.step.circle_like c r = ok true → A r) (hQ : SimQOk c Q A)
    (s : sim.state.St) (r : sim.step.Ref) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hQs : Q s) (hAr : A r) (hr : simRefOk c r)
    (hL : simInstOk c s r.top.val) (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.miss_forcefully c s r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.missForcefully (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0 ∧ Q s') := by
  obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c r hr
  obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
  obtain ⟨res, s', e1, r1, i1⟩ := sim.step.apply_result_frame tn fo E b0 n c hC hCS Q A hA hQ s f r
    (simHobj c r).min_result e hI hQs hAr hr hL hres
  refine ⟨res, s', by simp [sim.step.miss_forcefully, hh, hf, e1], ?_, i1⟩
  simp only [OsuModel.Sim.Sim.missForcefully, simM_bind, hfS, s3b_ebok, hhS]
  exact r1

end OsuProofs
