/-
Slider judgement (`sim::step::try_judge_nested`, `last_tick_index`, `slider_check_for_result` + helpers) against `OsuModel.Sim.Sim.tryJudgeNested`.
-/
import OsuProofs.Sim.ApplyResult
import OsuProofs.Sim3.SA_Track
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

def simIsTR : sim.playable.Kind → Bool | .Tick => true | .Repeat => true | _ => false

def simLastP {α : Type} (p : α → Bool) : List α → Nat → Option Nat → Option Nat
  | [], _, r => r
  | x :: t, j, r => simLastP p t (j + 1) (if p x then some j else r)

theorem sim_last_tick_loop (o : sim.playable.TopObj) : ∀ k (j : Usize) (r : Option Usize),
    o.nested.val.length - j.val = k → j.val ≤ o.nested.val.length →
    ∃ r', sim.step.last_tick_index_loop o r j = ok r' ∧
      r'.map (·.val) = simLastP simIsTR ((o.nested.val.drop j.val).map (·.kind)) j.val (r.map (·.val)) := by
  intro k
  induction k with
  | zero =>
    intro j r hk hj
    refine ⟨r, ?_, by simp [List.drop_of_length_le (show o.nested.val.length ≤ j.val by omega), simLastP]⟩
    unfold sim.step.last_tick_index_loop
    rw [loop_unfold]
    have : ¬ j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; omega
    simp [sim.step.last_tick_index_loop.body, this]
  | succ k ih =>
    intro j r hk hj
    have hlt : j.val < o.nested.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := o.nested.property; omega)
    have hd : o.nested.val.drop j.val = o.nested.val[j.val]'hlt :: o.nested.val.drop j1.val := by
      rw [hj1v]; exact List.drop_eq_getElem_cons hlt
    have hl : j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hlt
    have hb : sim.step.last_tick_index_loop.body o r j =
        ok (.cont (if simIsTR (o.nested.val[j.val]'hlt).kind then some j else r, j1)) := by
      simp only [sim.step.last_tick_index_loop.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok]
      cases hk2 : (o.nested.val[j.val]'hlt).kind <;>
        simp [hj1, simIsTR, sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, sim.playable.Kind.read_discriminant]
    obtain ⟨r', e, hr⟩ := ih j1 (if simIsTR (o.nested.val[j.val]'hlt).kind then some j else r) (by omega) (by omega)
    refine ⟨r', ?_, ?_⟩
    · unfold sim.step.last_tick_index_loop at e ⊢
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]; exact e
    · rw [hr, hd]; simp only [List.map_cons, simLastP, hj1v]
      congr 1; split <;> rfl

-- NOT-CONDITIONAL: total (`r.map val` is the last tick/repeat index)
theorem sim.step.last_tick_index_refines (o : sim.playable.TopObj) :
    ∃ r, sim.step.last_tick_index o = ok r ∧
      r.map (·.val) = simLastP simIsTR (o.nested.val.map (·.kind)) 0 none := by
  obtain ⟨r, e, h⟩ := sim_last_tick_loop o _ 0#usize none rfl (by simp)
  exact ⟨r, e, by simpa using h⟩

theorem sim_kindS_tr (k : sim.playable.Kind) :
    (kindS k == OsuModel.Sim.Kind.tick || kindS k == OsuModel.Sim.Kind.«repeat») = simIsTR k := by
  cases k <;> rfl

theorem sim_tjn_last_loop (tn : Nat → String) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (o : sim.playable.TopObj)
    (F : Nat → Option Nat → OsuModel.Sim.SimM (ForInStep (Option Nat)))
    (hF : ∀ k r, F k r = (do
        let a ← OsuModel.Sim.Sim.nestedOf (topS tn o) k
        let b ← OsuModel.Sim.Sim.nestedOf (topS tn o) k
        if (a.kind == .tick || b.kind == .«repeat») = true then pure (ForInStep.yield (some k))
        else pure (ForInStep.yield r))) :
    ∀ m j (r : Option Nat), j + m = o.nested.val.length →
      forIn (m := OsuModel.Sim.SimM) (List.range' j m) r F C S =
        .ok (simLastP simIsTR ((o.nested.val.drop j).map (·.kind)) j r, S) := by
  intro m
  induction m with
  | zero => intro j r hk; rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ m ih =>
    intro j r hk
    have hj : j < o.nested.val.length := by omega
    have hn : OsuModel.Sim.Sim.nestedOf (topS tn o) j C S = .ok (hobjS tn (o.nested.val[j]'hj), S) := by
      simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hj]
    rw [List.range'_succ, List.forIn_cons, List.drop_eq_getElem_cons hj, hF]
    have hk : (hobjS tn (o.nested.val[j]'hj)).kind = kindS (o.nested.val[j]'hj).kind := rfl
    simp only [simM_bind, hn, Except.bind, hk, sim_kindS_tr, List.map_cons, simLastP]
    cases simIsTR (o.nested.val[j]'hj).kind <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, simM_pure] <;>
      exact ih (j + 1) _ (by omega)

theorem sim_tjn_br (tn : Nat → String) (r : core.result.Result Unit sim.err.SimErr) (s1 : sim.state.St)
    (X : Except String (Unit × OsuModel.Sim.St)) (I : sim.state.St → Prop) (h : simRelM tn s1 r X)
    (hi : r = .Ok () → I s1) :
    ∃ res s', (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok (), s1)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame sim.err.SimErr) residual
        ok (r1, s1)) = ok (res, s') ∧ simRelM tn s' res X ∧ (res = .Ok () → I s') := by
  cases r with
  | Ok u => exact ⟨.Ok (), s1, by simp [core.result.Result.Insts.CoreOpsTry.branch], h, fun _ => hi rfl⟩
  | Err er =>
    refine ⟨.Err er, s1, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame], h, ?_⟩
    intro hc; cases hc

theorem sim_simLastP_lt {α : Type} (p : α → Bool) : ∀ (l : List α) j r x, simLastP p l j r = some x →
    x < j + l.length ∨ r = some x := by
  intro l
  induction l with
  | nil => intro j r x h; exact Or.inr h
  | cons a t ih =>
    intro j r x h
    rcases ih (j + 1) _ x h with h1 | h1
    · left; simp; omega
    · by_cases hp : p a = true
      · simp [hp] at h1; left; simp; omega
      · simp [hp] at h1; exact Or.inr h1

set_option hygiene false in
macro "tjn_jp" : tactic => `(tactic| (
  simp only [vec_index_eq _ _ hhi, lift, bind_ok, hbh, simM_bind, ehead, ebh', Except.bind]
  cases bh
  · exact ⟨_, _, rfl, rfl, fun _ => hI⟩
  · simp only [vec_index_eq _ _ ho, bind_ok, simM_bind, eos, Except.bind, htrS, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true]
    cases htr : (s.objs.val[i.val]'ho).tracking
    · simp only [hf0, float.F64.le, bind_ok, ite_false, Bool.false_eq_true]
      by_cases h0 : (0 : F64) ≤ x
      · simp only [h0, decide_true, ite_true, emf, bind_ok, uncurry_apply_pair]
        exact sim_tjn_br tn _ _ _ (fun s' => SimARInv tn fo P b0 n c s' e 0 0) rmf imf
      · simp only [h0, decide_false, ite_false, Bool.false_eq_true]
        exact ⟨_, _, rfl, rfl, fun _ => hI⟩
    · simp only [ite_true, ehf, bind_ok, uncurry_apply_pair]
      exact sim_tjn_br tn _ _ _ (fun s' => SimARInv tn fo P b0 n c s' e 0 0) rhf ihf))

/-- `try_judge_nested` (Rust) refines `Sim.tryJudgeNested` for a nested object of a slider whose slot is unjudged
(both callers, `updateSlider`'s containers and `onKilled`, test `judged` right before the call). -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.try_judge_nested_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i j : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hL : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length) (hj : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider)
    (hres : sim.step.res_of s ⟨i, UScalar.hcast .I64 j⟩ = ok none) :
    ∃ res s', sim.step.try_judge_nested c s i j = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.tryJudgeNested i.val j.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hsmall := hI.inv.nested_small _ (List.getElem_mem hi)
  have hnl := hI.inv.nested_len _ ho hi
  obtain ⟨hhi, hh63, hhb⟩ := hC.hd i.val hi
  have hhl := hhb (Or.inl hsl)
  have hcj : (UScalar.hcast .I64 j).val = (j.val : Int) := sim_usize_to_i64 j (by omega)
  have hch : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) :=
    sim_usize_to_i64 _ hh63
  have hrj : simRefOk c ⟨i, UScalar.hcast .I64 j⟩ := ⟨hi, fun _ => by
    show (UScalar.hcast .I64 j).val.toNat < _; rw [hcj]; simpa using hj⟩
  have hsh : simSRefOk s ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := ⟨ho, fun _ => by
    show (UScalar.hcast .I64 _).val.toNat < _; rw [hch, hnl]; simpa using hhl⟩
  obtain ⟨bh, hbh, ebh⟩ := sim.step.judged_refines tn fo c s _ hsh
  have ebh' : OsuModel.Sim.Sim.judged (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) (simCtxS tn fo c) (simStS tn s) =
      .ok (bh, simStS tn s) := by
    rw [← ebh]; congr 2; simp [abs, hch]
  have ehead : OsuModel.Sim.Sim.headOf i.val (simCtxS tn fo c) (simStS tn s) =
      .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn s) := by
    have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
    simp [OsuModel.Sim.Sim.headOf, OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi',
      Except.bind, simCtxS, abs, hhi]
  have eabsj : (abs (⟨i, UScalar.hcast .I64 j⟩ : sim.step.Ref) : Nat × Int) = (i.val, (j.val : Int)) := by
    simp [abs, hcj]
  obtain ⟨rh, sh, ehf, rhf, ihf⟩ := sim.step.hit_forcefully_refines tn fo E b0 n c hC hCS hlen s _ e hI hrj hL hres
  obtain ⟨rm, sm, emf, rmf, imf⟩ := sim.step.miss_forcefully_refines tn fo E b0 n c hC hCS hlen s _ e hI hrj hL hres
  rw [eabsj] at rhf rmf
  have eos : OsuModel.Sim.Sim.ostate i.val (simCtxS tn fo c) (simStS tn s) = .ok (ostateS (s.objs.val[i.val]'ho), simStS tn s) := by
    rw [simS_ostate _ _ _ (by simpa using ho), sim_stS_obj]
  have hf0 : sim.step.F64_0 = ok (0 : F64) := by simp [sim.step.F64_0]
  have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j.val (simCtxS tn fo c) (simStS tn s) =
      .ok (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj), simStS tn s) := by
    simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hj]
  have htrS : (ostateS (s.objs.val[i.val]'ho)).tracking = (s.objs.val[i.val]'ho).tracking := rfl
  rw [OsuModel.Sim.Sim.tryJudgeNested.eq_1]
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, enj, Except.bind, OsuModel.Sim.Sim.st, simM_get]
  unfold sim.step.try_judge_nested
  simp only [vec_index_eq _ _ hi, vec_index_eq _ _ hj, bind_ok, float.F64.sub]
  have hT : (simStS tn s).t = s.t := rfl
  have hE : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj)).endTime =
    ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).end_time := rfl
  have hK : (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj)).kind =
    kindS ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).kind := rfl
  simp only [hT, hE, hK]
  generalize s.t - ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).end_time = x
  cases hk : ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hj).kind <;>
    simp only [kindS, bind_ok, ite_false, Bool.false_eq_true]
  all_goals first | exact ⟨_, _, rfl, rfl, fun _ => hI⟩ | skip
  · -- tick
    simp only [hf0, float.F64.lt, bind_ok]
    by_cases hx0 : x < 0
    · simp only [hx0, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, decide_false]
      exact ⟨_, _, rfl, rfl, fun _ => hI⟩
    · have hb0 : decide (x < 0) = false := decide_eq_false hx0
      simp only [hb0, if_neg hx0, Bool.false_eq_true, not_false_eq_true, decide_true, ite_true]
      tjn_jp
  · -- repeat
    simp only [hf0, float.F64.lt, bind_ok]
    by_cases hx0 : x < 0
    · simp only [hx0, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, decide_false]
      exact ⟨_, _, rfl, rfl, fun _ => hI⟩
    · have hb0 : decide (x < 0) = false := decide_eq_false hx0
      simp only [hb0, if_neg hx0, Bool.false_eq_true, not_false_eq_true, decide_true, ite_true]
      tjn_jp
  · -- tail
    simp only [sim.step.TAIL_LENIENCY, fb64_13853635403745067008, float.F64.lt, bind_ok]
    by_cases hx0 : x < -36
    · simp only [hx0, decide_true, ite_true, bind_ok, Bool.false_eq_true, ite_false]
      exact ⟨_, _, rfl, rfl, fun _ => hI⟩
    · have hb0 : decide (x < -36) = false := decide_eq_false hx0
      simp only [hb0, if_neg hx0, Bool.false_eq_true, ite_false]
      obtain ⟨lt, hlt, elt⟩ := sim.step.last_tick_index_refines (c.pb.objects.val[i.val]'hi)
      rw [hlt]; simp only [bind_ok]
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, simM_bind]
      rw [sim_tjn_last_loop tn _ _ (c.pb.objects.val[i.val]'hi) _ (fun _ _ => rfl) _ 0 none (by simp [topS])]
      simp only [List.drop_zero, ← elt, Except.bind]
      cases lt with
      | none =>
        simp only [Option.map_none]
        tjn_jp
      | some k =>
        simp only [Option.map_some]
        have hkl : k.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by
          rcases sim_simLastP_lt simIsTR _ 0 none k.val elt.symm with h | h
          · simpa using h
          · cases h
        have hck : (UScalar.hcast .I64 k).val = (k.val : Int) := sim_usize_to_i64 k (by omega)
        have hsk : simSRefOk s ⟨i, UScalar.hcast .I64 k⟩ := ⟨ho, fun _ => by
          show (UScalar.hcast .I64 k).val.toNat < _; rw [hck, hnl]; simpa using hkl⟩
        obtain ⟨bk, hbk, ebk⟩ := sim.step.judged_refines tn fo c s _ hsk
        have ebk' : OsuModel.Sim.Sim.judged (i.val, (k.val : Int)) (simCtxS tn fo c) (simStS tn s) =
            .ok (bk, simStS tn s) := by
          rw [← ebk]; congr 2; simp [abs, hck]
        simp only [lift, bind_ok, hbk, simM_bind, ebk', Except.bind]
        cases bk
        · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
          exact ⟨_, _, rfl, rfl, fun _ => hI⟩
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          tjn_jp


def simHF (n : Nat) : Option sim.state.Res → Nat
  | some x => if (hrS x.ty).isHit then n + 1 else n
  | none => n

theorem sim_count_hits_loop (os : sim.state.OState) (hsm : os.nested.val.length < 2 ^ 63) :
    ∀ k (j : Usize) (h : U64), os.nested.val.length - j.val = k → j.val ≤ os.nested.val.length → h.val ≤ j.val →
    ∃ r, sim.step.count_nested_hits_loop os h j = ok r ∧ r.val = (os.nested.val.drop j.val).foldl simHF h.val := by
  intro k
  induction k with
  | zero =>
    intro j h hk hj hh
    refine ⟨h, ?_, by simp [List.drop_of_length_le (show os.nested.val.length ≤ j.val by omega)]⟩
    unfold sim.step.count_nested_hits_loop
    rw [loop_unfold]
    have : ¬ j < alloc.vec.Vec.len os.nested := by rw [vec_lt_len_iff]; omega
    simp [sim.step.count_nested_hits_loop.body, this]
  | succ k ih =>
    intro j h hk hj hh
    have hlt : j.val < os.nested.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := os.nested.property; omega)
    have hd : os.nested.val.drop j.val = os.nested.val[j.val]'hlt :: os.nested.val.drop j1.val := by
      rw [hj1v]; exact List.drop_eq_getElem_cons hlt
    have hl : j < alloc.vec.Vec.len os.nested := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨h1, hb, hv, hle⟩ : ∃ h1 : U64, sim.step.count_nested_hits_loop.body os h j = ok (.cont (h1, j1)) ∧
        h1.val = simHF h.val (os.nested.val[j.val]'hlt) ∧ h1.val ≤ j1.val := by
      simp only [sim.step.count_nested_hits_loop.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok]
      cases hx : os.nested.val[j.val]'hlt with
      | none => exact ⟨h, by simp [hj1], rfl, by omega⟩
      | some x =>
        obtain ⟨b, hb, eb⟩ := sim.basic.is_hit_refines x.ty
        simp only [hb, bind_ok]
        cases b
        · refine ⟨h, by simp [hj1], ?_, by omega⟩
          simp only [simHF]; rw [show (hrS x.ty).isHit = false from eb]; simp
        · obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U64.add_spec (x := h) (y := 1#u64) (by scalar_tac))
          refine ⟨z, by simp [hz, hj1], ?_, by scalar_tac⟩
          simp only [simHF]; rw [show (hrS x.ty).isHit = true from eb]; simp [hzv]
    obtain ⟨r, e, hr⟩ := ih j1 h1 (by omega) (by omega) hle
    refine ⟨r, ?_, ?_⟩
    · unfold sim.step.count_nested_hits_loop at e ⊢
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]; exact e
    · rw [hr, hd, List.foldl_cons, hv]

-- NOT-CONDITIONAL: (nested count < 2^63, from SimInv.nested_small)
theorem sim.step.count_nested_hits_refines (os : sim.state.OState) (hsm : os.nested.val.length < 2 ^ 63) :
    ∃ r, sim.step.count_nested_hits os = ok r ∧
      r.val = (ostateS os).nested.foldl (fun n r => match r with
        | some (ty, _) => if ty.isHit then n + 1 else n | none => n) 0 := by
  obtain ⟨r, e, h⟩ := sim_count_hits_loop os hsm _ 0#usize 0#u64 rfl (by simp) (by simp)
  refine ⟨r, e, ?_⟩
  rw [h]
  simp only [ostateS, List.foldl_toArray', List.foldl_map]
  have h0 : (0#usize).val = 0 := rfl
  have h0' : (0#u64).val = 0 := rfl
  rw [h0, h0', List.drop_zero]
  congr 1; funext n x; cases x <;> rfl

-- NOT-CONDITIONAL: total
theorem sim.step.slider_result_refines (classic : Bool) (hits total : U64) (mx mn : sim.basic.HitResult) :
    ∃ r, sim.step.slider_result classic hits total mx mn = ok r ∧ hrS r =
      (if classic then (if hits.val == total.val then .great else if hits.val == 0 then .miss else
        if (0.5 : F64) ≤ F64.ofInt hits.val / F64.ofInt total.val then .ok else .meh)
       else if hits.val > 0 then hrS mx else hrS mn) := by
  unfold sim.step.slider_result
  cases classic
  · by_cases h0 : hits > 0#u64
    · have : hits.val > 0 := by scalar_tac
      simp [h0, this]
    · have : ¬ hits.val > 0 := by scalar_tac
      simp [h0, this]
  · by_cases ht : hits = total
    · subst ht; simp [hrS]
    · have ht' : ¬ hits.val = total.val := fun h => ht (by scalar_tac)
      by_cases hz : hits = 0#u64
      · subst hz; have : ¬ (0 : Nat) = total.val := by intro h; apply ht; scalar_tac
        simp [hrS, this]
      · have hz' : ¬ hits.val = 0 := fun h => hz (by scalar_tac)
        simp only [ht, hz, if_false, float.F64.from_u64, float.F64.div, fb64_4602678819172646912, float.F64.le, bind_ok,
          Bool.true_eq_false, if_true, beq_iff_eq, ht', hz']
        split <;> simp_all [hrS]

/-- `slider_check_for_result` (Rust) refines `Sim.sliderCheckForResult` for an unjudged slider (tail index in range). -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.slider_check_for_result_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (i : Usize) (e : Nat) (hI : SimARInv tn fo P b0 n c s e 0 0) (hL : simInstOk c s i.val)
    (hi : i.val < c.pb.objects.val.length)
    (hti : i.val < c.tail_idx.val.length)
    (htl : (c.tail_idx.val[i.val]'hti).val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hres : sim.step.res_of s ⟨i, (-1)#i64⟩ = ok none) :
    ∃ res s', sim.step.slider_check_for_result c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.sliderCheckForResult i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  have ho : i.val < s.objs.val.length := by rw [hI.inv.objs_len]; exact hi
  have hsmall := hI.inv.nested_small _ (List.getElem_mem hi)
  have hnl := hI.inv.nested_len _ ho hi
  have hct : (UScalar.hcast .I64 (c.tail_idx.val[i.val]'hti)).val = ((c.tail_idx.val[i.val]'hti).val : Int) :=
    sim_usize_to_i64 _ (by omega)
  have hst : simSRefOk s ⟨i, UScalar.hcast .I64 (c.tail_idx.val[i.val]'hti)⟩ := ⟨ho, fun _ => by
    show (UScalar.hcast .I64 _).val.toNat < _; rw [hct, hnl]; simpa using htl⟩
  obtain ⟨bt, hbt, ebt⟩ := sim.step.judged_refines tn fo c s _ hst
  have ebt' : OsuModel.Sim.Sim.judged (i.val, ((c.tail_idx.val[i.val]'hti).val : Int)) (simCtxS tn fo c) (simStS tn s) =
      .ok (bt, simStS tn s) := by
    rw [← ebt]; congr 2; simp [abs, hct]
  have etail : OsuModel.Sim.Sim.tailOf i.val (simCtxS tn fo c) (simStS tn s) =
      .ok ((c.tail_idx.val[i.val]'hti).val, simStS tn s) := by
    have hti' : i.val < (simCtxS tn fo c).tailIdx.size := by simpa [simCtxS, abs] using hti
    simp [OsuModel.Sim.Sim.tailOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, Except.bind, simCtxS, abs, hti]
  have hr1 : simRefOk c ⟨i, (-1)#i64⟩ := ⟨hi, fun h => by simp at h⟩
  have eabs1 : (abs (⟨i, (-1)#i64⟩ : sim.step.Ref) : Nat × Int) = (i.val, -1) := by simp [abs]
  have eos := s3a_ostate tn fo c s i.val ho
  have hT : (simStS tn s).t = s.t := rfl
  have hE : (hobjS tn (c.pb.objects.val[i.val]'hi).h).endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
  rw [OsuModel.Sim.Sim.sliderCheckForResult.eq_1]
  unfold sim.step.slider_check_for_result
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, OsuModel.Sim.Sim.st, simM_get, etail, ebt',
    vec_index_eq _ _ hi, vec_index_eq _ _ hti, lift, bind_ok, hbt, hT, hE]
  have hE' : (topS tn (c.pb.objects.val[i.val]'hi)).h.endTime = (c.pb.objects.val[i.val]'hi).h.end_time := rfl
  rw [hE']
  cases bt
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_or, ite_true]
    exact ⟨_, _, rfl, rfl, fun _ => hI⟩
  · by_cases hlt : s.t < (c.pb.objects.val[i.val]'hi).h.end_time
    · simp only [ite_true, float.F64.lt, hlt, decide_true, bind_ok, Bool.not_true, Bool.false_or]
      exact ⟨_, _, rfl, rfl, fun _ => hI⟩
    · simp only [ite_true, float.F64.lt, hlt, decide_false, bind_ok, Bool.not_true, Bool.false_or,
        Bool.false_eq_true, ite_false]
      obtain ⟨sr, hsr, esr⟩ := sim.step.slider_data_refines tn fo c i hi
      have esr' := esr (simStS tn s)
      rw [hsr]; simp only [bind_ok]
      cases sr with
      | Err er =>
        obtain ⟨m, hm⟩ := esr'
        refine ⟨.Err er, s, by simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], ⟨m, ?_⟩, fun h => by cases h⟩
        simp only [simM_bind, hm, Except.bind]
      | Ok sd =>
        have esr2 : OsuModel.Sim.Sim.sliderData i.val (simCtxS tn fo c) (simStS tn s) = .ok (abs sd, simStS tn s) := esr'
        obtain ⟨hits, hh, hhv⟩ := sim.step.count_nested_hits_refines (s.objs.val[i.val]'ho) (by omega)
        obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
        have htot : (UScalar.cast .U64 (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested)).val =
            (topS tn (c.pb.objects.val[i.val]'hi)).nested.size := by
          simp [topS]
        obtain ⟨ty, hty, ety⟩ := sim.step.slider_result_refines sd.classic hits
          (UScalar.cast .U64 (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested))
          (c.pb.objects.val[i.val]'hi).h.max_result (c.pb.objects.val[i.val]'hi).h.min_result
        obtain ⟨res, s', ear, rar, iar⟩ := sim.step.apply_result_refines tn fo E b0 n c hC hCS s f _ ty e hI hr1 hL hres
        refine ⟨res, s', ?_, ?_, iar⟩
        · simp [core.result.Result.Insts.CoreOpsTry.branch, vec_index_eq _ _ ho, hh, hty, hf, ear]
        · rw [eabs1, show (abs ty : OsuModel.Sim.HitResult) = hrS ty from rfl, ety, hhv, htot] at rar
          simp only [simM_bind, esr2, eos, hfS, Except.bind]
          exact rar

end OsuProofs
