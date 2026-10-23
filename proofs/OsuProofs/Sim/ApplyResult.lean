/-
`sim::step::{apply_result, handle_hit, handle_hit_sto, handle_hit_sto_from}` (Rust, mutually recursive with a `fuel`
bound) refine `Sim.applyResult` / `Sim.handleHit`. Proof: strong induction on the fuel with a well-formedness invariant
whose budgets (transform counters, emit counters, as_seen pushes) are charged to the number of unjudged result slots
(`simUnj`), which every `apply_result` decreases by one before it recurses.
-/
import OsuProofs.Sim.EmitProps
import OsuProofs.Sim.ProcPhase
import OsuProofs.Sim3.SB_CS
import OsuProofs.Sim3.SB_AS
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- number of unjudged slots of an object (its own result + its nested results) -/
def simUnjO (o : sim.state.OState) : Nat :=
  (if o.result.isNone then 1 else 0) + (o.nested.val.filter (fun x => x.isNone)).length

/-- number of unjudged slots of the state: bounds the number of judgements still to come -/
def simUnj (s : sim.state.St) : Nat := (s.objs.val.map simUnjO).sum

theorem sim_sum_map_set {α} (f : α → Nat) (l : List α) (i : Nat) (h : i < l.length) (x : α) :
    ((l.set i x).map f).sum + f (l[i]'h) = (l.map f).sum + f x := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have := ih i (by simpa using h); omega

theorem sim_filter_set_none {α} (l : List (Option α)) (j : Nat) (h : j < l.length) (hn : l[j]'h = none) (x : α) :
    ((l.set j (some x)).filter (fun y => y.isNone)).length + 1 = (l.filter (fun y => y.isNone)).length := by
  induction l generalizing j with
  | nil => simp at h
  | cons a t ih =>
    cases j with
    | zero =>
      have e : a = none := hn
      subst e; simp [List.filter_cons]
    | succ j =>
      simp only [List.set_cons_succ, List.filter_cons]
      have := ih j (by simpa using h) (by simpa using hn)
      split <;> (try simp) <;> omega

theorem sim_unjO_result (o : sim.state.OState) (hn : o.result = none) (x : sim.state.Res) :
    simUnjO { o with result := some x } + 1 = simUnjO o := by
  simp [simUnjO, hn]; omega

theorem sim_unjO_nested (o : sim.state.OState) (j : Usize) (h : j.val < o.nested.val.length)
    (hn : o.nested.val[j.val]'h = none) (x : sim.state.Res) :
    simUnjO { o with nested := o.nested.set j (some x) } + 1 = simUnjO o := by
  have := sim_filter_set_none o.nested.val j.val h hn x
  have hv : (o.nested.set j (some x)).val = o.nested.val.set j.val (some x) := by simp [alloc.vec.Vec.set]
  simp only [simUnjO, hv]
  omega

theorem sim_unj_set (s : sim.state.St) (i : Usize) (h : i.val < s.objs.val.length) (o : sim.state.OState)
    (ho : simUnjO o + 1 = simUnjO (s.objs.val[i.val]'h)) :
    simUnj { s with objs := s.objs.set i o } + 1 = simUnj s := by
  have := sim_sum_map_set simUnjO s.objs.val i.val h o
  have hv : (s.objs.set i o).val = s.objs.val.set i.val o := by simp [alloc.vec.Vec.set]
  simp only [simUnj, hv]
  omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the score counters can take `m` more judgements -/
def simScBud (ss : sim.scoring.ScoreSt) (m : Nat) : Prop :=
  ss.judged_hits.val + m ≤ U64.max ∧ (∀ k, k < 18 → (ss.stats.val.getD k 0#u64).val + m ≤ U64.max) ∧
    ss.combo.val + m ≤ U64.max ∧ ss.current_accuracy_judgement_count.val + m ≤ U64.max

/-- both processor pairs and the judgement record list can take `m` more `emit`s -/
def simEmitBud (c : sim.state.Ctx) (s : sim.state.St) (m : Nat) : Prop :=
  (∀ k, sim.mods.FailOverride.Easy k ∈ c.cfg.fail_overrides.val →
      k.val < s.health.retries.val.length ∧ k.val < s.health_rp.retries.val.length) ∧
    s.health.fail_triggers.val + m * (1 + 2 * c.cfg.acc_challenges.val.length) ≤ U64.max ∧
    s.health_rp.fail_triggers.val + m * (1 + 2 * c.cfg.acc_challenges.val.length) ≤ U64.max ∧
    simScBud s.score m ∧ simScBud s.score_rp m ∧ s.out.val.length + m < Usize.max

theorem sim_scBud_mono (ss : sim.scoring.ScoreSt) (m m' : Nat) (h : m' ≤ m) (hb : simScBud ss m) : simScBud ss m' := by
  obtain ⟨a, b, c, d⟩ := hb
  exact ⟨by omega, fun k hk => by have := b k hk; omega, by omega, by omega⟩

theorem sim_emitBud_mono (c : sim.state.Ctx) (s : sim.state.St) (m m' : Nat) (h : m' ≤ m) (hb : simEmitBud c s m) :
    simEmitBud c s m' := by
  obtain ⟨a, b, b2, d, e, f⟩ := hb
  have hm : m' * (1 + 2 * c.cfg.acc_challenges.val.length) ≤ m * (1 + 2 * c.cfg.acc_challenges.val.length) :=
    Nat.mul_le_mul_right _ h
  exact ⟨a, by omega, by omega, sim_scBud_mono _ _ _ h d, sim_scBud_mono _ _ _ h e, by omega⟩

theorem sim_emitOk_of_bud (c : sim.state.Ctx) (s : sim.state.St) (m : Nat) (hb : simEmitBud c s (m + 1)) :
    simEmitOk c s.health s.score ∧ simEmitOk c s.health_rp s.score_rp ∧ s.out.val.length < Usize.max := by
  obtain ⟨a, b, b2, ⟨d1, d2, d3, d4⟩, ⟨e1, e2, e3, e4⟩, f⟩ := hb
  have hm : 1 * (1 + 2 * c.cfg.acc_challenges.val.length) ≤ (m + 1) * (1 + 2 * c.cfg.acc_challenges.val.length) :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨⟨fun k hk => (a k hk).1, by omega, by omega, fun k hk => by have := d2 k hk; omega, by omega, by omega⟩,
    ⟨fun k hk => (a k hk).2, by omega, by omega, fun k hk => by have := e2 k hk; omega, by omega, by omega⟩, by omega⟩

theorem sim_scBud_step (a b : sim.scoring.ScoreSt) (m : Nat) (hs : simScoreStep a b) (hb : simScBud a (m + 1)) :
    simScBud b m := by
  obtain ⟨s1, s2, s3, s4⟩ := hs
  obtain ⟨b1, b2, b3, b4⟩ := hb
  exact ⟨by omega, fun k hk => by have := s4 k hk; have := b2 k hk; omega, by omega, by omega⟩

theorem sim_emitBud_emit (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref) (ty : sim.basic.HitResult) (t : F64)
    (hr : simRefOk c r) (m : Nat) (hb : simEmitBud c s (m + 1)) (s' : sim.state.St)
    (he : sim.step.emit c s r ty t = ok s') :
    simEmitBud c s' m ∧ ∃ hl hr' sl sr v, s' = { s with score := sl, health := hl, score_rp := sr, health_rp := hr', out := v } := by
  obtain ⟨o1, o2, o3⟩ := sim_emitOk_of_bud c s m hb
  obtain ⟨hl, hr', sl, sr, v, hs', hv, p1, p2, p3, p4, p5, p6⟩ := sim.step.emit_props c s r ty t hr o1 o2 o3 s' he
  refine ⟨?_, hl, hr', sl, sr, v, hs'⟩
  subst hs'
  obtain ⟨a, b, b2, d, e, f⟩ := hb
  have hm : (m + 1) * (1 + 2 * c.cfg.acc_challenges.val.length) = m * (1 + 2 * c.cfg.acc_challenges.val.length) +
      (1 + 2 * c.cfg.acc_challenges.val.length) := by rw [Nat.add_mul, Nat.one_mul]
  refine ⟨fun k hk => ⟨by rw [p1]; exact (a k hk).1, by rw [p3]; exact (a k hk).2⟩, by simp only; omega, by simp only; omega,
    sim_scBud_step _ _ _ p5 d, sim_scBud_step _ _ _ p6 e, by simp only; omega⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_sRefOk_of (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s) (r : sim.step.Ref) (hr : simRefOk c r) :
    simSRefOk s r := by
  obtain ⟨ht, hn⟩ := hr
  have ht' : r.top.val < s.objs.val.length := by rw [hinv.objs_len]; exact ht
  exact ⟨ht', fun h0 => by rw [hinv.nested_len _ ht' ht]; exact hn h0⟩

/-- object `i` has its pooled instances (it became alive at least once): top / head instances and its spinner-tick
instances are in range, and every spinner-tick reference of it has a tick-instance slot. Objects whose lifetime passed
between two steps never get instances (Future → Past directly), so this holds only for alive (and killed) objects. -/
def simInstOk (c : sim.state.Ctx) (s : sim.state.St) (i : Nat) : Prop :=
  ∃ h : i < s.objs.val.length, (s.objs.val[i]'h).inst.val < s.insts.val.length ∧
    (s.objs.val[i]'h).head_inst.val < s.insts.val.length ∧
    (∀ j (hj : j < (s.objs.val[i]'h).tick_insts.val.length),
      ((s.objs.val[i]'h).tick_insts.val[j]'hj).val < s.insts.val.length) ∧
    (∀ r, simRefOk c r → r.top.val = i → ((simHobj c r).kind = .SpinnerTick ∨ (simHobj c r).kind = .SpinnerBonusTick) →
      r.nested.val.toNat < (s.objs.val[i]'h).tick_insts.val.length)

/-- every alive-dictionary entry has its instances (D67b, restricted: pristine / never-alive objects have none) -/
def simIK (c : sim.state.Ctx) (s : sim.state.St) : Prop :=
  ∀ x, some x ∈ s.dict_slots.val → simInstOk c s x.val

/-- `apply_result` at fuel `f` refines `Sim.applyResult` from every unjudged reference, preserving the invariant `I` -/
def simAROk (tn : Nat → String) (fo : alloc.vec.Vec Usize) (I : sim.state.St → Nat → Prop) (c : sim.state.Ctx)
    (f : U64) : Prop :=
  ∀ s r ty e, I s e → simRefOk c r → simInstOk c s r.top.val → sim.step.res_of s r = ok none →
    ∃ res s', sim.step.apply_result c s f r ty = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyResult f.val (abs r) (abs ty) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → I s' e ∧ s'.dict_slots = s.dict_slots)

theorem sim_forIn_cons_simM {α} (x : α) (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) :
    forIn (x :: l) PUnit.unit F C S = (F x PUnit.unit C S).bind (fun p => match p.1 with
      | .done b => .ok (b, p.2) | .yield b => forIn l b F C p.2) := by
  rw [List.forIn_cons]; simp only [simM_bind]
  congr 1; funext p; rcases p with ⟨_ | _, S'⟩ <;> rfl

theorem sim_sto_from_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (I : sim.state.St → Nat → Prop)
    (c : sim.state.Ctx) (hI : ∀ s e, I s e → SimInv c s) (hD : ∀ s e, I s e → simIK c s) (f : U64)
    (hAR : simAROk tn fo I c f) (D : alloc.vec.Vec (Option Usize))
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
        obtain ⟨res, s1, e1, r1, i1⟩ := hAR s o (simHobj c o).min_result e hs hor hoL hres
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
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_enumL_top_mem (objs : Array OsuModel.Sim.TopObj) (target : F64) :
    ∀ (l : List Nat), ∀ r ∈ simEnumL objs target l, r.1 ∈ l := by
  intro l
  induction l with
  | nil => intro r hr; simp [simEnumL] at hr
  | cons i t ih =>
    intro r hr
    simp only [simEnumL] at hr
    split at hr
    · rw [List.mem_append, List.mem_cons] at hr
      rcases hr with (hr | hr) | hr
      · subst hr; exact List.mem_cons_self
      · simp only [simNestedTW, List.mem_map] at hr
        obtain ⟨j, _, hjr⟩ := hr
        subst hjr; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih r hr)
    · simp at hr

/-- the references `enumerate_up_to` returns belong to alive-dictionary entries -/
theorem sim_enum_refs_dict (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (target : F64) (hinv : SimInv c s)
    (objs : alloc.vec.Vec sim.step.Ref)
    (eo : OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) = .ok (abs objs, simStS tn s)) :
    ∀ o ∈ objs.val, some o.top ∈ s.dict_slots.val := by
  have hS : ∀ i ∈ ((simStS tn s).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro i hi
    simp [simStS, abs] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hinv.dict_in _ ha a rfl
  rw [simS_enumerateUpTo _ _ _ hS] at eo
  have e := congrArg (fun e => match e with | .ok p => p.1.toList | .error _ => []) eo
  simp only [List.toList_toArray] at e
  intro o ho
  have hmem : (abs o : OsuModel.Sim.Ref) ∈ simEnumL (simCtxS tn fo c).pb.objects target
      (simSortL (fun a b => decide (simKeyS (simCtxS tn fo c) a < simKeyS (simCtxS tn fo c) b))
        ((simStS tn s).dictSlots.filterMap id).toList) := by
    rw [e]; simp [abs]; exact ⟨o, ho, rfl, rfl⟩
  have h1 := sim_simSortL_mem _ _ _ (sim_enumL_top_mem _ target _ _ hmem)
  simp [simStS, abs] at h1
  obtain ⟨a, ha, hai⟩ := h1
  have : a = o.top := by
    apply UScalar.eq_of_val_eq; simpa [abs] using hai
  rw [← this]; exact ha

theorem sim_handle_hit (tn : Nat → String) (fo : alloc.vec.Vec Usize) (I : sim.state.St → Nat → Prop)
    (c : sim.state.Ctx) (hI : ∀ s e, I s e → SimInv c s) (hD : ∀ s e, I s e → simIK c s)
    (hcap : ∀ s e, I s e → ∀ target v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) =
      .ok (v, simStS tn s) → v.size < Usize.max)
    (f : U64) (hAR : simAROk tn fo I c f) (s : sim.state.St) (r : sim.step.Ref) (e : Nat) (hs : I s e)
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
      obtain ⟨res, s', e1, r1, i1⟩ := sim_sto_from_loop tn fo I c hI hD f hAR s.dict_slots (alloc.vec.Vec.deref objs)
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
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- objects keep their instance indices (results may change) -/
def simKeep (s s' : sim.state.St) : Prop :=
  s'.objs.val.length = s.objs.val.length ∧ ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
    (s'.objs.val[j]'h').inst = (s.objs.val[j]'h).inst ∧ (s'.objs.val[j]'h').head_inst = (s.objs.val[j]'h).head_inst ∧
    (s'.objs.val[j]'h').tick_insts = (s.objs.val[j]'h).tick_insts

theorem sim_keep_of_objFrame {s s' : sim.state.St} (h : s3b_objFrame s s') : simKeep s s' := by
  obtain ⟨hl, hj⟩ := h
  exact ⟨hl, fun j h1 h2 => ⟨(hj j h1 h2).1, (hj j h1 h2).2.1, (hj j h1 h2).2.2.1⟩⟩

theorem sim_instOk_keep {c : sim.state.Ctx} {s s' : sim.state.St} (hk : simKeep s s')
    (hl : s.insts.val.length ≤ s'.insts.val.length) {i : Nat} (h : simInstOk c s i) : simInstOk c s' i := by
  obtain ⟨hi, x, y, z, w⟩ := h
  have hi' : i < s'.objs.val.length := by rw [hk.1]; exact hi
  obtain ⟨a, b, d⟩ := hk.2 i hi hi'
  refine ⟨hi', by rw [a]; omega, by rw [b]; omega, fun j hj => ?_, fun r hr ht hkd => by rw [d]; exact w r hr ht hkd⟩
  have hj' : j < (s.objs.val[i]'hi).tick_insts.val.length := by rw [← d]; exact hj
  have : ((s'.objs.val[i]'hi').tick_insts.val[j]'hj) = ((s.objs.val[i]'hi).tick_insts.val[j]'hj') := by simp only [d]
  rw [this]; have := z j hj'; omega

theorem sim_ik_keep {c : sim.state.Ctx} {s s' : sim.state.St} (hk : simKeep s s') (hl : s'.insts.val.length = s.insts.val.length)
    (hd : s'.dict_slots = s.dict_slots) (h : simIK c s) : simIK c s' := by
  intro x hx
  rw [hd] at hx
  exact sim_instOk_keep hk (by omega) (h x hx)

theorem sim_keep_set (s : sim.state.St) (i : Usize) (hi : i.val < s.objs.val.length) (o' : sim.state.OState)
    (hin : o'.inst = (s.objs.val[i.val]'hi).inst) (hhd : o'.head_inst = (s.objs.val[i.val]'hi).head_inst)
    (htk : o'.tick_insts = (s.objs.val[i.val]'hi).tick_insts) : simKeep s { s with objs := s.objs.set i o' } := by
  have hv : (s.objs.set i o').val = s.objs.val.set i.val o' := by simp [alloc.vec.Vec.set]
  have hlen : (s.objs.set i o').val.length = s.objs.val.length := by rw [hv]; simp
  refine ⟨hlen, fun j h h' => ?_⟩
  change ((s.objs.set i o').val[j]'h').inst = (s.objs.val[j]'h).inst ∧
    ((s.objs.set i o').val[j]'h').head_inst = (s.objs.val[j]'h).head_inst ∧
    ((s.objs.set i o').val[j]'h').tick_insts = (s.objs.val[j]'h).tick_insts
  simp only [hv, List.getElem_set]
  split
  · rename_i hij; subst hij; exact ⟨hin, hhd, htk⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem sim_keep_refl (s : sim.state.St) : simKeep s s := ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem sim_sum_map_congr {α} (f g : α → Nat) (l l' : List α) (hl : l'.length = l.length)
    (h : ∀ j (h : j < l.length) (h' : j < l'.length), g (l'[j]'h') = f (l[j]'h)) : (l'.map g).sum = (l.map f).sum := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a t ih =>
    cases l' with
    | nil => simp at hl
    | cons a' t' =>
      simp only [List.map_cons, List.sum_cons]
      have h0 := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      rw [h0, ih t' (by simpa using hl) (fun j hj hj' => by
        have := h (j + 1) (by simpa using hj) (by simpa using hj'); simpa using this)]

theorem sim_unj_objFrame {s s' : sim.state.St} (h : s3b_objFrame s s') : simUnj s' = simUnj s := by
  obtain ⟨hl, hj⟩ := h
  unfold simUnj
  apply sim_sum_map_congr _ _ _ _ hl
  intro j h1 h2
  obtain ⟨_, _, _, e4, e5⟩ := hj j h1 h2
  simp only [simUnjO, e4, e5]

theorem sim_enum_transfer (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s s' : sim.state.St)
    (hinv : SimInv c s) (hd : s'.dict_slots = s.dict_slots)
    (hcap : ∀ target v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) =
      .ok (v, simStS tn s) → v.size < Usize.max) :
    ∀ target v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s') =
      .ok (v, simStS tn s') → v.size < Usize.max := by
  have hS : ∀ (t : sim.state.St), t.dict_slots = s.dict_slots →
      ∀ i ∈ ((simStS tn t).dictSlots.filterMap id), i < (simCtxS tn fo c).pb.objects.size := by
    intro t ht i hi
    simp [simStS, abs, ht] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [← hai]; simpa using hinv.dict_in _ ha a rfl
  have hdS : (simStS tn s').dictSlots = (simStS tn s).dictSlots := by simp [simStS, hd]
  intro target v hv
  rw [simS_enumerateUpTo _ _ _ (hS s' hd)] at hv
  have hv' := hcap target _ (simS_enumerateUpTo (target := target) _ _ (hS s rfl))
  simp only [Except.ok.injEq, Prod.mk.injEq] at hv
  rw [← hv.1, hdS]; exact hv'
end OsuProofs


namespace OsuProofs
open OsuImpl OsuModel.Net

/-- what `apply_result` needs of the context (all established by `mk_ctx`) -/
structure SimARCtx (c : sim.state.Ctx) : Prop where
  hd : ∀ i (hi : i < c.pb.objects.val.length), ∃ hhi : i < c.head_idx.val.length, (c.head_idx.val[i]'hhi).val < 2 ^ 63 ∧
    (((c.pb.objects.val[i]'hi).h.kind = .Slider ∨ ∃ r, simRefOk c r ∧ r.top.val = i ∧ (simHobj c r).kind = .Head) →
      (c.head_idx.val[i]'hhi).val < (c.pb.objects.val[i]'hi).nested.val.length)
  pre : ∀ r, simRefOk c r → (∃ d ∈ c.cfg.dyn_rates.val, s3b_isAd d = true) → s3b_precOk c r
  tkn : ∀ r, simRefOk c r → ((simHobj c r).kind = .SpinnerTick ∨ (simHobj c r).kind = .SpinnerBonusTick) →
    0 ≤ r.nested.val

/-- the `apply_result` invariant. `e`: judgements already owed to `emit` (pending in callers); `ut`/`us`: one transform /
`as_seen` budget unit already released by the current judgement (its slot is judged but its hooks have not run). -/
structure SimARInv (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b0 n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (e ut us : Nat) : Prop where
  inv : SimInv c s
  tf : s3b_TfInv P (b0 + (simUnj s + ut) * (n + n + 4)) s
  ik : simIK c s
  em : simEmitBud c s (simUnj s + e)
  sp : c.cfg.dyn_rates.val.length ≤ s.speed.val.length
  cnt : (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_target.val.length ∧
    (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_recent.val.length ∧
    (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_seen.val.length
  seen : ∀ l ∈ s.as_seen.val, l.val.length + simUnj s + us < Usize.max
  enum : ∀ target v, OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) =
    .ok (v, simStS tn s) → v.size < Usize.max

theorem sim_tfInv_mono {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b b' : Nat) (s : sim.state.St)
    (hb : b' ≤ b) (h : s3b_TfInv P b s) : s3b_TfInv P b' s :=
  fun ins hins => ⟨E.mono _ _ _ hb (h ins hins).1, E.mono _ _ _ hb (h ins hins).2⟩

theorem sim_mul_le (a a' k : Nat) (h : a' ≤ a) : a' * k ≤ a * k := Nat.mul_le_mul_right _ h

/-- T1: writing the result of an unjudged slot (same instances, same nested length, one slot fewer unjudged) -/
theorem sim_ar_inv_set (tn fo P b0 n c s e) (i : Usize) (hi : i.val < s.objs.val.length) (o' : sim.state.OState)
    (hI : SimARInv tn fo P b0 n c s e 0 0)
    (hin : o'.inst = (s.objs.val[i.val]'hi).inst) (hhd : o'.head_inst = (s.objs.val[i.val]'hi).head_inst)
    (htk : o'.tick_insts = (s.objs.val[i.val]'hi).tick_insts)
    (hnl : o'.nested.val.length = (s.objs.val[i.val]'hi).nested.val.length)
    (hu : simUnjO o' + 1 = simUnjO (s.objs.val[i.val]'hi)) :
    SimARInv tn fo P b0 n c { s with objs := s.objs.set i o' } (e + 1) 1 1 := by
  have hU := sim_unj_set s i hi o' hu
  have hv : (s.objs.set i o').val = s.objs.val.set i.val o' := by simp [alloc.vec.Vec.set]
  have hlen : (s.objs.set i o').val.length = s.objs.val.length := by rw [hv]; simp
  have hget : ∀ j (h : j < s.objs.val.length) (h' : j < (s.objs.set i o').val.length),
      (s.objs.set i o').val[j]'h' = if i.val = j then o' else s.objs.val[j]'h := by
    intro j h h'; simp only [hv, List.getElem_set]
  have hkeep : simKeep s { s with objs := s.objs.set i o' } := by
    refine ⟨hlen, fun j h h' => ?_⟩
    change ((s.objs.set i o').val[j]'h').inst = (s.objs.val[j]'h).inst ∧
      ((s.objs.set i o').val[j]'h').head_inst = (s.objs.val[j]'h).head_inst ∧
      ((s.objs.set i o').val[j]'h').tick_insts = (s.objs.val[j]'h).tick_insts
    rw [hget j h h']
    split
    · rename_i hij; subst hij; exact ⟨hin, hhd, htk⟩
    · exact ⟨rfl, rfl, rfl⟩
  obtain ⟨hinv, htf, hik, hem, hsp, hcnt, hseen, henum⟩ := hI
  refine ⟨⟨?_, ?_, hinv.nested_small, hinv.dict_in, hinv.dict_small⟩, ?_, sim_ik_keep hkeep rfl rfl hik,
    ?_, hsp, hcnt, ?_, sim_enum_transfer tn fo c s _ hinv rfl henum⟩
  · show (s.objs.set i o').val.length = _; rw [hlen]; exact hinv.objs_len
  · intro j h1 h2
    show ((s.objs.set i o').val[j]'h1).nested.val.length = _
    have h1' : j < s.objs.val.length := by rw [← hlen]; exact h1
    rw [hget j h1' h1]
    split
    · rename_i hij; subst hij; rw [hnl]; exact hinv.nested_len _ h1' h2
    · exact hinv.nested_len _ h1' h2
  · intro ins hins; exact htf ins (by simpa using hins) |> fun x => by
      have : b0 + (simUnj { s with objs := s.objs.set i o' } + 1) * (n + n + 4) = b0 + (simUnj s + 0) * (n + n + 4) := by
        rw [Nat.add_zero, ← hU]
      rw [this]; exact x
  · show simEmitBud c s _
    have : simUnj { s with objs := s.objs.set i o' } + (e + 1) = simUnj s + e := by omega
    rw [this]; exact hem
  · intro l hl
    have := hseen l hl; omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_emitBud_congr (c : sim.state.Ctx) (s s' : sim.state.St) (m : Nat) (h1 : s'.score = s.score)
    (h2 : s'.health = s.health) (h3 : s'.score_rp = s.score_rp) (h4 : s'.health_rp = s.health_rp) (h5 : s'.out = s.out)
    (h : simEmitBud c s m) : simEmitBud c s' m := by
  unfold simEmitBud; rw [h1, h2, h3, h4, h5]; exact h

/-- T2: a state hook (update_state / tick_state / nothing) that keeps the objects' instances and results -/
theorem sim_ar_inv_hook (tn fo P b0 n c s E ut us ut') (hI : SimARInv tn fo P b0 n c s E ut us) (s' : sim.state.St)
    (hinv' : SimInv c s') (hof : s3b_objFrame s s') (hil : s'.insts.val.length = s.insts.val.length)
    (htf : s3b_TfInv P (b0 + (simUnj s + ut') * (n + n + 4)) s')
    (h1 : s'.score = s.score) (h2 : s'.health = s.health) (h3 : s'.score_rp = s.score_rp)
    (h4 : s'.health_rp = s.health_rp) (h5 : s'.out = s.out) (h6 : s'.as_target = s.as_target)
    (h7 : s'.as_recent = s.as_recent) (h8 : s'.as_seen = s.as_seen) (h9 : s'.speed = s.speed)
    (h10 : s'.dict_slots = s.dict_slots) :
    SimARInv tn fo P b0 n c s' E ut' us := by
  have hU := sim_unj_objFrame hof
  have hk := sim_keep_of_objFrame hof
  obtain ⟨hinv, htf0, hik, hem, hsp, hcnt, hseen, henum⟩ := hI
  refine ⟨hinv', by rw [hU]; exact htf, sim_ik_keep hk hil h10 hik, ?_, by rw [h9]; exact hsp,
    by rw [h6, h7, h8]; exact hcnt, by rw [h8, hU]; exact hseen, sim_enum_transfer tn fo c s s' hinv h10 henum⟩
  rw [hU]; exact sim_emitBud_congr c s s' _ h1 h2 h3 h4 h5 hem

/-- T5: the adaptive-speed hook (only the three AS fields change; each `as_seen` list grows by at most one) -/
theorem sim_ar_inv_as (tn fo P b0 n c s E) (hI : SimARInv tn fo P b0 n c s E 0 1)
    (a : alloc.vec.Vec F64) (b : alloc.vec.Vec (alloc.vec.Vec F64)) (d : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref))
    (hinv' : SimInv c { s with as_target := a, as_recent := b, as_seen := d })
    (ha : a.val.length = s.as_target.val.length) (hb : b.val.length = s.as_recent.val.length)
    (hd : d.val.length = s.as_seen.val.length)
    (hg : ∀ i (h : i < s.as_seen.val.length) (h' : i < d.val.length), (d.val[i]'h').val.length ≤ (s.as_seen.val[i]'h).val.length + 1) :
    SimARInv tn fo P b0 n c { s with as_target := a, as_recent := b, as_seen := d } E 0 0 := by
  obtain ⟨hinv, htf, hik, hem, hsp, hcnt, hseen, henum⟩ := hI
  refine ⟨hinv', htf, hik, hem, hsp, ?_, ?_, sim_enum_transfer tn fo c s _ hinv rfl henum⟩
  · show _ ≤ a.val.length ∧ _ ≤ b.val.length ∧ _ ≤ d.val.length
    rw [ha, hb, hd]; exact hcnt
  · intro l hl
    change l ∈ d.val at hl
    show l.val.length + simUnj s + 0 < Usize.max
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < s.as_seen.val.length := by rw [← hd]; exact hi
    have := hg i hi' hi
    have := hseen _ (List.getElem_mem hi')
    omega

/-- T6: `emit` (pays one pending judgement) -/
theorem sim_ar_inv_emit (tn fo P b0 n c s e) (hI : SimARInv tn fo P b0 n c s (e + 1) 0 0) (r : sim.step.Ref)
    (ty : sim.basic.HitResult) (t : F64) (hr : simRefOk c r) (s' : sim.state.St) (he : sim.step.emit c s r ty t = ok s') :
    SimARInv tn fo P b0 n c s' e 0 0 := by
  obtain ⟨hinv, htf, hik, hem, hsp, hcnt, hseen, henum⟩ := hI
  obtain ⟨hb, hl, hr', sl, sr, v, rfl⟩ := sim_emitBud_emit c s r ty t hr (simUnj s + e) hem s' he
  exact ⟨s3b_inv_of hinv rfl rfl, htf, hik, hb, hsp, hcnt, hseen, sim_enum_transfer tn fo c s _ hinv rfl henum⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_stS_objs_set (tn) (s : sim.state.St) (i : Usize) (h : i.val < s.objs.val.length) (o' : sim.state.OState)
    (f : OsuModel.Sim.OState → OsuModel.Sim.OState) (hf : f (ostateS (s.objs.val[i.val]'h)) = ostateS o')
    (S : OsuModel.Sim.St) (hS : S = simStS tn s) (j : Nat) (hj : j = i.val) :
    { S with objs := S.objs.modify j f } = simStS tn { s with objs := s.objs.set i o' } := by
  subst hS hj
  have e : (simStS tn s).objs.modify i.val f = (simStS tn { s with objs := s.objs.set i o' }).objs := by
    show (s.objs.val.map ostateS).toArray.modify i.val f = ((s.objs.set i o').val.map ostateS).toArray
    rw [s3b_arr_modify_toArray _ _ _ h, hf]
    simp [alloc.vec.Vec.set, List.map_set]
  rw [e]; rfl

theorem sim_modifyObj_stS (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (i : Usize) (h : i.val < s.objs.val.length)
    (o' : sim.state.OState) (f : OsuModel.Sim.OState → OsuModel.Sim.OState)
    (hf : f (ostateS (s.objs.val[i.val]'h)) = ostateS o') (j : Nat) (hj : j = i.val) :
    OsuModel.Sim.Sim.modifyObj j f C (simStS tn s) = .ok ((), simStS tn { s with objs := s.objs.set i o' }) := by
  rw [s3b_modifyObj_ok _ _ _ _ (by subst hj; simpa using h)]
  rw [sim_stS_objs_set tn s i h o' f hf _ rfl j hj]


theorem sim_hobjS_kind (tn : Nat → String) (h : sim.playable.HObj) : (hobjS tn h).kind = kindS h.kind := rfl
theorem sim_armedS_ite (b : Bool) :
    armedS (if b = true then .Hit else .Miss) = if b = true then OsuModel.Sim.Armed.hit else .miss := by cases b <;> rfl
theorem sim_ns_ok (b : Bool) : (if b = true then ok sim.state.Armed.Hit else ok sim.state.Armed.Miss : Result sim.state.Armed) =
    ok (if b = true then .Hit else .Miss) := by cases b <;> rfl

/-- the custom-state obligation of `update_state_refines`, for every in-range object (`s3b_csOk_of` gives it when no
`Wiggle` mod is active) -/
def simCSH (P : Nat → sim.transforms.TObj → Prop) (n : Nat) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) : Prop :=
  ∀ (i : Usize) p ns (hi : i.val < c.pb.objects.val.length) (hhi : i.val < c.head_idx.val.length),
    (c.head_idx.val[i.val]'hhi).val < 2 ^ 63 →
    (p = sim.step.Part.Head → (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length) →
    s3b_CSOk P n tn fo c i p ns

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

set_option hygiene false in
/-- the part of `apply_result` after the state hook: adaptive speed, the handle-hit recursion and `emit` -/
macro "sim_ar_cont" : tactic => `(tactic| (
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
      obtain ⟨res3, s3, e3, r3, i3⟩ := sim_handle_hit tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0) c
        (fun _ _ h => h.inv) (fun _ _ h => h.ik) (fun _ _ h => h.enum) i (hAR i (by omega)) _ r (e + 1) hI2 hr
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
        obtain ⟨hI3, hd3⟩ := i3 rfl
        obtain ⟨o1, o2, o3⟩ := sim_emitOk_of_bud c s3 (simUnj s3 + e) (by exact hI3.em)
        obtain ⟨s4, e4, eS4⟩ := sim.step.emit_refines tn fo c s3 r ty s.t hr o1 o2 o3
        obtain ⟨_, _, _, _, _, _, hs4⟩ := sim_emitBud_emit c s3 r ty s.t hr _ hI3.em s4 e4
        refine ⟨.Ok (), s4, by simp [core.result.Result.Insts.CoreOpsTry.branch, e4], ?_,
          fun _ => ⟨sim_ar_inv_emit tn fo P b0 n c s3 e hI3 r ty s.t hr s4 e4,
            by rw [hs4]; exact hd3.trans (hd1.trans hd0)⟩⟩
        simp only [simRelM]; exact eS4))

set_option hygiene false in
/-- `apply_result` after the result write (state `s0`, invariant `hI0`) -/
macro "sim_ar_tail" : tactic => `(tactic| (
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
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1⟩ := sim.step.update_state_refines tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Top (if b = true then .Hit else .Miss) false 1#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun h => by cases h)) hio hk1 hk2 hhi hhb (fun h => h.elim (fun h' => by cases h') (fun h' => hhn (Or.inl h')))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .top (if b = true then .hit else .miss) false 1
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_ar_cont
  case Slider =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1⟩ := sim.step.update_state_refines tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Top (if b = true then .Hit else .Miss) false 1#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun h => by cases h)) hio hk1 hk2 hhi hhb (fun h => h.elim (fun h' => by cases h') (fun h' => hhn (Or.inl h')))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .top (if b = true then .hit else .miss) false 1
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_ar_cont
  case Spinner =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1⟩ := sim.step.update_state_refines tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Top (if b = true then .Hit else .Miss) false 1#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun h => by cases h)) hio hk1 hk2 hhi hhb (fun h => h.elim (fun h' => by cases h') (fun h' => hhn (Or.inl h')))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .top (if b = true then .hit else .miss) false 1
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_ar_cont
  case Head =>
    obtain ⟨_, hk1, hk2, _⟩ := hL0
    obtain ⟨hhi, hhb, hhn⟩ := hC.hd r.top.val hr.1
    obtain ⟨s1, e1, eS1, inv1, tf1, il1, ol1, fo1, fr1, of1⟩ := sim.step.update_state_refines tn fo E
      (b0 + simUnj s0 * (n + n + 4)) n c s0 r.top .Head (if b = true then .Hit else .Miss) false 2#u64 hI0.inv htf0
      (hCS _ _ _ hr.1 hhi hhb (fun _ => hhn (Or.inr ⟨r, hr, rfl, hk⟩))) hio hk1 hk2 hhi hhb (fun _ => hhn (Or.inr ⟨r, hr, rfl, hk⟩))
    have eS1' : OsuModel.Sim.Sim.updateState (abs r : Nat × Int).1 .head (if b = true then .hit else .miss) false 2
        (simCtxS tn fo c) (simStS tn s0) = .ok ((), simStS tn s1) := by rw [← sim_armedS_ite]; exact eS1
    simp only [e1, bind_ok, simM_bind]
    rw [eS1', s3b_ebok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s1 inv1 of1 il1
      (by rw [Nat.add_zero]; exact tf1) fr1.1 fr1.2.1 fr1.2.2.1 fr1.2.2.2.1 fr1.2.2.2.2.1 fr1.2.2.2.2.2.1
      fr1.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.1 fr1.2.2.2.2.2.2.2.2.2.2
    have hd1 : s1.dict_slots = s0.dict_slots := fr1.2.2.2.2.2.2.2.2.2.2
    sim_ar_cont
  case Tick =>
    simp only [bind_ok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s0 hI0.inv (s3b_objFrame_of_eq rfl) rfl
      (sim_tfInv_mono E _ _ s0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hI0.tf)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hd1 : s0.dict_slots = s0.dict_slots := rfl
    generalize s0 = s1 at hI1 hd0 hd1 ⊢
    sim_ar_cont
  case Repeat =>
    simp only [bind_ok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s0 hI0.inv (s3b_objFrame_of_eq rfl) rfl
      (sim_tfInv_mono E _ _ s0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hI0.tf)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hd1 : s0.dict_slots = s0.dict_slots := rfl
    generalize s0 = s1 at hI1 hd0 hd1 ⊢
    sim_ar_cont
  case Tail =>
    simp only [bind_ok]
    have hI1 := sim_ar_inv_hook tn fo P b0 n c s0 (e + 1) 1 1 0 hI0 s0 hI0.inv (s3b_objFrame_of_eq rfl) rfl
      (sim_tfInv_mono E _ _ s0 (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hI0.tf)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hd1 : s0.dict_slots = s0.dict_slots := rfl
    generalize s0 = s1 at hI1 hd0 hd1 ⊢
    sim_ar_cont
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
    have hd1 : s1.dict_slots = s0.dict_slots := by rw [hs1]
    sim_ar_cont
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
    have hd1 : s1.dict_slots = s0.dict_slots := by rw [hs1]
    sim_ar_cont))

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim_ar_step (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c)
    (fuel : U64) (hAR : ∀ f : U64, f.val < fuel.val → simAROk tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0) c f) :
    simAROk tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0) c fuel := by
  intro s r ty e hI hr hL hres
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
    have hL0 := sim_instOk_keep (sim_keep_set s r.top ht { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ }
      rfl rfl rfl) (Nat.le_refl _) hL
    have hd0 : ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ } } :
      sim.state.St).dict_slots = s.dict_slots := rfl
    generalize ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with result := some ⟨ty, s.t⟩ } } :
      sim.state.St) = s0 at hI0 hL0 hd0 ⊢
    sim_ar_tail
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
      simp [ostateS, alloc.vec.Vec.set, List.map_set, hcv, abs]; rfl
    have hI0 := sim_ar_inv_set tn fo P b0 n c s e r.top ht { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) }
      hI rfl rfl rfl (by simp [alloc.vec.Vec.set]) (sim_unjO_nested _ _ hnl' hnone _)
    have hL0 := sim_instOk_keep (sim_keep_set s r.top ht { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) }
      rfl rfl rfl) (Nat.le_refl _) hL
    have hd0 : ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) } } :
      sim.state.St).dict_slots = s.dict_slots := rfl
    generalize ({ s with objs := s.objs.set r.top { s.objs.val[r.top.val]'ht with
      nested := (s.objs.val[r.top.val]'ht).nested.set (IScalar.hcast .Usize r.nested) (some ⟨ty, s.t⟩) } } :
      sim.state.St) = s0 at hI0 hL0 hd0 ⊢
    sim_ar_tail
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim_ar_all (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) :
    ∀ N (fuel : U64), fuel.val ≤ N → simAROk tn fo (fun s e => SimARInv tn fo P b0 n c s e 0 0) c fuel := by
  intro N
  induction N with
  | zero =>
    intro fuel hf
    exact sim_ar_step tn fo E b0 n c hC hCS fuel (fun f hlt => absurd hlt (by omega))
  | succ N ih =>
    intro fuel hf
    exact sim_ar_step tn fo E b0 n c hC hCS fuel (fun f hlt => ih f (by omega))

/-- `DrawableHitObject.ApplyResult` + the `NewResult` chain (HandleHit recursion bounded by `fuel`), from an unjudged
reference under the `apply_result` invariant (which it re-establishes on success). -/
-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.apply_result_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c)
    (s : sim.state.St) (fuel : U64) (r : sim.step.Ref) (ty : sim.basic.HitResult) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hr : simRefOk c r) (hL : simInstOk c s r.top.val)
    (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.apply_result c s fuel r ty = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyResult fuel.val (abs r) (abs ty) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  obtain ⟨res, s', e1, r1, i1⟩ := sim_ar_all tn fo E b0 n c hC hCS fuel.val fuel (Nat.le_refl _) s r ty e hI hr hL hres
  exact ⟨res, s', e1, r1, fun h => (i1 h).1⟩

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.handle_hit_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c)
    (s : sim.state.St) (fuel : U64) (r : sim.step.Ref) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hr : simRefOk c r) :
    ∃ res s', sim.step.handle_hit c s fuel r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.handleHit fuel.val (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  obtain ⟨res, s', e1, r1, i1⟩ := sim_handle_hit tn fo _ c (fun _ _ h => h.inv) (fun _ _ h => h.ik) (fun _ _ h => h.enum) fuel
    (sim_ar_all tn fo E b0 n c hC hCS fuel.val fuel (Nat.le_refl _)) s r e hI hr
  exact ⟨res, s', e1, r1, fun h => (i1 h).1⟩

theorem sim.step.max_fuel_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (h : c.pb.objects.val.length + 4 ≤ U64.max) (S : OsuModel.Sim.St) :
    ∃ f : U64, sim.step.max_fuel c = ok f ∧ OsuModel.Sim.Sim.maxFuel (simCtxS tn fo c) S = .ok (f.val, S) := by
  have hc : c.pb.objects.val.length ≤ U64.max := by omega
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (U64.add_spec (x := UScalar.cast .U64 (alloc.vec.Vec.len c.pb.objects))
    (y := 4#u64) (by simp; scalar_tac))
  refine ⟨z, ?_, ?_⟩
  · unfold sim.step.max_fuel; simp [lift, hz]
  · simp [OsuModel.Sim.Sim.maxFuel, OsuModel.Sim.Sim.ctx, simCtxS, playableS] at hzv ⊢
    omega

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.hit_forcefully_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (r : sim.step.Ref) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hr : simRefOk c r) (hL : simInstOk c s r.top.val)
    (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.hit_forcefully c s r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.hitForcefully (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c r hr
  obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
  obtain ⟨res, s', e1, r1, i1⟩ := sim.step.apply_result_refines tn fo E b0 n c hC hCS s f r
    (simHobj c r).max_result e hI hr hL hres
  refine ⟨res, s', by simp [sim.step.hit_forcefully, hh, hf, e1], ?_, i1⟩
  simp only [OsuModel.Sim.Sim.hitForcefully, simM_bind, hfS, s3b_ebok, hhS]
  exact r1

-- NOT-CONDITIONAL: simCSH is a context premise discharged by sim_ar_cs (custom_state_refines, unconditional since c069f00)
theorem sim.step.miss_forcefully_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop}
    (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (s : sim.state.St) (r : sim.step.Ref) (e : Nat)
    (hI : SimARInv tn fo P b0 n c s e 0 0) (hr : simRefOk c r) (hL : simInstOk c s r.top.val)
    (hres : sim.step.res_of s r = ok none) :
    ∃ res s', sim.step.miss_forcefully c s r = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.missForcefully (abs r) (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimARInv tn fo P b0 n c s' e 0 0) := by
  obtain ⟨hh, hhS⟩ := sim_hobj_of_eq tn fo c r hr
  obtain ⟨f, hf, hfS⟩ := sim.step.max_fuel_refines tn fo c hlen (simStS tn s)
  obtain ⟨res, s', e1, r1, i1⟩ := sim.step.apply_result_refines tn fo E b0 n c hC hCS s f r
    (simHobj c r).min_result e hI hr hL hres
  refine ⟨res, s', by simp [sim.step.miss_forcefully, hh, hf, e1], ?_, i1⟩
  simp only [OsuModel.Sim.Sim.missForcefully, simM_bind, hfS, s3b_ebok, hhS]
  exact r1
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `simCSH` for sim2's budgeted transform invariant, from `custom_state_refines` -/
-- NOT-CONDITIONAL: (custom_state_refines is unconditional since sim3c c069f00)
theorem sim_ar_cs (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length) :
    simCSH s2_tfOk (s3b_csCostFrom c.cfg.vis_mods.val 0) tn fo c :=
  fun i p ns hi hhi hhb hhn => s3c_csOk_of tn fo s3b_tfEng_s2 c i p ns hi hhi hhb hhn hfo
end OsuProofs
