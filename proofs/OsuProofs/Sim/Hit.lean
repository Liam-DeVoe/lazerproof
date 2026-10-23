/-
StartTimeOrderedHitPolicy (`IHitPolicy.CheckHittable`, `StartTimeOrderedHitPolicy.cs:26-52`): `circle_like`,
`check_hittable_sto` / `check_hittable` (STO policy) refine `Sim.circleLike` / `Sim.checkHittable`.
`SimInv`: the structural invariants of the simulation state used for in-range accesses.
-/
import OsuProofs.Sim.Enum
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs

section
open OsuImpl OsuModel.Net

/-- Structural invariants of the simulation state that the step functions rely on for in-range accesses
(established by `initState`, preserved by every step). -/
structure SimInv (c : sim.state.Ctx) (s : sim.state.St) : Prop where
  objs_len : s.objs.val.length = c.pb.objects.val.length
  nested_len : ∀ i (h1 : i < s.objs.val.length) (h2 : i < c.pb.objects.val.length),
    (s.objs.val[i]'h1).nested.val.length = (c.pb.objects.val[i]'h2).nested.val.length
  nested_small : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 63
  dict_in : ∀ o ∈ s.dict_slots.val, ∀ x, o = some x → x.val < c.pb.objects.val.length
  dict_small : s.dict_slots.val.length < Usize.max

theorem sim_enumL_valid (objs : Array OsuModel.Sim.TopObj) (target : F64) :
    ∀ (l : List Nat), (∀ i ∈ l, i < objs.size) → ∀ r ∈ simEnumL objs target l,
      ∃ h : r.1 < objs.size, 0 ≤ r.2 → r.2.toNat < (objs[r.1]'h).nested.size := by
  intro l
  induction l with
  | nil => intro _ r hr; simp [simEnumL] at hr
  | cons i t ih =>
    intro hl r hr
    simp only [simEnumL] at hr
    split at hr
    · rw [List.mem_append, List.mem_cons] at hr
      have hi := hl i List.mem_cons_self
      rcases hr with (hr | hr) | hr
      · subst hr; exact ⟨hi, by simp⟩
      · simp only [simNestedTW, List.mem_map] at hr
        obtain ⟨j, hj, hjr⟩ := hr
        subst hjr
        have hj' : ∃ a ∈ List.takeWhile (fun j => decide ((objs[i]!.nested[j]!).start < target))
            (List.range (objs[i]!).nested.size), j = (a : Int) := by
          simpa [List.mem_flatMap] using hj
        obtain ⟨a, ha, haj⟩ := hj'
        have ha' := (List.takeWhile_sublist _).subset ha
        rw [List.mem_range] at ha'
        refine ⟨hi, fun _ => ?_⟩
        simp only at ha' ⊢
        rw [haj]; simp [getElem!_def, hi] at ha' ⊢; omega
      · exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) r hr
    · simp at hr

end
section
open OsuImpl OsuModel.Net

theorem sim_foldr_yield {α β} (f : α → β → β) :
    ∀ (l : List α) (b : β), l.foldr (simForStep (fun x b => .yield (f x b))) id b = l.foldl (fun b x => f x b) b := by
  intro l; induction l with
  | nil => intro b; rfl
  | cons x t ih => intro b; simp only [List.foldr_cons, List.foldl_cons, simForStep]; exact ih _

theorem sim.step.circle_like_refines (tn fo) (c : sim.state.Ctx) (r : sim.step.Ref) (hr : simRefOk c r) :
    ∃ b, sim.step.circle_like c r = ok b ∧
      ∀ S, OsuModel.Sim.Sim.circleLike (abs r) (simCtxS tn fo c) S = .ok (b, S) := by
  obtain ⟨h, hh, eh⟩ := sim.step.hobj_of_refines tn fo c r hr
  obtain ⟨b, hb, eb⟩ := sim.playable.is_circle_like_refines h.kind
  refine ⟨b, by simp [sim.step.circle_like, hh, hb], fun S => ?_⟩
  simp only [OsuModel.Sim.Sim.circleLike, simM_bind, eh, Except.bind, simM_pure]
  simp only [abs] at eb; simp [hobjS, eb]

/-- `hobjOf` as a total function on Rust references (in range: `sim_hobj_of_eq`) -/
def simHobj (c : sim.state.Ctx) (r : sim.step.Ref) : sim.playable.HObj :=
  if r.nested.val < 0 then (c.pb.objects.val[r.top.val]!).h else (c.pb.objects.val[r.top.val]!).nested.val[r.nested.val.toNat]!

theorem sim_hobj_of_eq (tn fo) (c : sim.state.Ctx) (r : sim.step.Ref) (hr : simRefOk c r) :
    sim.step.hobj_of c r = ok (simHobj c r) ∧
      ∀ S, OsuModel.Sim.Sim.hobjOf (abs r) (simCtxS tn fo c) S = .ok (hobjS tn (simHobj c r), S) := by
  obtain ⟨h, hh, eh⟩ := sim.step.hobj_of_refines tn fo c r hr
  obtain ⟨ht, hn⟩ := hr
  have e : h = simHobj c r := by
    unfold sim.step.hobj_of at hh
    simp only [vec_index_eq _ _ ht, bind_ok] at hh
    unfold simHobj
    by_cases hneg : r.nested < 0#i64
    · have h0 : r.nested.val < 0 := by scalar_tac
      simp [hneg] at hh; simp [h0, ← hh, getElem!_def, ht]
    · have h0 : 0 ≤ r.nested.val := by scalar_tac
      have hl := hn h0
      have hc := sim_ref_cast r h0 _ hl (c.pb.objects.val[r.top.val]'ht).nested.property
      have hl' : (IScalar.hcast .Usize r.nested).val < (c.pb.objects.val[r.top.val]'ht).nested.val.length := by omega
      simp only [hneg, lift, vec_index_eq _ _ hl', bind_ok, if_false, Bool.false_eq_true, ite_false, decide_false] at hh
      have hh2 := (Result.ok_injective hh).symm
      have : ¬ r.nested.val < 0 := by omega
      rw [hh2]
      have hl2 : r.nested.val.toNat < (c.pb.objects.val[r.top.val]'ht).nested.val.length := hl
      simp only [this, if_false, getElem!_def, List.getElem?_eq_getElem ht, Option.getD_some,
        List.getElem?_eq_getElem hl2]
      congr 1
  subst e; exact ⟨hh, eh⟩

/-- the blocking object of `StartTimeOrderedHitPolicy.CheckHittable`: the last circle-like object -/
def simBlocking (c : sim.state.Ctx) (l : List sim.step.Ref) : Option sim.step.Ref :=
  l.foldl (fun b o => if (kindS (simHobj c o).kind).isCircleLike then some o else b) none

end
section
open OsuImpl OsuModel.Net

theorem sim_circle_like_eq (c : sim.state.Ctx) (r : sim.step.Ref) (hr : simRefOk c r) :
    sim.step.circle_like c r = ok (kindS (simHobj c r).kind).isCircleLike := by
  have := (sim_hobj_of_eq (fun _ => "") (alloc.vec.Vec.new _) c r hr).1
  obtain ⟨b, hb, eb⟩ := sim.playable.is_circle_like_refines (simHobj c r).kind
  simp only [abs] at eb
  simp [sim.step.circle_like, this, hb]; exact eb.symm

theorem sim_sto_loop (c : sim.state.Ctx) (objs : alloc.vec.Vec sim.step.Ref) (hv : ∀ o ∈ objs.val, simRefOk c o) :
    sim.step.check_hittable_sto_loop c objs none 0#usize = ok (simBlocking c objs.val) := by
  obtain ⟨v, hl, hvr⟩ := loop_fold_gen' (fun x => sim.step.check_hittable_sto_loop.body c objs x.1 x.2) (·.2)
    objs.val.length (by have := objs.property; omega)
    (fun _ => True) (fun x => x.1)
    (fun k b => if (kindS (simHobj c (objs.val[k]!)).kind).isCircleLike then some (objs.val[k]!) else b)
    (fun y b => y = b)
    (by
      rintro ⟨b, k⟩ _ hk j1 hj1 hj1v
      simp only at hk hj1 hj1v ⊢
      have hkv : k.val < objs.val.length := hk
      refine ⟨(if (kindS (simHobj c (objs.val[k.val]'hkv)).kind).isCircleLike then some (objs.val[k.val]'hkv) else b, j1),
        ?_, rfl, ?_, trivial⟩
      · simp [sim.step.check_hittable_sto_loop.body, vec_lt_len_iff, hkv, vec_index_usize_ok _ _ hkv,
          sim_circle_like_eq c _ (hv _ (List.getElem_mem hkv)), hj1]
      · simp [getElem!_def, hkv])
    (by
      rintro ⟨b, k⟩ _ hge
      have : ¬ k < alloc.vec.Vec.len objs := by rw [vec_lt_len_iff]; simp at hge; omega
      exact ⟨b, by simp only [sim.step.check_hittable_sto_loop.body, this, ite_false], rfl⟩)
    (none, 0#usize) trivial (by simp)
  unfold sim.step.check_hittable_sto_loop
  rw [hl, hvr]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  unfold simBlocking
  rw [foldl_iterR]

end
section
open OsuImpl OsuModel.Net

def clickS : sim.step.ClickAction → OsuModel.Sim.Sim.ClickAction
  | .Ignore => .ignore | .Shake => .shake | .Hit => .hit
instance : AbsTo sim.step.ClickAction OsuModel.Sim.Sim.ClickAction := ⟨clickS⟩

/-- the spec `circleLike` as a function (its value when it succeeds) -/
def simCircS (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (x : OsuModel.Sim.Ref) : Bool :=
  match OsuModel.Sim.Sim.circleLike x C S with | .ok p => p.1 | .error _ => false

theorem sim_blocking_spec (tn fo) (c : sim.state.Ctx) (S : OsuModel.Sim.St) (l : List sim.step.Ref)
    (hv : ∀ o ∈ l, simRefOk c o) :
    (l.map (fun r => (abs r : OsuModel.Sim.Ref))).foldl
      (fun b x => if simCircS (simCtxS tn fo c) S x = true then some x else b) none =
      (simBlocking c l).map (fun r => (abs r : OsuModel.Sim.Ref)) := by
  unfold simBlocking
  suffices ∀ acc : Option sim.step.Ref, (l.map (fun r => (abs r : OsuModel.Sim.Ref))).foldl
      (fun b x => if simCircS (simCtxS tn fo c) S x = true then some x else b) (acc.map abs) =
      (l.foldl (fun b o => if (kindS (simHobj c o).kind).isCircleLike then some o else b) acc).map abs by
    simpa using this none
  induction l with
  | nil => intro acc; simp
  | cons o t ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    obtain ⟨b, hb, eb⟩ := sim.step.circle_like_refines tn fo c o (hv o List.mem_cons_self)
    have hcs : simCircS (simCtxS tn fo c) S (abs o) = (kindS (simHobj c o).kind).isCircleLike := by
      unfold simCircS; rw [eb S]; simp only
      rw [sim_circle_like_eq c o (hv o List.mem_cons_self)] at hb
      exact (Result.ok_injective hb).symm
    rw [hcs]
    have := ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    split <;> [exact this (some o); exact this acc]

end
section
open OsuImpl OsuModel.Net

theorem sim_enum_refs_valid (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (target : F64) (hinv : SimInv c s)
    (objs : alloc.vec.Vec sim.step.Ref)
    (eo : OsuModel.Sim.Sim.enumerateUpTo target (simCtxS tn fo c) (simStS tn s) = .ok (abs objs, simStS tn s)) :
    ∀ o ∈ objs.val, simRefOk c o ∧ simSRefOk s o := by
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
  obtain ⟨h1, h2⟩ := sim_enumL_valid _ target _ (fun i hi => hS i (by simpa using sim_simSortL_mem _ _ _ hi)) _ hmem
  have ht : o.top.val < c.pb.objects.val.length := by simpa [abs] using h1
  have hn : 0 ≤ o.nested.val → o.nested.val.toNat < (c.pb.objects.val[o.top.val]'ht).nested.val.length := by
    intro h0; have := h2 h0; rw [sim_ctxS_object] at this; simpa [abs, topS] using this
  refine ⟨⟨ht, hn⟩, ?_⟩
  have ht' : o.top.val < s.objs.val.length := by rw [hinv.objs_len]; exact ht
  exact ⟨ht', fun h0 => by rw [hinv.nested_len _ ht' ht]; exact hn h0⟩

end
section
open OsuImpl OsuModel.Net

theorem sim_simBlocking_mem (c : sim.state.Ctx) (l : List sim.step.Ref) (b : sim.step.Ref)
    (h : simBlocking c l = some b) : b ∈ l := by
  unfold simBlocking at h
  suffices ∀ (l : List sim.step.Ref) (acc : Option sim.step.Ref) x,
      l.foldl (fun b o => if (kindS (simHobj c o).kind).isCircleLike then some o else b) acc = some x →
      acc = some x ∨ x ∈ l by
    rcases this l none b h with h' | h'
    · cases h'
    · exact h'
  intro l
  induction l with
  | nil => intro acc x hx; exact Or.inl hx
  | cons o t ih =>
    intro acc x hx
    simp only [List.foldl_cons] at hx
    rcases ih _ x hx with h' | h'
    · split at h'
      · cases h'; exact Or.inr List.mem_cons_self
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

/-- `checkHittable` with `StartTimeOrderedHitPolicy` (the default; Classic note lock = `LegacyHitPolicy` is separate).
Guards: the simulation invariants and the enumeration fitting in a `Vec`. -/
theorem sim.step.check_hittable_sto_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (time : F64) (result : sim.basic.HitResult) (hinv : SimInv c s) (hr : simRefOk c r)
    (hpol : c.cfg.policy = .StartTimeOrdered)
    (hcap : ∀ v, OsuModel.Sim.Sim.enumerateUpTo (simHobj c r).start (simCtxS tn fo c) (simStS tn s) =
      .ok (v, simStS tn s) → v.size < Usize.max) :
    ∃ a, sim.step.check_hittable c s r time result = ok a ∧
      OsuModel.Sim.Sim.checkHittable (abs r) (abs time) (abs result) (simCtxS tn fo c) (simStS tn s) =
        .ok (abs a, simStS tn s) := by
  obtain ⟨hh, eh⟩ := sim_hobj_of_eq tn fo c r hr
  obtain ⟨objs, ho, eo⟩ := sim.step.enumerate_up_to_refines tn fo c s (simHobj c r).start hinv.dict_in
    hinv.dict_small hinv.nested_small hcap
  have hv := sim_enum_refs_valid tn fo c s _ hinv objs eo
  have hbl := sim_sto_loop c objs (fun o h => (hv o h).1)
  have hpolS : (simCtxS tn fo c).cfg.policy = .startTimeOrdered := by simp [simCtxS, abs, configS, hpol]
  unfold OsuModel.Sim.Sim.checkHittable
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind, eh, hpolS]
  have eo' : OsuModel.Sim.Sim.enumerateUpTo (hobjS tn (simHobj c r)).start (simCtxS tn fo c) (simStS tn s) =
      .ok (abs objs, simStS tn s) := eo
  rw [eo']
  simp only
  rw [simM_forIn_array_eval _ _
    (fun x b => ForInStep.yield (if simCircS (simCtxS tn fo c) (simStS tn s) x = true then some x else b))
    (simCtxS tn fo c) (simStS tn s) ?hF]
  case hF =>
    intro x hx b
    have hx' : x ∈ objs.val.map (fun r => (abs r : OsuModel.Sim.Ref)) := by simpa [abs] using hx
    obtain ⟨o, hoo, hox⟩ := List.mem_map.mp hx'
    subst hox
    obtain ⟨bb, hbb, ebb⟩ := sim.step.circle_like_refines tn fo c o (hv o hoo).1
    have hc : simCircS (simCtxS tn fo c) (simStS tn s) (abs o) = bb := by unfold simCircS; rw [ebb]
    simp only [simM_bind, ebb, Except.bind, hc]
    cases bb <;> rfl
  rw [sim_foldr_yield]
  have hl : (abs objs : _root_.Array OsuModel.Sim.Ref).toList = objs.val.map (fun r => (abs r : OsuModel.Sim.Ref)) := by
    simp [abs]
  rw [hl, sim_blocking_spec tn fo c (simStS tn s) objs.val (fun o h => (hv o h).1)]
  unfold sim.step.check_hittable
  simp only [hh, bind_ok, hpol]
  unfold sim.step.check_hittable_sto
  simp only [ho, hbl, bind_ok]
  cases hb : simBlocking c objs.val with
  | none =>
    cases result <;> simp (config := {decide := true}) [abs, hrS, clickS]
  | some b =>
    have hbv := hv b (sim_simBlocking_mem c _ b hb)
    obtain ⟨hhb, ehb⟩ := sim_hobj_of_eq tn fo c b hbv.1
    obtain ⟨jb, hjb, ejb⟩ := sim.step.judged_refines tn fo c s b hbv.2
    simp only [Option.map_some, hhb, hjb, bind_ok, simM_bind, ehb, ejb, Except.bind]
    cases jb <;> by_cases ht : time < (simHobj c b).start <;> cases result <;>
      simp (config := {decide := true}) [abs, hrS, clickS, ht, hobjS]

end

end OsuProofs
