/-
`sim::step` read-only accessors (Rust, `(c: &Ctx, s: &St)`) refine the `SimM` accessors of `OsuModel.Sim.Sim`
(Step.lean): they return the abstract value and leave the state unchanged. Index hypotheses state the in-range
accesses (simulation invariants: the spec's `getA` would reject, the Rust would panic).
-/
import OsuProofs.Sim.SimM
import OsuProofs.Sim.Basic
import OsuProofs.Sim.Consts
import OsuProofs.Sim.Eqs
import OsuProofs.LoopsR
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

deriving instance Inhabited for OsuImpl.sim.step.Ref

namespace OsuProofs
open OsuImpl

/-- In-range reference: the top-level object exists, and so does the nested one when `nested ≥ 0`. -/
def simRefOk (c : sim.state.Ctx) (r : sim.step.Ref) : Prop :=
  ∃ h : r.top.val < c.pb.objects.val.length, 0 ≤ r.nested.val → r.nested.val.toNat < (c.pb.objects.val[r.top.val]'h).nested.val.length

theorem sim_i64_cast_usize (x : I64) (h : 0 ≤ x.val) (h2 : x.val.toNat ≤ Usize.max) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have e1 : Usize.max = 2 ^ Usize.numBits - 1 := Usize.max_def
  have e2 : Usize.numBits = UScalarTy.Usize.numBits := Usize.numBits_def
  rw [e2] at e1
  have hp : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  have hbN : x.val.toNat < 2 ^ UScalarTy.Usize.numBits := by omega
  have hb : x.val < (2 : Int) ^ UScalarTy.Usize.numBits := by
    have e3 := Int.toNat_of_nonneg h; rw [← e3]; exact_mod_cast hbN
  simp only [UScalarTy.Usize_numBits_eq] at hb ⊢
  rw [Int.emod_eq_of_lt h (by exact_mod_cast hb)]

@[simp] theorem sim_ctxS_objects_size (tn fo) (c : sim.state.Ctx) :
    (simCtxS tn fo c).pb.objects.size = c.pb.objects.val.length := by simp [simCtxS, playableS]
theorem sim_ctxS_object (tn fo) (c : sim.state.Ctx) (i : Nat) (h : i < (simCtxS tn fo c).pb.objects.size) :
    (simCtxS tn fo c).pb.objects[i]'h = topS tn (c.pb.objects.val[i]'(by simpa using h)) := by
  simp [simCtxS, playableS]

theorem sim.step.hobj_of_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (r : sim.step.Ref)
    (hr : simRefOk c r) :
    ∃ h, sim.step.hobj_of c r = ok h ∧
      ∀ S, OsuModel.Sim.Sim.hobjOf (abs r) (simCtxS tn fo c) S = .ok (hobjS tn h, S) := by
  obtain ⟨ht, hn⟩ := hr
  have ht' : (abs r : Nat × Int).1 < (simCtxS tn fo c).pb.objects.size := by simpa [abs] using ht
  have hn' : 0 ≤ (abs r : Nat × Int).2 → (abs r : Nat × Int).2.toNat <
      ((simCtxS tn fo c).pb.objects[(abs r : Nat × Int).1]'ht').nested.size := by
    intro h0; rw [sim_ctxS_object]; simpa [topS, abs] using hn h0
  unfold sim.step.hobj_of
  simp only [vec_index_eq _ _ ht, bind_ok]
  by_cases hneg : r.nested < 0#i64
  · have h0 : r.nested.val < 0 := by scalar_tac
    refine ⟨(c.pb.objects.val[r.top.val]'ht).h, by simp [hneg], fun S => ?_⟩
    rw [simS_hobjOf _ _ _ ht' hn', sim_ctxS_object]
    simp [abs, h0, topS]
  · have h0 : 0 ≤ r.nested.val := by scalar_tac
    have hl := hn h0
    have hc : (IScalar.hcast .Usize r.nested).val = r.nested.val.toNat :=
      sim_i64_cast_usize _ h0 (by have := (c.pb.objects.val[r.top.val]'ht).nested.property; omega)
    have hl' : (IScalar.hcast .Usize r.nested).val < (c.pb.objects.val[r.top.val]'ht).nested.val.length := by omega
    refine ⟨(c.pb.objects.val[r.top.val]'ht).nested.val[(IScalar.hcast .Usize r.nested).val]'hl',
      by simp only [hneg, lift, bind_ok, vec_index_eq _ _ hl', if_false], fun S => ?_⟩
    rw [simS_hobjOf _ _ _ ht' hn', sim_ctxS_object]
    have : ¬ r.nested.val < 0 := by omega
    simp [abs, this, topS, hc, getElem!_pos, hl]

/-! ## State reads -/
def simSRefOk (s : sim.state.St) (r : sim.step.Ref) : Prop :=
  ∃ h : r.top.val < s.objs.val.length, 0 ≤ r.nested.val → r.nested.val.toNat < (s.objs.val[r.top.val]'h).nested.val.length

@[simp] theorem sim_stS_objs_size (tn) (s : sim.state.St) : (simStS tn s).objs.size = s.objs.val.length := by
  simp [simStS, abs]
theorem sim_stS_obj (tn) (s : sim.state.St) (i : Nat) (h : i < (simStS tn s).objs.size) :
    (simStS tn s).objs[i]'h = ostateS (s.objs.val[i]'(by simpa using h)) := by
  simp [simStS, abs]

theorem sim_ref_cast (r : sim.step.Ref) (h0 : 0 ≤ r.nested.val) (n : Nat) (hl : r.nested.val.toNat < n)
    (hn : n ≤ Usize.max) : (IScalar.hcast .Usize r.nested).val = r.nested.val.toNat :=
  sim_i64_cast_usize _ h0 (by omega)

theorem sim.step.res_of_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (r : sim.step.Ref) (hr : simSRefOk s r) :
    ∃ o, sim.step.res_of s r = ok o ∧
      OsuModel.Sim.Sim.resOf (abs r) (simCtxS tn fo c) (simStS tn s) = .ok (o.map abs, simStS tn s) := by
  obtain ⟨ht, hn⟩ := hr
  have ht' : (abs r : Nat × Int).1 < (simStS tn s).objs.size := by simpa [abs] using ht
  have hn' : 0 ≤ (abs r : Nat × Int).2 → (abs r : Nat × Int).2.toNat <
      ((simStS tn s).objs[(abs r : Nat × Int).1]'ht').nested.size := by
    intro h0; rw [sim_stS_obj]; simpa [ostateS, abs] using hn h0
  unfold sim.step.res_of
  simp only [vec_index_eq _ _ ht, bind_ok]
  rw [simS_resOf _ _ _ ht' hn', sim_stS_obj]
  by_cases hneg : r.nested < 0#i64
  · have h0 : r.nested.val < 0 := by scalar_tac
    refine ⟨(s.objs.val[r.top.val]'ht).result, by simp [hneg], ?_⟩
    simp [abs, h0, ostateS]
  · have h0 : 0 ≤ r.nested.val := by scalar_tac
    have hl := hn h0
    have hc := sim_ref_cast r h0 _ hl (s.objs.val[r.top.val]'ht).nested.property
    have hl' : (IScalar.hcast .Usize r.nested).val < (s.objs.val[r.top.val]'ht).nested.val.length := by omega
    refine ⟨(s.objs.val[r.top.val]'ht).nested.val[(IScalar.hcast .Usize r.nested).val]'hl',
      by simp only [hneg, lift, bind_ok, vec_index_eq _ _ hl', if_false], ?_⟩
    have : ¬ r.nested.val < 0 := by omega
    simp [abs, this, ostateS, hc, getElem!_pos, hl]

theorem sim_res_of_eq (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref) (hr : simSRefOk s r) :
    ∃ o, sim.step.res_of s r = ok o ∧
      ∀ C', C' = simCtxS tn fo c → OsuModel.Sim.Sim.resOf (abs r) C' (simStS tn s) = .ok (o.map abs, simStS tn s) := by
  obtain ⟨o, h, e⟩ := sim.step.res_of_refines tn fo c s r hr; exact ⟨o, h, fun _ hc => hc ▸ e⟩

theorem sim.step.judged_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (r : sim.step.Ref) (hr : simSRefOk s r) :
    ∃ b, sim.step.judged s r = ok b ∧
      OsuModel.Sim.Sim.judged (abs r) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
  obtain ⟨o, h, e⟩ := sim.step.res_of_refines tn fo c s r hr
  refine ⟨o.isSome, by simp [sim.step.judged, h, core.option.Option.is_some], ?_⟩
  unfold OsuModel.Sim.Sim.judged; simp [e, Except.bind]

theorem sim.step.is_hit_ref_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (r : sim.step.Ref) (hr : simSRefOk s r) :
    ∃ b, sim.step.is_hit_ref s r = ok b ∧
      OsuModel.Sim.Sim.isHitRef (abs r) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
  obtain ⟨o, h, e⟩ := sim.step.res_of_refines tn fo c s r hr
  unfold sim.step.is_hit_ref OsuModel.Sim.Sim.isHitRef
  simp only [h, bind_ok, simM_bind, e, Except.bind]
  rcases o with _ | ⟨ty, t⟩
  · exact ⟨false, rfl, rfl⟩
  · obtain ⟨b, hb, eb⟩ := sim.basic.is_hit_refines ty
    exact ⟨b, by simp [hb], by simp [abs] at eb ⊢; rw [eb]⟩


theorem sim_all_map_foldl {X Y : Type} (f : X → Y) (p : Y → Bool) (l : List X) :
    ∀ acc, ((l.map f).all p && acc) = l.foldl (fun acc x => acc && p (f x)) acc := by
  induction l with
  | nil => intro acc; simp
  | cons x t ih => intro acc; simp [← ih]; cases p (f x) <;> simp

theorem sim_not_dec_none {α} (x : Option α) : (!decide (x = none)) = x.isSome := by cases x <;> rfl

theorem sim.step.os_all_judged_refines (o : sim.state.OState) :
    ∃ b, sim.step.os_all_judged o = ok b ∧
      ((abs o : OsuModel.Sim.OState).result.isSome && (abs o : OsuModel.Sim.OState).nested.all (·.isSome)) = b := by
  unfold sim.step.os_all_judged
  cases hr : o.result
  · exact ⟨false, by simp [hr, core.option.Option.is_none], by simp [abs, ostateS, hr]⟩
  · obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => sim.step.os_all_judged_loop.body o.nested x.1 x.2) (·.1)
      o.nested.val.length (by have := o.nested.property; omega)
      (fun _ => True) (fun x => x.2)
      (fun k acc => acc && (o.nested.val[k]!).isSome) (fun y acc => y = acc)
      (by loop_step [sim.step.os_all_judged_loop.body, core.option.Option.is_none, sim_not_dec_none, Bool.and_comm])
      (by loop_end [sim.step.os_all_judged_loop.body])
      (0#usize, true) trivial (by simp)
    refine ⟨v, by simp [hr, core.option.Option.is_none]; unfold sim.step.os_all_judged_loop; exact hl, ?_⟩
    simp only at hv
    rw [hv, show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
    have := sim_all_map_foldl (fun x : Option sim.state.Res => x.map (fun r => (abs r : OsuModel.Sim.Res))) (·.isSome) o.nested.val true
    rw [foldl_iterR] at this
    simp only [Bool.and_true] at this
    simp only [abs, ostateS, hr, Option.isSome_some, Bool.true_and, List.all_toArray, Option.isSome_map] at this ⊢
    rw [this]

theorem sim.step.all_judged_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St)
    (i : Usize) (hi : i.val < s.objs.val.length) :
    ∃ b, sim.step.all_judged s i = ok b ∧
      OsuModel.Sim.Sim.allJudged i.val (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
  obtain ⟨b, hb, eb⟩ := sim.step.os_all_judged_refines (s.objs.val[i.val]'hi)
  refine ⟨b, by simp [sim.step.all_judged, vec_index_eq _ _ hi, hb], ?_⟩
  have hi' : i.val < (simStS tn s).objs.size := by simpa using hi
  rw [simS_allJudged _ _ _ hi', sim_stS_obj]
  simp only [abs] at eb; rw [← eb]


@[simp] theorem armed_eq_ok (a b : sim.state.Armed) :
    sim.state.Armed.Insts.CoreCmpPartialEqArmed.eq a b = ok (armedS a == armedS b) := by
  cases a <;> cases b <;> simp [sim.state.Armed.Insts.CoreCmpPartialEqArmed.eq, sim.state.Armed.read_discriminant, armedS] <;> decide
@[simp] theorem part_eq_ok (a b : sim.step.Part) :
    sim.step.Part.Insts.CoreCmpPartialEqPart.eq a b = ok (decide (a.read_discriminant = b.read_discriminant)) := by
  cases a <;> cases b <;> simp [sim.step.Part.Insts.CoreCmpPartialEqPart.eq]

def partS : sim.step.Part → OsuModel.Sim.Sim.Part | .Top => .top | .Head => .head
instance : AbsTo sim.step.Part OsuModel.Sim.Sim.Part := ⟨partS⟩

theorem sim.step.pool_kind_refines (k : sim.playable.Kind) :
    ∃ n, sim.step.pool_kind k = ok n ∧ OsuModel.Sim.Sim.poolKind (abs k) = abs n := by
  cases k <;> simp [sim.step.pool_kind, OsuModel.Sim.Sim.poolKind, abs, kindS]

theorem sim.step.placement_of_refines (tf : sim.transforms.TObj) :
    ∃ p, sim.step.placement_of tf = ok p ∧ OsuModel.Sim.Sim.placementOf (abs tf) = abs p := by
  simp [sim.step.placement_of, OsuModel.Sim.Sim.placementOf, abs]

theorem sim.step.present_tf_refines (tf : sim.transforms.TObj) (a : sim.state.Armed) (now ls : F64) :
    ∃ b, sim.step.present_tf tf a now ls = ok b ∧
      OsuModel.Sim.Sim.presentTf (abs tf) (abs a) (abs now) (abs ls) = abs b := by
  unfold sim.step.present_tf OsuModel.Sim.Sim.presentTf
  simp only [sim.step.ALPHA_PRESENT, sim_basic_F32_0, fb32_953267991, float.F32.lt, float.F32.eq, float.F64.le,
    armed_eq_ok, bind_ok, abs, id]
  cases a <;> by_cases h1 : (Float32.ofBits 953267991 : F32) < tf.alpha <;> by_cases h2 : (tf.scale.x == 0) = true <;>
    by_cases h3 : (tf.scale.y == 0) = true <;> by_cases h4 : ls ≤ now <;> simp [h1, h2, h3, h4, armedS]

@[simp] theorem sim_part_beq_tt : (OsuModel.Sim.Sim.Part.top == .top) = true := rfl
@[simp] theorem sim_part_beq_ht : (OsuModel.Sim.Sim.Part.head == .top) = false := rfl
@[simp] theorem sim_part_beq_th : (OsuModel.Sim.Sim.Part.top == .head) = false := rfl
@[simp] theorem sim_part_beq_hh : (OsuModel.Sim.Sim.Part.head == .head) = true := rfl

theorem sim.step.part_inst_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part)
    (hi : i.val < s.objs.val.length) :
    ∃ k, sim.step.part_inst s i p = ok k ∧
      OsuModel.Sim.Sim.partInst i.val (abs p) (simCtxS tn fo c) (simStS tn s) = .ok (k.val, simStS tn s) := by
  have hi' : i.val < (simStS tn s).objs.size := by simpa using hi
  unfold sim.step.part_inst OsuModel.Sim.Sim.partInst
  cases p <;> simp [vec_index_eq _ _ hi, simS_ostate _ _ _ hi', sim_stS_obj, Except.bind, abs, partS, ostateS,
    sim.step.Part.read_discriminant]

theorem sim.step.part_armed_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part)
    (hi : i.val < s.objs.val.length) :
    ∃ a, sim.step.part_armed s i p = ok a ∧
      OsuModel.Sim.Sim.partArmed i.val (abs p) (simCtxS tn fo c) (simStS tn s) = .ok (abs a, simStS tn s) := by
  have hi' : i.val < (simStS tn s).objs.size := by simpa using hi
  unfold sim.step.part_armed OsuModel.Sim.Sim.partArmed
  cases p <;> simp [vec_index_eq _ _ hi, simS_ostate _ _ _ hi', sim_stS_obj, Except.bind, abs, partS, ostateS,
    sim.step.Part.read_discriminant]

theorem sim.step.part_ref_refines (tn fo) (c : sim.state.Ctx) (S : OsuModel.Sim.St) (i : Usize) (p : sim.step.Part)
    (hi : i.val < c.head_idx.val.length) (hh : (c.head_idx.val[i.val]'hi).val < 2 ^ 63) :
    ∃ r, sim.step.part_ref c i p = ok r ∧
      OsuModel.Sim.Sim.partRef i.val (abs p) (simCtxS tn fo c) S = .ok (abs r, S) := by
  unfold sim.step.part_ref OsuModel.Sim.Sim.partRef
  have hi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hi
  cases p
  · simp [abs, partS, sim.step.Part.read_discriminant]
  · have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hi)).val = ((c.head_idx.val[i.val]'hi).val : Int) := by
      rw [UScalar.hcast_val_eq]; simp
      rw [Int.bmod_eq_of_le] <;> omega
    refine ⟨⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hi)⟩,
      by simp [vec_index_eq _ _ hi, lift, sim.step.Part.read_discriminant], ?_⟩
    simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hi', hi, Except.bind, abs, partS, hc,
      simCtxS]

end OsuProofs
