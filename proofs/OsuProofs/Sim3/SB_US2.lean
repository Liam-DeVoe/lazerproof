/-
Sim3b part 8: `update_state` refines `Sim.updateState` (via `s3b_updateState_spec`).
-/
import OsuProofs.Sim3.SB_US
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-! ## strong frames (sim3c, sim core request 2026-10-22 19:17) -/
/-- (sim3c) `s'` differs from `s` at most in `insts`, `theta` and `objs` -/
def s3c_ito (s s' : sim.state.St) : Prop := s' = { s with insts := s'.insts, theta := s'.theta, objs := s'.objs }

theorem s3c_ito_refl (s : sim.state.St) : s3c_ito s s := rfl

theorem s3c_ito_trans {s1 s2 s3 : sim.state.St} (h1 : s3c_ito s1 s2) (h2 : s3c_ito s2 s3) : s3c_ito s1 s3 := by
  unfold s3c_ito at *
  rw [h2, h1]

theorem s3c_ito_frame {s s' : sim.state.St} (h : s3c_ito s s') : s3b_frame s s' := by
  unfold s3c_ito at h; rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (sim3c) the armed states / lifetime ends written by `update_state` -/
def s3c_osw (o : sim.state.OState) (a ha : sim.state.Armed) (le hle : F64) : sim.state.OState :=
  { o with armed := a, head_armed := ha, lifetime_end := le, head_lifetime_end := hle }

/-- (sim3c) the strong frame of `update_state`: only `insts` (same length), `theta`, and the armed states / lifetime
ends of object `i` change -/
def s3c_usFrame (i : Usize) (s s' : sim.state.St) : Prop :=
  ∃ (hio : i.val < s.objs.val.length) (a ha : sim.state.Armed) (le hle : F64),
    s' = { s with insts := s'.insts, theta := s'.theta, objs := s.objs.set i (s3c_osw (s.objs.val[i.val]'hio) a ha le hle) } ∧
    s'.insts.val.length = s.insts.val.length

theorem s3c_usFrame_refl (i : Usize) (s : sim.state.St) (hio : i.val < s.objs.val.length) : s3c_usFrame i s s := by
  refine ⟨hio, (s.objs.val[i.val]'hio).armed, (s.objs.val[i.val]'hio).head_armed, (s.objs.val[i.val]'hio).lifetime_end,
    (s.objs.val[i.val]'hio).head_lifetime_end, ?_, rfl⟩
  have : s.objs.set i (s3c_osw (s.objs.val[i.val]'hio) (s.objs.val[i.val]'hio).armed (s.objs.val[i.val]'hio).head_armed
      (s.objs.val[i.val]'hio).lifetime_end (s.objs.val[i.val]'hio).head_lifetime_end) = s.objs := by
    apply alloc.vec.Vec.ext
    rw [vec_set_val', show s3c_osw (s.objs.val[i.val]'hio) (s.objs.val[i.val]'hio).armed (s.objs.val[i.val]'hio).head_armed
      (s.objs.val[i.val]'hio).lifetime_end (s.objs.val[i.val]'hio).head_lifetime_end = s.objs.val[i.val]'hio from rfl,
      List.set_getElem_self]
  rw [this]

theorem s3c_usFrame_ito {i : Usize} {s X s' : sim.state.St} (h1 : s3c_usFrame i s X) (h2 : s3c_ito X s')
    (ho : s'.objs = X.objs) (hl : s'.insts.val.length = X.insts.val.length) : s3c_usFrame i s s' := by
  obtain ⟨hio, a, ha, le, hle, e, l⟩ := h1
  refine ⟨hio, a, ha, le, hle, ?_, by rw [hl, l]⟩
  have hO : s'.objs = s.objs.set i (s3c_osw (s.objs.val[i.val]'hio) a ha le hle) := by
    rw [ho, e]
  unfold s3c_ito at h2
  rw [h2, e, hO]

/-- the `customState` refinement for part `(i, p)` and state `ns` (both passes), on every state with the invariants
(proved separately: `sim.step.custom_state_refines`) -/
def s3b_CSOk (P : Nat → sim.transforms.TObj → Prop) (n : Nat) (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) : Prop :=
  ∀ b s fw, SimInv c s → s3b_TfInv P (b + n) s → ∀ (hio : i.val < s.objs.val.length),
    (s.objs.val[i.val]'hio).inst.val < s.insts.val.length → (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length →
    ∃ s', sim.step.custom_state c s i p ns fw = ok s' ∧
    OsuModel.Sim.Sim.customState i.val (abs p) (abs ns) fw (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
    SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧ s'.objs = s.objs ∧
    s'.future_order = s.future_order ∧ s3c_ito s s'

theorem s3b_topObj (tn fo) (c : sim.state.Ctx) (S : OsuModel.Sim.St) (i : Nat) (hi : i < c.pb.objects.val.length) :
    OsuModel.Sim.Sim.topObj i (simCtxS tn fo c) S = .ok (topS tn (c.pb.objects.val[i]'hi), S) := by
  have hi' : i < (simCtxS tn fo c).pb.objects.size := by simpa using hi
  simp only [OsuModel.Sim.Sim.topObj, simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok, OsuModel.Sim.Sim.getA,
    dif_pos hi', simM_pure, sim_ctxS_object]

theorem s3b_map_set_set {α β : Type} (f : α → β) (l : List α) (k : Nat) (hk : k < l.length) (A B : α) :
    ((l.set k A).set k B).map f = (l.map f).set k (f B) := by
  simp [List.map_set]

theorem s3b_arr_modify_toArray {α β : Type} (f : α → β) (l : List α) (k : Nat) (hk : k < l.length) (g : β → β) :
    (l.map f).toArray.modify k g = ((l.map f).set k (g (f (l[k]'hk)))).toArray := by
  rw [s3b_arr_modify _ _ (by simpa using hk)]
  simp

/-- the abstract insts after `update_state`'s two writes to instance `k` -/
theorem s3b_us_insts (tn) (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length)
    (tfR bodyR : sim.transforms.TObj) :
    (abs ((s.insts.set k { s.insts.val[k.val]'hk with tf := tfR }).set k
      { s.insts.val[k.val]'hk with tf := tfR, body_tf := bodyR }) : _root_.Array OsuModel.Sim.Inst) =
    (simStS tn s).insts.modify k.val (fun ins => { ins with tf := abs tfR, bodyTf := abs bodyR }) := by
  rw [s3b_stS_insts, s3b_arr_modify_toArray _ _ _ hk]
  show ((((s.insts.set k _).set k _).val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray) = _
  rw [vec_set_val', vec_set_val', s3b_map_set_set _ _ _ hk]
  rfl

/-- the abstract objs after `update_state`'s two writes to object `i` (part `Top`) -/
theorem s3b_us_objs_top (s : sim.state.St) (i : Usize) (hio : i.val < s.objs.val.length) (ns : sim.state.Armed)
    (le : F64) :
    (abs ((s.objs.set i { s.objs.val[i.val]'hio with armed := ns }).set i
      { s.objs.val[i.val]'hio with armed := ns, lifetime_end := le }) : _root_.Array OsuModel.Sim.OState) =
    (abs s.objs : _root_.Array OsuModel.Sim.OState).modify i.val (fun os => { os with armed := abs ns, lifetimeEnd := le }) := by
  rw [show (abs s.objs : _root_.Array OsuModel.Sim.OState) = (s.objs.val.map abs).toArray from rfl,
    s3b_arr_modify_toArray _ _ _ hio]
  show ((((s.objs.set i _).set i _).val.map (fun x => (abs x : OsuModel.Sim.OState))).toArray) = _
  rw [vec_set_val', vec_set_val', s3b_map_set_set _ _ _ hio]
  rfl

theorem s3b_us_objs_head (s : sim.state.St) (i : Usize) (hio : i.val < s.objs.val.length) (ns : sim.state.Armed)
    (le : F64) :
    (abs ((s.objs.set i { s.objs.val[i.val]'hio with head_armed := ns }).set i
      { s.objs.val[i.val]'hio with head_armed := ns, head_lifetime_end := le }) : _root_.Array OsuModel.Sim.OState) =
    (abs s.objs : _root_.Array OsuModel.Sim.OState).modify i.val (fun os => { os with headArmed := abs ns, headLifetimeEnd := le }) := by
  rw [show (abs s.objs : _root_.Array OsuModel.Sim.OState) = (s.objs.val.map abs).toArray from rfl,
    s3b_arr_modify_toArray _ _ _ hio]
  show ((((s.objs.set i _).set i _).val.map (fun x => (abs x : OsuModel.Sim.OState))).toArray) = _
  rw [vec_set_val', vec_set_val', s3b_map_set_set _ _ _ hio]
  rfl

@[simp] theorem s3b_vec_set_get {α : Type} (v : alloc.vec.Vec α) (i : Usize) (x : α)
    (h : i.val < (v.set i x).val.length) : (v.set i x).val[i.val]'h = x := by
  simp only [vec_set_val', List.getElem_set_self]

theorem s3b_inv_objs {c : sim.state.Ctx} {s X : sim.state.St} (h : SimInv c s)
    (hl : X.objs.val.length = s.objs.val.length)
    (hn : ∀ j (h1 : j < X.objs.val.length) (h2 : j < s.objs.val.length), (X.objs.val[j]'h1).nested = (s.objs.val[j]'h2).nested)
    (hd : X.dict_slots = s.dict_slots) : SimInv c X := by
  obtain ⟨a, b, d, e, f⟩ := h
  refine ⟨by rw [hl]; exact a, fun j h1 h2 => ?_, d, by rw [hd]; exact e, by rw [hd]; exact f⟩
  rw [hn j h1 (by omega)]; exact b j _ h2

theorem s3b_tfinv_set2 {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) {b b' : Nat} (hb : b ≤ b')
    {s X : sim.state.St} (hP : s3b_TfInv P b' s)
    (k : Usize) (B : sim.state.Inst) (hX : X.insts.val = s.insts.val.set k.val B) (hB : P b B.tf ∧ P b B.body_tf) :
    s3b_TfInv P b X := by
  intro ins hins
  rw [hX] at hins
  rcases List.mem_or_eq_of_mem_set hins with h1 | h1
  · exact ⟨E.mono _ _ _ hb (hP _ h1).1, E.mono _ _ _ hb (hP _ h1).2⟩
  · subst h1; exact hB

theorem s3b_dec_ht : decide (sim.step.Part.Head.read_discriminant = sim.step.Part.Top.read_discriminant) = false := by
  simp [sim.step.Part.read_discriminant]
theorem s3b_dec_tt : decide (sim.step.Part.Top.read_discriminant = sim.step.Part.Top.read_discriminant) = true := by
  simp

theorem s3b_ite_main {α : Type} (b f : Bool) (M d : Result α) (h : ¬ (b && !f) = true) :
    (if b = true then (if f = true then M else d) else M) = M := by
  cases b <;> cases f <;> simp_all

/-- the two `ApplyCustomUpdateState` passes after `updateState`'s writes -/
theorem s3b_cs_exists {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) {n b : Nat} {tn fo} {c : sim.state.Ctx}
    {i : Usize} {p : sim.step.Part}
    {ns : sim.state.Armed} (hCS : s3b_CSOk P n tn fo c i p ns) (passes : U64) (s X : sim.state.St)
    (S0 : OsuModel.Sim.St) (hinv : SimInv c X) (hP : s3b_TfInv P (b + n + n) X)
    (hio : i.val < X.objs.val.length) (hr1 : (X.objs.val[i.val]'hio).inst.val < X.insts.val.length)
    (hr2 : (X.objs.val[i.val]'hio).head_inst.val < X.insts.val.length) (hfX : s3b_frame s X)
    (hoX : s3b_objFrame s X) (hS0 : simStS tn X = S0)
    (h1 : X.insts.val.length = s.insts.val.length) (h2 : X.objs.val.length = s.objs.val.length)
    (h3 : X.future_order = s.future_order) (hXu : s3c_usFrame i s X) :
    ∃ s', (do
        let s1 ← sim.step.custom_state c X i p ns false
        if passes >= 2#u64 then sim.step.custom_state c s1 i p ns true else ok s1) = ok s' ∧
      (do OsuModel.Sim.Sim.customState i.val (abs p) (abs ns) false
          if passes.val ≥ 2 then OsuModel.Sim.Sim.customState i.val (abs p) (abs ns) true else pure ()) (simCtxS tn fo c) S0 =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' ∧ s3c_usFrame i s s' := by
  subst hS0
  obtain ⟨s1, hs1, es1, i1, p1, l1, o1, f1, fr1⟩ := hCS (b + n) X false hinv hP hio hr1 hr2
  by_cases hp2 : passes.val ≥ 2
  · have hp2' : passes >= 2#u64 := by scalar_tac
    have hio1 : i.val < s1.objs.val.length := by rw [o1]; exact hio
    obtain ⟨s2, hs2, es2, i2, p2, l2, o2, f2, fr2⟩ := hCS b s1 true i1 p1 hio1
      (by have := hr1; simp only [o1, l1] at *; exact this) (by have := hr2; simp only [o1, l1] at *; exact this)
    refine ⟨s2, by simp [hs1, hp2', hs2], ?_, i2, p2, by omega, by rw [o2, o1]; exact h2, by rw [f2, f1, h3],
      s3b_frame_trans hfX (s3c_ito_frame (s3c_ito_trans fr1 fr2)),
      s3b_objFrame_trans hoX (s3b_objFrame_of_eq (o2.trans o1)), s3c_usFrame_ito hXu (s3c_ito_trans fr1 fr2) (o2.trans o1) (l2.trans l1)⟩
    simp only [simM_bind, es1, Except.bind, simM_ite, if_pos hp2, es2]
  · have hp2' : ¬ passes >= 2#u64 := by intro h; apply hp2; scalar_tac
    refine ⟨s1, by simp [hs1, hp2'], ?_, i1,
      fun ins hins => ⟨E.mono _ _ _ (by omega) (p1 ins hins).1, E.mono _ _ _ (by omega) (p1 ins hins).2⟩, by omega, by rw [o1]; exact h2, by rw [f1, h3],
      s3b_frame_trans hfX (s3c_ito_frame fr1), s3b_objFrame_trans hoX (s3b_objFrame_of_eq o1),
      s3c_usFrame_ito hXu fr1 o1 l1⟩
    simp only [simM_bind, es1, Except.bind, simM_ite, if_neg hp2, simM_pure]

set_option hygiene false in
/-- finishing steps of `update_state_refines` (part `Top`): the two writes, the custom-state passes, the invariants.
Expects `hX`, `ptfF : P tfF`, `pbodyF : P bodyF` and the final Rust values `tfF bodyF leF` in context. -/
macro "s3b_fin_top" : tactic => `(tactic| (
  have hkv' : ∀ x, k.val < (s.insts.set k x).val.length := by intro x; simpa [alloc.vec.Vec.set] using hkv
  simp only [vec_index_mut_eq _ _ hkv, vec_index_mut_eq _ _ (hkv' _), vec_index_mut_eq _ _ hio, bind_ok,
    uncurry_apply_pair]
  have hio' : ∀ x, i.val < (s.objs.set i x).val.length := by intro x; simpa [alloc.vec.Vec.set] using hio
  simp only [vec_index_mut_eq _ _ (hio' _), bind_ok, uncurry_apply_pair]
  apply s3b_cs_exists E hCS passes s _ _ ?inv ?tfi ?hio ?r1 ?r2 ?fr ?ofr ?st ?l1 ?l2 ?l3 ?usf
  case hio => simpa [alloc.vec.Vec.set] using hio
  case fr => exact s3b_frame_refl s
  case usf =>
    refine ⟨hio, ns, (s.objs.val[i.val]'hio).head_armed, leF, (s.objs.val[i.val]'hio).head_lifetime_end, ?_,
      by simp [alloc.vec.Vec.set]⟩
    simp only [s3b_vec_set_get]
    congr 1
    apply alloc.vec.Vec.ext; simp only [vec_set_val', List.set_set]; try rfl
  case ofr =>
    refine ⟨by simp [alloc.vec.Vec.set], fun j h1 h2 => ?_⟩
    simp only [vec_set_val'] at h2 ⊢
    by_cases hj : j = i.val
    · subst hj; simp
    · simp [List.getElem_set, Ne.symm hj]
  case r1 => simp [vec_set_val', List.getElem_set_self]; first | exact hk1 | simpa [alloc.vec.Vec.set] using hk1
  case r2 => simp [vec_set_val', List.getElem_set_self]; first | exact hk2 | simpa [alloc.vec.Vec.set] using hk2
  case l3 => rfl
  case l1 => simp [alloc.vec.Vec.set]
  case l2 => simp [alloc.vec.Vec.set]
  case st =>
    unfold s3b_usSt; rw [hX]
    have e1 := s3b_us_insts tn s k hkv { tfF with delay := 0 } { bodyF with delay := 0 }
    have e2 := s3b_us_objs_top s i hio ns leF
    have e3 : ∀ (O : alloc.vec.Vec sim.state.OState) (I : alloc.vec.Vec sim.state.Inst),
        simStS tn { s with objs := O, insts := I } = { simStS tn s with objs := abs O, insts := abs I } :=
      fun _ _ => rfl
    simp only [s3b_vec_set_get]
    rw [e3, e1, e2]
    rfl
  case inv =>
    refine s3b_inv_objs hinv (by simp [alloc.vec.Vec.set]) ?_ rfl
    intro j h1 h2
    simp only [vec_set_val'] at h1 ⊢
    by_cases hj : j = i.val
    · subst hj; simp
    · simp [List.getElem_set, Ne.symm hj]
  case tfi =>
    refine s3b_tfinv_set2 E (by omega) hP k ({ s.insts.val[k.val]'hkv with tf := { tfF with delay := 0 }, body_tf := { bodyF with delay := 0 } }) ?_
      ⟨E.mono _ _ _ (by omega) (E.delay _ _ _ ptfF), E.mono _ _ _ (by omega) (E.delay _ _ _ pbodyF)⟩
    simp only [vec_set_val', List.set_set, List.getElem_set_self]))

set_option hygiene false in
/-- `s3b_fin_top` for part `Head` -/
macro "s3b_fin_head" : tactic => `(tactic| (
  have hkv' : ∀ x, k.val < (s.insts.set k x).val.length := by intro x; simpa [alloc.vec.Vec.set] using hkv
  simp only [vec_index_mut_eq _ _ hkv, vec_index_mut_eq _ _ (hkv' _), vec_index_mut_eq _ _ hio, bind_ok,
    uncurry_apply_pair]
  have hio' : ∀ x, i.val < (s.objs.set i x).val.length := by intro x; simpa [alloc.vec.Vec.set] using hio
  simp only [vec_index_mut_eq _ _ (hio' _), bind_ok, uncurry_apply_pair]
  apply s3b_cs_exists E hCS passes s _ _ ?inv ?tfi ?hio ?r1 ?r2 ?fr ?ofr ?st ?l1 ?l2 ?l3 ?usf
  case hio => simpa [alloc.vec.Vec.set] using hio
  case fr => exact s3b_frame_refl s
  case usf =>
    refine ⟨hio, (s.objs.val[i.val]'hio).armed, ns, (s.objs.val[i.val]'hio).lifetime_end, leF, ?_,
      by simp [alloc.vec.Vec.set]⟩
    simp only [s3b_vec_set_get]
    congr 1
    apply alloc.vec.Vec.ext; simp only [vec_set_val', List.set_set]; try rfl
  case ofr =>
    refine ⟨by simp [alloc.vec.Vec.set], fun j h1 h2 => ?_⟩
    simp only [vec_set_val'] at h2 ⊢
    by_cases hj : j = i.val
    · subst hj; simp
    · simp [List.getElem_set, Ne.symm hj]
  case r1 => simp [vec_set_val', List.getElem_set_self]; first | exact hk1 | simpa [alloc.vec.Vec.set] using hk1
  case r2 => simp [vec_set_val', List.getElem_set_self]; first | exact hk2 | simpa [alloc.vec.Vec.set] using hk2
  case l3 => rfl
  case l1 => simp [alloc.vec.Vec.set]
  case l2 => simp [alloc.vec.Vec.set]
  case st =>
    unfold s3b_usSt; rw [hX]
    have e1 := s3b_us_insts tn s k hkv { tfF with delay := 0 } { bodyF with delay := 0 }
    have e2 := s3b_us_objs_head s i hio ns leF
    have e3 : ∀ (O : alloc.vec.Vec sim.state.OState) (I : alloc.vec.Vec sim.state.Inst),
        simStS tn { s with objs := O, insts := I } = { simStS tn s with objs := abs O, insts := abs I } :=
      fun _ _ => rfl
    simp only [s3b_vec_set_get]
    rw [e3, e1, e2]
    rfl
  case inv =>
    refine s3b_inv_objs hinv (by simp [alloc.vec.Vec.set]) ?_ rfl
    intro j h1 h2
    simp only [vec_set_val'] at h1 ⊢
    by_cases hj : j = i.val
    · subst hj; simp
    · simp [List.getElem_set, Ne.symm hj]
  case tfi =>
    refine s3b_tfinv_set2 E (by omega) hP k ({ s.insts.val[k.val]'hkv with tf := { tfF with delay := 0 }, body_tf := { bodyF with delay := 0 } }) ?_
      ⟨E.mono _ _ _ (by omega) (E.delay _ _ _ ptfF), E.mono _ _ _ (by omega) (E.delay _ _ _ pbodyF)⟩
    simp only [vec_set_val', List.set_set, List.getElem_set_self]))

-- CONDITIONAL: s3b_CSOk (owed: sim.step.custom_state_refines)
theorem s3b_update_state_top (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) (force : Bool)
    (passes : U64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + n + n + 4) s) (hCS : s3b_CSOk P n tn fo c i p ns)
    (hpv : p = sim.step.Part.Top) (hio : i.val < s.objs.val.length) (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length) :
    ∃ s', sim.step.update_state c s i p ns force passes = ok s' ∧
      OsuModel.Sim.Sim.updateState i.val (abs p) (abs ns) force passes.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' ∧ s3c_usFrame i s s' := by
  have hi : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact hio
  obtain ⟨a, ha, ea⟩ := sim.step.part_armed_refines tn fo c s i p hio
  obtain ⟨k, hkk, ek⟩ := sim.step.part_inst_refines tn fo c s i p hio
  obtain ⟨r, hr, er⟩ := sim.step.part_ref_refines tn fo c (simStS tn s) i p hhi hhb
  have hkv : k.val < s.insts.val.length := by
    cases p <;> simp [sim.step.part_inst, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hio] at hkk <;>
      rw [← hkk] <;> assumption
  have hhv : (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length → simRefOk c ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := by
    intro hl
    have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
      rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
    exact ⟨hi, fun _ => by simp only [hc]; simpa using hl⟩
  have hrok : simRefOk c r := by
    cases p
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      rw [← hr]; exact ⟨hi, fun h0 => by simp at h0⟩
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hhi, lift] at hr
      rw [← hr]; exact hhv (hhn (Or.inl rfl))
  have hsrok : ∀ r, simRefOk c r → simSRefOk s r := by
    intro r ⟨h1, h2⟩
    have h1' : r.top.val < s.objs.val.length := by rw [hinv.objs_len]; exact h1
    exact ⟨h1', fun h0 => by rw [hinv.nested_len _ h1' h1]; exact h2 h0⟩
  obtain ⟨h, hh, eh⟩ := sim.step.hobj_of_refines tn fo c r hrok
  obtain ⟨ro, hro, ero⟩ := sim.step.res_of_refines tn fo c s r (hsrok r hrok)
  have hhead : kindS h.kind = .slider → simRefOk c ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := by
    intro hks
    apply hhv; apply hhn
    cases p
    · right
      simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      subst hr
      simp [sim.step.hobj_of, vec_index_eq _ _ hi] at hh
      rw [← hh] at hks; cases hk : (c.pb.objects.val[i.val]'hi).h.kind <;> simp_all [kindS]
    · left; rfl
  have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
    rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
  have ehead : ∀ S, OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) S = .ok ((c.head_idx.val[i.val]'hhi).val, S) := by
    intro S
    have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
    simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]
  obtain ⟨hb, hhb, ehb⟩ : ∃ hb : Bool, (kindS h.kind = .slider →
      sim.step.is_hit_ref s ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ = ok hb) ∧
      ((hobjS tn h).kind = .slider → ∃ hj, OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) (simStS tn s) = .ok (hj, simStS tn s) ∧
        OsuModel.Sim.Sim.isHitRef (i.val, (hj : Int)) (simCtxS tn fo c) (simStS tn s) = .ok (hb, simStS tn s)) := by
    by_cases hks : kindS h.kind = .slider
    · obtain ⟨b, hb1, eb1⟩ := sim.step.is_hit_ref_refines tn fo c s _ (hsrok _ (hhead hks))
      refine ⟨b, fun _ => hb1, fun _ => ⟨_, ehead _, ?_⟩⟩
      have : (abs (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
          (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) := by simp [abs, hc]
      rw [← this]; exact eb1
    · exact ⟨false, fun h' => absurd h' hks, fun h' => absurd (by simpa [hobjS] using h') hks⟩
  have hkS : k.val < (simStS tn s).insts.size := by simpa [s3b_stS_insts] using hkv
  have hioS : i.val < (simStS tn s).objs.size := by simpa using hio
  rw [s3b_updateState_spec (simCtxS tn fo c) (simStS tn s) i.val (abs p) (abs ns) force passes.val (abs a) k.val
    (topS tn (c.pb.objects.val[i.val]'hi)) (abs r) (hobjS tn h) (ro.map abs) hb ea ek (s3b_topObj tn fo c _ i.val hi)
    er (eh _) ero hkS hioS ehb rfl]
  unfold sim.step.update_state
  rw [ha]
  simp only [bind_ok, armed_eq_ok]
  have hcond : ((abs a : OsuModel.Sim.Armed) == abs ns) = (armedS a == armedS ns) := rfl
  rw [hcond]
  by_cases hb2 : ((armedS a == armedS ns) && !force) = true
  · have hb3 : (armedS a == armedS ns) = true := by revert hb2; cases (armedS a == armedS ns) <;> simp
    have hf : force = false := by revert hb2; cases force <;> simp [hb3]
    subst hf
    exact ⟨s, by simp [hb3], by rw [if_pos hb2], hinv,
      fun ins hins => ⟨E.mono _ _ _ (by omega) (hP ins hins).1, E.mono _ _ _ (by omega) (hP ins hins).2⟩,
      rfl, rfl, rfl, s3b_frame_refl s, s3b_objFrame_of_eq rfl, s3c_usFrame_refl i s hio⟩
  rw [if_neg hb2]
  rw [s3b_ite_main _ _ _ _ hb2]
  simp only [hkk, hr, hh, hro, bind_ok, part_eq_ok, kind_eq_ok, vec_index_eq _ _ hi, vec_index_eq _ _ hkv,
    s3b_tobj_clone]
  have hPk := hP _ (List.getElem_mem hkv)
  obtain ⟨tf1, hc1, ec1, pc1⟩ := E.clear _ _ hPk.1
  rw [hc1]
  obtain ⟨hst, ehst, hhst⟩ : ∃ hst, s3b_hst (hobjS tn h) (ro.map (fun x => (abs x : OsuModel.Sim.Res))) = hst ∧
      ((ro = none ∧ hst = h.end_time) ∨ ∃ x, ro = some x ∧ sim.step.time_absolute h x.time = ok hst) := by
    rcases ro with _ | x
    · exact ⟨_, rfl, Or.inl ⟨rfl, by simp [s3b_hst, hobjS]⟩⟩
    · obtain ⟨ta, hta, eta⟩ := sim.step.time_absolute_refines h x.time
      refine ⟨ta, ?_, Or.inr ⟨x, rfl, hta⟩⟩
      simp only [Option.map_some, s3b_hst]
      have : OsuModel.Sim.Sim.timeAbsolute (hobjS tn h) (abs x : OsuModel.Sim.Res).2 =
          OsuModel.Sim.Sim.timeAbsolute (hobjS simTnDefault h) x.time := by
        simp [OsuModel.Sim.Sim.timeAbsolute, hobjS, abs]
      rw [this]; exact eta
  rw [ehst]
  have e0 : ((simStS tn s).insts[k.val]'hkS) = abs (s.insts.val[k.val]'hkv) := by simp [s3b_stS_insts]
  rw [e0]
  obtain ⟨tf3, hf3, ef3, pf3⟩ := E.fade (b + n + n + 2) { tf1 with delay := h.start - h.preempt - s.t } s.t 0 .None
    (E.delay _ _ _ pc1)
  have ef3' : OsuModel.Sim.fadeInFromZero (OsuModel.Sim.absSeq (OsuModel.Sim.clearState
      (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf) (simStS tn s).t
      ((hobjS tn h).start - (hobjS tn h).preempt)) (simStS tn s).t = abs tf3 := by
    rw [show (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf = abs (s.insts.val[k.val]'hkv).tf from rfl, ec1]
    exact ef3
  rcases hhst with ⟨rfl, rfl⟩ | ⟨x, rfl, hta⟩
  on_goal 1 =>
    simp only [bind_ok, uncurry_apply_pair]
    generalize h.end_time = hst at ehst ⊢
  on_goal 2 => simp only [bind_ok, hta, uncurry_apply_pair]
  all_goals (
    subst hpv; simp only [s3b_dec_ht, s3b_dec_tt, decide_true, if_true, if_false, bind_ok,
      Bool.false_eq_true, sim.transforms.abs_seq, float.F64.sub, sim_step_F64_0]
    have hho : h = (c.pb.objects.val[i.val]'hi).h := by
      simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      subst hr
      simp [sim.step.hobj_of, vec_index_eq _ _ hi] at hh
      exact hh.symm
    cases hsl : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Slider) <;>
      simp only [if_true, if_false, Bool.false_eq_true, bind_ok]
    · rw [hf3]; simp only [bind_ok]
      cases hkd : h.kind <;> simp (config := {decide := true}) only [kindS, if_true, if_false, Bool.false_eq_true]
      all_goals first
        | (
              obtain ⟨leF, tfF, hcs, ptfF, ecs, ele⟩ := sim.step.circle_hit_state_refines E (b + n + n) _ (E.delay _ _ (hst - s.t) pf3) s.t ns
              rw [hcs]; simp only [bind_ok, uncurry_apply_pair]
              generalize hBF : (s.insts.val[k.val]'hkv).body_tf = bodyF
              have pbodyF : P (b + n + n) bodyF := by rw [← hBF]; exact E.mono _ _ _ (by omega) hPk.2
              have hX : s3b_usCore (simStS tn s).t hst ((hobjS tn h).start - (hobjS tn h).preempt) (hobjS tn h).fadeIn
                  (hobjS tn h).kind (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider)
                  (abs ns) hb (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf =
                  (abs { tfF with delay := 0 }, abs { bodyF with delay := 0 }, leF) := by
                subst hBF
                have hk' : (hobjS tn h).kind = kindS h.kind := rfl
                have hsl' : (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider) = false := by
                  rw [show (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top) = true from rfl, Bool.true_and]
                  simpa [topS, hobjS, kindS] using hsl
                unfold s3b_usCore
                rw [hk', hsl', hkd]
                simp only [kindS, Bool.false_eq_true, if_false]
                rw [ef3', ele]
                refine Prod.ext ?_ (Prod.ext ?_ ?_)
                · show _ = { (abs tfF : OsuModel.Sim.TObj) with delay := 0 }
                  rw [ecs]; rfl
                · rfl
                · show _ = OsuModel.Sim.latestEnd (abs tfF) _
                  rw [ecs]; rfl
              s3b_fin_top)
        | (
              obtain ⟨leF, tfF, hcs, ptfF, ecs, ele⟩ := sim.step.other_hit_state_refines E (b + n + n) _ (E.mono _ _ _ (by omega) (E.delay _ _ (hst - s.t) pf3)) s.t
              rw [hcs]; simp only [bind_ok, uncurry_apply_pair]
              generalize hBF : (s.insts.val[k.val]'hkv).body_tf = bodyF
              have pbodyF : P (b + n + n) bodyF := by rw [← hBF]; exact E.mono _ _ _ (by omega) hPk.2
              have hX : s3b_usCore (simStS tn s).t hst ((hobjS tn h).start - (hobjS tn h).preempt) (hobjS tn h).fadeIn
                  (hobjS tn h).kind (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider)
                  (abs ns) hb (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf =
                  (abs { tfF with delay := 0 }, abs { bodyF with delay := 0 }, leF) := by
                subst hBF
                have hk' : (hobjS tn h).kind = kindS h.kind := rfl
                have hsl' : (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider) = false := by
                  rw [show (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top) = true from rfl, Bool.true_and]
                  simpa [topS, hobjS, kindS] using hsl
                unfold s3b_usCore
                rw [hk', hsl', hkd]
                simp only [kindS, Bool.false_eq_true, if_false]
                rw [ef3', ele]
                refine Prod.ext ?_ (Prod.ext ?_ ?_)
                · show _ = { (abs tfF : OsuModel.Sim.TObj) with delay := 0 }
                  rw [ecs]; rfl
                · rfl
                · show _ = OsuModel.Sim.latestEnd (abs tfF) _
                  rw [ecs]; rfl
              s3b_fin_top)
        | (exfalso; rw [hho] at hkd; rw [hkd] at hsl; exact absurd hsl (by decide))
    · obtain ⟨b1, hcb, ecb, pcb⟩ := E.clear _ _ hPk.2
      rw [hcb]; simp only [bind_ok]
      rw [hf3]; simp only [bind_ok]
      obtain ⟨b3, hfb, efb, pfb⟩ := E.fade (b + n + n + 2) { b1 with delay := h.start - h.preempt - s.t } s.t h.fade_in .None
        (E.delay _ _ _ pcb)
      rw [hfb]; simp only [bind_ok]
      have hkd : h.kind = .Slider := by
        rw [hho]; cases hk0 : (c.pb.objects.val[i.val]'hi).h.kind <;> simp [hk0, kindS] at hsl ⊢ <;>
          exact absurd hsl (by decide)
      have hks : kindS h.kind = .slider := by rw [hkd]; rfl
      rw [hkd]; simp (config := {decide := true}) only [kindS, if_true, if_false, Bool.false_eq_true]
      simp only [vec_index_eq _ _ hhi, lift, bind_ok, hhb hks]
      obtain ⟨leF, tfF, bodyF, hss, ptfF, pbodyF, ebs, ets, ele⟩ :=
        sim.step.slider_hit_state_refines E (b + n + n) _ _ (E.mono _ _ _ (by omega) (E.delay _ _ (hst - s.t) pf3))
          (E.mono _ _ _ (by omega) (E.delay _ _ (hst - s.t) pfb)) s.t ns hb
      rw [hss]; simp only [bind_ok, uncurry_apply_pair]
      have hX : s3b_usCore (simStS tn s).t hst ((hobjS tn h).start - (hobjS tn h).preempt) (hobjS tn h).fadeIn
                  (hobjS tn h).kind (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider)
                  (abs ns) hb (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf =
                  (abs { tfF with delay := 0 }, abs { bodyF with delay := 0 }, leF) := by
        have hk' : (hobjS tn h).kind = kindS h.kind := rfl
        have hsl' : (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top &&
            (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider) = true := by
          rw [show (abs sim.step.Part.Top == OsuModel.Sim.Sim.Part.top) = true from rfl, Bool.true_and]
          simpa [topS, hobjS, kindS] using hsl
        have efb' : OsuModel.Sim.fadeInFromZero (OsuModel.Sim.absSeq (OsuModel.Sim.clearState
            (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf) (simStS tn s).t
            ((hobjS tn h).start - (hobjS tn h).preempt)) (simStS tn s).t (hobjS tn h).fadeIn = abs b3 := by
          rw [show (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf = abs (s.insts.val[k.val]'hkv).body_tf from rfl, ecb]
          exact efb
        unfold s3b_usCore
        rw [hk', hsl', hks]
        simp only [if_true]
        rw [ef3', efb', ele]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show _ = { (abs tfF : OsuModel.Sim.TObj) with delay := 0 }
          rw [ets]; rfl
        · show _ = { (abs bodyF : OsuModel.Sim.TObj) with delay := 0 }
          rw [ebs]; rfl
        · rw [ets]; rfl
      s3b_fin_top)

-- CONDITIONAL: s3b_CSOk (owed: sim.step.custom_state_refines)
theorem s3b_update_state_head (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) (force : Bool)
    (passes : U64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + n + n + 4) s) (hCS : s3b_CSOk P n tn fo c i p ns)
    (hpv : p = sim.step.Part.Head) (hio : i.val < s.objs.val.length) (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length) :
    ∃ s', sim.step.update_state c s i p ns force passes = ok s' ∧
      OsuModel.Sim.Sim.updateState i.val (abs p) (abs ns) force passes.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' ∧ s3c_usFrame i s s' := by
  have hi : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact hio
  obtain ⟨a, ha, ea⟩ := sim.step.part_armed_refines tn fo c s i p hio
  obtain ⟨k, hkk, ek⟩ := sim.step.part_inst_refines tn fo c s i p hio
  obtain ⟨r, hr, er⟩ := sim.step.part_ref_refines tn fo c (simStS tn s) i p hhi hhb
  have hkv : k.val < s.insts.val.length := by
    cases p <;> simp [sim.step.part_inst, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hio] at hkk <;>
      rw [← hkk] <;> assumption
  have hhv : (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length → simRefOk c ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := by
    intro hl
    have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
      rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
    exact ⟨hi, fun _ => by simp only [hc]; simpa using hl⟩
  have hrok : simRefOk c r := by
    cases p
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      rw [← hr]; exact ⟨hi, fun h0 => by simp at h0⟩
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hhi, lift] at hr
      rw [← hr]; exact hhv (hhn (Or.inl rfl))
  have hsrok : ∀ r, simRefOk c r → simSRefOk s r := by
    intro r ⟨h1, h2⟩
    have h1' : r.top.val < s.objs.val.length := by rw [hinv.objs_len]; exact h1
    exact ⟨h1', fun h0 => by rw [hinv.nested_len _ h1' h1]; exact h2 h0⟩
  obtain ⟨h, hh, eh⟩ := sim.step.hobj_of_refines tn fo c r hrok
  obtain ⟨ro, hro, ero⟩ := sim.step.res_of_refines tn fo c s r (hsrok r hrok)
  have hhead : kindS h.kind = .slider → simRefOk c ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ := by
    intro hks
    apply hhv; apply hhn
    cases p
    · right
      simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      subst hr
      simp [sim.step.hobj_of, vec_index_eq _ _ hi] at hh
      rw [← hh] at hks; cases hk : (c.pb.objects.val[i.val]'hi).h.kind <;> simp_all [kindS]
    · left; rfl
  have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
    rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
  have ehead : ∀ S, OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) S = .ok ((c.head_idx.val[i.val]'hhi).val, S) := by
    intro S
    have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
    simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]
  obtain ⟨hb, hhb, ehb⟩ : ∃ hb : Bool, (kindS h.kind = .slider →
      sim.step.is_hit_ref s ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ = ok hb) ∧
      ((hobjS tn h).kind = .slider → ∃ hj, OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) (simStS tn s) = .ok (hj, simStS tn s) ∧
        OsuModel.Sim.Sim.isHitRef (i.val, (hj : Int)) (simCtxS tn fo c) (simStS tn s) = .ok (hb, simStS tn s)) := by
    by_cases hks : kindS h.kind = .slider
    · obtain ⟨b, hb1, eb1⟩ := sim.step.is_hit_ref_refines tn fo c s _ (hsrok _ (hhead hks))
      refine ⟨b, fun _ => hb1, fun _ => ⟨_, ehead _, ?_⟩⟩
      have : (abs (⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
          (i.val, ((c.head_idx.val[i.val]'hhi).val : Int)) := by simp [abs, hc]
      rw [← this]; exact eb1
    · exact ⟨false, fun h' => absurd h' hks, fun h' => absurd (by simpa [hobjS] using h') hks⟩
  have hkS : k.val < (simStS tn s).insts.size := by simpa [s3b_stS_insts] using hkv
  have hioS : i.val < (simStS tn s).objs.size := by simpa using hio
  rw [s3b_updateState_spec (simCtxS tn fo c) (simStS tn s) i.val (abs p) (abs ns) force passes.val (abs a) k.val
    (topS tn (c.pb.objects.val[i.val]'hi)) (abs r) (hobjS tn h) (ro.map abs) hb ea ek (s3b_topObj tn fo c _ i.val hi)
    er (eh _) ero hkS hioS ehb rfl]
  unfold sim.step.update_state
  rw [ha]
  simp only [bind_ok, armed_eq_ok]
  have hcond : ((abs a : OsuModel.Sim.Armed) == abs ns) = (armedS a == armedS ns) := rfl
  rw [hcond]
  by_cases hb2 : ((armedS a == armedS ns) && !force) = true
  · have hb3 : (armedS a == armedS ns) = true := by revert hb2; cases (armedS a == armedS ns) <;> simp
    have hf : force = false := by revert hb2; cases force <;> simp [hb3]
    subst hf
    exact ⟨s, by simp [hb3], by rw [if_pos hb2], hinv,
      fun ins hins => ⟨E.mono _ _ _ (by omega) (hP ins hins).1, E.mono _ _ _ (by omega) (hP ins hins).2⟩,
      rfl, rfl, rfl, s3b_frame_refl s, s3b_objFrame_of_eq rfl, s3c_usFrame_refl i s hio⟩
  rw [if_neg hb2]
  rw [s3b_ite_main _ _ _ _ hb2]
  simp only [hkk, hr, hh, hro, bind_ok, part_eq_ok, kind_eq_ok, vec_index_eq _ _ hi, vec_index_eq _ _ hkv,
    s3b_tobj_clone]
  have hPk := hP _ (List.getElem_mem hkv)
  obtain ⟨tf1, hc1, ec1, pc1⟩ := E.clear _ _ hPk.1
  rw [hc1]
  obtain ⟨hst, ehst, hhst⟩ : ∃ hst, s3b_hst (hobjS tn h) (ro.map (fun x => (abs x : OsuModel.Sim.Res))) = hst ∧
      ((ro = none ∧ hst = h.end_time) ∨ ∃ x, ro = some x ∧ sim.step.time_absolute h x.time = ok hst) := by
    rcases ro with _ | x
    · exact ⟨_, rfl, Or.inl ⟨rfl, by simp [s3b_hst, hobjS]⟩⟩
    · obtain ⟨ta, hta, eta⟩ := sim.step.time_absolute_refines h x.time
      refine ⟨ta, ?_, Or.inr ⟨x, rfl, hta⟩⟩
      simp only [Option.map_some, s3b_hst]
      have : OsuModel.Sim.Sim.timeAbsolute (hobjS tn h) (abs x : OsuModel.Sim.Res).2 =
          OsuModel.Sim.Sim.timeAbsolute (hobjS simTnDefault h) x.time := by
        simp [OsuModel.Sim.Sim.timeAbsolute, hobjS, abs]
      rw [this]; exact eta
  rw [ehst]
  have e0 : ((simStS tn s).insts[k.val]'hkS) = abs (s.insts.val[k.val]'hkv) := by simp [s3b_stS_insts]
  rw [e0]
  obtain ⟨tf3, hf3, ef3, pf3⟩ := E.fade (b + n + n + 2) { tf1 with delay := h.start - h.preempt - s.t } s.t 0 .None
    (E.delay _ _ _ pc1)
  have ef3' : OsuModel.Sim.fadeInFromZero (OsuModel.Sim.absSeq (OsuModel.Sim.clearState
      (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf) (simStS tn s).t
      ((hobjS tn h).start - (hobjS tn h).preempt)) (simStS tn s).t = abs tf3 := by
    rw [show (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf = abs (s.insts.val[k.val]'hkv).tf from rfl, ec1]
    exact ef3
  rcases hhst with ⟨rfl, rfl⟩ | ⟨x, rfl, hta⟩
  on_goal 1 =>
    simp only [bind_ok, uncurry_apply_pair]
    generalize h.end_time = hst at ehst ⊢
  on_goal 2 => simp only [bind_ok, hta, uncurry_apply_pair]
  all_goals (
    subst hpv; simp only [s3b_dec_ht, s3b_dec_tt, decide_true, if_true, if_false, bind_ok,
      Bool.false_eq_true, sim.transforms.abs_seq, float.F64.sub, sim_step_F64_0]
    rw [hf3]; simp only [bind_ok]
    cases hkd : h.kind <;> simp (config := {decide := true}) only [kindS, if_true, if_false, Bool.false_eq_true]
    all_goals first
      | (
              obtain ⟨leF, tfF, hcs, ptfF, ecs, ele⟩ := sim.step.circle_hit_state_refines E (b + n + n) _ (E.delay _ _ (hst - s.t) pf3) s.t ns
              rw [hcs]; simp only [bind_ok, uncurry_apply_pair]
              generalize hBF : (s.insts.val[k.val]'hkv).body_tf = bodyF
              have pbodyF : P (b + n + n) bodyF := by rw [← hBF]; exact E.mono _ _ _ (by omega) hPk.2
              have hX : s3b_usCore (simStS tn s).t hst ((hobjS tn h).start - (hobjS tn h).preempt) (hobjS tn h).fadeIn
                  (hobjS tn h).kind (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider)
                  (abs ns) hb (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf =
                  (abs { tfF with delay := 0 }, abs { bodyF with delay := 0 }, leF) := by
                subst hBF
                have hk' : (hobjS tn h).kind = kindS h.kind := rfl
                have hsl' : (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider) = false := rfl
                unfold s3b_usCore
                rw [hk', hsl', hkd]
                simp only [kindS, Bool.false_eq_true, if_false]
                rw [ef3', ele]
                refine Prod.ext ?_ (Prod.ext ?_ ?_)
                · show _ = { (abs tfF : OsuModel.Sim.TObj) with delay := 0 }
                  rw [ecs]; rfl
                · rfl
                · show _ = OsuModel.Sim.latestEnd (abs tfF) _
                  rw [ecs]; rfl
              s3b_fin_head)
      | (
              obtain ⟨leF, tfF, hcs, ptfF, ecs, ele⟩ := sim.step.other_hit_state_refines E (b + n + n) _ (E.mono _ _ _ (by omega) (E.delay _ _ (hst - s.t) pf3)) s.t
              rw [hcs]; simp only [bind_ok, uncurry_apply_pair]
              generalize hBF : (s.insts.val[k.val]'hkv).body_tf = bodyF
              have pbodyF : P (b + n + n) bodyF := by rw [← hBF]; exact E.mono _ _ _ (by omega) hPk.2
              have hX : s3b_usCore (simStS tn s).t hst ((hobjS tn h).start - (hobjS tn h).preempt) (hobjS tn h).fadeIn
                  (hobjS tn h).kind (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider)
                  (abs ns) hb (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf =
                  (abs { tfF with delay := 0 }, abs { bodyF with delay := 0 }, leF) := by
                subst hBF
                have hk' : (hobjS tn h).kind = kindS h.kind := rfl
                have hsl' : (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider) = false := rfl
                unfold s3b_usCore
                rw [hk', hsl', hkd]
                simp only [kindS, Bool.false_eq_true, if_false]
                rw [ef3', ele]
                refine Prod.ext ?_ (Prod.ext ?_ ?_)
                · show _ = { (abs tfF : OsuModel.Sim.TObj) with delay := 0 }
                  rw [ecs]; rfl
                · rfl
                · show _ = OsuModel.Sim.latestEnd (abs tfF) _
                  rw [ecs]; rfl
              s3b_fin_head)
      | (
        have hks : kindS h.kind = .slider := by rw [hkd]; rfl
        simp only [vec_index_eq _ _ hhi, lift, bind_ok, hhb hks]
        obtain ⟨leF, tfF, bodyF, hss, ptfF, pbodyF, ebs, ets, ele⟩ :=
          sim.step.slider_hit_state_refines E (b + n + n) _ _ (E.mono _ _ _ (by omega) (E.delay _ _ (hst - s.t) pf3))
            (E.mono _ _ _ (by omega) (E.delay _ _ (hst - s.t) hPk.2)) s.t ns hb
        rw [hss]; simp only [bind_ok, uncurry_apply_pair]
        have hX : s3b_usCore (simStS tn s).t hst ((hobjS tn h).start - (hobjS tn h).preempt) (hobjS tn h).fadeIn
                  (hobjS tn h).kind (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top &&
                    (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider)
                  (abs ns) hb (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).tf (abs (s.insts.val[k.val]'hkv) : OsuModel.Sim.Inst).bodyTf =
                  (abs { tfF with delay := 0 }, abs { bodyF with delay := 0 }, leF) := by
          have hk' : (hobjS tn h).kind = kindS h.kind := rfl
          have hsl' : (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top &&
              (topS tn (c.pb.objects.val[i.val]'hi)).h.kind == OsuModel.Sim.Kind.slider) = false := rfl
          unfold s3b_usCore
          rw [hk', hsl', hks]
          simp only [Bool.false_eq_true, if_false]
          rw [ef3', ele]
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · show _ = { (abs tfF : OsuModel.Sim.TObj) with delay := 0 }
            rw [ets]; rfl
          · show _ = { (abs bodyF : OsuModel.Sim.TObj) with delay := 0 }
            rw [ebs]; rfl
          · rw [ets]; rfl
        s3b_fin_head))

/-- `DrawableHitObject.UpdateState` (`Sim.updateState`): the part's transformables are rebuilt (clear, initial
fade-in, hit-state transforms), its armed state and lifetime end written, then the custom-state handlers run (twice
for a forwarded nested part). Only `insts[k]`, `objs[i]` (armed / lifetime end) and what `customState` touches
change; `insts`/`objs` sizes are preserved. Plus the strong frame `s3c_usFrame` (sim3c). -/
theorem s3c_update_state_strong (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) (force : Bool)
    (passes : U64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + n + n + 4) s) (hCS : s3b_CSOk P n tn fo c i p ns)
    (hio : i.val < s.objs.val.length) (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length) :
    ∃ s', sim.step.update_state c s i p ns force passes = ok s' ∧
      OsuModel.Sim.Sim.updateState i.val (abs p) (abs ns) force passes.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' ∧ s3c_usFrame i s s' := by
  cases p
  · exact s3b_update_state_top tn fo E b n c s i _ ns force passes hinv hP hCS rfl hio hk1 hk2 hhi hhb hhn
  · exact s3b_update_state_head tn fo E b n c s i _ ns force passes hinv hP hCS rfl hio hk1 hk2 hhi hhb hhn

-- CONDITIONAL: s3b_CSOk (owed: sim.step.custom_state_refines)
theorem sim.step.update_state_refines (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) (force : Bool)
    (passes : U64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + n + n + 4) s) (hCS : s3b_CSOk P n tn fo c i p ns)
    (hio : i.val < s.objs.val.length) (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length) :
    ∃ s', sim.step.update_state c s i p ns force passes = ok s' ∧
      OsuModel.Sim.Sim.updateState i.val (abs p) (abs ns) force passes.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
    s3c_update_state_strong tn fo E b n c s i p ns force passes hinv hP hCS hio hk1 hk2 hhi hhb hhn
  exact ⟨s', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `update_state_from_result_refines` + the strong frame `s3c_usFrame` (sim3c) -/
theorem s3c_update_state_from_result_strong (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part)     (passes : U64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + n + n + 4) s) (hCS : ∀ ns, s3b_CSOk P n tn fo c i p ns)
    (hio : i.val < s.objs.val.length) (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length) :
    ∃ s', sim.step.update_state_from_result c s i p passes = ok s' ∧
      OsuModel.Sim.Sim.updateStateFromResult i.val (abs p) passes.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' ∧ s3c_usFrame i s s' := by
  have hi : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact hio
  obtain ⟨r, hr, er⟩ := sim.step.part_ref_refines tn fo c (simStS tn s) i p hhi hhb
  have hrs : simSRefOk s r := by
    have hio' : i.val < s.objs.val.length := hio
    cases p
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant] at hr
      rw [← hr]; exact ⟨hio', fun h0 => by simp at h0⟩
    · simp [sim.step.part_ref, part_eq_ok, sim.step.Part.read_discriminant, vec_index_eq _ _ hhi, lift] at hr
      rw [← hr]
      have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
        rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
      refine ⟨hio', fun _ => ?_⟩
      simp only [hc, Int.toNat_natCast]
      rw [hinv.nested_len _ hio' hi]; exact hhn (Or.inl rfl)
  obtain ⟨ro, hro, ero⟩ := sim.step.res_of_refines tn fo c s r hrs
  have fin : ∀ st2 : sim.state.Armed, sim.step.update_state_from_result c s i p passes = sim.step.update_state c s i p st2 true passes →
      OsuModel.Sim.Sim.updateStateFromResult i.val (abs p) passes.val (simCtxS tn fo c) (simStS tn s) =
        OsuModel.Sim.Sim.updateState i.val (abs p) (abs st2) true passes.val (simCtxS tn fo c) (simStS tn s) →
      ∃ s', sim.step.update_state_from_result c s i p passes = ok s' ∧
        OsuModel.Sim.Sim.updateStateFromResult i.val (abs p) passes.val (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
        SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
        s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
        s3b_objFrame s s' ∧ s3c_usFrame i s s' := by
    intro st2 hR hS
    obtain ⟨s', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := s3c_update_state_strong tn fo E b n c s i p st2 true passes hinv hP
      (hCS st2) hio hk1 hk2 hhi hhb hhn
    exact ⟨s', by rw [hR]; exact h1, by rw [hS]; exact h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hR0 : sim.step.update_state_from_result c s i p passes = (do
      let st2 ← (match ro with
        | none => ok sim.state.Armed.Idle
        | some x => do let b ← sim.basic.is_hit x.ty; if b then ok sim.state.Armed.Hit else ok sim.state.Armed.Miss)
      sim.step.update_state c s i p st2 true passes) := by
    unfold sim.step.update_state_from_result; rw [hr, bind_ok, hro, bind_ok]; rfl
  have hS0 : OsuModel.Sim.Sim.updateStateFromResult i.val (abs p) passes.val (simCtxS tn fo c) (simStS tn s) =
      OsuModel.Sim.Sim.updateState i.val (abs p) (match ro.map (fun x => (abs x : OsuModel.Sim.Res)) with
        | some (ty, _) => if ty.isHit then OsuModel.Sim.Armed.hit else .miss
        | none => .idle) true passes.val (simCtxS tn fo c) (simStS tn s) := by
    unfold OsuModel.Sim.Sim.updateStateFromResult
    rw [simM_bind, er, s3b_ebok, simM_bind, ero, s3b_ebok]
    rfl
  rcases ro with _ | x
  · exact fin .Idle (by rw [hR0]; simp only [bind_ok]) (by rw [hS0]; rfl)
  · obtain ⟨b, hb, eb⟩ := sim.basic.is_hit_refines x.ty
    have eb' : (hrS x.ty).isHit = b := eb
    cases b
    · exact fin .Miss (by rw [hR0]; simp [hb]) (by
        rw [hS0]; simp only [Option.map_some]
        have : (abs x : OsuModel.Sim.Res).1.isHit = (hrS x.ty).isHit := rfl
        rw [this, eb']; rfl)
    · exact fin .Hit (by rw [hR0]; simp [hb]) (by
        rw [hS0]; simp only [Option.map_some]
        have : (abs x : OsuModel.Sim.Res).1.isHit = (hrS x.ty).isHit := rfl
        rw [this, eb']; rfl)

-- CONDITIONAL: s3b_CSOk (owed: sim.step.custom_state_refines)
theorem sim.step.update_state_from_result_refines (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part)     (passes : U64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + n + n + 4) s) (hCS : ∀ ns, s3b_CSOk P n tn fo c i p ns)
    (hio : i.val < s.objs.val.length) (hk1 : (s.objs.val[i.val]'hio).inst.val < s.insts.val.length)
    (hk2 : (s.objs.val[i.val]'hio).head_inst.val < s.insts.val.length)
    (hhi : i.val < c.head_idx.val.length) (hhb : (c.head_idx.val[i.val]'hhi).val < 2 ^ 63)
    (hhn : p = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'(by rw [← hinv.objs_len]; exact hio)).nested.val.length) :
    ∃ s', sim.step.update_state_from_result c s i p passes = ok s' ∧
      OsuModel.Sim.Sim.updateStateFromResult i.val (abs p) passes.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧
      s'.objs.val.length = s.objs.val.length ∧ s'.future_order = s.future_order ∧ s3b_frame s s' ∧
      s3b_objFrame s s' := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
    s3c_update_state_from_result_strong tn fo E b n c s i p passes hinv hP hCS hio hk1 hk2 hhi hhb hhn
  exact ⟨s', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end OsuProofs
