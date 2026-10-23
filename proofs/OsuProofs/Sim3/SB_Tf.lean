/-
Sim3b part 6: the transform-engine interface used by the DHO state hooks, and the hit-state transforms of
`updateState` (`circle_hit_state`, `slider_hit_state`, `other_hit_state`).

`s3b_TfEng P` packages the refinement statements of the Sim2 engine functions (`clear_state`, `transform_to`,
`seq_append`, `fade_in_from_zero`) for transformables with an add budget `P b o` (each `add_transform` costs 1);
`s3b_tfEng_s2` instantiates it with Sim2's `s2_tfOk` (Sim2/TrEngine.lean), so theorems taking `E` are unconditional.
-/
import OsuProofs.Sim3.SB_State
import OsuProofs.Sim2.TrEngine
import OsuProofs.Sim.Processors
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

structure s3b_TfEng (P : Nat → sim.transforms.TObj → Prop) : Prop where
  delay : ∀ b o d, P b o → P b { o with delay := d }
  mono : ∀ b b' o, b' ≤ b → P b o → P b' o
  clear : ∀ b o, P b o → ∃ o', sim.transforms.clear_state o = ok o' ∧
    OsuModel.Sim.clearState (abs o) = abs o' ∧ P b o'
  tto : ∀ b o now m v dur e off, P (b + 1) o → ∃ sq o', sim.transforms.transform_to o now m v dur e off = ok (sq, o') ∧
    OsuModel.Sim.transformTo (abs o) now (abs m) (abs v) dur (abs e) (off.map abs) = (abs o', abs sq) ∧ P b o'
  app : ∀ b s o now m v dur e off, P (b + 1) o → ∃ sq o', sim.transforms.seq_append s o now m v dur e off = ok (sq, o') ∧
    OsuModel.Sim.Seq.append (abs s) (abs o) now (abs m) (abs v) dur (abs e) (off.map abs) = (abs o', abs sq) ∧ P b o'
  fade : ∀ b o now dur e, P (b + 2) o → ∃ o', sim.transforms.fade_in_from_zero o now dur e = ok o' ∧
    OsuModel.Sim.fadeInFromZero (abs o) now dur (abs e) = abs o' ∧ P b o'

theorem s3b_tfOkS_mono (b b' : Nat) (a : OsuModel.Sim.TObj) (hb : b' ≤ b) (h : s2_tfOkS b a) : s2_tfOkS b' a := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, fun tk htk => by have := h2 tk htk; omega⟩

/-- the Sim2 engine (Sim2/TrEngine.lean) with its budget invariant `s2_tfOk` -/
theorem s3b_tfEng_s2 : s3b_TfEng s2_tfOk where
  delay b o d h := s2_tfOk_delay b o d h
  mono b b' o hb h := s3b_tfOkS_mono b b' _ hb h
  clear b o h := s2_eng_clear b o h
  tto b o now m v dur e off h := s2_eng_tto b o now m v dur e off h
  app b s o now m v dur e off h := s2_eng_app b s o now m v dur e off h
  fade b o now dur e h := s2_eng_fade b o now dur e h

/-- every instance's transformables satisfy `P` with budget `b` -/
def s3b_TfInv (P : Nat → sim.transforms.TObj → Prop) (b : Nat) (s : sim.state.St) : Prop :=
  ∀ ins ∈ s.insts.val, P b ins.tf ∧ P b ins.body_tf

/-! ## clones are the identity -/
theorem s3b_clone_vec {T : Type} (inst : core.clone.Clone T) (h : ∀ x, inst.clone x = ok x) (v : alloc.vec.Vec T) :
    alloc.vec.CloneVec.clone inst v = ok v := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := inst.clone) (s := v.slice) (by intro x _; exact h x))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp

@[simp] theorem s3b_tr_clone (t : sim.transforms.Tr) : sim.transforms.Tr.Insts.CoreCloneClone.clone t = ok t := by
  rcases t with ⟨a, m, b, c, d, e, f, g, h, i, j⟩
  cases m <;> cases g <;>
    simp [sim.transforms.Tr.Insts.CoreCloneClone.clone, sim.transforms.Member.Insts.CoreCloneClone.clone,
      sim.basic.Vec2.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone,
      float.F32.Insts.CoreCloneClone.clone, core.option.Option.Insts.CoreCloneClone.clone, lift]

@[simp] theorem s3b_tracker_clone (t : sim.transforms.Tracker) :
    sim.transforms.Tracker.Insts.CoreCloneClone.clone t = ok t := by
  rcases t with ⟨m, ts, c, l⟩
  cases m <;> simp [sim.transforms.Tracker.Insts.CoreCloneClone.clone, sim.transforms.Member.Insts.CoreCloneClone.clone,
    s3b_clone_vec sim.transforms.Tr.Insts.CoreCloneClone s3b_tr_clone, lift]

@[simp] theorem s3b_tobj_clone (o : sim.transforms.TObj) : sim.transforms.TObj.Insts.CoreCloneClone.clone o = ok o := by
  simp [sim.transforms.TObj.Insts.CoreCloneClone.clone, sim.basic.Vec2.Insts.CoreCloneClone.clone,
    float.F64.Insts.CoreCloneClone.clone, float.F32.Insts.CoreCloneClone.clone, s3b_clone_vec sim.transforms.Tracker.Insts.CoreCloneClone s3b_tracker_clone]

@[simp] theorem s3b_tr_F32_0 : sim.transforms.F32_0 = ok (0 : F32) := by
  unfold sim.transforms.F32_0; simp; decide +kernel
@[simp] theorem s3b_vs (x : F32) : sim.transforms.vs x = ok ⟨x, 0⟩ := by simp [sim.transforms.vs]
@[simp] theorem s3b_F64_800C : sim.step.F64_800C = ok (800 : F64) := by simp [sim.step.F64_800C]

theorem s3b_tfinv_of_tfSame {P : Nat → sim.transforms.TObj → Prop} {b : Nat} {s s' : sim.state.St}
    (h : s3b_tfSame s s') (hP : s3b_TfInv P b s) : s3b_TfInv P b s' := by
  intro ins hins
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hins
  have hk0 : k < s.insts.val.length := h.1 ▸ hk
  obtain ⟨e1, e2⟩ := h.2 k hk0 hk
  rw [e1, e2]; exact hP _ (List.getElem_mem hk0)

/-- `tick_state` preserves every transform invariant (sim core request 16:50) -/
theorem sim.step.tick_state_tfinv (c : sim.state.Ctx) (s : sim.state.St) (i j : Usize) (passes : U64)
    (ns : sim.state.Armed) (force : Bool) (hinv : SimInv c s)
    (hi : i.val < c.pb.objects.val.length) (hj : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hio : i.val < s.objs.val.length) (htj : j.val < (s.objs.val[i.val]'hio).tick_insts.val.length)
    (htk : ((s.objs.val[i.val]'hio).tick_insts.val[j.val]'htj).val < s.insts.val.length)
    (s' : sim.state.St) (h : sim.step.tick_state c s i j passes ns force = ok s') :
    ∀ (P : Nat → sim.transforms.TObj → Prop) b, s3b_TfInv P b s → s3b_TfInv P b s' :=
  fun _ _ hP => s3b_tfinv_of_tfSame (sim.step.tick_state_tfSame c s i j passes ns force hinv hi hj hio htj htk s' h) hP

/-! ## hit-state transforms of `updateState` -/
theorem sim.step.circle_hit_state_refines {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat)
    (tf : sim.transforms.TObj) (hP : P (b + 2) tf) (now : F64) (ns : sim.state.Armed) :
    ∃ le tf', sim.step.circle_hit_state tf now ns = ok (le, tf') ∧ P b tf' ∧
      abs tf' = (let T1 := ((OsuModel.Sim.delaySeq (abs tf) now 800).append (abs tf) now .alpha (OsuModel.Sim.vs 0) 0).1
                 if (abs ns : OsuModel.Sim.Armed) == .miss then (OsuModel.Sim.transformTo T1 now .alpha (OsuModel.Sim.vs 0) 100).1 else T1) ∧
      le = OsuModel.Sim.latestEnd (abs tf') now := by
  obtain ⟨d, hd, ed⟩ := sim.transforms.delay_seq_refines tf now 800
  obtain ⟨sq1, tf1, h1, e1, p1⟩ := E.app (b + 1) d tf now .Alpha ⟨0, 0⟩ 0 .None none hP
  have e1' : (((OsuModel.Sim.delaySeq (abs tf) now 800).append (abs tf) now .alpha (OsuModel.Sim.vs 0) 0).1) = abs tf1 := by
    rw [ed]; exact congrArg Prod.fst e1
  cases ns with
  | Miss =>
    obtain ⟨sq2, tf2, h2, e2, p2⟩ := E.tto b tf1 now .Alpha ⟨0, 0⟩ 100 .None none p1
    refine ⟨_, tf2, ?_, p2, ?_, rfl⟩
    · simp only [sim.step.circle_hit_state, s3b_F64_800C, hd, sim_basic_F32_0, s3b_vs, sim_step_F64_0, bind_ok, h1,
        armed_eq_ok, sim_step_F64_100, h2, sim.transforms.latest_end_refines, uncurry_apply_pair]
      rw [if_pos (by decide)]; simp only [bind_ok]
    · simp only [e1']
      exact (congrArg Prod.fst e2).symm
  | Idle | Hit =>
    refine ⟨_, tf1, ?_, E.mono _ _ _ (by omega) p1, ?_, rfl⟩
    · simp only [sim.step.circle_hit_state, s3b_F64_800C, hd, sim_basic_F32_0, s3b_vs, sim_step_F64_0, bind_ok, h1,
        armed_eq_ok, sim.transforms.latest_end_refines, uncurry_apply_pair]
      rw [if_neg (by decide)]; simp only [bind_ok]
    · simp only [e1']; rfl

theorem sim.step.other_hit_state_refines {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat)
    (tf : sim.transforms.TObj) (hP : P (b + 1) tf) (now : F64) :
    ∃ le tf', sim.step.other_hit_state tf now = ok (le, tf') ∧ P b tf' ∧
      abs tf' = (OsuModel.Sim.transformTo (abs tf) now .alpha (OsuModel.Sim.vs 0) 240).1 ∧
      le = OsuModel.Sim.latestEnd (abs tf') now := by
  obtain ⟨sq1, tf1, h1, e1, p1⟩ := E.tto b tf now .Alpha ⟨0, 0⟩ 240 .None none hP
  refine ⟨_, tf1, ?_, p1, (congrArg Prod.fst e1).symm, rfl⟩
  simp only [sim.step.other_hit_state, sim_basic_F32_0, s3b_vs, sim_step_F64_240, bind_ok, h1,
    sim.transforms.latest_end_refines, uncurry_apply_pair]

theorem sim.step.slider_hit_state_refines {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat)
    (tf body : sim.transforms.TObj) (hP : P (b + 1) tf) (hB : P (b + 1) body) (now : F64) (ns : sim.state.Armed)
    (hh : Bool) :
    ∃ le tf' body', sim.step.slider_hit_state tf body now ns hh = ok (le, tf', body') ∧ P b tf' ∧ P b body' ∧
      abs body' = (if ((abs ns : OsuModel.Sim.Armed) == .hit && hh) = true then
        (OsuModel.Sim.transformTo (abs body) now .alpha (OsuModel.Sim.vs 0) 40).1 else abs body) ∧
      abs tf' = (OsuModel.Sim.transformTo (abs tf) now .alpha (OsuModel.Sim.vs 0) 240).1 ∧
      le = OsuModel.Sim.latestEnd (OsuModel.Sim.absSeq (abs tf') now
        (OsuModel.Sim.transformTo (abs tf) now .alpha (OsuModel.Sim.vs 0) 240).2.currentTime) now := by
  obtain ⟨sq1, tf1, h1, e1, p1⟩ := E.tto b tf now .Alpha ⟨0, 0⟩ 240 .None none hP
  obtain ⟨sq2, b2, h2, e2, p2⟩ := E.tto b body now .Alpha ⟨0, 0⟩ 40 .None none hB
  have hsq : (OsuModel.Sim.transformTo (abs tf) now .alpha (OsuModel.Sim.vs 0) 240).2 = abs sq1 := congrArg Prod.snd e1
  have hc : sq1.current_time = (abs sq1 : OsuModel.Sim.Seq).currentTime := rfl
  obtain ⟨tmp, htmp, etmp⟩ := sim.transforms.abs_seq_refines tf1 now sq1.current_time
  by_cases hc2 : ((abs ns : OsuModel.Sim.Armed) == .hit && hh) = true
  · have hc2' : (armedS ns == .hit && hh) = true := hc2
    have hns : ns = .Hit := by cases ns <;> first | rfl | (exfalso; revert hc2'; cases hh <;> decide)
    subst hns
    have hhh : hh = true := by revert hc2'; cases hh <;> decide
    subst hhh
    refine ⟨OsuModel.Sim.latestEnd (abs tmp) now, tf1, b2, ?_, p1, p2, by rw [if_pos hc2]; exact (congrArg Prod.fst e2).symm,
      (congrArg Prod.fst e1).symm, ?_⟩
    · simp only [sim.step.slider_hit_state, armed_eq_ok, sim_basic_F32_0, s3b_vs, bind_ok, fb64_4630826316843712512,
        h2, sim_step_F64_240, h1, s3b_tobj_clone, htmp, sim.transforms.latest_end_refines, uncurry_apply_pair]
      rw [if_pos (by decide)]; simp only [if_true, bind_ok, h2, uncurry_apply_pair]
    · rw [hsq, ← hc, etmp]
  · refine ⟨OsuModel.Sim.latestEnd (abs tmp) now, tf1, body, ?_, p1, E.mono _ _ _ (by omega) hB, by rw [if_neg hc2],
      (congrArg Prod.fst e1).symm, by rw [hsq, ← hc, etmp]⟩
    have hc2' : ¬ (armedS ns == .hit && hh) = true := hc2
    simp only [sim.step.slider_hit_state, armed_eq_ok, sim_basic_F32_0, s3b_vs, bind_ok, fb64_4630826316843712512,
      h2, sim_step_F64_240, h1, s3b_tobj_clone, htmp, sim.transforms.latest_end_refines, uncurry_apply_pair]
    cases ns <;> cases hh <;> first | (exfalso; exact hc2' rfl) | (rw [if_neg (by decide)]; simp only [bind_ok]) | (rw [if_pos (by decide), if_neg (by decide)]; simp only [bind_ok])

end OsuProofs
