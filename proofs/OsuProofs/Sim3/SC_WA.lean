/-
Sim3c part 0: the `withAbs` block helpers of the custom-state handlers (moved from Sim3/SB_CS, sim3b names kept):
`s3b_waSt`, `s3b_csPost` (now with the strong frame `s3c_ito`), `s3b_wa`, `s3b_waR_end`, `s3b_cs_yield`, `s3b_bind_ok'`.
-/
import OsuProofs.Sim3.SB_US2
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

/-- the state after a Rust `with_abs_begin … with_abs_end` block writing `tf'` into instance `k` -/
def s3b_waSt (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (tf' : sim.transforms.TObj) : sim.state.St :=
  { s with insts := s.insts.set k { s.insts.val[k.val]'hk with tf := { tf' with delay := (s.insts.val[k.val]'hk).tf.delay } } }

/-- one handler step's invariant bundle -/
def s3b_csPost (P : Nat → sim.transforms.TObj → Prop) (b : Nat) (c : sim.state.Ctx) (s s' : sim.state.St) : Prop :=
  SimInv c s' ∧ s3b_TfInv P b s' ∧ s'.insts.val.length = s.insts.val.length ∧ s'.objs = s.objs ∧ s3c_ito s s'

theorem s3b_csPost_refl {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) {b b' : Nat} (hb : b ≤ b') (c : sim.state.Ctx)
    (s : sim.state.St) (hinv : SimInv c s) (hP : s3b_TfInv P b' s) : s3b_csPost P b c s s :=
  ⟨hinv, fun ins h => ⟨E.mono _ _ _ hb (hP ins h).1, E.mono _ _ _ hb (hP ins h).2⟩, rfl, rfl, s3c_ito_refl s⟩

theorem s3b_wa (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b b' : Nat) (hb : b ≤ b')
    (c : sim.state.Ctx) (s : sim.state.St)
    (k : Usize) (hk : k.val < s.insts.val.length) (now t : F64) (g : OsuModel.Sim.TObj → OsuModel.Sim.TObj)
    (tf' : sim.transforms.TObj) (hinv : SimInv c s) (hP : s3b_TfInv P b' s)
    (hg : g (abs { (s.insts.val[k.val]'hk).tf with delay := t - now }) = abs tf') (hp : P b tf') :
    OsuModel.Sim.Sim.withAbs k.val now t g (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn (s3b_waSt s k hk tf')) ∧
    s3b_csPost P b c s (s3b_waSt s k hk tf') := by
  have hk' : k.val < (simStS tn s).insts.size := by simpa [s3b_stS_insts] using hk
  refine ⟨?_, s3b_inv_objs hinv rfl (fun _ _ _ => rfl) rfl, ?_, by simp [s3b_waSt], rfl, rfl⟩
  · rw [s3b_withAbs_spec _ _ _ _ _ _ hk']
    have hS : simStS tn (s3b_waSt s k hk tf') =
        { simStS tn s with insts := ((s3b_waSt s k hk tf').insts.val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray } := rfl
    rw [hS]
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
    congr 1
    simp only [s3b_waSt, vec_set_val', List.map_set]
    have e2 : ∀ X, X = (abs (s.insts.val[k.val]'hk) : OsuModel.Sim.Inst) → g (OsuModel.Sim.absSeq X.tf now t) = abs tf' := by
      rintro X rfl; exact hg
    simp only [s3b_stS_insts]
    rw [e2 _ (by simp)]
    simp only [List.set_toArray]
    congr 2
    simp only [List.getElem_toArray, List.getElem_map]
    rfl
  · exact s3b_tfinv_set2 E hb hP k { s.insts.val[k.val]'hk with tf := { tf' with delay := (s.insts.val[k.val]'hk).tf.delay } }
      (by simp only [s3b_waSt]; rw [vec_set_val'])
      ⟨E.delay _ _ _ hp, E.mono _ _ _ hb (hP _ (List.getElem_mem hk)).2⟩

theorem s3b_index_mut_set {α} (v : alloc.vec.Vec α) (k : Usize) (x : α) (hk : k.val < v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) (v.set k x) k = ok (x, (v.set k x).set k) := by
  rw [vec_index_mut_eq _ _ (by simp [vec_set_val', hk])]; simp

theorem s3b_index_mut_set2 {α} (v : alloc.vec.Vec α) (k : Usize) (x y : α) (hk : k.val < v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) ((v.set k x).set k y) k =
      ok (y, ((v.set k x).set k y).set k) := by
  rw [vec_index_mut_eq _ _ (by simp [vec_set_val', hk])]; simp

theorem s3b_waR_end (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (d : F64) (tf1 : sim.transforms.TObj) :
    let X : sim.state.Inst := { s.insts.val[k.val]'hk with tf := { (s.insts.val[k.val]'hk).tf with delay := d } }
    let Y : sim.state.Inst := { s.insts.val[k.val]'hk with tf := tf1 }
    sim.step.with_abs_end { s with insts := (s.insts.set k X).set k Y } k (s.insts.val[k.val]'hk).tf.delay =
      ok (s3b_waSt s k hk tf1) := by
  intro X Y
  rw [sim.step.with_abs_end_eq _ _ _ (by simp [vec_set_val', hk])]
  unfold s3b_waSt
  congr 2
  refine alloc.vec.Vec.ext _ _ ?_
  simp [vec_set_val', X, Y]

theorem s3b_cs_yield (X : OsuModel.Sim.SimM Unit) (C : OsuModel.Sim.Ctx) (S S' : OsuModel.Sim.St)
    (h : X C S = .ok ((), S')) :
    (X >>= fun _ => pure (ForInStep.yield PUnit.unit) : OsuModel.Sim.SimM (ForInStep PUnit)) C S =
      .ok (ForInStep.yield PUnit.unit, S') := by
  rw [simM_bind, h]; rfl
theorem s3b_bind_ok' {α β : Type} (X : OsuModel.Sim.SimM α) (f : α → OsuModel.Sim.SimM β) (C : OsuModel.Sim.Ctx)
    (S : OsuModel.Sim.St) (a : α) (S' : OsuModel.Sim.St) (h : X C S = .ok (a, S')) : (X >>= f) C S = f a C S' := by
  rw [simM_bind, h]; rfl
end OsuProofs
