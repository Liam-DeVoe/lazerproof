/-
sim6: discharge of sim3d's `s3d_TPOk` (relax_change_state / relax_update / playfield_update's `trigger_pressed`
obligation) by `sim.step.trigger_pressed_refines`, for the invariant `s3d_PInv c ∧ s6PI ..`.
-/
import OsuProofs.Sim.Press
import OsuProofs.Sim3.SD_Play
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- what `trigger_pressed` needs of the state beyond `s3d_PInv` -/
def s6PI (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b0 n : Nat)
    (c : sim.state.Ctx) (e : Nat) (s : sim.state.St) : Prop :=
  SimARInv tn fo P b0 n c s e 0 0 ∧ simLP s ∧ s6Blk c s ∧ (actListS s.pressed).Nodup ∧
    s.active.val.length < Usize.max

theorem s6_filter_take_lt {α} (p : α → Bool) (l : List α) (k : Nat) (hk : k < l.length) (hp : p (l[k]'hk) = true) :
    ((l.take k).filter p).length < (l.filter p).length := by
  have h := List.take_append_drop k l
  rw [List.drop_eq_getElem_cons hk] at h
  have e : (l.filter p).length = ((l.take k ++ l[k] :: l.drop (k+1)).filter p).length := by rw [h]
  rw [e, List.filter_append, List.length_append, List.filter_cons_of_pos hp, List.length_cons]
  omega

theorem s6_pinv {tn fo} {P : Nat → sim.transforms.TObj → Prop} {b0 n : Nat} {c : sim.state.Ctx} {e : Nat}
    {s s' : sim.state.St} (hP : s3d_PInv c s) (hI : SimARInv tn fo P b0 n c s' e 0 0) (hL : simLP s')
    (hF : s6PFr s s') (hB : s6Blk c s') : s3d_PInv c s' := by
  obtain ⟨_, hik0, hact, hk, hap, _, hdyn, hib, _⟩ := hP
  have k := hF.keep
  simp only [s6KeepT, Prod.mk.injEq] at k
  obtain ⟨ek, _, _, _, _, eact, edict, _, _, _, _, _, esp, _, _, _, _, eap, _, _, _⟩ := k
  have hik' : s3d_IK s' := by
    refine ⟨fun x hx => ?_, fun i h hal => ?_, fun x hx => ?_⟩
    · obtain ⟨h, h1, h2, -⟩ := hI.ik x hx
      exact ⟨h, h1, h2⟩
    · have h0 : i < s.objs.val.length := by rw [← hF.len]; exact h
      have e := hF.ow i h0 h
      simp only [s6KeepO, Prod.mk.injEq] at e
      rw [edict]
      exact hik0.2.1 i h0 (by rw [← e.1]; exact hal)
    · rw [edict]; rw [eact] at hx; exact hik0.2.2 x hx
  refine ⟨hI.inv, hik', by rw [eact]; exact hact, by rw [ek]; exact hk,
    by rw [eap]; exact hap, hL.1, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨h1, h2, _⟩ := hdyn j hj
    refine ⟨h1, by rw [esp]; exact h2, fun had => ?_⟩
    have := s6_filter_take_lt s3b_isAd c.cfg.dyn_rates.val j.val h1 had
    have := hI.cnt.1
    omega
  · intro j hj
    obtain ⟨h1, h2⟩ := hib j hj
    exact ⟨by rw [hF.bi]; exact h1, by rw [hF.bl]; exact h2⟩
  · intro h0 j hj
    exact hB.2.2 h0 _ (List.getElem_mem hj)

-- NOT-CONDITIONAL: SimARCtx/simCSH/s3aPathOk are context premises (ev_ctxWF; simCSH via sim_ar_cs)
theorem s6_tpOk (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c)
    (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i) (e : Nat) :
    s3d_TPOk tn fo c (fun s => s3d_PInv c s ∧ s6PI tn fo P b0 n c e s) := by
  intro s a ⟨hP, hI, hL, hB, hN, hAl⟩
  obtain ⟨res, s', e1, r1, i1⟩ := sim.step.trigger_pressed_refines h64 tn fo E b0 n c hC hCS hlen hp s a e hI hL hB hN
    hP.2.2.1 hAl hP.2.1.2.2
  refine ⟨res, s', e1, ?_, fun h => ?_⟩
  · cases res with
    | Ok u => exact r1
    | Err er => exact r1
  · obtain ⟨j1, j2, j3, j4, j5⟩ := i1 h
    have eact : s'.active = s.active := by
      have k := j4.keep; simp only [s6KeepT, Prod.mk.injEq] at k; exact k.2.2.2.2.2.1
    exact ⟨s6_pinv hP j1 j2 j4 j3, j1, j2, j3, j5, by rw [eact]; exact hAl⟩

end OsuProofs
