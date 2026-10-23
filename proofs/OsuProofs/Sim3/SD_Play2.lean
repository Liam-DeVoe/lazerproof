/-
sim3d: `playfield_update_refines` (`Sim.playfieldUpdate`) for the invariant `s3d_PI = s3d_PInv ∧ s6PI` that
`trigger_pressed` needs (sim6, Sim/Press2.lean `s6_tpOk`). Every playfield hook keeps `s6PI` (`SimARInv`, `simLP`,
`s6Blk`, a duplicate-free `pressed`); the transform invariant crosses depth / magnet because those only write the
position / scale of transform objects (`s3d_TfPS`), under the closure `s3d_TfPosOk P` of the transform predicate.
-/
import OsuProofs.Sim.Press2
import OsuProofs.Sim3.SD_PS
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the playfield invariant: `s3d_PInv` plus what `trigger_pressed` needs (`s6PI`) -/
def s3d_PI (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b0 n : Nat)
    (c : sim.state.Ctx) (e : Nat) (s : sim.state.St) : Prop :=
  s3d_PInv c s ∧ s6PI tn fo P b0 n c e s

/-- the transform predicate survives position / scale writes (depth, magnetised, repel) -/
def s3d_TfPosOk (P : Nat → sim.transforms.TObj → Prop) : Prop :=
  ∀ b o p q, P b o → P b { o with pos := p, scale := q }

theorem s3d_TfInv_ps {P : Nat → sim.transforms.TObj → Prop} (hP : s3d_TfPosOk P) (b : Nat) (s s' : sim.state.St)
    (hs : s3d_TfPS s.insts s'.insts) (h : s3b_TfInv P b s) : s3b_TfInv P b s' := by
  intro ins hins
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hins
  have hj0 : j < s.insts.val.length := by rw [← hs.1]; exact hj
  obtain ⟨p, q, e⟩ := hs.2 j hj0 hj
  rw [e]
  have := h _ (List.getElem_mem hj0)
  exact ⟨hP _ _ _ _ this.1, this.2⟩

theorem s3d_PI_relaxCl (tn fo) (P : Nat → sim.transforms.TObj → Prop) (b0 n : Nat) (c : sim.state.Ctx) (e : Nat) :
    s3d_RelaxCl (s3d_PI tn fo P b0 n c e) := by
  refine ⟨fun s h => h.1.2.2.2.2.2.1, fun s d l w p h hp hsl => ⟨(s3d_PInv_relaxCl c).2 s d l w p h.1 hp hsl, ?_⟩⟩
  obtain ⟨hAR, hL, hB, hN, hAl⟩ := h.2
  exact ⟨sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hAR _ (s3b_inv_of hAR.inv rfl rfl) (s3b_objFrame_of_eq rfl) rfl hAR.tf
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, ⟨hp, hL.2⟩, hB, List.Nodup.sublist hsl hN, hAl⟩

theorem s3d_PI_hook (tn fo) {P : Nat → sim.transforms.TObj → Prop} (hPos : s3d_TfPosOk P) (b0 n : Nat)
    (c : sim.state.Ctx) (e : Nat) :
    ∀ s s', s3d_PI tn fo P b0 n c e s → s3d_PInv c s' → s3d_HookFr c s s' → s3d_PI tn fo P b0 n c e s' := by
  rintro s s' ⟨-, hAR, hL, hB, hN, hAl⟩ hP' hF
  refine ⟨hP', ?_⟩
  rcases hF with ⟨sp, rfl, hsp⟩ | ⟨ins, rfl, hps⟩ | ⟨r, rfl⟩ | ⟨⟨af, mv, m, cp, o, rfl⟩, hinv', hol, hkh⟩ |
    ⟨bl, bi, rfl, hbl, hbi, hbb⟩
  · exact ⟨⟨s3b_inv_of hAR.inv rfl rfl, hAR.tf, hAR.ik, hAR.em,
      by show _ ≤ sp.val.length; rw [hsp]; exact hAR.sp, hAR.cnt, hAR.seen,
      sim_enum_transfer tn fo c s _ hAR.inv rfl hAR.enum⟩, hL, hB, hN, hAl⟩
  · exact ⟨sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hAR _ (s3b_inv_of hAR.inv rfl rfl) (s3b_objFrame_of_eq rfl)
      hps.1 (s3d_TfInv_ps hPos _ s _ hps hAR.tf) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hL, hB, hN, hAl⟩
  · exact ⟨sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hAR _ (s3b_inv_of hAR.inv rfl rfl) (s3b_objFrame_of_eq rfl) rfl
      hAR.tf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hL, hB, hN, hAl⟩
  · have hof : s3b_objFrame s { s with ap_frame := af, mouse_valid := mv, mouse := m, cursor_pos := cp, objs := o } :=
      ⟨hol, fun j h h' => by
        have e := hkh j h' h
        simp only [s3d_keepH, Prod.mk.injEq] at e
        exact ⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1⟩⟩
    refine ⟨sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hAR _ hinv' hof rfl hAR.tf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      ⟨hL.1, fun j h => ?_⟩, hB, hN, hAl⟩
    have h0 : j < s.objs.val.length := by rw [← hol]; exact h
    have e := hkh j h h0
    simp only [s3d_keepH, Prod.mk.injEq] at e
    rw [e.2.2.2.2.2.1]; exact hL.2 j h0
  · exact ⟨sim_ar_inv_hook tn fo P b0 n c s e 0 0 0 hAR _ (s3b_inv_of hAR.inv rfl rfl) (s3b_objFrame_of_eq rfl) rfl
      hAR.tf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hL,
      ⟨by show _ ≤ bl.val.length; rw [hbl]; exact hB.1, by show _ ≤ bi.val.length; rw [hbi]; exact hB.2.1,
       fun h0 x hx => by obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx; exact hbb h0 j hj⟩, hN, hAl⟩

/-- `relax_change_state` (the local `changeState` of `Sim.relaxUpdate`, `s3d_csS`) for the invariant `s3d_PI` -/
-- NOT-CONDITIONAL: SimARCtx/simCSH/s3aPathOk are context premises (ev_ctxWF), E fixes the transform predicate
theorem sim.step.relax_change_state_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat)
    (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i) (e : Nat) (s : sim.state.St) (down : Bool) (time : F64)
    (hI : s3d_PI tn fo P b0 n c e s) :
    ∃ r s', sim.step.relax_change_state c s down time = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (s3d_csS time down (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → s3d_PI tn fo P b0 n c e s') :=
  s3d_relax_change_state_gen tn fo c s down time _ hI (s3d_PI_relaxCl tn fo P b0 n c e)
    (s6_tpOk h64 tn fo E b0 n c hC hCS hlen hp e)

/-- `ModRelax.Update` (`Sim.relaxUpdate`) for the invariant `s3d_PI` -/
-- NOT-CONDITIONAL: SimARCtx/simCSH/s3d_RCtx/s3aPathOk are context premises (ev_ctxWF), E fixes the transform predicate
theorem sim.step.relax_update_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b0 n : Nat)
    (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i) (hrc : s3d_RCtx c) (e : Nat) (s : sim.state.St)
    (hI : s3d_PI tn fo P b0 n c e s) :
    ∃ r s', sim.step.relax_update c s = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (OsuModel.Sim.Sim.relaxUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → s3d_PI tn fo P b0 n c e s') :=
  s3d_relax_update_gen h64 tn fo c s _ hI (s3d_PI_relaxCl tn fo P b0 n c e) (s6_tpOk h64 tn fo E b0 n c hC hCS hlen hp e)
    hI.1.1 hI.1.2.1 hrc

/-- `ModX.Update` for every playfield updatable (`Sim.playfieldUpdate`). The premises are context facts
(`SimARCtx`, `simCSH`, `s3d_PCtx`, path sizes, object count) and the transform-predicate closures `E`, `hPos`;
the state invariant `s3d_PI` is re-established on a normal exit. -/
-- NOT-CONDITIONAL: SimARCtx/simCSH/s3d_PCtx/s3aPathOk are context premises (ev_ctxWF), E/hPos fix the transform predicate
theorem sim.step.playfield_update_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (hPos : s3d_TfPosOk P)
    (b0 n : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (hPC : s3d_PCtx c) (e : Nat) (s : sim.state.St) (hI : s3d_PI tn fo P b0 n c e s) :
    ∃ r s', sim.step.playfield_update c s = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (OsuModel.Sim.Sim.playfieldUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → s3d_PI tn fo P b0 n c e s') :=
  s3d_playfield_gen h64 tn fo c s _ hI (fun _ h => h.1) (s3d_PI_hook tn fo hPos b0 n c e) (s3d_PI_relaxCl tn fo P b0 n c e)
    hPC (s6_tpOk h64 tn fo E b0 n c hC hCS hlen hp e)

end OsuProofs
