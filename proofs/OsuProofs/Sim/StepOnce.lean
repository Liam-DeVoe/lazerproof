/-
`sim::step::step_once` (simcore2): the per-object update contract (`sc2UpdC`) for the concrete update invariant
`sc2J` (transform budget 2 units per update, completed_spins headroom per update, alive → dictionary, spinner tick
slots, plus a caller predicate `Y` closed under the update frame `sc2DFr`).
-/
import OsuProofs.Sim.StepInv
import OsuProofs.Sim.InputStep
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- what one `update_dho` keeps of every object -/
def sc2KO (o : sim.state.OState) :=
  (o.life, o.child_id, o.inst, o.head_inst, o.tick_insts, o.tick_live.val.length)

/-- the frame of one `update_dho c s i` -/
structure sc2DFr (i : Nat) (s s' : sim.state.St) : Prop where
  keep : simKeepS s' = simKeepS s
  len : s'.objs.val.length = s.objs.val.length
  ko : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), sc2KO (s'.objs.val[j]'h') = sc2KO (s.objs.val[j]'h)
  cs : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
    (s'.objs.val[j]'h').completed_spins.val ≤ (s.objs.val[j]'h).completed_spins.val + (if j = i then 2000000 else 0)
  il : s'.insts.val.length = s.insts.val.length

theorem sc2DFr_ar {i : Nat} {s s2 : sim.state.St} (A : simARFr s s2) : sc2DFr i s s2 := by
  refine ⟨A.keep, A.len, fun j h h' => ?_, fun j h h' => ?_, A.il⟩
  · have e := A.ow j h h'
    simp only [simKeepO, Prod.mk.injEq] at e
    simp only [sc2KO, e]
  · have e := A.ow j h h'
    simp only [simKeepO, Prod.mk.injEq] at e
    rw [e.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; omega

theorem sc2DFr_jfr {i : Nat} {s s2 s' : sim.state.St} (A : simARFr s s2) (T : simJFr s2 s') : sc2DFr i s s' := by
  have h2 : s2.objs.val.length = s.objs.val.length := A.len
  refine ⟨T.keep.trans A.keep, T.len.trans A.len, fun j h h' => ?_, fun j h h' => ?_, T.il.trans A.il⟩
  all_goals
    have hm : j < s2.objs.val.length := by rw [h2]; exact h
    have e1 := A.ow j h hm
    have e2 := T.ow j hm h'
    simp only [simKeepO, simKeepJ, Prod.mk.injEq] at e1 e2
  · simp only [sc2KO, e1, e2]
  · simp only [e1, e2]; omega

theorem sc2DFr_s7 {i : Nat} {s s2 s' : sim.state.St} (A : simARFr s s2) (T : s7Fr s2 s') : sc2DFr i s s' := by
  have h2 : s2.objs.val.length = s.objs.val.length := A.len
  refine ⟨T.keep.trans A.keep, T.len.trans A.len, fun j h h' => ?_, fun j h h' => ?_, T.il.trans A.il⟩
  all_goals
    have hm : j < s2.objs.val.length := by rw [h2]; exact h
    have e1 := A.ow j h hm
    have e2 := T.ow j hm h'
    simp only [simKeepO, s7KeepI, Prod.mk.injEq] at e1 e2
  · simp only [sc2KO, e1, e2]
  · simp only [e1, e2]; omega

theorem sc2DFr_s4 {i : Nat} {s s2 s' : sim.state.St} (A : simARFr s s2) (T : s4Fr simKeepO s4KeepSp i s2 s')
    (hc : ∀ (h : i < s2.objs.val.length) (h' : i < s'.objs.val.length),
      (s'.objs.val[i]'h').completed_spins.val ≤ (s2.objs.val[i]'h).completed_spins.val + 2000000) :
    sc2DFr i s s' := by
  have h2 : s2.objs.val.length = s.objs.val.length := A.len
  refine ⟨T.keep.trans A.keep, T.len.trans A.len, fun j h h' => ?_, fun j h h' => ?_, T.il.trans A.il⟩
  all_goals
    have hm : j < s2.objs.val.length := by rw [h2]; exact h
    have e1 := A.ow j h hm
    simp only [simKeepO, Prod.mk.injEq] at e1
  · by_cases hji : j = i
    · subst hji
      have e2 := T.oi hm h'
      simp only [s4KeepSp, Prod.mk.injEq] at e2
      simp only [sc2KO, e1, e2]
    · have e2 := T.ow j hm h' hji
      simp only [simKeepO, Prod.mk.injEq] at e2
      simp only [sc2KO, e1, e2]
  · by_cases hji : j = i
    · subst hji
      have := hc hm h'
      rw [e1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at this
      simp only [if_pos rfl]; exact this
    · have e2 := T.ow j hm h' hji
      simp only [simKeepO, Prod.mk.injEq] at e2
      rw [e2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, e1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; omega

/-- the custom-state cost `n` of the context -/
abbrev sc2N (c : sim.state.Ctx) : Nat := s3b_csCostFrom c.cfg.vis_mods.val 0

/-- the update-loop invariant with `b` updates left: transform budget `B + b·2u`, completed_spins headroom `b·2·10^6`,
alive objects in the dictionary, alive spinners' tick slots, the step index / speed facts, and a caller predicate `Y` -/
def sc2J (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (B : Nat) (Y : sim.state.St → Prop)
    (b : Nat) (s : sim.state.St) : Prop :=
  SimARInv tn fo s2_tfOk (B + b * (2 * (sc2N c + sc2N c + 4))) (sc2N c) c s 0 0 0 ∧ simLP s ∧
  (∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).life = .Alive → ∃ x, some x ∈ s.dict_slots.val ∧ x.val = j) ∧
  (∀ j (h : j < s.objs.val.length) (hj : j < c.pb.objects.val.length), (s.objs.val[j]'h).life = .Alive →
    (c.pb.objects.val[j]'hj).h.kind = .Spinner →
    (s.objs.val[j]'h).tick_live.val.length = (c.pb.objects.val[j]'hj).nested.val.length ∧
    (s.objs.val[j]'h).tick_insts.val.length = (c.pb.objects.val[j]'hj).nested.val.length) ∧
  (∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).completed_spins.val + b * 2000000 ≤ 2 ^ 54) ∧
  (s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) ∧
  (∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < s.speed.val.length) ∧ Y s

theorem sc2_J_fr {tn fo c B} {Y : sim.state.St → Prop} (hY : ∀ i s s', Y s → sc2DFr i s s' → Y s') {b : Nat}
    {i : Nat} {s s' : sim.state.St} (hJ : sc2J tn fo c B Y (b + 1) s) (F : sc2DFr i s s')
    (hI : SimARInv tn fo s2_tfOk (B + b * (2 * (sc2N c + sc2N c + 4))) (sc2N c) c s' 0 0 0) (hLP : simLP s') :
    sc2J tn fo c B Y b s' := by
  obtain ⟨-, -, hAD, hTK, hCS, hst, hd, hYs⟩ := hJ
  have hkk : s'.k = s.k := congrArg (fun x => x.1) F.keep
  have hsp : s'.speed = s.speed := (s8_keepS F.keep).2.2.2.2.2.2.2.2.2.1
  have hds : s'.dict_slots = s.dict_slots := sim_keepS_dict F.keep
  refine ⟨hI, hLP, fun j h hal => ?_, fun j h hj hal hk => ?_, fun j h => ?_, by rw [hkk]; exact hst,
    by rw [hsp]; exact hd, hY i s s' hYs F⟩
  · have h0 : j < s.objs.val.length := by rw [← F.len]; exact h
    have e := F.ko j h0 h
    simp only [sc2KO, Prod.mk.injEq] at e
    rw [hds]; exact hAD j h0 (by rw [← e.1]; exact hal)
  · have h0 : j < s.objs.val.length := by rw [← F.len]; exact h
    have e := F.ko j h0 h
    simp only [sc2KO, Prod.mk.injEq] at e
    obtain ⟨a, b⟩ := hTK j h0 hj (by rw [← e.1]; exact hal) hk
    exact ⟨by rw [e.2.2.2.2.2]; exact a, by rw [e.2.2.2.2.1]; exact b⟩
  · have h0 : j < s.objs.val.length := by rw [← F.len]; exact h
    have e := F.cs j h0 h
    have := hCS j h0
    split at e <;> omega

/-- the transform budget of the `sc2J` state at `b+1` is that of `SimARInv .. e 1 0` one unit lower -/
theorem sc2_ut1 {tn fo c} {X u : Nat} {s : sim.state.St} (hu : u = sc2N c + sc2N c + 4)
    (hI : SimARInv tn fo s2_tfOk (X + u) (sc2N c) c s 0 0 0) : SimARInv tn fo s2_tfOk X (sc2N c) c s 0 1 0 := by
  refine ⟨hI.inv, ?_, hI.ik, hI.em, hI.sp, hI.cnt, hI.seen, hI.enum⟩
  have h := hI.tf
  rwa [show X + u + (simUnj s + 0) * (sc2N c + sc2N c + 4) = X + (simUnj s + 1) * (sc2N c + sc2N c + 4) by
    subst hu; ring] at h

/-- the per-object update contract for `sc2J` -/
-- NOT-CONDITIONAL: hC/hlen/hfo/hp/hsl/hST are context premises (ev_ctxWF; hST: s7StrictOk, json)
theorem sc2_upd (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (hC : SimARCtx c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (hsl : ∀ i (hi : i < c.pb.objects.val.length), (c.pb.objects.val[i]'hi).h.kind = .Slider →
      ∃ hti : i < c.tail_idx.val.length, (c.tail_idx.val[i]'hti).val < (c.pb.objects.val[i]'hi).nested.val.length)
    (hST : ∀ i, s7StrictOk tn c i) (B : Nat) (Y : sim.state.St → Prop) (hY : ∀ i s s', Y s → sc2DFr i s s' → Y s') :
    sc2UpdC tn fo c (sc2J tn fo c B Y) := by
  intro b s i hi hJ hal
  have hJ0 := hJ
  obtain ⟨hI, hLP, hAD, hTK, hCSb, hst, hd, hYs⟩ := hJ
  set u := sc2N c + sc2N c + 4 with hu
  have hic : i.val < c.pb.objects.val.length := by rw [← hI.inv.objs_len]; exact hi
  have hD : some i ∈ s.dict_slots.val := by
    obtain ⟨x, hx, hxv⟩ := hAD i.val hi hal
    rwa [show x = i from UScalar.eq_of_val_eq hxv] at hx
  have hIn := hI.ik i hD
  have hI1 : SimARInv tn fo s2_tfOk (B + b * (2 * u) + u) (sc2N c) c s 0 1 0 := by
    refine sc2_ut1 hu ?_
    rwa [show B + b * (2 * u) + u + u = B + (b + 1) * (2 * u) by ring]
  have hCS := sim_ar_cs tn fo c hfo
  let Q : sim.state.St → Prop := fun s' => sc2J tn fo c B Y b s' ∧ s'.objs.val.length = s.objs.val.length
  have hW : ∀ s', SimARInv tn fo s2_tfOk (B + b * (2 * u) + u) (sc2N c) c s' 0 0 0 →
      SimARInv tn fo s2_tfOk (B + b * (2 * u)) (sc2N c) c s' 0 0 0 := fun s' h => sim_ar_weak s3b_tfEng_s2 (by omega) h
  obtain ⟨r, s', e1, r1, i1⟩ := sim.step.update_dho_refines h64 tn fo s3b_tfEng_s2 sc2_tfU_s2 (B + b * (2 * u) + u)
    (sc2N c) c hC hCS hlen s i 0 hI1 hIn hic (hp _ hic) Q (by
      intro s2 hI2 hfr hof hil hIn2 hA2
      have hLP2 := simLP_fr hLP hA2
      have hD2 : some i ∈ s2.dict_slots.val := by rw [sim_keepS_dict hA2.keep]; exact hD
      have hlen2 : s2.objs.val.length = s.objs.val.length := hA2.len
      refine ⟨hLP2, ⟨sc2_J_fr hY hJ0 (sc2DFr_ar (i := i.val) hA2) (hW _ hI2) hLP2, hlen2⟩,
        fun s' hI' T hL' => ⟨sc2_J_fr hY hJ0 (sc2DFr_jfr (i := i.val) hA2 T) (hW _ hI') hL', by rw [T.len, hlen2]⟩,
        fun hk => ?_, fun hk => ?_⟩
      · obtain ⟨hti, htl⟩ := hsl i.val hic hk
        obtain ⟨res, s', e, rr, ii⟩ := sim.step.update_slider_refines h64 tn fo s3b_tfEng_s2 s7_ut_s2 (B + b * (2 * u))
          (sc2N c) c hC hCS hlen s2 i 0 hI2 hD2 hLP2 hic hk (hp _ hic) hti htl (hST i.val)
        refine ⟨res, s', e, rr, fun h => ?_⟩
        obtain ⟨a, F, l⟩ := ii h
        exact ⟨sc2_J_fr hY hJ0 (sc2DFr_s7 (i := i.val) hA2 F) a l, by rw [F.len, hlen2]⟩
      · have ho2 : i.val < s2.objs.val.length := by rw [hlen2]; exact hi
        have e0 := (sc2DFr_ar (i := i.val) hA2).ko i.val hi ho2
        simp only [sc2KO, Prod.mk.injEq] at e0
        obtain ⟨htl0, htk0⟩ := hTK i.val hi hic hal hk
        have hkk : s2.k = s.k := congrArg (fun x => x.1) hA2.keep
        have hsp : s2.speed = s.speed := (s8_keepS hA2.keep).2.2.2.2.2.2.2.2.2.1
        have hcs0 : (s2.objs.val[i.val]'ho2).completed_spins = (s.objs.val[i.val]'hi).completed_spins := by
          have e := hA2.ow i.val hi ho2
          simp only [simKeepO, Prod.mk.injEq] at e
          simp only [e]
        obtain ⟨res, s', e, rr, ii⟩ := sim.step.update_spinner_refines tn fo s3b_tfEng_s2 (B + b * (2 * u) + u)
          (sc2N c) c hC hCS hlen s2 i 0 hI2 hD2 hic hk hLP2.1 (by rw [hkk]; exact hst) (by rw [hsp]; exact hd)
          (fun h => by rw [e0.2.2.2.2.2]; exact htl0) (fun h => by rw [e0.2.2.2.2.1]; exact htk0)
          (fun h => by rw [hcs0]; have := hCSb i.val hi; nlinarith)
        refine ⟨res, s', e, rr, fun h => ?_⟩
        obtain ⟨a, F, l⟩ := ii h
        have hLP' : simLP s' := by
          refine ⟨?_, fun j hj => ?_⟩
          · rw [(s8_keepS F.keep).2.2.2.2.2.2.2.2.1]; exact hLP2.1
          · have hj0 : j < s2.objs.val.length := by rw [← F.len]; exact hj
            by_cases hji : j = i.val
            · subst hji
              have e := F.oi hj0 hj
              simp only [s4KeepSp, Prod.mk.injEq] at e
              rw [e.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hLP2.2 _ hj0
            · have e := F.ow j hj0 hj hji
              simp only [simKeepO, Prod.mk.injEq] at e
              rw [e.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hLP2.2 _ hj0
        exact ⟨sc2_J_fr hY hJ0 (sc2DFr_s4 hA2 F l) (hW _ a) hLP', by rw [F.len, hlen2]⟩)
  exact ⟨r, s', e1, r1, i1⟩

end OsuProofs
