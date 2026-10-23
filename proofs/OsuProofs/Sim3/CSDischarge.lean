/-
Unconditional forms of `update_state_refines` / `update_state_from_result_refines` (infra lead, orchestrator 00:15):
their `s3b_CSOk` hypothesis (owed `custom_state_refines`) is discharged by `s3c_csOk_of` (Sim3/SB_CS.lean) at
`n = s3b_csCostFrom c.cfg.vis_mods.val 0`. Remaining hypotheses are state / context preconditions (D67).
-/
import OsuProofs.Sim3.SB_US2
import OsuProofs.Sim3.SB_CS
set_option maxHeartbeats 400000
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem sim.step.update_state_refines_full (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (ns : sim.state.Armed) (force : Bool)
    (passes : U64) (hinv : SimInv c s)
    (hP : s3b_TfInv P (b + s3b_csCostFrom c.cfg.vis_mods.val 0 + s3b_csCostFrom c.cfg.vis_mods.val 0 + 4) s)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
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
      s3b_objFrame s s' :=
  sim.step.update_state_refines tn fo E b _ c s i p ns force passes hinv hP
    (s3c_csOk_of tn fo E c i p ns (by rw [← hinv.objs_len]; exact hio) hhi hhb (fun h => hhn (Or.inl h)) hfo)
    hio hk1 hk2 hhi hhb hhn

theorem sim.step.update_state_from_result_refines_full (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P)
    (b : Nat) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (passes : U64) (hinv : SimInv c s)
    (hP : s3b_TfInv P (b + s3b_csCostFrom c.cfg.vis_mods.val 0 + s3b_csCostFrom c.cfg.vis_mods.val 0 + 4) s)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
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
      s3b_objFrame s s' :=
  sim.step.update_state_from_result_refines tn fo E b _ c s i p passes hinv hP
    (fun ns => s3c_csOk_of tn fo E c i p ns (by rw [← hinv.objs_len]; exact hio) hhi hhb (fun h => hhn (Or.inl h)) hfo)
    hio hk1 hk2 hhi hhb hhn

end OsuProofs
