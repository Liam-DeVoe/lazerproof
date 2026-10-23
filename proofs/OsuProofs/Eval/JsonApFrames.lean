/-
`sim.step.ap_frames_of_refines` (json agent): the `hAP` hypothesis of `sim.step.mk_ctx_refines`
(Eval/JsonMkCtx.lean), from sim2's `sim.autogen.generate_refines` (Sim2/AutoGen4).
-/
import OsuProofs.Eval.JsonMkCtx
import OsuProofs.Sim2.AutoGen4
import OsuProofs.Sim.Enum
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

def js_apF (a : sim.autogen.AFrame) : sim.state.ApFrame :=
  { time := a.time, pos := { x := a.pos.x, y := a.pos.y } }

theorem js_ap_loop (fs : alloc.vec.Vec sim.autogen.AFrame) : ∀ n (out : alloc.vec.Vec sim.state.ApFrame) (i : Usize),
    fs.val.length - i.val = n → i.val ≤ fs.val.length →
    out.val.length + (fs.val.length - i.val) ≤ Usize.max →
    ∃ w, sim.step.ap_frames_of_loop fs out i = ok w ∧
      w.val = out.val ++ (fs.val.drop i.val).map js_apF := by
  intro n; induction n with
  | zero =>
    intro out i hn hi hl
    refine ⟨out, ?_, by simp [List.drop_of_length_le (show fs.val.length ≤ i.val by omega)]⟩
    unfold sim.step.ap_frames_of_loop
    rw [loop_unfold]
    have : ¬ i < alloc.vec.Vec.len fs := by rw [vec_lt_len_iff]; omega
    simp [sim.step.ap_frames_of_loop.body, this]
  | succ n ih =>
    intro out i hn hi hl
    have hlt : i.val < fs.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := fs.property; omega)
    have hd : fs.val.drop i.val = fs.val[i.val]'hlt :: fs.val.drop i1.val := by
      rw [hi1v]; exact List.drop_eq_getElem_cons hlt
    have hpl : out.val.length < Usize.max := by omega
    obtain ⟨w, hw, hwv⟩ := ih (vpush out (js_apF (fs.val[i.val]'hlt)) hpl) i1 (by omega) (by omega) (by simp; omega)
    refine ⟨w, ?_, by rw [hwv, hd]; simp [js_apF]⟩
    have hl' : i < alloc.vec.Vec.len fs := by rw [vec_lt_len_iff]; exact hlt
    have hb : sim.step.ap_frames_of_loop.body fs out i = ok (.cont (vpush out (js_apF (fs.val[i.val]'hlt)) hpl, i1)) := by
      simp only [sim.step.ap_frames_of_loop.body, hl', if_true, vec_index_eq' fs i hlt, bind_ok, hi1, js_apF,
        vec_push_ok out _ hpl]
    unfold sim.step.ap_frames_of_loop at hw ⊢
    rw [loop_unfold]
    dsimp only
    rw [hb]
    simp only [bind_ok]
    exact hw

/-- `ap_frames_of` refines the `apFrames` computation of `mkCtx` (the `hAP` hypothesis of
`sim.step.mk_ctx_refines`). Size premises are those of `sim.autogen.generate_refines`. -/
theorem sim.step.ap_frames_of_refines (h64 : System.Platform.numBits = 64) (pb : sim.playable.Playable)
    (c : sim.mods.Config) (hn : pb.objects.val.length < 2^32)
    (hsd : ∀ o ∈ pb.objects.val, ∀ sd, o.slider = some sd → sd.cum_len.val.length < 2^62 ∧ sd.path.val.length < 2^62) :
    ∃ r, sim.step.ap_frames_of pb c = ok r ∧
      match r with
      | .Ok v => ∃ G, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = .ok G ∧
          G.map (fun f => (f.time, ({ x := f.pos.x, y := f.pos.y } : OsuModel.Sim.Vec2))) = js_apS v
      | .Err _ => ∃ m, OsuModel.Sim.AutoGen.generate (playableS ev_tn pb) (configS c).rateMods.toList = .error m := by
  have hm : (abs (alloc.vec.Vec.deref c.rate_mods) : List OsuModel.Sim.RateMod) = (configS c).rateMods.toList := by
    simp [abs, configS]
  obtain ⟨r, hr, hrel⟩ := sim.autogen.generate_refines h64 pb (alloc.vec.Vec.deref c.rate_mods) ev_tn hn hsd
  rw [hm] at hrel
  cases r with
  | Ok fs =>
    obtain ⟨w, hw, hwv⟩ := js_ap_loop fs _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simpa using fs.property)
    refine ⟨.Ok w, ?_, _, hrel, ?_⟩
    · unfold sim.step.ap_frames_of
      simp [hr, hw, core.result.Result.Insts.CoreOpsTry.branch]
    · simp [js_apS, hwv, js_apF, abs, s2_aframeS, Function.comp_def]
  | Err e =>
    refine ⟨.Err e, ?_, hrel⟩
    unfold sim.step.ap_frames_of
    simp [hr, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `push_nested_up_to` (RECON, json): appends `(i, j)` for the leading nested objects of `o` that start before
`target` (`simNestedTW`, the nested part of `enumerateUpTo`). Wrapper over sim core's `sim_push_nested_loop`. -/
theorem sim.step.push_nested_up_to_refines (tn : Nat → String) (out : alloc.vec.Vec sim.step.Ref)
    (o : sim.playable.TopObj) (i : Usize) (target : F64)
    (hn : o.nested.val.length < 2 ^ 63) (hcap : out.val.length + o.nested.val.length < Usize.max) :
    ∃ w, sim.step.push_nested_up_to out o i target = ok w ∧
      w.val.map (fun r => (abs r : Nat × Int)) = out.val.map (fun r => (abs r : Nat × Int)) ++
        simNestedTW (topS tn o) i.val target := by
  have hle := (List.takeWhile_sublist (fun k => decide ((o.nested.val[k]!).start < target))
    (l := List.range' (0#usize).val (o.nested.val.length - (0#usize).val))).length_le
  simp only [List.length_range'] at hle
  obtain ⟨w, hw, hwv⟩ := sim_push_nested_loop o i target hn _ 0#usize out rfl (by simp) (by
    have : (0#usize).val = 0 := rfl; simp only [this, Nat.sub_zero] at hle ⊢; omega)
  refine ⟨w, hw, ?_⟩
  rw [hwv, sim_nestedTW_topS]; rfl

end OsuProofs
