/-
`sim::scoring::mk_health_cfg` (Rust) refines `OsuModel.Sim.mkHealthCfg`: drain start / gameplay end, no-drain
periods, the legacy branch (`compute_legacy_drain_rate`) and the simulated-autoplay branch (health increases of
the non-bonus simulated judgements, target `clampK`, `compute_drain_rate`).
-/
import OsuProofs.Sim.LegacyDrain
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

def simIncsS (c : OsuModel.Sim.HealthCfg) (l : List OsuModel.Sim.JInfo) : List (F64 × F64) :=
  l.filterMap (fun j => if j.ty.isBonus then none
    else some (j.endTime + j.timeOffset, (({} : OsuModel.Sim.HealthSt).increaseFor c j true).2))

theorem sim_mhc_loop (legacy : Bool) (hp f f1 ds ge : F64) (periods : alloc.vec.Vec sim.playable.Period)
    (js : alloc.vec.Vec sim.scoring.JInfo) (h0 : sim.scoring.HealthSt) (hh0 : (abs h0 : OsuModel.Sim.HealthSt) = {}) :
    ∀ n (incs : alloc.vec.Vec sim.scoring.Inc) (i : Usize), js.val.length - i.val = n → i.val ≤ js.val.length →
      incs.val.length ≤ i.val →
      ∃ w, sim.scoring.mk_health_cfg_loop legacy hp f f1 ds ge periods js h0 incs i = ok w ∧
        w.val.map (fun x => (x.time, x.amount)) = incs.val.map (fun x => (x.time, x.amount)) ++
          simIncsS (abs (⟨legacy, hp, f, f1, ds, ge, periods⟩ : sim.scoring.HealthCfg)) ((js.val.drop i.val).map abs) := by
  intro n
  induction n with
  | zero =>
    intro incs i hn hi hl
    have hdn : js.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨incs, ?_, by simp [hdn, simIncsS]⟩
    unfold sim.scoring.mk_health_cfg_loop; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len js) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.mk_health_cfg_loop.body, this]
  | succ n ih =>
    intro incs i hn hi hl
    have hlt : i.val < js.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len js := by rw [vec_lt_len_iff]; exact hlt
    have hjm := js.property
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by omega)
    set j := js.val[i.val]'hlt with hj
    obtain ⟨bb, hbb, ebb⟩ := sim.basic.is_bonus_refines j.ty
    obtain ⟨cr, inc, hinc, einc⟩ := sim.scoring.increase_for_refines h0 ⟨legacy, hp, f, f1, ds, ge, periods⟩ j true
    rw [hh0] at einc
    have hpl : incs.val.length < Usize.max := by omega
    let incs1 := if bb then incs else vpush incs ⟨j.end_time + j.time_offset, inc⟩ hpl
    obtain ⟨w, hw, ew⟩ := ih incs1 i1 (by omega) (by omega) (by simp only [incs1]; split <;> (try simp) <;> omega)
    refine ⟨w, ?_, ?_⟩
    · unfold sim.scoring.mk_health_cfg_loop; rw [loop_unfold]; dsimp only
      rw [show sim.scoring.mk_health_cfg_loop.body legacy hp f f1 ds ge periods js h0 incs i = ok (.cont (incs1, i1)) by
        cases bb <;> simp [sim.scoring.mk_health_cfg_loop.body, hlt', vec_index_eq _ _ hlt, vec_index_usize_ok _ _ hlt,
          ← hj, hbb, hinc, float.F64.add, vec_push_ok _ _ hpl, hi1, incs1]]
      simp only [bind_ok]
      unfold sim.scoring.mk_health_cfg_loop at hw; exact hw
    · rw [ew, ei1, List.drop_eq_getElem_cons hlt, ← hj]
      simp only [abs, id] at ebb
      simp only [List.map_cons, simIncsS, List.filterMap_cons]
      have e2 : (abs j : OsuModel.Sim.JInfo).ty.isBonus = bb := ebb
      cases bb
      · simp only [incs1, Bool.false_eq_true, if_false, vpush_val, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, e2, einc]
        rfl
      · simp only [incs1, if_true, e2]

theorem sim_exc_forIn_filter_push {J X : Type} (q : J → Bool) (f : J → X) (arr : _root_.Array J) (acc : _root_.Array X) :
    forIn (m := Except String) arr acc (fun j s => if q j = true then pure (ForInStep.yield (s.push (f j)))
      else pure (ForInStep.yield s)) =
      .ok (acc ++ (arr.toList.filterMap (fun j => if q j = true then some (f j) else none)).toArray) := by
  rw [← Array.forIn_toList]
  generalize arr.toList = l
  induction l generalizing acc with
  | nil => simp
  | cons x t ih =>
    rw [List.forIn_cons]
    by_cases h : q x = true
    · simp only [h, if_true]
      simp only [pure_bind]
      rw [ih]; simp [h]
    · simp only [h, if_false, Bool.false_eq_true]
      simp only [pure_bind]
      rw [ih]; simp [h]

theorem sim_hp_to_f64 (x : F32) : float.F32.to_f64 x = ok x.toF64 := by
  simp [float.F32.to_f64]

theorem sim_clampOr01 (x : F64) : simClampOrD x 0 1 = OsuModel.Sim.clampK x 0 1 := by
  unfold simClampOrD OsuModel.Sim.clampK F64.clamp
  have : ¬ ((1 : F64) < 0) := by decide
  by_cases h1 : x < 0 <;> by_cases h2 : (1 : F64) < x <;> simp [h1, h2, this]

theorem sim_filterMap_incs (c : OsuModel.Sim.HealthCfg) (l : List OsuModel.Sim.JInfo) :
    l.filterMap (fun j => if (!j.ty.isBonus) = true then some (j.endTime + j.timeOffset,
      (({} : OsuModel.Sim.HealthSt).increaseFor c j true).2) else none) = simIncsS c l := by
  unfold simIncsS; congr 1; funext j; cases j.ty.isBonus <;> rfl

theorem sim.scoring.mk_health_cfg_refines (tn) (pb : sim.playable.Playable) (legacy : Bool)
    (hcap : (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < Usize.max) :
    ∃ R, sim.scoring.mk_health_cfg pb legacy = ok R ∧
      simRel (fun c => (abs c : OsuModel.Sim.HealthCfg)) R (OsuModel.Sim.mkHealthCfg (playableS tn pb) legacy) := by
  obtain ⟨per, hper, eper⟩ := sim.scoring.no_drain_periods_refines tn pb
  have hn := pb.objects.property
  -- drain start / gameplay end
  let dsv : F64 := match pb.objects.val[0]? with | some o => o.h.start | none => 0
  let gev : F64 := match pb.objects.val.getLast? with | some o => o.h.end_time | none => 0
  have hds : (if alloc.vec.Vec.len pb.objects > 0#usize then (do
        let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) pb.objects 0#usize
        ok «to».h.start) else sim.scoring.F64_0) = ok dsv := by
    by_cases h0 : pb.objects.val.length = 0
    · have : ¬ alloc.vec.Vec.len pb.objects > 0#usize := by scalar_tac
      have e : pb.objects.val = [] := List.eq_nil_of_length_eq_zero h0
      simp [this, dsv, e, sim_scoring_F64_0]
    · have : alloc.vec.Vec.len pb.objects > 0#usize := by scalar_tac
      have h0' : (0#usize : Usize).val < pb.objects.val.length := by simp; omega
      simp [this, dsv, vec_index_eq _ _ h0', List.getElem?_eq_getElem (show 0 < pb.objects.val.length by omega)]
  have hge : (if alloc.vec.Vec.len pb.objects > 0#usize then (do
        let i ← alloc.vec.Vec.len pb.objects - 1#usize
        let «to» ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.TopObj) pb.objects i
        ok «to».h.end_time) else sim.scoring.F64_0) = ok gev := by
    by_cases h0 : pb.objects.val.length = 0
    · have : ¬ alloc.vec.Vec.len pb.objects > 0#usize := by scalar_tac
      have e : pb.objects.val = [] := List.eq_nil_of_length_eq_zero h0
      simp [this, gev, e, sim_scoring_F64_0]
    · have : alloc.vec.Vec.len pb.objects > 0#usize := by scalar_tac
      obtain ⟨i, hi, ei⟩ : ∃ z, alloc.vec.Vec.len pb.objects - 1#usize = ok z ∧ z.val = pb.objects.val.length - 1 := by
        obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len pb.objects) (y := 1#usize)
          (by simp; omega))
        exact ⟨z, hz, by simp at hv; omega⟩
      have hil : i.val < pb.objects.val.length := by omega
      simp [this, gev, hi, vec_index_eq _ _ hil, vec_index_usize_ok _ _ hil, List.getLast?_eq_getElem?, ei,
        List.getElem?_eq_getElem (show pb.objects.val.length - 1 < pb.objects.val.length by omega)]
  have hS0 : (playableS tn pb).objects[0]? = (pb.objects.val[0]?).map (topS tn) := by simp [playableS]
  have hSl : (playableS tn pb).objects.back? = (pb.objects.val.getLast?).map (topS tn) := by
    simp [playableS, List.getLast?_map]
  have hhp : (playableS tn pb).difficulty.hp = pb.difficulty.hp := rfl
  have hBr : (playableS tn pb).breaks = (simPS (alloc.vec.Vec.deref pb.breaks)).toArray := by
    simp [playableS, abs, simPS, alloc.vec.Vec.deref]
  unfold sim.scoring.mk_health_cfg OsuModel.Sim.mkHealthCfg
  simp only [sim_hp_to_f64, bind_ok, hds, hge, hper, hhp, hS0, hSl, eper]
  have hdsv : ∀ o, pb.objects.val[0]? = o → dsv = (match o with | some o => o.h.start | none => 0) := by
    intro o ho; simp only [dsv, ho]
  have hgev : ∀ o, pb.objects.val.getLast? = o → gev = (match o with | some o => o.h.end_time | none => 0) := by
    intro o ho; simp only [gev, ho]
  cases hx : pb.objects.val[0]? with
  | none =>
    cases hy : pb.objects.val.getLast? with
    | none =>
      simp only [Option.map_none, Option.map_some]
      rw [hdsv _ hx, hgev _ hy]; dsimp only
      try simp only [show ∀ o : sim.playable.TopObj, (topS tn o).h.endTime = o.h.end_time from fun _ => rfl,
        show ∀ o : sim.playable.TopObj, (topS tn o).h.start = o.h.start from fun _ => rfl]
      cases legacy
      · simp only [Bool.false_eq_true, if_false]
        obtain ⟨js, hjs, ejs⟩ := sim.scoring.simulated_judgements_refines tn pb hcap
        obtain ⟨h0, hh0, eh0⟩ := sim.scoring.health_st_init_refines (alloc.vec.Vec.new U64)
        have eh0' : (abs h0 : OsuModel.Sim.HealthSt) = {} := by rw [← eh0]; rfl
        obtain ⟨t0, ht0, et0⟩ := sim.scoring.difficulty_range_refines (F32.toF64 pb.difficulty.hp) 0.99 0.9 0.4
        simp only [abs, id] at et0
        obtain ⟨w, hw, ew⟩ := sim_mhc_loop false (F32.toF64 pb.difficulty.hp) 0 1 (0 : F64) (0 : F64) per js h0 eh0' _
          (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
        have htg : OsuModel.Sim.clampK (t0 + 0 * (1 - t0)) 0 1 = simClampOrD (t0 + 0 * (1 - t0)) 0 1 := (sim_clampOr01 _).symm
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_drain_rate_refines (alloc.vec.Vec.deref w)
          (alloc.vec.Vec.deref pb.breaks) (0 : F64) (simClampOrD (t0 + 0 * (1 - t0)) 0 1)
        have hinc : (simIncs (alloc.vec.Vec.deref w)) = simIncsS (abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (0 : F64), (0 : F64), per⟩ :
            sim.scoring.HealthCfg)) (js.val.map abs) := by
          simp only [simIncs]
          have e : (alloc.vec.Vec.deref w).val = w.val := by simp [alloc.vec.Vec.deref]
          simp only [e]; simpa using ew
        simp only [ejs, et0, htg]
        rw [sim_exc_forIn_filter_push]
        simp only [Array.empty_append, sim_filterMap_incs]
        have hcfg : ({ legacy := false, hp := F32.toF64 pb.difficulty.hp, drainRate := 0, drainStartTime := (0 : F64), gameplayEndTime := (0 : F64), periods := (List.map simPP ↑per).toArray } : OsuModel.Sim.HealthCfg) =
            abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (0 : F64), (0 : F64), per⟩ : sim.scoring.HealthCfg) := rfl
        have hjl : (abs js : _root_.Array OsuModel.Sim.JInfo).toList = js.val.map abs := by simp [abs]
        rw [hcfg, hjl, ← hinc, hBr]
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨false, F32.toF64 pb.difficulty.hp, v, 1, (0 : F64), (0 : F64), per⟩, ?_, ?_⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from, fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
      · simp only [if_true]
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_legacy_drain_rate_refines tn pb (F32.toF64 pb.difficulty.hp) (0 : F64)
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨true, F32.toF64 pb.difficulty.hp, v.test_drop, v.mult, (0 : F64), (0 : F64), per⟩, ?_, ?_⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
    | some ol =>
      simp only [Option.map_none, Option.map_some]
      rw [hdsv _ hx, hgev _ hy]; dsimp only
      try simp only [show ∀ o : sim.playable.TopObj, (topS tn o).h.endTime = o.h.end_time from fun _ => rfl,
        show ∀ o : sim.playable.TopObj, (topS tn o).h.start = o.h.start from fun _ => rfl]
      cases legacy
      · simp only [Bool.false_eq_true, if_false]
        obtain ⟨js, hjs, ejs⟩ := sim.scoring.simulated_judgements_refines tn pb hcap
        obtain ⟨h0, hh0, eh0⟩ := sim.scoring.health_st_init_refines (alloc.vec.Vec.new U64)
        have eh0' : (abs h0 : OsuModel.Sim.HealthSt) = {} := by rw [← eh0]; rfl
        obtain ⟨t0, ht0, et0⟩ := sim.scoring.difficulty_range_refines (F32.toF64 pb.difficulty.hp) 0.99 0.9 0.4
        simp only [abs, id] at et0
        obtain ⟨w, hw, ew⟩ := sim_mhc_loop false (F32.toF64 pb.difficulty.hp) 0 1 (0 : F64) (ol.h.end_time : F64) per js h0 eh0' _
          (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
        have htg : OsuModel.Sim.clampK (t0 + 0 * (1 - t0)) 0 1 = simClampOrD (t0 + 0 * (1 - t0)) 0 1 := (sim_clampOr01 _).symm
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_drain_rate_refines (alloc.vec.Vec.deref w)
          (alloc.vec.Vec.deref pb.breaks) (0 : F64) (simClampOrD (t0 + 0 * (1 - t0)) 0 1)
        have hinc : (simIncs (alloc.vec.Vec.deref w)) = simIncsS (abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (0 : F64), (ol.h.end_time : F64), per⟩ :
            sim.scoring.HealthCfg)) (js.val.map abs) := by
          simp only [simIncs]
          have e : (alloc.vec.Vec.deref w).val = w.val := by simp [alloc.vec.Vec.deref]
          simp only [e]; simpa using ew
        simp only [ejs, et0, htg]
        rw [sim_exc_forIn_filter_push]
        simp only [Array.empty_append, sim_filterMap_incs]
        have hcfg : ({ legacy := false, hp := F32.toF64 pb.difficulty.hp, drainRate := 0, drainStartTime := (0 : F64), gameplayEndTime := (ol.h.end_time : F64), periods := (List.map simPP ↑per).toArray } : OsuModel.Sim.HealthCfg) =
            abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (0 : F64), (ol.h.end_time : F64), per⟩ : sim.scoring.HealthCfg) := rfl
        have hjl : (abs js : _root_.Array OsuModel.Sim.JInfo).toList = js.val.map abs := by simp [abs]
        rw [hcfg, hjl, ← hinc, hBr]
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨false, F32.toF64 pb.difficulty.hp, v, 1, (0 : F64), (ol.h.end_time : F64), per⟩, ?_, ?_⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from, fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
      · simp only [if_true]
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_legacy_drain_rate_refines tn pb (F32.toF64 pb.difficulty.hp) (0 : F64)
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨true, F32.toF64 pb.difficulty.hp, v.test_drop, v.mult, (0 : F64), (ol.h.end_time : F64), per⟩, ?_, ?_⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
  | some o0 =>
    cases hy : pb.objects.val.getLast? with
    | none =>
      simp only [Option.map_none, Option.map_some]
      rw [hdsv _ hx, hgev _ hy]; dsimp only
      try simp only [show ∀ o : sim.playable.TopObj, (topS tn o).h.endTime = o.h.end_time from fun _ => rfl,
        show ∀ o : sim.playable.TopObj, (topS tn o).h.start = o.h.start from fun _ => rfl]
      cases legacy
      · simp only [Bool.false_eq_true, if_false]
        obtain ⟨js, hjs, ejs⟩ := sim.scoring.simulated_judgements_refines tn pb hcap
        obtain ⟨h0, hh0, eh0⟩ := sim.scoring.health_st_init_refines (alloc.vec.Vec.new U64)
        have eh0' : (abs h0 : OsuModel.Sim.HealthSt) = {} := by rw [← eh0]; rfl
        obtain ⟨t0, ht0, et0⟩ := sim.scoring.difficulty_range_refines (F32.toF64 pb.difficulty.hp) 0.99 0.9 0.4
        simp only [abs, id] at et0
        obtain ⟨w, hw, ew⟩ := sim_mhc_loop false (F32.toF64 pb.difficulty.hp) 0 1 (o0.h.start : F64) (0 : F64) per js h0 eh0' _
          (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
        have htg : OsuModel.Sim.clampK (t0 + 0 * (1 - t0)) 0 1 = simClampOrD (t0 + 0 * (1 - t0)) 0 1 := (sim_clampOr01 _).symm
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_drain_rate_refines (alloc.vec.Vec.deref w)
          (alloc.vec.Vec.deref pb.breaks) (o0.h.start : F64) (simClampOrD (t0 + 0 * (1 - t0)) 0 1)
        have hinc : (simIncs (alloc.vec.Vec.deref w)) = simIncsS (abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (o0.h.start : F64), (0 : F64), per⟩ :
            sim.scoring.HealthCfg)) (js.val.map abs) := by
          simp only [simIncs]
          have e : (alloc.vec.Vec.deref w).val = w.val := by simp [alloc.vec.Vec.deref]
          simp only [e]; simpa using ew
        simp only [ejs, et0, htg]
        rw [sim_exc_forIn_filter_push]
        simp only [Array.empty_append, sim_filterMap_incs]
        have hcfg : ({ legacy := false, hp := F32.toF64 pb.difficulty.hp, drainRate := 0, drainStartTime := (o0.h.start : F64), gameplayEndTime := (0 : F64), periods := (List.map simPP ↑per).toArray } : OsuModel.Sim.HealthCfg) =
            abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (o0.h.start : F64), (0 : F64), per⟩ : sim.scoring.HealthCfg) := rfl
        have hjl : (abs js : _root_.Array OsuModel.Sim.JInfo).toList = js.val.map abs := by simp [abs]
        rw [hcfg, hjl, ← hinc, hBr]
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨false, F32.toF64 pb.difficulty.hp, v, 1, (o0.h.start : F64), (0 : F64), per⟩, ?_, ?_⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from, fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
      · simp only [if_true]
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_legacy_drain_rate_refines tn pb (F32.toF64 pb.difficulty.hp) (o0.h.start : F64)
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨true, F32.toF64 pb.difficulty.hp, v.test_drop, v.mult, (o0.h.start : F64), (0 : F64), per⟩, ?_, ?_⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
    | some ol =>
      simp only [Option.map_none, Option.map_some]
      rw [hdsv _ hx, hgev _ hy]; dsimp only
      try simp only [show ∀ o : sim.playable.TopObj, (topS tn o).h.endTime = o.h.end_time from fun _ => rfl,
        show ∀ o : sim.playable.TopObj, (topS tn o).h.start = o.h.start from fun _ => rfl]
      cases legacy
      · simp only [Bool.false_eq_true, if_false]
        obtain ⟨js, hjs, ejs⟩ := sim.scoring.simulated_judgements_refines tn pb hcap
        obtain ⟨h0, hh0, eh0⟩ := sim.scoring.health_st_init_refines (alloc.vec.Vec.new U64)
        have eh0' : (abs h0 : OsuModel.Sim.HealthSt) = {} := by rw [← eh0]; rfl
        obtain ⟨t0, ht0, et0⟩ := sim.scoring.difficulty_range_refines (F32.toF64 pb.difficulty.hp) 0.99 0.9 0.4
        simp only [abs, id] at et0
        obtain ⟨w, hw, ew⟩ := sim_mhc_loop false (F32.toF64 pb.difficulty.hp) 0 1 (o0.h.start : F64) (ol.h.end_time : F64) per js h0 eh0' _
          (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
        have htg : OsuModel.Sim.clampK (t0 + 0 * (1 - t0)) 0 1 = simClampOrD (t0 + 0 * (1 - t0)) 0 1 := (sim_clampOr01 _).symm
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_drain_rate_refines (alloc.vec.Vec.deref w)
          (alloc.vec.Vec.deref pb.breaks) (o0.h.start : F64) (simClampOrD (t0 + 0 * (1 - t0)) 0 1)
        have hinc : (simIncs (alloc.vec.Vec.deref w)) = simIncsS (abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (o0.h.start : F64), (ol.h.end_time : F64), per⟩ :
            sim.scoring.HealthCfg)) (js.val.map abs) := by
          simp only [simIncs]
          have e : (alloc.vec.Vec.deref w).val = w.val := by simp [alloc.vec.Vec.deref]
          simp only [e]; simpa using ew
        simp only [ejs, et0, htg]
        rw [sim_exc_forIn_filter_push]
        simp only [Array.empty_append, sim_filterMap_incs]
        have hcfg : ({ legacy := false, hp := F32.toF64 pb.difficulty.hp, drainRate := 0, drainStartTime := (o0.h.start : F64), gameplayEndTime := (ol.h.end_time : F64), periods := (List.map simPP ↑per).toArray } : OsuModel.Sim.HealthCfg) =
            abs (⟨false, F32.toF64 pb.difficulty.hp, 0, 1, (o0.h.start : F64), (ol.h.end_time : F64), per⟩ : sim.scoring.HealthCfg) := rfl
        have hjl : (abs js : _root_.Array OsuModel.Sim.JInfo).toList = js.val.map abs := by simp [abs]
        rw [hcfg, hjl, ← hinc, hBr]
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨false, F32.toF64 pb.difficulty.hp, v, 1, (o0.h.start : F64), (ol.h.end_time : F64), per⟩, ?_, ?_⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [ht0, sim_scoring_F64_1, sim_scoring_F64_0, float.F64.sub, float.F64.mul, float.F64.add,
              sim.netx.f64_clamp_or_refines, hjs, hh0, hw, hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from, fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
      · simp only [if_true]
        obtain ⟨R, hR, eR⟩ := sim.scoring.compute_legacy_drain_rate_refines tn pb (F32.toF64 pb.difficulty.hp) (o0.h.start : F64)
        cases R with
        | Ok v =>
          refine ⟨.Ok ⟨true, F32.toF64 pb.difficulty.hp, v.test_drop, v.mult, (o0.h.start : F64), (ol.h.end_time : F64), per⟩, ?_, ?_⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch]
          · simp only [simRel] at eR ⊢; simp only [Bind.bind, Except.bind]; first | (rw [eR]; rfl) | rw [eR]
        | Err e =>
          obtain ⟨m, hm⟩ := eR
          refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
          · simp [hR, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              core.convert.From.from]
          · simp only [Bind.bind, Except.bind]; first | (rw [hm]; rfl) | rw [hm]
end OsuProofs
