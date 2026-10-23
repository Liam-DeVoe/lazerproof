/-
`sim::step` slider head/tail indices of `mkCtx` (Rust) refine the local `idxOf` of `OsuModel.Sim.mkCtx`
(`simIdxOfS`, a copy of the local function; the bridge to the elaborated `mkCtx` body is part of `mk_ctx`):
`first_idx_of_kind` (`findIdx?`), `last_idx_of_kind` (`simLastFrom`), `idx_of_kind`, `idx_list` (`mapM`).
-/
import OsuProofs.Sim.MkHealthCfg
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

def simLastFrom (k : OsuModel.Sim.Kind) : List OsuModel.Sim.Kind → Nat → Option Nat → Option Nat
  | [], _, r => r
  | x :: t, j, r => simLastFrom k t (j + 1) (if x == k then some j else r)

def simKinds (o : sim.playable.TopObj) : List OsuModel.Sim.Kind := o.nested.val.map (fun n => kindS n.kind)

theorem sim_last_idx_loop (o : sim.playable.TopObj) (k : sim.playable.Kind) :
    ∀ n (r : Option Usize) (j : Usize), o.nested.val.length - j.val = n → j.val ≤ o.nested.val.length →
      ∃ r', sim.step.last_idx_of_kind_loop o k r j = ok r' ∧
        r'.map (·.val) = simLastFrom (kindS k) ((simKinds o).drop j.val) j.val (r.map (·.val)) := by
  intro n
  induction n with
  | zero =>
    intro r j hn hj
    have hdn : (simKinds o).drop j.val = [] := List.drop_of_length_le (by simp [simKinds]; omega)
    refine ⟨r, ?_, by simp [hdn, simLastFrom]⟩
    unfold sim.step.last_idx_of_kind_loop; rw [loop_unfold]
    have : ¬ (j < alloc.vec.Vec.len o.nested) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.last_idx_of_kind_loop.body, this]
  | succ n ih =>
    intro r j hn hj
    have hlt : j.val < o.nested.val.length := by omega
    have hlt' : j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨j1, hj1, ej1⟩ := usize_add_one j (by have := o.nested.property; omega)
    let r1 : Option Usize := if (kindS (o.nested.val[j.val]'hlt).kind == kindS k) = true then some j else r
    obtain ⟨r', hr', er'⟩ := ih r1 j1 (by omega) (by omega)
    refine ⟨r', ?_, ?_⟩
    · unfold sim.step.last_idx_of_kind_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.last_idx_of_kind_loop.body o k r j = ok (.cont (r1, j1)) by
        by_cases hc : (kindS (o.nested.val[j.val]'hlt).kind == kindS k) = true <;>
          simp [sim.step.last_idx_of_kind_loop.body, hlt', vec_index_usize_ok _ _ hlt, hc, hj1, r1]]
      simp only [bind_ok]
      unfold sim.step.last_idx_of_kind_loop at hr'; exact hr'
    · rw [er', ej1]
      have hd : (simKinds o).drop j.val = kindS (o.nested.val[j.val]'hlt).kind :: (simKinds o).drop (j.val + 1) := by
        simp only [simKinds]; rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
      rw [hd, simLastFrom]
      congr 1
      by_cases hc : (kindS (o.nested.val[j.val]'hlt).kind == kindS k) = true <;> simp [hc, r1]

theorem sim_first_idx_loop (o : sim.playable.TopObj) (k : sim.playable.Kind) :
    ∀ n (j : Usize), o.nested.val.length - j.val = n → j.val ≤ o.nested.val.length →
      ∃ r', sim.step.first_idx_of_kind_loop o k none j = ok r' ∧
        r'.map (·.val) = (((simKinds o).drop j.val).findIdx? (· == kindS k)).map (· + j.val) := by
  intro n
  induction n with
  | zero =>
    intro j hn hj
    have hdn : (simKinds o).drop j.val = [] := List.drop_of_length_le (by simp [simKinds]; omega)
    refine ⟨none, ?_, by simp [hdn]⟩
    unfold sim.step.first_idx_of_kind_loop; rw [loop_unfold]
    have : ¬ (j < alloc.vec.Vec.len o.nested) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.first_idx_of_kind_loop.body, this]
  | succ n ih =>
    intro j hn hj
    have hlt : j.val < o.nested.val.length := by omega
    have hlt' : j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨j1, hj1, ej1⟩ := usize_add_one j (by have := o.nested.property; omega)
    have hd : (simKinds o).drop j.val = kindS (o.nested.val[j.val]'hlt).kind :: (simKinds o).drop (j.val + 1) := by
      simp only [simKinds]; rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hd, List.findIdx?_cons]
    by_cases hc : (kindS (o.nested.val[j.val]'hlt).kind == kindS k) = true
    · refine ⟨some j, ?_, by simp [hc]⟩
      unfold sim.step.first_idx_of_kind_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.first_idx_of_kind_loop.body o k none j = ok (.cont (some j, j1)) by
        simp [sim.step.first_idx_of_kind_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt, hc, hj1]]
      simp only [bind_ok]; rw [loop_unfold]
      by_cases h2 : j1 < alloc.vec.Vec.len o.nested <;>
        simp [sim.step.first_idx_of_kind_loop.body, h2, core.option.Option.is_none]
    · obtain ⟨r', hr', er'⟩ := ih j1 (by omega) (by omega)
      refine ⟨r', ?_, ?_⟩
      · unfold sim.step.first_idx_of_kind_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.first_idx_of_kind_loop.body o k none j = ok (.cont (none, j1)) by
          simp [sim.step.first_idx_of_kind_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt,
            hc, hj1]]
        simp only [bind_ok]
        unfold sim.step.first_idx_of_kind_loop at hr'; exact hr'
      · rw [er', ej1]; simp only [hc, Bool.false_eq_true, if_false, Option.map_map]
        congr 1; funext x; simp; omega

/-- the local `idxOf` of `mkCtx` -/
def simIdxOfS (o : OsuModel.Sim.TopObj) (k : OsuModel.Sim.Kind) (last : Bool) : Except String Nat :=
  if (o.h.kind != .slider) = true then .ok 0
  else match (if last then simLastFrom k (o.nested.toList.map (·.kind)) 0 none
      else (o.nested.toList.map (·.kind)).findIdx? (· == k)) with
    | some j => .ok j
    | none => .error s!"malformed playable: slider at {o.h.start} without a {repr k}"

-- FRAGMENT-OF: OsuModel.Sim.mkCtx (bridge owed: simIdxOfS = the local `idxOf` of mkCtx: = simIdxOfSpec (verbatim copy) by sim_idxOfSpec_eq in Sim/MkCtx; the copy is identified with the local lambda in mk_ctx_refines)
theorem sim.step.idx_of_kind_refines (tn) (o : sim.playable.TopObj) (k : sim.playable.Kind) (last : Bool) :
    ∃ R, sim.step.idx_of_kind o k last = ok R ∧ simRel (·.val) R (simIdxOfS (topS tn o) (kindS k) last) := by
  have hks : (topS tn o).nested.toList.map (·.kind) = simKinds o := by simp [topS, hobjS, simKinds]
  unfold sim.step.idx_of_kind simIdxOfS
  have hk : (topS tn o).h.kind = kindS o.h.kind := rfl
  have hsl : kindS sim.playable.Kind.Slider = OsuModel.Sim.Kind.slider := rfl
  simp only [sim_kind_ne_ok, bind_ok, hk, hks, hsl]
  by_cases hs : (kindS o.h.kind != OsuModel.Sim.Kind.slider) = true
  · refine ⟨.Ok 0#usize, by simp [hs], ?_⟩
    simp [hs, simRel]
  · have hs' : (kindS o.h.kind != OsuModel.Sim.Kind.slider) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, if_false]
    cases last
    · obtain ⟨r, hr, er⟩ := sim_first_idx_loop o k _ 0#usize rfl (by simp)
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Nat.add_zero, Option.map_id'] at er
      rw [← er]
      cases r with
      | none => exact ⟨.Err (.SliderWithout o.h.start k), by simp [sim.step.first_idx_of_kind, hr, hs'], ⟨_, rfl⟩⟩
      | some j => exact ⟨.Ok j, by simp [sim.step.first_idx_of_kind, hr, hs'], rfl⟩
    · obtain ⟨r, hr, er⟩ := sim_last_idx_loop o k _ none 0#usize rfl (by simp)
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Option.map_none] at er
      simp only [if_true]
      rw [← er]
      cases r with
      | none => exact ⟨.Err (.SliderWithout o.h.start k), by simp [sim.step.last_idx_of_kind, hr, hs'], ⟨_, rfl⟩⟩
      | some j => exact ⟨.Ok j, by simp [sim.step.last_idx_of_kind, hr, hs'], rfl⟩

theorem sim_idx_list_loop (tn) (pb : sim.playable.Playable) (k : sim.playable.Kind) (last : Bool) :
    ∀ n (out : alloc.vec.Vec Usize) (i : Usize), pb.objects.val.length - i.val = n → i.val ≤ pb.objects.val.length →
      out.val.length = i.val →
      ∃ R, sim.step.idx_list_loop pb k last out i = ok R ∧
        simRel (fun v : alloc.vec.Vec Usize => v.val.map (·.val)) R
          ((((pb.objects.val.drop i.val).map (topS tn)).mapM (simIdxOfS · (kindS k) last)).map
            (out.val.map (·.val) ++ ·)) := by
  intro n
  induction n with
  | zero =>
    intro out i hn hi ho
    have hdn : pb.objects.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨.Ok out, ?_, by simp [hdn, simRel, Except.map]⟩
    unfold sim.step.idx_list_loop; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.objects) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.idx_list_loop.body, this]
  | succ n ih =>
    intro out i hn hi ho
    have hlt : i.val < pb.objects.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    have hmax := pb.objects.property
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by omega)
    obtain ⟨r, hr, er⟩ := sim.step.idx_of_kind_refines tn (pb.objects.val[i.val]'hlt) k last
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.mapM_cons]
    cases r with
    | Err e =>
      obtain ⟨m, hm⟩ := er
      refine ⟨.Err e, ?_, ⟨m, by simp [hm, Except.map, Bind.bind, Except.bind]⟩⟩
      unfold sim.step.idx_list_loop; rw [loop_unfold]
      simp [sim.step.idx_list_loop.body, hlt', vec_index_usize_ok _ _ hlt, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.From.from]
    | Ok v =>
      simp only [simRel] at er
      have hpl : out.val.length < Usize.max := by omega
      obtain ⟨R, hR, eR⟩ := ih (vpush out v hpl) i1 (by omega) (by omega) (by simp; omega)
      refine ⟨R, ?_, ?_⟩
      · unfold sim.step.idx_list_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.idx_list_loop.body pb k last out i = ok (.cont (vpush out v hpl, i1)) by
          simp [sim.step.idx_list_loop.body, hlt', vec_index_usize_ok _ _ hlt, hr,
            core.result.Result.Insts.CoreOpsTry.branch, vec_push_ok _ _ hpl, hi1]]
        simp only [bind_ok]
        unfold sim.step.idx_list_loop at hR; exact hR
      · rw [er]; rw [ei1] at eR
        have key : ∀ (E : Except String (List Nat)),
            Except.map (out.val.map (·.val) ++ ·) (do let x ← (Except.ok v.val : Except String Nat); let y ← E; pure (x :: y)) =
            Except.map ((vpush out v hpl).val.map (·.val) ++ ·) E := by
          intro E; cases E <;> simp [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
        simp only [Functor.map] at eR ⊢
        rw [key]; exact eR

-- FRAGMENT-OF: OsuModel.Sim.mkCtx (bridge owed: simIdxOfS = the local `idxOf` of mkCtx: = simIdxOfSpec (verbatim copy) by sim_idxOfSpec_eq in Sim/MkCtx; the copy is identified with the local lambda in mk_ctx_refines)
theorem sim.step.idx_list_refines (tn) (pb : sim.playable.Playable) (k : sim.playable.Kind) (last : Bool) :
    ∃ R, sim.step.idx_list pb k last = ok R ∧
      simRel (fun v : alloc.vec.Vec Usize => v.val.map (·.val)) R
        ((pb.objects.val.map (topS tn)).mapM (simIdxOfS · (kindS k) last)) := by
  obtain ⟨R, hR, eR⟩ := sim_idx_list_loop tn pb k last _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  refine ⟨R, hR, ?_⟩
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.map_nil,
    List.nil_append] at eR
  cases h : (pb.objects.val.map (topS tn)).mapM (simIdxOfS · (kindS k) last) <;> rw [h] at eR <;>
    simpa [Except.map, Functor.map] using eR
end OsuProofs
