/-
Pieces of `sim::step::mk_ctx` (Rust) against `OsuModel.Sim.mkCtx`: `has_autopilot` / `has_adaptive` (the `any`
conditions of `apFrames` / `precEnd`) and `first_objects` (`firstObj`).
-/
import OsuProofs.Sim.ApplyResult
import OsuProofs.Sim.IdxKind
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

def simIsAP : sim.mods.Updatable → Bool | .Autopilot => true | _ => false
def simIsAd : sim.mods.DynRate → Bool | .Adaptive _ => true | _ => false

theorem sim_has_ap_loop (cfg : sim.mods.Config) : ∀ k (i : Usize) (r : Bool),
    cfg.updatables.val.length - i.val = k → i.val ≤ cfg.updatables.val.length →
    sim.step.has_autopilot_loop cfg i r = ok (r || (cfg.updatables.val.drop i.val).any simIsAP) := by
  intro k
  induction k with
  | zero =>
    intro i r hk hi
    unfold sim.step.has_autopilot_loop
    rw [loop_unfold]
    have : ¬ i < alloc.vec.Vec.len cfg.updatables := by rw [vec_lt_len_iff]; omega
    simp [sim.step.has_autopilot_loop.body, this, List.drop_of_length_le (show cfg.updatables.val.length ≤ i.val by omega)]
  | succ k ih =>
    intro i r hk hi
    have hlt : i.val < cfg.updatables.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := cfg.updatables.property; omega)
    have hd : cfg.updatables.val.drop i.val = cfg.updatables.val[i.val]'hlt :: cfg.updatables.val.drop i1.val := by
      rw [hi1v]; exact List.drop_eq_getElem_cons hlt
    have hl : i < alloc.vec.Vec.len cfg.updatables := by rw [vec_lt_len_iff]; exact hlt
    have hb : sim.step.has_autopilot_loop.body cfg i r =
        ok (.cont (i1, r || simIsAP (cfg.updatables.val[i.val]'hlt))) := by
      simp only [sim.step.has_autopilot_loop.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok]
      cases hu : cfg.updatables.val[i.val]'hlt <;> simp [hi1, simIsAP]
    have e2 := ih i1 (r || simIsAP (cfg.updatables.val[i.val]'hlt)) (by omega) (by omega)
    unfold sim.step.has_autopilot_loop at e2 ⊢
    rw [loop_unfold]
    dsimp only
    rw [hb]
    simp only [bind_ok]
    rw [e2, hd]
    simp [Bool.or_assoc]
theorem sim_has_ad_loop (cfg : sim.mods.Config) : ∀ k (i : Usize) (r : Bool),
    cfg.dyn_rates.val.length - i.val = k → i.val ≤ cfg.dyn_rates.val.length →
    sim.step.has_adaptive_loop cfg i r = ok (r || (cfg.dyn_rates.val.drop i.val).any simIsAd) := by
  intro k
  induction k with
  | zero =>
    intro i r hk hi
    unfold sim.step.has_adaptive_loop
    rw [loop_unfold]
    have : ¬ i < alloc.vec.Vec.len cfg.dyn_rates := by rw [vec_lt_len_iff]; omega
    simp [sim.step.has_adaptive_loop.body, this, List.drop_of_length_le (show cfg.dyn_rates.val.length ≤ i.val by omega)]
  | succ k ih =>
    intro i r hk hi
    have hlt : i.val < cfg.dyn_rates.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := cfg.dyn_rates.property; omega)
    have hd : cfg.dyn_rates.val.drop i.val = cfg.dyn_rates.val[i.val]'hlt :: cfg.dyn_rates.val.drop i1.val := by
      rw [hi1v]; exact List.drop_eq_getElem_cons hlt
    have hl : i < alloc.vec.Vec.len cfg.dyn_rates := by rw [vec_lt_len_iff]; exact hlt
    have hb : sim.step.has_adaptive_loop.body cfg i r =
        ok (.cont (i1, r || simIsAd (cfg.dyn_rates.val[i.val]'hlt))) := by
      simp only [sim.step.has_adaptive_loop.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok]
      cases hu : cfg.dyn_rates.val[i.val]'hlt <;> simp [hi1, simIsAd]
    have e2 := ih i1 (r || simIsAd (cfg.dyn_rates.val[i.val]'hlt)) (by omega) (by omega)
    unfold sim.step.has_adaptive_loop at e2 ⊢
    rw [loop_unfold]
    dsimp only
    rw [hb]
    simp only [bind_ok]
    rw [e2, hd]
    simp [Bool.or_assoc]

theorem sim_abs_any {A B : Type} [AbsTo A B] (v : alloc.vec.Vec A) (p : B → Bool) (q : A → Bool)
    (h : ∀ a, p (abs a) = q a) : (abs v : _root_.Array B).any p = v.val.any q := by
  simp [abs, Array.any_toList, List.any_map, Function.comp_def, h]

theorem sim.step.has_autopilot_refines (cfg : sim.mods.Config) (p : OsuModel.Sim.Updatable → Bool)
    (hp : ∀ u, p (abs u) = simIsAP u) : sim.step.has_autopilot cfg = ok ((configS cfg).updatables.any p) := by
  unfold sim.step.has_autopilot
  rw [sim_has_ap_loop cfg _ 0#usize false rfl (by simp)]
  simp only [Bool.false_or, configS]
  rw [sim_abs_any _ _ _ hp]; simp

theorem sim.step.has_adaptive_refines (cfg : sim.mods.Config) (p : OsuModel.Sim.DynRate → Bool)
    (hp : ∀ u, p (abs u) = simIsAd u) : sim.step.has_adaptive cfg = ok ((configS cfg).dynRates.any p) := by
  unfold sim.step.has_adaptive
  rw [sim_has_ad_loop cfg _ 0#usize false rfl (by simp)]
  simp only [Bool.false_or, configS]
  rw [sim_abs_any _ _ _ hp]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def simIsSpin : sim.playable.Kind → Bool | .Spinner => true | _ => false
def simFOp (skips : Bool) (o : sim.playable.TopObj) : Bool := !(skips && simIsSpin o.h.kind)

theorem sim_fo_inner (pb : sim.playable.Playable) (skips : Bool) : ∀ k (i : Usize),
    pb.objects.val.length - i.val = k → i.val ≤ pb.objects.val.length →
    ∃ r, sim.step.first_objects_loop0_loop0 pb skips none i = ok (pb.beatmap_version, pb.audio_lead_in, pb.difficulty,
        pb.base_difficulty, pb.slider_multiplier, pb.slider_tick_rate, pb.breaks, pb.objects, r) ∧
      r.map (·.val) = ((pb.objects.val.drop i.val).findIdx? (simFOp skips)).map (· + i.val) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    refine ⟨none, ?_, by simp [List.drop_of_length_le (show pb.objects.val.length ≤ i.val by omega)]⟩
    unfold sim.step.first_objects_loop0_loop0
    rw [loop_unfold]
    have : ¬ i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; omega
    simp [sim.step.first_objects_loop0_loop0.body, this]
  | succ k ih =>
    intro i hk hi
    have hlt : i.val < pb.objects.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := pb.objects.property; omega)
    have hd : pb.objects.val.drop i.val = pb.objects.val[i.val]'hlt :: pb.objects.val.drop i1.val := by
      rw [hi1v]; exact List.drop_eq_getElem_cons hlt
    have hl : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    by_cases hp : simFOp skips (pb.objects.val[i.val]'hlt) = true
    · have hb : sim.step.first_objects_loop0_loop0.body pb skips none i = ok (.cont (some i, i1)) := by
        simp only [simFOp, simIsSpin] at hp
        cases skips <;> cases hk2 : (pb.objects.val[i.val]'hlt).h.kind <;>
          simp_all [sim.step.first_objects_loop0_loop0.body, hl, vec_index_eq _ _ hlt, core.option.Option.is_none,
            sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, sim.playable.Kind.read_discriminant]
      have hb2 : sim.step.first_objects_loop0_loop0.body pb skips (some i) i1 = ok (.done (pb.beatmap_version,
          pb.audio_lead_in, pb.difficulty, pb.base_difficulty, pb.slider_multiplier, pb.slider_tick_rate, pb.breaks,
          pb.objects, some i)) := by
        unfold sim.step.first_objects_loop0_loop0.body
        split <;> simp [core.option.Option.is_none]
      refine ⟨some i, ?_, by rw [hd]; simp [List.findIdx?_cons, hp]⟩
      unfold sim.step.first_objects_loop0_loop0
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
      rw [loop_unfold]; dsimp only; rw [hb2]; simp only [bind_ok]
    · have hb : sim.step.first_objects_loop0_loop0.body pb skips none i = ok (.cont (none, i1)) := by
        simp only [simFOp, simIsSpin] at hp
        cases skips <;> cases hk2 : (pb.objects.val[i.val]'hlt).h.kind <;>
          simp_all [sim.step.first_objects_loop0_loop0.body, hl, vec_index_eq _ _ hlt, core.option.Option.is_none,
            sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq, sim.playable.Kind.read_discriminant]
      obtain ⟨r, e, hr⟩ := ih i1 (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · unfold sim.step.first_objects_loop0_loop0 at e ⊢
        rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]; exact e
      · rw [hr, hd, List.findIdx?_cons]
        have hp' : simFOp skips (pb.objects.val[i.val]'hlt) = false := by simpa using hp
        rw [hp', if_neg (by simp), Option.map_map]
        congr 1; funext x; simp only [Function.comp_def, hi1v]; omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def simFOv (pb : sim.playable.Playable) (vm : sim.mods.VisMod) : Option Nat :=
  pb.objects.val.findIdx? (simFOp (OsuModel.Sim.VisMod.skipsSpinners (abs vm)))

theorem sim_fo_outer (cfg : sim.mods.Config) (pb : sim.playable.Playable) : ∀ k (vi : Usize)
    (out : alloc.vec.Vec (Option Usize)), cfg.vis_mods.val.length - vi.val = k → vi.val ≤ cfg.vis_mods.val.length →
    out.val.length = vi.val →
    ∃ v, sim.step.first_objects_loop0 cfg pb out vi = ok v ∧
      v.val.map (·.map (·.val)) = out.val.map (·.map (·.val)) ++ (cfg.vis_mods.val.drop vi.val).map (simFOv pb) := by
  intro k
  induction k with
  | zero =>
    intro vi out hk hv ho
    refine ⟨out, ?_, by simp [List.drop_of_length_le (show cfg.vis_mods.val.length ≤ vi.val by omega)]⟩
    unfold sim.step.first_objects_loop0
    rw [loop_unfold]
    have : ¬ vi < alloc.vec.Vec.len cfg.vis_mods := by rw [vec_lt_len_iff]; omega
    simp [sim.step.first_objects_loop0.body, this]
  | succ k ih =>
    intro vi out hk hv ho
    have hlt : vi.val < cfg.vis_mods.val.length := by omega
    have hmax := cfg.vis_mods.property
    obtain ⟨vi1, hvi1, hvi1v⟩ := usize_add_one vi (by omega)
    have hd : cfg.vis_mods.val.drop vi.val = cfg.vis_mods.val[vi.val]'hlt :: cfg.vis_mods.val.drop vi1.val := by
      rw [hvi1v]; exact List.drop_eq_getElem_cons hlt
    have hl : vi < alloc.vec.Vec.len cfg.vis_mods := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨r, hr, hrv⟩ := sim_fo_inner pb (OsuModel.Sim.VisMod.skipsSpinners (abs (cfg.vis_mods.val[vi.val]'hlt)))
      _ 0#usize rfl (by simp)
    have hpl : out.val.length < Usize.max := by omega
    have hb : sim.step.first_objects_loop0.body cfg pb out vi = ok (.cont (pb, vpush out r hpl, vi1)) := by
      simp only [sim.step.first_objects_loop0.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok,
        sim.mods.vis_mod_skips_spinners_refines, hr, uncurry_apply_pair, vec_push_ok _ _ hpl, hvi1]
    obtain ⟨v, e, hvv⟩ := ih vi1 (vpush out r hpl) (by omega) (by omega) (by simp [ho, hvi1v])
    refine ⟨v, ?_, ?_⟩
    · unfold sim.step.first_objects_loop0 at e ⊢
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]; exact e
    · rw [hvv, hd]
      simp only [vpush_val, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append]
      congr 2
      rw [hrv]; simp [simFOv]

theorem sim.step.first_objects_refines (tn : Nat → String) (cfg : sim.mods.Config) (pb : sim.playable.Playable) :
    ∃ v, sim.step.first_objects cfg pb = ok v ∧
      (v.val.map (·.map (·.val))).toArray = (configS cfg).visMods.map fun vm =>
        (playableS tn pb).objects.findIdx? fun o => !(vm.skipsSpinners && o.h.kind == .spinner) := by
  obtain ⟨v, e, hv⟩ := sim_fo_outer cfg pb _ 0#usize (alloc.vec.Vec.new _) rfl (by simp) (by simp)
  refine ⟨v, e, ?_⟩
  rw [hv]
  simp only [alloc.vec.Vec.new, List.map_nil, List.nil_append, List.drop_zero, configS, playableS]
  apply Array.ext'
  simp only [Array.toList_map, List.toList_toArray]
  have e0 : (alloc.vec.Vec.new (Option Usize)).val = [] := rfl
  have hp : ∀ (vm : sim.mods.VisMod) (o : sim.playable.TopObj),
      (!((abs vm : OsuModel.Sim.VisMod).skipsSpinners && (topS tn o).h.kind == OsuModel.Sim.Kind.spinner)) =
        simFOp (OsuModel.Sim.VisMod.skipsSpinners (abs vm)) o := by
    intro vm o
    simp only [simFOp, topS, hobjS]
    cases o.h.kind <;> rfl
  have ev : (abs cfg.vis_mods : _root_.Array OsuModel.Sim.VisMod).toList = cfg.vis_mods.val.map abs := by simp [abs]
  rw [ev, e0]
  simp only [List.map_nil, List.nil_append, List.map_map, Function.comp_def]
  show _ = List.map (fun x => Array.findIdx? _ _) _
  simp only [List.findIdx?_toArray, List.findIdx?_map, Function.comp_def, hp]
  rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net
open OsuModel.Sim in
/-- the local `idxOf` of `mkCtx`, verbatim -/
def simIdxOfSpec (o : TopObj) (k : Kind) (last : Bool) : Except String Nat := do
    if o.h.kind != .slider then return 0
    let mut r : Option Nat := none
    for n in o.nested, j in [0:o.nested.size] do
      if n.kind == k then
        r := some j
        if !last then break
    match r with
    | some j => return j
    | none => throw s!"malformed playable: slider at {o.h.start} without a {repr k}"

def simIdxStep (k : OsuModel.Sim.Kind) (last : Bool) : List OsuModel.Sim.Kind → Nat → Option Nat → Option Nat
  | [], _, r => r
  | x :: t, j, r => if x == k then (if !last then some j else simIdxStep k last t (j + 1) (some j))
      else simIdxStep k last t (j + 1) r

def simIdxFull (k : OsuModel.Sim.Kind) (last : Bool) : List OsuModel.Sim.HObj → Nat → Nat → Option Nat →
    Option Nat × Std.Legacy.Range
  | [], j, n, r => (r, s3b_rg j n)
  | x :: t, j, n, r => if x.kind == k then (if !last then (some j, s3b_rg (j + 1) n)
      else simIdxFull k last t (j + 1) n (some j)) else simIdxFull k last t (j + 1) n r

theorem sim_idxFull_fst (k : OsuModel.Sim.Kind) (last : Bool) : ∀ (l : List OsuModel.Sim.HObj) j n r,
    (simIdxFull k last l j n r).1 = simIdxStep k last (l.map (·.kind)) j r := by
  intro l; induction l with
  | nil => intro j n r; rfl
  | cons x t ih =>
    intro j n r; simp only [simIdxFull, simIdxStep, List.map_cons]
    by_cases hk : (x.kind == k) = true <;> cases last <;> simp [hk, ih]

theorem sim_idx_forIn (k : OsuModel.Sim.Kind) (last : Bool)
    (F : OsuModel.Sim.HObj → Option Nat × Std.Legacy.Range → Except String (ForInStep (Option Nat × Std.Legacy.Range)))
    (l : List OsuModel.Sim.HObj) (j n : Nat) (r : Option Nat)
    (hF : ∀ x r j n, j < n → F x (r, s3b_rg j n) = .ok (if x.kind == k then
        (if !last then .done (some j, s3b_rg (j + 1) n) else .yield (some j, s3b_rg (j + 1) n))
      else .yield (r, s3b_rg (j + 1) n)))
    (hl : l.length + j ≤ n) :
    forIn l (r, s3b_rg j n) F = .ok (simIdxFull k last l j n r) := by
  induction l generalizing j r with
  | nil => rfl
  | cons x t ih =>
    simp only [List.length_cons] at hl
    rw [List.forIn_cons, hF x r j n (by omega)]
    simp only [simIdxFull]
    by_cases hk : (x.kind == k) = true
    · simp only [hk, if_true]
      cases last
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, if_false]
        exact ih (j + 1) (some j) (by omega)
    · simp only [hk, Bool.false_eq_true, if_false]
      exact ih (j + 1) r (by omega)

theorem sim_idxStep_last (k : OsuModel.Sim.Kind) :
    ∀ (l : List OsuModel.Sim.Kind) j r, simIdxStep k true l j r = simLastFrom k l j r := by
  intro l; induction l with
  | nil => intro j r; rfl
  | cons x t ih => intro j r; simp only [simIdxStep, simLastFrom]; split <;> simp [ih]

theorem sim_idxStep_first (k : OsuModel.Sim.Kind) :
    ∀ (l : List OsuModel.Sim.Kind) j, simIdxStep k false l j none = (l.findIdx? (· == k)).map (· + j) := by
  intro l; induction l with
  | nil => intro j; rfl
  | cons x t ih =>
    intro j; simp only [simIdxStep, List.findIdx?_cons]
    split
    · simp_all
    · rename_i h; simp only [Bool.not_eq_true] at h; simp [h, ih, Option.map_map, Function.comp_def]; congr 1; funext y; omega

theorem sim_idxOfSpec_eq (o : OsuModel.Sim.TopObj) (k : OsuModel.Sim.Kind) (last : Bool) :
    simIdxOfSpec o k last = simIdxOfS o k last := by
  unfold simIdxOfSpec simIdxOfS
  split
  · rfl
  · have hrg : (Std.toStream [:o.nested.size] : Std.Legacy.Range) = s3b_rg 0 o.nested.size := rfl
    simp only [hrg]
    rw [← Array.forIn_toList]
    rw [sim_idx_forIn k last _ o.nested.toList 0 o.nested.size none ?hF (by simp)]
    case hF =>
      intro x r j n hj
      simp only [s3b_rg_next j n hj]
      by_cases hk : (x.kind == k) = true <;> cases last <;> simp [hk]
    simp only [Bind.bind, Except.bind]
    rw [sim_idxFull_fst]
    cases last
    · rw [sim_idxStep_first]; simp only [Bool.false_eq_true, if_false, Nat.add_zero, Option.map_id']
      cases (o.nested.toList.map (·.kind)).findIdx? (· == k) <;> rfl
    · rw [sim_idxStep_last]; simp only [if_true]
      cases simLastFrom k (o.nested.toList.map (·.kind)) 0 none <;> rfl
end OsuProofs
