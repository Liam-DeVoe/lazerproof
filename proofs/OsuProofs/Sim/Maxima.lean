/-
`sim::scoring` maxima (Rust) refine `OsuModel.Sim.simulatedJudgements` / `scoreMaxima`: `sim_jinfo`,
`push_simulated`, `simulated_judgements`, `score_maxima` (with the config's `rankAdjust`, as `mkCtx` sets it).
Counter guards of `score_apply` hold along the fold because every counter grows by at most one per judgement
(`sim_apply_bounds`) and the number of judgements fits a `usize`.
-/
import OsuProofs.Sim.LegacyHit
import OsuProofs.Sim.ScoreApply2
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the spec's simulated judgement of a hit object (`simulatedJudgements`) -/
def simSJ (h : OsuModel.Sim.HObj) : OsuModel.Sim.JInfo :=
  { kind := h.kind, maxResult := h.maxResult, ty := h.maxResult, timeAbsolute := h.endTime, endTime := h.endTime
    timeOffset := 0, newCombo := h.newCombo, lastInCombo := h.lastInCombo }

theorem sim_simulatedJudgements_eq (pb : OsuModel.Sim.Playable) :
    OsuModel.Sim.simulatedJudgements pb =
      (pb.objects.toList.flatMap (fun o => o.nested.toList.map simSJ ++ [simSJ o.h])).toArray := by
  unfold OsuModel.Sim.simulatedJudgements
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, pure_bind]
  have hin : ∀ (l : List OsuModel.Sim.HObj) (acc : _root_.Array OsuModel.Sim.JInfo),
      l.foldl (fun b a => b.push (simSJ a)) acc = acc ++ (l.map simSJ).toArray := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons x t ih => intro acc; simp [ih]
  have hout : ∀ (l : List OsuModel.Sim.TopObj) (acc : _root_.Array OsuModel.Sim.JInfo),
      l.foldl (fun b o => (o.nested.foldl (fun b a => b.push (simSJ a)) b).push (simSJ o.h)) acc =
        acc ++ (l.flatMap (fun o => o.nested.toList.map simSJ ++ [simSJ o.h])).toArray := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons x t ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih, ← Array.foldl_toList, hin]
      simp
  rw [← Array.foldl_toList]
  have := hout pb.objects.toList #[]
  simp only [Array.empty_append] at this
  exact this

def simJI (n : sim.playable.HObj) : sim.scoring.JInfo :=
  { kind := n.kind, max_result := n.max_result, min_result := .None, ty := n.max_result, time_absolute := n.end_time
    end_time := n.end_time, time_offset := 0, new_combo := n.new_combo, last_in_combo := n.last_in_combo }

-- FRAGMENT-OF: OsuModel.Sim.simulatedJudgements (simSJ = its inline JInfo literal; bridged in sim.scoring.simulated_judgements_refines)
theorem sim.scoring.sim_jinfo_refines (tn) (n : sim.playable.HObj) :
    sim.scoring.sim_jinfo n = ok (simJI n) ∧ simSJ (hobjS tn n) = abs (simJI n) := by
  refine ⟨by simp [sim.scoring.sim_jinfo, simJI], rfl⟩

theorem sim_push_simulated_loop (o : sim.playable.TopObj) :
    ∀ n (out : alloc.vec.Vec sim.scoring.JInfo) (k : Usize), o.nested.val.length - k.val = n →
      k.val ≤ o.nested.val.length → out.val.length + n < Usize.max →
      ∃ w, sim.scoring.push_simulated_loop out o k = ok (w, o.h) ∧
        w.val = out.val ++ (o.nested.val.drop k.val).map simJI := by
  intro n
  induction n with
  | zero =>
    intro out k hn hk hc
    refine ⟨out, ?_, by simp; omega⟩
    unfold sim.scoring.push_simulated_loop; rw [loop_unfold]
    have : ¬ (k < alloc.vec.Vec.len o.nested) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.push_simulated_loop.body, this]
  | succ n ih =>
    intro out k hn hk hc
    have hlt : k.val < o.nested.val.length := by omega
    have hlt' : k < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hlt
    have hks : k.val + 1 ≤ Usize.max := by have := o.nested.property; omega
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k hks
    have hpl : out.val.length < Usize.max := by omega
    obtain ⟨w, hw, ew⟩ := ih (vpush out (simJI (o.nested.val[k.val]'hlt)) hpl) k1 (by omega) (by omega)
      (by simp; omega)
    refine ⟨w, ?_, ?_⟩
    · unfold sim.scoring.push_simulated_loop; rw [loop_unfold]; dsimp only
      rw [show sim.scoring.push_simulated_loop.body o out k =
          ok (.cont (vpush out (simJI (o.nested.val[k.val]'hlt)) hpl, k1)) by
        simp [sim.scoring.push_simulated_loop.body, hlt', vec_index_usize_ok _ _ hlt, (sim.scoring.sim_jinfo_refines (fun _ => "") _).1,
          vec_push_ok _ _ hpl, hk1]]
      simp only [bind_ok]
      unfold sim.scoring.push_simulated_loop at hw; exact hw
    · rw [ew, vpush_val, ek1, List.drop_eq_getElem_cons hlt]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem sim.scoring.push_simulated_refines (out : alloc.vec.Vec sim.scoring.JInfo) (o : sim.playable.TopObj)
    (hc : out.val.length + o.nested.val.length + 1 < Usize.max) :
    ∃ w, sim.scoring.push_simulated out o = ok w ∧
      w.val = out.val ++ o.nested.val.map simJI ++ [simJI o.h] := by
  obtain ⟨w, hw, ew⟩ := sim_push_simulated_loop o _ out 0#usize rfl (by simp) (by simp; omega)
  have hpl : w.val.length < Usize.max := by rw [ew]; simp; omega
  refine ⟨vpush w (simJI o.h) hpl, ?_, by simp [ew]⟩
  simp [sim.scoring.push_simulated, hw, (sim.scoring.sim_jinfo_refines (fun _ => "") _).1, vec_push_ok _ _ hpl]

def simJIs (o : sim.playable.TopObj) : List sim.scoring.JInfo := o.nested.val.map simJI ++ [simJI o.h]

theorem sim_simulated_loop (pb : sim.playable.Playable) :
    ∀ n (out : alloc.vec.Vec sim.scoring.JInfo) (i : Usize), pb.objects.val.length - i.val = n →
      i.val ≤ pb.objects.val.length →
      out.val.length + ((pb.objects.val.drop i.val).map (fun o => o.nested.val.length + 1)).sum < Usize.max →
      ∃ w, sim.scoring.simulated_judgements_loop pb out i = ok w ∧
        w.val = out.val ++ (pb.objects.val.drop i.val).flatMap simJIs := by
  intro n
  induction n with
  | zero =>
    intro out i hn hi hc
    have hdn : pb.objects.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨out, ?_, by simp [hdn]⟩
    unfold sim.scoring.simulated_judgements_loop; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.objects) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.simulated_judgements_loop.body, this]
  | succ n ih =>
    intro out i hn hi hc
    have hlt : i.val < pb.objects.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    have hks : i.val + 1 ≤ Usize.max := by have := pb.objects.property; omega
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i hks
    have hd := List.drop_eq_getElem_cons hlt
    rw [hd] at hc
    simp only [List.map_cons, List.sum_cons] at hc
    obtain ⟨w1, hw1, ew1⟩ := sim.scoring.push_simulated_refines out (pb.objects.val[i.val]'hlt) (by omega)
    obtain ⟨w, hw, ew⟩ := ih w1 i1 (by omega) (by omega) (by rw [ew1, ei1]; simp only [List.length_append, List.length_map, List.length_singleton]; omega)
    refine ⟨w, ?_, ?_⟩
    · unfold sim.scoring.simulated_judgements_loop; rw [loop_unfold]; dsimp only
      rw [show sim.scoring.simulated_judgements_loop.body pb out i = ok (.cont (w1, i1)) by
        simp [sim.scoring.simulated_judgements_loop.body, hlt', vec_index_usize_ok _ _ hlt, hw1, hi1]]
      simp only [bind_ok]
      unfold sim.scoring.simulated_judgements_loop at hw; exact hw
    · rw [ew, ew1, ei1, hd]; simp only [List.flatMap_cons, simJIs, List.append_assoc, List.singleton_append, List.cons_append]

theorem sim.scoring.simulated_judgements_refines (tn) (pb : sim.playable.Playable)
    (hcap : (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < Usize.max) :
    ∃ w, sim.scoring.simulated_judgements pb = ok w ∧
      OsuModel.Sim.simulatedJudgements (playableS tn pb) = abs w := by
  obtain ⟨w, hw, ew⟩ := sim_simulated_loop pb _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simpa using hcap)
  refine ⟨w, hw, ?_⟩
  rw [sim_simulatedJudgements_eq]
  simp only [abs, ew, playableS, alloc.vec.Vec.new]
  simp [List.map_flatMap, List.flatMap_map, simJIs, topS, Function.comp_def]
  rfl

/-- `updateScore`'s `TotalScoreWithoutMods` reads only the combo / accuracy-count maxima of `ScoreMax` -/
theorem sim_updScore_wm (s : OsuModel.Sim.ScoreSt) (m m' : OsuModel.Sim.ScoreMax)
    (h2 : m.maximumComboPortion = m'.maximumComboPortion)
    (h3 : m.maximumAccuracyJudgementCount = m'.maximumAccuracyJudgementCount) :
    (s.updateScore m).totalScoreWithoutMods = (s.updateScore m').totalScoreWithoutMods := by
  simp only [OsuModel.Sim.ScoreSt.updateScore, h2, h3]

theorem sim_apply_sim_indep (s : OsuModel.Sim.ScoreSt) (m m' : OsuModel.Sim.ScoreMax) (j : OsuModel.Sim.JInfo) :
    s.apply m j false true = s.apply m' j false true := by
  simp [OsuModel.Sim.ScoreSt.apply]

/-- counters grow by at most one per applied judgement -/
theorem sim_apply_bounds (s : OsuModel.Sim.ScoreSt) (m : OsuModel.Sim.ScoreMax) (j : OsuModel.Sim.JInfo) (B : Nat)
    (hj : s.judgedHits ≤ B) (hc : s.combo ≤ B) (hn : s.currentAccuracyJudgementCount ≤ B)
    (hs : ∀ i (h : i < s.stats.size), s.stats[i] ≤ B) :
    (s.apply m j false true).1.judgedHits ≤ B + 1 ∧ (s.apply m j false true).1.combo ≤ B + 1 ∧
      (s.apply m j false true).1.currentAccuracyJudgementCount ≤ B + 1 ∧
      ∀ i (h : i < (s.apply m j false true).1.stats.size), (s.apply m j false true).1.stats[i] ≤ B + 1 := by
  unfold OsuModel.Sim.ScoreSt.apply
  simp only [Bool.false_eq_true, if_false, if_true]
  simp only [apply_ite OsuModel.Sim.ScoreSt.judgedHits, apply_ite OsuModel.Sim.ScoreSt.combo,
    apply_ite OsuModel.Sim.ScoreSt.currentAccuracyJudgementCount, apply_ite OsuModel.Sim.ScoreSt.stats]
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_ifs <;> (try simp) <;> omega
  · split_ifs <;> (try simp) <;> omega
  · split_ifs <;> (try simp) <;> omega
  · intro i hi
    have hsz : s.stats.size = OsuModel.Sim.nStats := s.stats_size
    split_ifs at hi ⊢ <;> simp only [Array.getElem_modify] at hi ⊢ <;> split_ifs <;>
      first | (have := hs i (by simpa using hi); omega) | (have := hs _ (by simpa using hi); omega)

theorem sim_statsS_get (a : Std.Array U64 18#usize) (k : Nat) (hk : k < 18) :
    (a.val.getD k 0#u64).val = (statsS a)[if k = 17 then 99 else k]! := by
  have hsz : (statsS a).size = 100 := by simp [statsS]
  by_cases h : k = 17
  · subst h; simp [statsS]
  · have : k < 100 := by omega
    simp only [h, if_false]
    rw [getElem!_pos (statsS a) k (by rw [hsz]; omega)]
    simp [statsS, h, show k ≠ 99 by omega, show k < 17 by omega]

theorem sim_u64_max_ge : Usize.max ≤ U64.max := by
  rw [Usize.max_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]
  have : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)
  rw [this]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

def simScoreInit : sim.scoring.ScoreSt :=
  ⟨0#u64, 0#u64, Std.Array.repeat 18#usize 0#u64, 0, 0, 0#u64, 0, 0, 1, 0#i64, 0#i64, 0#u64, none, false, 1, .X⟩

theorem sim_score_init : sim.scoring.SCORE_ST_INIT = ok simScoreInit := by
  simp [sim.scoring.SCORE_ST_INIT, simScoreInit]

theorem sim_score_init_abs : (abs simScoreInit : OsuModel.Sim.ScoreSt) = {} := by
  have hst : statsS (Std.Array.repeat 18#usize 0#u64) = Array.replicate OsuModel.Sim.nStats 0 := by
    apply Array.ext
    · simp [statsS, OsuModel.Sim.nStats]
    · intro i h1 h2
      simp [statsS, Std.Array.repeat, List.getD_eq_getElem?_getD]
      intro _ h3
      show ((List.replicate 18 0#u64)[i]?.getD 0#u64).val = 0
      rw [List.getElem?_replicate, if_pos (by omega)]; rfl
  simp only [abs, scoreS, simScoreInit, hst]
  rfl

def simBnd (S : OsuModel.Sim.ScoreSt) (B : Nat) : Prop :=
  S.judgedHits ≤ B ∧ S.combo ≤ B ∧ S.currentAccuracyJudgementCount ≤ B ∧ ∀ i (h : i < S.stats.size), S.stats[i] ≤ B

theorem sim_score_maxima_loop (f : F64) (a : Std.Array U64 18#usize) (mult : F64) (ra : Bool)
    (js : alloc.vec.Vec sim.scoring.JInfo) (M : OsuModel.Sim.ScoreMax) :
    ∀ n (s : sim.scoring.ScoreSt) (i : Usize), js.val.length - i.val = n → i.val ≤ js.val.length →
      simBnd (abs s) i.val →
      ∃ r, sim.scoring.score_maxima_loop f f a mult ra js s i = ok r ∧
        (abs r : OsuModel.Sim.ScoreSt) = (js.val.drop i.val).foldl
          (fun S j => (S.apply M (abs j) false true).1) (abs s) := by
  intro n
  induction n with
  | zero =>
    intro s i hn hi hb
    have hdn : js.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨s, ?_, by simp [hdn]⟩
    unfold sim.scoring.score_maxima_loop; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len js) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.score_maxima_loop.body, this]
  | succ n ih =>
    intro s i hn hi hb
    have hlt : i.val < js.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len js := by rw [vec_lt_len_iff]; exact hlt
    have hjl := js.property
    have hks : i.val + 1 ≤ Usize.max := by omega
    have hmax := sim_u64_max_ge
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i hks
    obtain ⟨hbj, hbc, hbn, hbs⟩ := hb
    have hj : s.judged_hits.val + 1 ≤ U64.max := by
      have : s.judged_hits.val = (abs s : OsuModel.Sim.ScoreSt).judgedHits := rfl
      omega
    have hc : s.combo.val + 1 ≤ U64.max := by
      have : s.combo.val = (abs s : OsuModel.Sim.ScoreSt).combo := rfl
      omega
    have hnn : s.current_accuracy_judgement_count.val + 1 ≤ U64.max := by
      have : s.current_accuracy_judgement_count.val = (abs s : OsuModel.Sim.ScoreSt).currentAccuracyJudgementCount := rfl
      omega
    have hst : ∀ k, k < 18 → (s.stats.val.getD k 0#u64).val + 1 ≤ U64.max := by
      intro k hk
      rw [sim_statsS_get _ k hk]
      have hsz : (statsS s.stats).size = 100 := by simp [statsS]
      have hk' : (if k = 17 then 99 else k) < (statsS s.stats).size := by rw [hsz]; split <;> omega
      rw [getElem!_pos (statsS s.stats) _ hk']
      have := hbs _ hk'
      have e : (abs s : OsuModel.Sim.ScoreSt).stats = statsS s.stats := rfl
      simp only [e] at this
      omega
    let m0R : sim.scoring.ScoreMax := ⟨f, f, 0#u64, a, 0#u64, mult, ra, 0#i64⟩
    obtain ⟨r, hr, er⟩ := sim.scoring.score_apply_refines s m0R (js.val[i.val]'hlt) false true hj hst hc hnn
    have er1 : (abs r.1 : OsuModel.Sim.ScoreSt) = ((abs s : OsuModel.Sim.ScoreSt).apply M (abs (js.val[i.val]'hlt)) false true).1 := by
      rw [sim_apply_sim_indep _ M (abs m0R), er]
    have hb' := sim_apply_bounds (abs s) M (abs (js.val[i.val]'hlt)) i.val hbj hbc hbn hbs
    obtain ⟨w, hw, ew⟩ := ih r.1 i1 (by omega) (by omega) (by rw [er1, ei1]; exact hb')
    refine ⟨w, ?_, ?_⟩
    · unfold sim.scoring.score_maxima_loop; rw [loop_unfold]; dsimp only
      rw [show sim.scoring.score_maxima_loop.body f f a mult ra js s i = ok (.cont (r.1, i1)) by
        simp [sim.scoring.score_maxima_loop.body, hlt', vec_index_usize_ok _ _ hlt, hi1]
        rw [hr]; cases r; simp]
      simp only [bind_ok]
      unfold sim.scoring.score_maxima_loop at hw; exact hw
    · rw [ew, er1, ei1, List.drop_eq_getElem_cons hlt, List.foldl_cons]

/-- `scoreMaxima` with the config's `rankAdjust` (as `mkCtx` sets it). `hcap`: the simulated judgements fit a `Vec`. -/
theorem sim.scoring.score_maxima_refines (tn) (pb : sim.playable.Playable) (mult : F64) (ra : Bool)
    (hcap : (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < Usize.max) :
    ∃ r, sim.scoring.score_maxima pb mult ra = ok r ∧
      { OsuModel.Sim.scoreMaxima (playableS tn pb) mult with rankAdjust := ra } = abs r := by
  obtain ⟨js, hjs, ejs⟩ := sim.scoring.simulated_judgements_refines tn pb hcap
  have hb0 : simBnd (abs simScoreInit) (0#usize : Usize).val := by
    rw [sim_score_init_abs]
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro i h; simp
  obtain ⟨s1, hs1, es1⟩ := sim_score_maxima_loop 0 (Std.Array.repeat 18#usize 0#u64) mult ra js
    { scoreMultiplier := mult } _ simScoreInit 0#usize rfl (by simp) hb0
  obtain ⟨ss, hss, ess⟩ := sim.scoring.update_score_refines s1
    ⟨0, 0, 0#u64, Std.Array.repeat 18#usize 0#u64, 0#u64, mult, ra, 0#i64⟩
  refine ⟨⟨s1.current_base_score, s1.current_combo_portion, s1.current_accuracy_judgement_count, s1.stats,
    s1.judged_hits, mult, ra, ss.total_score_without_mods⟩, ?_, ?_⟩
  · simp only [sim.scoring.score_maxima, sim_scoring_F64_0, hjs, sim_score_init, bind_ok]
    rw [hs1]; simp only [bind_ok]
    rw [hss]; simp only [bind_ok]
  · unfold OsuModel.Sim.scoreMaxima
    simp only [Id.run, Array.forIn_pure_yield_eq_foldl, ejs]
    rw [sim_score_init_abs] at es1
    simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at es1
    have : (abs js : _root_.Array OsuModel.Sim.JInfo).foldl
        (fun S j => (S.apply { scoreMultiplier := mult } j false true).1) {} =
        (abs s1 : OsuModel.Sim.ScoreSt) := by
      rw [es1]; simp [abs, Array.foldl_toList, List.foldl_map]
    simp only [this, pure_bind]
    have hw : ((abs s1 : OsuModel.Sim.ScoreSt).updateScore { scoreMultiplier := mult }).totalScoreWithoutMods =
        ss.total_score_without_mods.val := by
      have h := congrArg OsuModel.Sim.ScoreSt.totalScoreWithoutMods ess
      rw [sim_updScore_wm (abs s1) ({ scoreMultiplier := mult } : OsuModel.Sim.ScoreMax) (abs (⟨0, 0, 0#u64, Std.Array.repeat 18#usize 0#u64, 0#u64, mult, ra, 0#i64⟩ :
        sim.scoring.ScoreMax)) (by simp [abs]) (by simp [abs]), h]
      simp [abs, scoreS]
    simp only [abs, scoreS] at hw ⊢
    rw [hw]
    rfl
end OsuProofs
