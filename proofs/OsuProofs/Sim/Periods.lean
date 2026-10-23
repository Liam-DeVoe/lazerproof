/-
`sim::scoring` health periods and drain (Rust) refine `OsuModel.Sim` Scoring: `period_is_in_any` (the
`PeriodTracker.IsInAny` scans with fuel `ps.size`; the Rust `while` loops reach the same index: `simFwd`/`simBwd`
with any sufficient fuel), `drain_clamp`, `drain` (`HealthSt.drain`; `Result<_, SimErr>` vs `Except String` by
`simRel`: `Ok` ↦ `.ok`, `Err` ↦ some `.error`).
-/
import OsuProofs.Sim.Maxima
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the forward scan of `PeriodTracker.IsInAny` with fuel -/
def simFwd (P : List (F64 × F64)) (time : F64) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if (P[i]?.map (·.2)).getD 0 < time ∧ i < P.length - 1 then simFwd P time f (i + 1) else i

/-- the backward scan -/
def simBwd (P : List (F64 × F64)) (time : F64) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if time < (P[i]?.map (·.1)).getD 0 ∧ i > 0 then simBwd P time f (i - 1) else i

theorem sim_fwd_fuel (P : List (F64 × F64)) (time : F64) :
    ∀ f g i, P.length - 1 - i ≤ f → P.length - 1 - i ≤ g → simFwd P time f i = simFwd P time g i := by
  intro f
  induction f with
  | zero =>
    intro g i hf hg
    cases g with
    | zero => rfl
    | succ g => simp only [simFwd]; split_ifs with h <;> [omega; rfl]
  | succ f ih =>
    intro g i hf hg
    cases g with
    | zero => simp only [simFwd]; split_ifs with h <;> [omega; rfl]
    | succ g =>
      simp only [simFwd]; split_ifs with h
      · exact ih g (i + 1) (by omega) (by omega)
      · rfl

theorem sim_bwd_fuel (P : List (F64 × F64)) (time : F64) :
    ∀ f g i, i ≤ f → i ≤ g → simBwd P time f i = simBwd P time g i := by
  intro f
  induction f with
  | zero =>
    intro g i hf hg
    cases g with
    | zero => rfl
    | succ g => simp only [simBwd]; split_ifs with h <;> [omega; rfl]
  | succ f ih =>
    intro g i hf hg
    cases g with
    | zero => simp only [simBwd]; split_ifs with h <;> [omega; rfl]
    | succ g =>
      simp only [simBwd]; split_ifs with h
      · exact ih g (i - 1) (by omega) (by omega)
      · rfl

theorem sim_fwd_lt (P : List (F64 × F64)) (time : F64) : ∀ f i, i < P.length → simFwd P time f i < P.length := by
  intro f; induction f with
  | zero => intro i h; exact h
  | succ f ih => intro i h; simp only [simFwd]; split_ifs with h1 <;> [exact ih _ (by omega); exact h]

theorem sim_bwd_lt (P : List (F64 × F64)) (time : F64) : ∀ f i, i < P.length → simBwd P time f i < P.length := by
  intro f; induction f with
  | zero => intro i h; exact h
  | succ f ih => intro i h; simp only [simBwd]; split_ifs with h1 <;> [exact ih _ (by omega); exact h]

def simPS (ps : Slice sim.playable.Period) : List (F64 × F64) := ps.val.map (fun p => (p.start, p.«end»))

theorem sim_simPS_get (ps : Slice sim.playable.Period) (i : Nat) (h : i < ps.val.length) :
    (simPS ps)[i]? = some ((ps.val[i]'h).start, (ps.val[i]'h).«end») := by
  simp [simPS, List.getElem?_eq_getElem h]

theorem sim_pia_loop0 (ps : Slice sim.playable.Period) (time : F64) :
    ∀ n (i : Usize), ps.val.length - i.val = n → i.val < ps.val.length →
      ∃ j, sim.scoring.period_is_in_any_loop0 ps time i = ok j ∧ j.val = simFwd (simPS ps) time n i.val := by
  intro n
  induction n with
  | zero => intro i hn hi; omega
  | succ n ih =>
    intro i hn hi
    have hlen : (simPS ps).length = ps.val.length := by simp [simPS]
    have hsl : (Slice.len ps).val = ps.val.length := by simp
    obtain ⟨l1, hl1, el1⟩ : ∃ z, Slice.len ps - 1#usize = ok z ∧ z.val = ps.val.length - 1 := by
      obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := Slice.len ps) (y := 1#usize) (by simp; omega))
      exact ⟨z, hz, by simp at hv; omega⟩
    unfold sim.scoring.period_is_in_any_loop0; rw [loop_unfold]
    by_cases hc : (ps.val[i.val]'hi).«end» < time ∧ i.val < ps.val.length - 1
    · have hks : i.val + 1 ≤ Usize.max := by have := ps.property; omega
      obtain ⟨i1, hi1, ei1⟩ := usize_add_one i hks
      obtain ⟨j, hj, ej⟩ := ih i1 (by omega) (by omega)
      have hlt2' : i.val < l1.val := by rw [el1]; exact hc.2
      have hlt2 : i < l1 := hlt2'
      rw [show sim.scoring.period_is_in_any_loop0.body ps time i = ok (.cont i1) by
        simp [sim.scoring.period_is_in_any_loop0.body, slice_index_ok ps i hi, float.F64.lt, hc.1, hl1, hlt2, hlt2', hi1]]
      simp only [bind_ok]
      unfold sim.scoring.period_is_in_any_loop0 at hj
      refine ⟨j, hj, ?_⟩
      rw [ej, ei1]; simp only [simFwd, sim_simPS_get ps _ hi, Option.map_some, Option.getD_some, hlen]
      rw [if_pos hc]
    · refine ⟨i, ?_, ?_⟩
      · rw [show sim.scoring.period_is_in_any_loop0.body ps time i = ok (.done i) by
          by_cases h1 : (ps.val[i.val]'hi).«end» < time
          · have h2 : ¬ i < l1 := by
              have : ¬ i.val < ps.val.length - 1 := fun h => hc ⟨h1, h⟩
              intro hh; exact this (by have : i.val < l1.val := hh; omega)
            have h2' : ¬ i.val < l1.val := h2
            simp [sim.scoring.period_is_in_any_loop0.body, slice_index_ok ps i hi, float.F64.lt, h1, hl1, h2, h2']
          · simp [sim.scoring.period_is_in_any_loop0.body, slice_index_ok ps i hi, float.F64.lt, h1]]
        simp only [bind_ok]
      · simp only [simFwd, sim_simPS_get ps _ hi, Option.map_some, Option.getD_some, hlen]
        rw [if_neg hc]

theorem sim_pia_loop1 (ps : Slice sim.playable.Period) (time : F64) :
    ∀ (i : Usize), i.val < ps.val.length →
      ∃ j, sim.scoring.period_is_in_any_loop1 ps time i = ok j ∧ j.val = simBwd (simPS ps) time (i.val + 1) i.val := by
  intro i
  induction h : i.val generalizing i with
  | zero =>
    intro hi
    refine ⟨i, ?_, ?_⟩
    · unfold sim.scoring.period_is_in_any_loop1; rw [loop_unfold]
      have h0 : ¬ i > 0#usize := by scalar_tac
      rw [show sim.scoring.period_is_in_any_loop1.body ps time i = ok (.done i) by
        simp [sim.scoring.period_is_in_any_loop1.body, slice_index_ok ps i (by omega), float.F64.lt, h0]]
      simp only [bind_ok]
    · simp [simBwd, h]
  | succ k ih =>
    intro hi
    have hpos : i > 0#usize := by scalar_tac
    obtain ⟨i1, hi1, ei1⟩ : ∃ z, i - 1#usize = ok z ∧ z.val = i.val - 1 := by
      obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
      exact ⟨z, hz, by simp at hv; omega⟩
    have hlen : (simPS ps).length = ps.val.length := by simp [simPS]
    unfold sim.scoring.period_is_in_any_loop1; rw [loop_unfold]
    by_cases hc : time < (ps.val[i.val]'(by omega)).start
    · obtain ⟨j, hj, ej⟩ := ih i1 (by omega) (by omega)
      rw [show sim.scoring.period_is_in_any_loop1.body ps time i = ok (.cont i1) by
        simp [sim.scoring.period_is_in_any_loop1.body, slice_index_ok ps i (by omega), float.F64.lt, hc, hpos, hi1]]
      simp only [bind_ok]
      unfold sim.scoring.period_is_in_any_loop1 at hj
      refine ⟨j, hj, ?_⟩
      have hk : i1.val = k := by omega
      rw [ej]
      conv_rhs => unfold simBwd
      rw [sim_simPS_get ps _ (show k + 1 < ps.val.length by omega)]
      simp only [Option.map_some, Option.getD_some]
      have : (ps.val[k + 1]'(by omega)).start = (ps.val[i.val]'(by omega)).start := by congr 1; simp [h]
      rw [this, if_pos ⟨hc, by omega⟩]; simp
    · refine ⟨i, ?_, ?_⟩
      · rw [show sim.scoring.period_is_in_any_loop1.body ps time i = ok (.done i) by
          simp [sim.scoring.period_is_in_any_loop1.body, slice_index_ok ps i (by omega), float.F64.lt, hc]]
        simp only [bind_ok]
      · rw [h]
        simp only [simBwd, sim_simPS_get ps _ (show k + 1 < ps.val.length by omega), Option.map_some, Option.getD_some]
        have : (ps.val[k + 1]'(by omega)).start = (ps.val[i.val]'(by omega)).start := by congr 1; simp [h]
        rw [this, if_neg (fun hh => hc hh.1)]

def simScan (g : Nat → ForInStep Nat) : Nat → Nat → Nat
  | 0, i => i
  | k + 1, i => match g i with | .done c => c | .yield c => simScan g k c

theorem sim_exc_forIn_scan {ε} (g : Nat → ForInStep Nat) (inv : Nat → Prop)
    (hinv : ∀ i c, inv i → g i = .yield c → inv c) :
    ∀ (l : List Nat) (F : Nat → Nat → Except ε (ForInStep Nat)), (∀ j i, inv i → F j i = .ok (g i)) →
      ∀ i, inv i → forIn l i F = .ok (simScan g l.length i) := by
  intro l F hF
  induction l with
  | nil => intro i _; rfl
  | cons j t ih =>
    intro i hi
    rw [List.forIn_cons, hF j i hi]
    simp only [List.length_cons, simScan]
    cases hg : g i with
    | done c => rfl
    | yield c => exact ih c (hinv i c hi hg)

def simGF (P : List (F64 × F64)) (time : F64) (i : Nat) : ForInStep Nat :=
  if (decide ((P[i]?.map (·.2)).getD 0 < time) && decide (i < P.length - 1)) = true then .yield (i + 1) else .done i
def simGB (P : List (F64 × F64)) (time : F64) (i : Nat) : ForInStep Nat :=
  if (decide (time < (P[i]?.map (·.1)).getD 0) && decide (i > 0)) = true then .yield (i - 1) else .done i

theorem sim_scan_fwd (P : List (F64 × F64)) (time : F64) : ∀ n i, simScan (simGF P time) n i = simFwd P time n i := by
  intro n; induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i; simp only [simScan, simFwd, simGF]
    by_cases h : (P[i]?.map (·.2)).getD 0 < time ∧ i < P.length - 1
    · simp [h.1, h.2, ih]
    · rw [if_neg h]
      by_cases h1 : (P[i]?.map (·.2)).getD 0 < time
      · have h2 : ¬ i < P.length - 1 := fun h2 => h ⟨h1, h2⟩
        simp [h1, h2]
      · simp [h1]

theorem sim_scan_bwd (P : List (F64 × F64)) (time : F64) : ∀ n i, simScan (simGB P time) n i = simBwd P time n i := by
  intro n; induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i; simp only [simScan, simBwd, simGB]
    by_cases h : time < (P[i]?.map (·.1)).getD 0 ∧ i > 0
    · simp [h.1, h.2, ih]
    · rw [if_neg h]
      by_cases h1 : time < (P[i]?.map (·.1)).getD 0
      · have h2 : ¬ i > 0 := fun h2 => h ⟨h1, h2⟩
        simp [h1, h2]
      · simp [h1]

theorem simS_periodIsInAny (P : List (F64 × F64)) (idx : Nat) (time : F64) (h : idx < P.length) :
    OsuModel.Sim.periodIsInAny P.toArray idx time =
      let i := if (P[idx]'h).2 < time then simFwd P time P.length idx else simBwd P time P.length idx
      .ok ((decide (((P[i]?.map (·.1)).getD 0) ≤ time) && decide (time ≤ (P[i]?.map (·.2)).getD 0)), i) := by
  have hne : P.toArray.size ≠ 0 := by simp only [List.size_toArray]; omega
  unfold OsuModel.Sim.periodIsInAny
  simp only [hne, beq_iff_eq, if_false, List.getElem?_toArray, List.getElem?_eq_getElem h, List.size_toArray]
  simp only [bind_pure_comp, pure_bind, Std.Legacy.Range.forIn_eq_forIn_range']
  have hl0 : ¬ P.length = 0 := by omega
  have hrs : [:P.length].size = P.length := by simp [Std.Legacy.Range.size]
  rw [if_neg hl0, hrs]
  by_cases hc : (P[idx]'h).2 < time
  · rw [if_pos hc]
    rw [sim_exc_forIn_scan (simGF P time) (· < P.length) ?inv (List.range' 0 P.length) _ ?hF idx h]
    case inv =>
      intro i c hi hg
      unfold simGF at hg
      split at hg
      · rename_i hh; simp at hh; cases hg; omega
      · cases hg
    case hF =>
      intro j i hi
      simp only [List.getElem?_eq_getElem hi, simGF, Option.map_some, Option.getD_some, pure_bind]
      split_ifs <;> rfl
    rw [List.length_range', sim_scan_fwd]
    have hl := sim_fwd_lt P time P.length idx h
    simp [List.getElem?_eq_getElem hl, hc]
  · rw [if_neg hc]
    rw [sim_exc_forIn_scan (simGB P time) (· < P.length) ?inv2 (List.range' 0 P.length) _ ?hF2 idx h]
    case inv2 =>
      intro i c hi hg
      unfold simGB at hg
      split at hg
      · cases hg; omega
      · cases hg
    case hF2 =>
      intro j i hi
      simp only [List.getElem?_eq_getElem hi, simGB, Option.map_some, Option.getD_some, pure_bind]
      split_ifs <;> rfl
    rw [List.length_range', sim_scan_bwd]
    have hl := sim_bwd_lt P time P.length idx h
    simp [List.getElem?_eq_getElem hl, hc]

theorem sim.scoring.period_is_in_any_refines (ps : Slice sim.playable.Period) (idx : Usize) (time : F64)
    (hidx : ps.val.length ≠ 0 → idx.val < ps.val.length) :
    ∃ r, sim.scoring.period_is_in_any ps idx time = ok r ∧
      OsuModel.Sim.periodIsInAny (simPS ps).toArray idx.val time = .ok (r.1, r.2.val) := by
  have hlen : (simPS ps).length = ps.val.length := by simp [simPS]
  by_cases h0 : ps.val.length = 0
  · have h0' : Slice.len ps = 0#usize := by scalar_tac
    refine ⟨(false, idx), by simp [sim.scoring.period_is_in_any, h0'], ?_⟩
    have : (simPS ps).toArray.size = 0 := by simp [hlen, h0]
    unfold OsuModel.Sim.periodIsInAny; simp [this]
  · have hi := hidx h0
    have h0' : ¬ Slice.len ps = 0#usize := fun e => h0 (by simpa using congrArg UScalar.val e)
    have hi' : idx.val < (simPS ps).length := by rw [hlen]; exact hi
    rw [simS_periodIsInAny (simPS ps) idx.val time hi']
    have hget : ∀ k (hk : k < ps.val.length), ((simPS ps)[k]?.map (·.1)).getD 0 = (ps.val[k]'hk).start ∧
        ((simPS ps)[k]?.map (·.2)).getD 0 = (ps.val[k]'hk).«end» := by
      intro k hk; simp [sim_simPS_get ps k hk]
    have hpi : ((simPS ps)[idx.val]'hi').2 = (ps.val[idx.val]'hi).«end» := by simp [simPS]
    by_cases hc : (ps.val[idx.val]'hi).«end» < time
    · obtain ⟨j, hj, ej⟩ := sim_pia_loop0 ps time _ idx rfl hi
      have ej' : j.val = simFwd (simPS ps) time (simPS ps).length idx.val := by
        rw [ej]; exact sim_fwd_fuel _ _ _ _ _ (by rw [hlen]; omega) (by rw [hlen]; omega)
      have hjl : j.val < ps.val.length := by
        rw [ej', ← hlen]; exact sim_fwd_lt _ _ _ _ hi'
      obtain ⟨g1, g2⟩ := hget j.val hjl
      refine ⟨(decide ((ps.val[j.val]'hjl).start ≤ time) && decide (time ≤ (ps.val[j.val]'hjl).«end»), j), ?_, ?_⟩
      · simp only [sim.scoring.period_is_in_any, h0', if_false, slice_index_ok ps idx hi, float.F64.lt, bind_ok, hc,
          decide_true, if_true, hj, slice_index_ok ps j hjl, float.F64.le]
        by_cases h1 : (ps.val[j.val]'hjl).start ≤ time <;> simp [h1]
      · simp only [hpi, hc, if_true, ← ej', g1, g2]
    · obtain ⟨j, hj, ej⟩ := sim_pia_loop1 ps time idx hi
      have ej' : j.val = simBwd (simPS ps) time (simPS ps).length idx.val := by
        rw [ej]; exact sim_bwd_fuel _ _ _ _ _ (by omega) (by rw [hlen]; omega)
      have hjl : j.val < ps.val.length := by
        rw [ej', ← hlen]; exact sim_bwd_lt _ _ _ _ hi'
      obtain ⟨g1, g2⟩ := hget j.val hjl
      refine ⟨(decide ((ps.val[j.val]'hjl).start ≤ time) && decide (time ≤ (ps.val[j.val]'hjl).«end»), j), ?_, ?_⟩
      · simp only [sim.scoring.period_is_in_any, h0', if_false, slice_index_ok ps idx hi, float.F64.lt, bind_ok, hc,
          decide_false, Bool.false_eq_true, hj, slice_index_ok ps j hjl, float.F64.le]
        by_cases h1 : (ps.val[j.val]'hjl).start ≤ time <;> simp [h1]
      · simp only [hpi, hc, if_false, ← ej', g1, g2]

/-- Rust `Result<α, SimErr>` vs a spec `Except String β`: `Ok v` ↦ `.ok (f v)`, `Err _` ↦ some `.error`. -/
def simRel {α β : Type} (f : α → β) : core.result.Result α sim.err.SimErr → Except String β → Prop
  | .Ok v, e => e = .ok (f v)
  | .Err _, e => ∃ m, e = .error m

theorem sim_mathops_f64_clamp (v lo hi : F64) :
    net.mathops.f64_clamp v lo hi = ok (exceptI id (F64.clamp v lo hi)) := by
  unfold net.mathops.f64_clamp F64.clamp
  by_cases h1 : hi < lo <;> by_cases h2 : v < lo <;> by_cases h3 : hi < v <;>
    simp [h1, h2, h3, exceptI, exnI]

theorem sim.scoring.drain_clamp_refines (x : F64) (c : sim.scoring.HealthCfg) :
    ∃ r, sim.scoring.drain_clamp x c = ok r ∧
      simRel id r (match F64.clamp x c.drain_start_time c.gameplay_end_time with
        | .ok v => pure v
        | .error e => throw s!"lazer would throw: Math.Clamp {repr e} (drain bounds)") := by
  unfold sim.scoring.drain_clamp
  rw [sim_mathops_f64_clamp]
  cases hc : F64.clamp x c.drain_start_time c.gameplay_end_time with
  | ok v => exact ⟨.Ok v, by simp [exceptI], rfl⟩
  | error e => exact ⟨.Err (.ClampDrain (exnI e)), by simp [exceptI], ⟨_, rfl⟩⟩

theorem sim.scoring.drain_refines (h : sim.scoring.HealthSt) (c : sim.scoring.HealthCfg) (t el : F64)
    (hidx : c.periods.val.length ≠ 0 → h.nearest_index.val < c.periods.val.length) :
    ∃ r h2, sim.scoring.drain h c t el = ok (r, h2) ∧
      simRel (fun _ => (abs h2 : OsuModel.Sim.HealthSt)) r
        ((abs h : OsuModel.Sim.HealthSt).drain (abs c) t el) := by
  obtain ⟨p, hp, ep⟩ := sim.scoring.period_is_in_any_refines (alloc.vec.Vec.deref c.periods) h.nearest_index t
    (by simpa [alloc.vec.Vec.deref] using hidx)
  have eps : (abs c : OsuModel.Sim.HealthCfg).periods = (simPS (alloc.vec.Vec.deref c.periods)).toArray := by
    simp [abs, simPS, alloc.vec.Vec.deref]
  unfold OsuModel.Sim.HealthSt.drain
  rw [eps]
  have ehn : (abs h : OsuModel.Sim.HealthSt).nearestIndex = h.nearest_index.val := rfl
  rw [ehn, ep]
  have ec1 : (abs c : OsuModel.Sim.HealthCfg).drainStartTime = c.drain_start_time := rfl
  have ec2 : (abs c : OsuModel.Sim.HealthCfg).gameplayEndTime = c.gameplay_end_time := rfl
  have ech : (abs h : OsuModel.Sim.HealthSt).health = h.health := rfl
  have ecr : (abs c : OsuModel.Sim.HealthCfg).drainRate = c.drain_rate := rfl
  obtain ⟨inAny, idx⟩ := p
  cases inAny
  · cases hc1 : F64.clamp (t - el) c.drain_start_time c.gameplay_end_time with
    | error e1 =>
      refine ⟨.Err (.ClampDrain (exnI e1)), { h with nearest_index := idx }, ?_, ?_⟩
      · simp [sim.scoring.drain, hp, sim.scoring.drain_clamp, sim_mathops_f64_clamp, hc1, exceptI,
          core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.From.from]
      · simp [simRel, Except.bind, ec1, ec2, hc1, throw, throwThe, MonadExceptOf.throw]
    | ok v1 =>
      cases hc2 : F64.clamp t c.drain_start_time c.gameplay_end_time with
      | error e2 =>
        refine ⟨.Err (.ClampDrain (exnI e2)), { h with nearest_index := idx }, ?_, ?_⟩
        · simp [sim.scoring.drain, hp, sim.scoring.drain_clamp, sim_mathops_f64_clamp, hc1, hc2, exceptI,
            core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, core.convert.From.from]
        · simp [simRel, Except.bind, ec1, ec2, hc1, hc2, throw, throwThe, MonadExceptOf.throw]
      | ok v2 =>
        obtain ⟨f4, hf4, ef4⟩ := sim.scoring.clamp01_refines (h.health - c.drain_rate * (v2 - v1))
        refine ⟨.Ok (), { h with health := f4, nearest_index := idx }, ?_, ?_⟩
        · simp [sim.scoring.drain, hp, sim.scoring.drain_clamp, sim_mathops_f64_clamp, hc1, hc2, exceptI,
            core.result.Result.Insts.CoreOpsTry.branch, float.F64.sub, float.F64.mul, hf4]
        · simp only [abs, id] at ef4
          simp [simRel, Except.bind, ec1, ec2, hc1, hc2, ech, ecr, ef4, pure, Except.pure]
          rfl
  · refine ⟨.Ok (), { h with nearest_index := idx }, by simp [sim.scoring.drain, hp], ?_⟩
    simp [simRel, Except.bind, pure, Except.pure]
    rfl

def simPP (p : sim.playable.Period) : F64 × F64 := (p.start, p.«end»)
def simPLt (a b : F64 × F64) : Bool := decide (a.1 < b.1)

theorem sim_ips_loop0 (out : alloc.vec.Vec sim.playable.Period) (p : sim.playable.Period) :
    ∀ (n : Nat) (i : Usize), i.val = n → i.val ≤ out.val.length →
      ∃ r, sim.scoring.insert_period_sorted_loop0 out p i = ok (p, r) ∧
        r.val = simInsPos simPLt (out.val.map simPP) (simPP p) n := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    refine ⟨i, ?_, by simp [hi, simInsPos]⟩
    unfold sim.scoring.insert_period_sorted_loop0; rw [loop_unfold]
    have : ¬ i > 0#usize := by scalar_tac
    simp [sim.scoring.insert_period_sorted_loop0.body, this]
  | succ n ih =>
    intro i hi hle
    have hpos : i > 0#usize := by scalar_tac
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = n := by rw [hi1v0]; simp; omega
    have hl1 : i1.val < out.val.length := by omega
    have hget : (out.val.map simPP)[n]? = some (simPP (out.val[i1.val]'hl1)) := by
      rw [← hi1v]; simp [List.getElem?_eq_getElem hl1]
    by_cases hlt : p.start < (out.val[i1.val]'hl1).start
    · obtain ⟨r, hr, hrv⟩ := ih i1 hi1v (by omega)
      refine ⟨r, ?_, by rw [hrv]; simp [simInsPos, hget, simPLt, simPP, hlt]⟩
      unfold sim.scoring.insert_period_sorted_loop0; rw [loop_unfold]
      unfold sim.scoring.insert_period_sorted_loop0 at hr
      rw [show sim.scoring.insert_period_sorted_loop0.body out p i = ok (.cont i1) by
        simp [sim.scoring.insert_period_sorted_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1, float.F64.lt, hlt]]
      simpa only [bind_ok] using hr
    · refine ⟨i, ?_, by simp [simInsPos, hget, simPLt, simPP, hlt, hi]⟩
      unfold sim.scoring.insert_period_sorted_loop0; rw [loop_unfold]
      rw [show sim.scoring.insert_period_sorted_loop0.body out p i = ok (.done (p, i)) by
        simp [sim.scoring.insert_period_sorted_loop0.body, hpos, hi1, vec_index_usize_ok _ _ hl1, float.F64.lt, hlt]]
      simp only [bind_ok]

theorem sim_ips_loop1 (v : List sim.playable.Period) (k : Usize) :
    ∀ (w : alloc.vec.Vec sim.playable.Period) (i : Usize), k.val ≤ i.val → i.val ≤ v.length →
      (∃ d, w.val = v.take i.val ++ d :: v.drop i.val) →
      ∃ w', sim.scoring.insert_period_sorted_loop1 w k i = ok w' ∧ ∃ d, w'.val = v.take k.val ++ d :: v.drop k.val := by
  intro w i hki hiv hw
  unfold sim.scoring.insert_period_sorted_loop1
  refine loop_ok _ (fun (x : alloc.vec.Vec sim.playable.Period × Usize) => x.2.val)
    (fun (x : alloc.vec.Vec sim.playable.Period × Usize) => k.val ≤ x.2.val ∧ x.2.val ≤ v.length ∧
      ∃ d, x.1.val = v.take x.2.val ++ d :: v.drop x.2.val)
    (fun (w' : alloc.vec.Vec sim.playable.Period) => ∃ d, w'.val = v.take k.val ++ d :: v.drop k.val) ?_ (w, i) ⟨hki, hiv, hw⟩
  rintro ⟨w, i⟩ ⟨hki, hiv, d, hw⟩
  dsimp only at hki hiv hw ⊢
  by_cases hik : k.val < i.val
  · right
    have hik' : i > k := hik
    obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hi1v : i1.val = i.val - 1 := by rw [hi1v0]; simp
    have hwl : w.val.length = v.length + 1 := by rw [hw]; simp; omega
    have hl1 : i1.val < w.val.length := by omega
    have hl2 : i.val < w.val.length := by omega
    have hget : w.val[i1.val]'hl1 = v[i.val - 1]'(by omega) := by
      simp only [hw, hi1v]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    refine ⟨(alloc.vec.Vec.set w i (v[i.val - 1]'(by omega)), i1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩,
      by dsimp only; omega⟩
    · simp [sim.scoring.insert_period_sorted_loop1.body, hik', hi1, vec_index_eq w i1 hl1, vec_index_usize_ok w i1 hl1, hget,
        vec_index_mut_eq w i hl2]
    · refine ⟨v[i.val - 1]'(by omega), ?_⟩
      dsimp only
      rw [alloc.vec.Vec.set_val_eq, hw, hi1v]
      have e1 : v.take i.val = v.take (i.val - 1) ++ [v[i.val - 1]'(by omega)] := by
        have e : i.val = (i.val - 1) + 1 := by omega
        conv_lhs => rw [e]
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
      have e2 : v.drop (i.val - 1) = v[i.val - 1]'(by omega) :: v.drop i.val := by
        rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
      rw [e2, e1]; simp only [List.append_assoc, List.singleton_append]
      rw [List.set_append_right _ _ (by simp)]
      have hl : (v.take (i.val - 1)).length = i.val - 1 := by simp; try omega
      rw [hl]
      have h1 : i.val - (i.val - 1) = 1 := by omega
      rw [h1]; rfl
  · left
    have hik' : ¬ i > k := hik
    refine ⟨w, by simp [sim.scoring.insert_period_sorted_loop1.body, hik'], ⟨d, ?_⟩⟩
    have : i.val = k.val := by omega
    rw [← this]; exact hw

theorem sim.scoring.insert_period_sorted_refines (out : alloc.vec.Vec sim.playable.Period) (p : sim.playable.Period)
    (hl : out.val.length < Usize.max) :
    ∃ w, sim.scoring.insert_period_sorted out p = ok w ∧
      w.val.map simPP = (out.val.map simPP).insertIdx
        (simInsPos simPLt (out.val.map simPP) (simPP p) (out.val.map simPP).length) (simPP p) := by
  obtain ⟨r, hr, hrv⟩ := sim_ips_loop0 out p out.val.length (alloc.vec.Vec.len out) (by simp) (by simp)
  have hrl : r.val ≤ out.val.length := by
    rw [hrv]; have := sim_simInsPos_le simPLt (out.val.map simPP) (simPP p) out.val.length; simpa using this
  obtain ⟨v1, hv1, hv1v⟩ := push_eq out p hl
  have hlen : (alloc.vec.Vec.len v1).val = out.val.length + 1 := by simp [hv1v]
  obtain ⟨i1, hi1, hi1v0, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len v1) (y := 1#usize) (by simp [hlen]))
  have hi1v : i1.val = out.val.length := by rw [hi1v0]; simp [hlen]
  obtain ⟨w2, hw2, d, hw2v⟩ := sim_ips_loop1 out.val r v1 i1 (by omega) (by omega) ⟨p, by rw [hv1v, hi1v]; simp⟩
  have hw2l : r.val < w2.val.length := by rw [hw2v]; simp; omega
  refine ⟨alloc.vec.Vec.set w2 r p, ?_, ?_⟩
  · have hm : alloc.vec.Vec.index_mut_usize w2 r = ok (w2.val[r.val]'hw2l, alloc.vec.Vec.set w2 r) := by
      rw [← alloc.vec.Vec.index_mut_slice_index]; exact vec_index_mut_eq w2 r hw2l
    simp [sim.scoring.insert_period_sorted, hr, hv1, hi1, hw2, hm]
  · rw [alloc.vec.Vec.set_val_eq, hw2v, List.length_map, ← hrv]
    rw [List.set_append_right _ _ (by simp; try omega)]
    have hl2 : (out.val.take r.val).length = r.val := by simp; omega
    rw [hl2, Nat.sub_self]
    simp only [List.set_cons_zero, List.map_append, List.map_cons]
    rw [insertIdx_take_drop _ _ _ (by simp; omega)]
    simp [List.map_take, List.map_drop]
end OsuProofs
