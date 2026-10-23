/-
`sim::scoring` drain rate (Rust) refines `OsuModel.Sim.computeDrainRate`
(`DrainingHealthProcessor.ComputeDrainRate`): models `simBrk` (break scan with fuel), `simPass` (one pass:
current/lowest health, current break), `simCDRStep`/`simCDRrun` (the outer `while` with fuel), `simCDRfin`
(fuel-exhausted check); `drain_pass`, `compute_drain_rate`.
-/
import OsuProofs.Sim.InitCtx
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the break scan of `computeDrainRate` with fuel -/
def simBrk (B : List (F64 × F64)) (t : F64) : Nat → Nat × F64 → Nat × F64
  | 0, s => s
  | f + 1, (cb, lt) => match B[cb]? with
    | some b => if b.2 ≤ t then simBrk B t f (cb + 1, t) else (cb, lt)
    | none => (cb, lt)

theorem sim_brk_fuel (B : List (F64 × F64)) (t : F64) :
    ∀ f g cb lt, B.length - cb ≤ f → B.length - cb ≤ g → simBrk B t f (cb, lt) = simBrk B t g (cb, lt) := by
  intro f
  induction f with
  | zero =>
    intro g cb lt hf hg
    cases g with
    | zero => rfl
    | succ g =>
      have : B[cb]? = none := List.getElem?_eq_none (by omega)
      simp [simBrk, this]
  | succ f ih =>
    intro g cb lt hf hg
    cases g with
    | zero =>
      have : B[cb]? = none := List.getElem?_eq_none (by omega)
      simp [simBrk, this]
    | succ g =>
      simp only [simBrk]
      cases hb : B[cb]? with
      | none => rfl
      | some b =>
        have hcb : cb < B.length := by
          by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
        dsimp only; split_ifs
        · exact ih g (cb + 1) t (by omega) (by omega)
        · rfl

theorem sim_brk_le (B : List (F64 × F64)) (t : F64) : ∀ f cb lt, cb ≤ B.length → (simBrk B t f (cb, lt)).1 ≤ B.length := by
  intro f; induction f with
  | zero => intro cb lt h; exact h
  | succ f ih =>
    intro cb lt h; simp only [simBrk]
    cases hb : B[cb]? with
    | none => exact h
    | some b =>
      have hcb : cb < B.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
      dsimp only; split_ifs
      · exact ih _ _ (by omega)
      · exact h

theorem sim_dp_brk_loop (breaks : Slice sim.playable.Period) (t : F64) :
    ∀ n (cb : Usize) (lt : F64), breaks.val.length - cb.val = n → cb.val ≤ breaks.val.length →
      ∃ cb', sim.scoring.drain_pass_loop0_loop0 breaks cb t lt = ok (cb', (simBrk (simPS breaks) t n (cb.val, lt)).2) ∧
        cb'.val = (simBrk (simPS breaks) t n (cb.val, lt)).1 := by
  have hlen : (simPS breaks).length = breaks.val.length := by simp [simPS]
  intro n
  induction n with
  | zero =>
    intro cb lt hn hc
    refine ⟨cb, ?_, rfl⟩
    unfold sim.scoring.drain_pass_loop0_loop0; rw [loop_unfold]
    have : ¬ (cb < Slice.len breaks) := by rw [slice_lt_len_iff]; omega
    simp [sim.scoring.drain_pass_loop0_loop0.body, this, simBrk]
  | succ n ih =>
    intro cb lt hn hc
    have hlt : cb.val < breaks.val.length := by omega
    have hlt' : cb < Slice.len breaks := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨cb1, hcb1, ecb1⟩ := usize_add_one cb (by have := breaks.property; omega)
    have hg := sim_simPS_get breaks cb.val hlt
    unfold sim.scoring.drain_pass_loop0_loop0; rw [loop_unfold]; dsimp only
    by_cases hb : (breaks.val[cb.val]'hlt).«end» ≤ t
    · obtain ⟨c2, hc2, ec2⟩ := ih cb1 t (by omega) (by omega)
      rw [show sim.scoring.drain_pass_loop0_loop0.body breaks t cb lt = ok (.cont (cb1, t)) by
        simp [sim.scoring.drain_pass_loop0_loop0.body, hlt', slice_index_ok _ _ hlt, float.F64.le, hb, hcb1]]
      simp only [bind_ok]
      unfold sim.scoring.drain_pass_loop0_loop0 at hc2
      simp only [simBrk, hg, hb, if_true, ← ecb1]
      exact ⟨c2, hc2, ec2⟩
    · refine ⟨cb, ?_, by simp [simBrk, hg, hb]⟩
      rw [show sim.scoring.drain_pass_loop0_loop0.body breaks t cb lt = ok (.done (cb, lt)) by
        simp [sim.scoring.drain_pass_loop0_loop0.body, hlt', slice_index_ok _ _ hlt, float.F64.le, hb]]
      simp [simBrk, hg, hb]

def simIncs (incs : Slice sim.scoring.Inc) : List (F64 × F64) := incs.val.map (fun x => (x.time, x.amount))

/-- one pass of `computeDrainRate` (state: current health, lowest health, current break) -/
def simPass (I B : List (F64 × F64)) (ds res : F64) : Nat → Nat → F64 × F64 × Nat → F64 × F64 × Nat
  | 0, _, st => st
  | f + 1, i, (cur, low, cb) =>
    let t := (I[i]?.map (·.1)).getD 0
    let last0 := if 0 < i then (I[i - 1]?.map (·.1)).getD 0 else ds
    let bs := simBrk B t B.length (cb, last0)
    let cur1 := cur - (t - bs.2) * res
    let low1 := F64.min low cur1
    let st' := (F64.min 1 (cur1 + (I[i]?.map (·.2)).getD 0), low1, bs.1)
    if low1 < 0 then st' else simPass I B ds res f (i + 1) st'

theorem sim_dp_loop (incs : Slice sim.scoring.Inc) (breaks : Slice sim.playable.Period) (ds res : F64) :
    ∀ n (cur low : F64) (cb i : Usize), incs.val.length - i.val = n → i.val ≤ incs.val.length →
      cb.val ≤ breaks.val.length →
      sim.scoring.drain_pass_loop0 1 incs breaks ds res cur low cb i false =
        ok (simPass (simIncs incs) (simPS breaks) ds res n i.val (cur, low, cb.val)).2.1 := by
  have hlenI : (simIncs incs).length = incs.val.length := by simp [simIncs]
  have hlenB : (simPS breaks).length = breaks.val.length := by simp [simPS]
  intro n
  induction n with
  | zero =>
    intro cur low cb i hn hi hcb
    unfold sim.scoring.drain_pass_loop0; rw [loop_unfold]
    have : ¬ (i < Slice.len incs) := by rw [slice_lt_len_iff]; omega
    simp [sim.scoring.drain_pass_loop0.body, this, simPass]
  | succ n ih =>
    intro cur low cb i hn hi hcb
    have hlt : i.val < incs.val.length := by omega
    have hlt' : i < Slice.len incs := by rw [slice_lt_len_iff]; exact hlt
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by have := incs.property; omega)
    have hgi : (simIncs incs)[i.val]? = some ((incs.val[i.val]'hlt).time, (incs.val[i.val]'hlt).amount) := by
      simp [simIncs, List.getElem?_eq_getElem hlt]
    -- last time
    obtain ⟨last0, hl0⟩ : ∃ x : F64, (if 0 < i.val then ((simIncs incs)[i.val - 1]?.map (·.1)).getD 0 else ds) = x :=
      ⟨_, rfl⟩
    have hL : (if i > 0#usize then (do let i3 ← i - 1#usize; let i4 ← Slice.index_usize incs i3; ok i4.time)
        else ok ds) = ok last0 := by
      by_cases h0 : i.val = 0
      · have : ¬ i > 0#usize := by scalar_tac
        simp [this, ← hl0, h0]
      · have hp : i > 0#usize := by scalar_tac
        obtain ⟨j, hj, ej⟩ : ∃ z, i - 1#usize = ok z ∧ z.val = i.val - 1 := by
          obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
          exact ⟨z, hz, by simp at hv; omega⟩
        have hjl : j.val < incs.val.length := by omega
        simp [hp, hj, slice_index_ok _ _ hjl, ← hl0, show 0 < i.val by omega, simIncs,
          List.getElem?_eq_getElem (show i.val - 1 < incs.val.length by omega), ej]
    obtain ⟨cb', hcb', ecb'⟩ := sim_dp_brk_loop breaks (incs.val[i.val]'hlt).time _ cb last0 rfl hcb
    have hbf : simBrk (simPS breaks) (incs.val[i.val]'hlt).time (breaks.val.length - cb.val) (cb.val, last0) =
        simBrk (simPS breaks) (incs.val[i.val]'hlt).time (simPS breaks).length (cb.val, last0) :=
      sim_brk_fuel _ _ _ _ _ _ (by omega) (by omega)
    rw [hbf] at hcb' ecb'
    have hcbl : cb'.val ≤ breaks.val.length := by
      rw [ecb', ← hlenB]; exact sim_brk_le _ _ _ _ _ (by omega)
    obtain ⟨bs, hbs⟩ : ∃ x, simBrk (simPS breaks) (incs.val[i.val]'hlt).time (simPS breaks).length (cb.val, last0) = x :=
      ⟨_, rfl⟩
    rw [hbs] at hcb' ecb'
    obtain ⟨cur1, hcur1⟩ : ∃ x, cur - ((incs.val[i.val]'hlt).time - bs.2) * res = x := ⟨_, rfl⟩
    obtain ⟨low1, hlow1⟩ : ∃ x, F64.min low cur1 = x := ⟨_, rfl⟩
    have hstep : sim.scoring.drain_pass_loop0.body 1 incs breaks ds res cur low cb i false =
        ok (.cont (F64.min 1 (cur1 + (incs.val[i.val]'hlt).amount), low1, cb', i1, decide (low1 < 0))) := by
      simp only [sim.scoring.drain_pass_loop0.body, hlt', if_true, Bool.false_eq_true, if_false,
        slice_index_ok _ _ hlt, bind_ok, hL, hcb', float.F64.sub, float.F64.mul, net.min_refines,
        float.F64.add, sim_scoring_F64_0, float.F64.lt, hi1]
      by_cases hn : low1 < 0 <;> simp [hn, hcur1, hlow1]
    unfold sim.scoring.drain_pass_loop0; rw [loop_unfold]; dsimp only
    rw [hstep]; simp only [bind_ok]
    simp only [simPass, hgi, Option.map_some, Option.getD_some, hl0, hbs, hcur1, hlow1]
    by_cases hneg : low1 < 0
    · rw [if_pos hneg]; simp only [hneg, decide_true]
      rw [loop_unfold]
      by_cases h2 : i1 < Slice.len incs <;> simp [sim.scoring.drain_pass_loop0.body, h2]
    · rw [if_neg hneg]; simp only [hneg, decide_false]
      have IH := ih (F64.min 1 (cur1 + (incs.val[i.val]'hlt).amount)) low1 cb' i1 (by omega) (by omega) hcbl
      unfold sim.scoring.drain_pass_loop0 at IH
      rw [IH, ei1, ← ecb']
theorem sim.scoring.drain_pass_refines (incs : Slice sim.scoring.Inc) (breaks : Slice sim.playable.Period) (ds res : F64) :
    sim.scoring.drain_pass incs breaks ds res =
      ok (simPass (simIncs incs) (simPS breaks) ds res (simIncs incs).length 0 (1, 1, 0)).2.1 := by
  have h := sim_dp_loop incs breaks ds res _ 1 1 0#usize 0#usize rfl (by simp) (by simp)
  simp only [sim.scoring.drain_pass, sim_scoring_F64_1, bind_ok]
  rw [h]; simp [simIncs]

def simScanG {β} (h : β → ForInStep β) : Nat → β → β
  | 0, b => b
  | k + 1, b => match h b with | .done c => c | .yield c => simScanG h k c

theorem sim_exc_forIn_const {β} (h : β → ForInStep β) :
    ∀ (l : List Nat) (b : β), forIn (m := Except String) l b (fun _ x => pure (h x)) = .ok (simScanG h l.length b) := by
  intro l; induction l with
  | nil => intro b; rfl
  | cons j t ih =>
    intro b; rw [List.forIn_cons]
    simp only [List.length_cons, simScanG]
    cases h b with
    | done c => rfl
    | yield c => exact ih c

theorem sim_exc_forIn'_list {β} (l : List Nat) (F : (j : Nat) → j ∈ l → β → Except String (ForInStep β))
    (g : Nat → β → ForInStep β) (hF : ∀ j h b, F j h b = .ok (g j b)) (b : β) :
    forIn' l b F = .ok (l.foldr (simForStep g) id b) := by
  induction l generalizing b with
  | nil => rfl
  | cons j t ih =>
    rw [List.forIn'_cons, hF]
    simp only [List.foldr_cons, simForStep]
    cases g j b with
    | done c => rfl
    | yield c => exact ih (fun a' m b => F a' (List.mem_cons_of_mem _ m) b) (fun j h b => hF j _ b) c

theorem sim_exc_forIn'_range {β} (n : Nat) (F : (i : Nat) → i ∈ [:n] → β → Except String (ForInStep β))
    (g : Nat → β → ForInStep β) (hF : ∀ i h b, F i h b = .ok (g i b)) (b : β) :
    forIn' [:n] b F = .ok (iterR g 0 n b) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [sim_exc_forIn'_list _ _ g (fun j h b => hF j _ b)]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact congrArg Except.ok (sim_foldr_range'_iterR g n 0 b)

def simPassG (I B : List (F64 × F64)) (ds res : F64) (i : Nat) (st : F64 × F64 × Nat) : ForInStep (F64 × F64 × Nat) :=
  let t := (I[i]?.map (·.1)).getD 0
  let last0 := if 0 < i then (I[i - 1]?.map (·.1)).getD 0 else ds
  let bs := simBrk B t B.length (st.2.2, last0)
  let cur1 := st.1 - (t - bs.2) * res
  let low1 := F64.min st.2.1 cur1
  let st' := (F64.min 1 (cur1 + (I[i]?.map (·.2)).getD 0), low1, bs.1)
  if low1 < 0 then .done st' else .yield st'

theorem sim_iterR_pass (I B : List (F64 × F64)) (ds res : F64) :
    ∀ k j st, iterR (simPassG I B ds res) j k st = simPass I B ds res k j st := by
  intro k; induction k with
  | zero => intro j st; rfl
  | succ k ih =>
    intro j st
    obtain ⟨cur, low, cb⟩ := st
    simp only [iterR, simPass, simPassG]
    split_ifs <;> first | rfl | exact ih _ _

theorem sim_scanG_brk (B : List (F64 × F64)) (t : F64) :
    ∀ n cb lt, simScanG (fun (s : Nat × F64) => match B[s.1]? with
        | some b => if b.2 ≤ t then ForInStep.yield (s.1 + 1, t) else ForInStep.done (s.1, s.2)
        | none => ForInStep.done (s.1, s.2)) n (cb, lt) = simBrk B t n (cb, lt) := by
  intro n; induction n with
  | zero => intro cb lt; rfl
  | succ n ih =>
    intro cb lt
    simp only [simScanG, simBrk]
    cases B[cb]? with
    | none => rfl
    | some b => dsimp only; split_ifs <;> [exact ih _ _; rfl]

theorem sim_exc_loop_unfold {β} (F : Unit → β → Except String (ForInStep β)) (b : β) :
    forIn Lean.Loop.mk b F = (do let r ← F () b; match r with | .done c => pure c | .yield c => forIn Lean.Loop.mk c F) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

def simCDRStep (I B : List (F64 × F64)) (ds target : F64) (st : Int32 × F64 × Nat) :
    Except String (ForInStep (Int32 × F64 × Nat)) :=
  if (decide (0 < st.1) && decide (st.2.2 > 0)) = true then
    if ((simPass I B ds st.2.1 I.length 0 (1, 1, 0)).2.1 - target).abs ≤ 1e-2 then .ok (.done (st.1, st.2.1, st.2.2 - 1))
    else match ((simPass I B ds st.2.1 I.length 0 (1, 1, 0)).2.1 - target).sign with
      | .ok v => .ok (.yield (st.1 * 2, st.2.1 + 1.0 / F64.ofInt32 (st.1 * 2) * F64.ofInt v.toInt, st.2.2 - 1))
      | .error e => .error (toString "lazer would throw: Math.Sign " ++ toString (repr e) ++ toString " (ComputeDrainRate)")
  else .ok (.done st)

def simCDRrun (I B : List (F64 × F64)) (ds target : F64) : Nat → Int32 × F64 × Nat → Except String (Int32 × F64 × Nat)
  | 0, st => .ok st
  | n + 1, st => match simCDRStep I B ds target st with
    | .error e => .error e
    | .ok (.done c) => .ok c
    | .ok (.yield c) => simCDRrun I B ds target n c

theorem sim_cdr_step_fuel (I B : List (F64 × F64)) (ds target : F64) (st c : Int32 × F64 × Nat)
    (h : simCDRStep I B ds target st = .ok (.yield c)) : c.2.2 + 1 = st.2.2 := by
  unfold simCDRStep at h
  split_ifs at h with h1 h2
  · cases h
  · split at h
    · cases h; simp at h1 ⊢; omega
    · cases h
  · cases h

theorem sim_cdr_loop (I B : List (F64 × F64)) (ds target : F64)
    (F : Unit → Int32 × F64 × Nat → Except String (ForInStep (Int32 × F64 × Nat)))
    (hF : ∀ st, F () st = simCDRStep I B ds target st) :
    ∀ n st, st.2.2 < n → forIn Lean.Loop.mk st F = simCDRrun I B ds target n st := by
  intro n
  induction n with
  | zero => intro st h; omega
  | succ n ih =>
    intro st h
    rw [sim_exc_loop_unfold, hF]
    simp only [simCDRrun]
    cases hs : simCDRStep I B ds target st with
    | error e => rfl
    | ok r =>
      cases r with
      | done c => rfl
      | yield c =>
        have := sim_cdr_step_fuel I B ds target st c hs
        exact ih c (by omega)

theorem sim_exc_forIn_constF {β} (h : β → ForInStep β) (F : Nat → β → Except String (ForInStep β))
    (hF : ∀ j x, F j x = .ok (h x)) :
    ∀ (l : List Nat) (b : β), forIn l b F = .ok (simScanG h l.length b) := by
  intro l; induction l with
  | nil => intro b; rfl
  | cons j t ih =>
    intro b; rw [List.forIn_cons, hF]
    simp only [List.length_cons, simScanG]
    cases h b with
    | done c => rfl
    | yield c => exact ih c

theorem simS_computeDrainRate (incs breaks : _root_.Array (F64 × F64)) (ds target : F64) (h : ¬ incs.size ≤ 1) :
    OsuModel.Sim.computeDrainRate incs breaks ds target =
      (simCDRrun incs.toList breaks.toList ds target 100001 (1, 1, 100000)).bind (fun s =>
        if (s.2.2 == 0 && decide (0 < s.1)) = true then .error "internal: ComputeDrainRate fuel exhausted"
        else .ok s.2.1) := by
  unfold OsuModel.Sim.computeDrainRate
  simp only [h, if_false]
  rw [sim_cdr_loop incs.toList breaks.toList ds target _ ?hF 100001 _ (by decide)]
  case hF =>
    intro st
    unfold simCDRStep
    by_cases hc : (decide (0 < st.1) && decide (st.2.2 > 0)) = true
    · rw [if_pos hc, if_pos hc]
      rw [sim_exc_forIn'_range _ _ (simPassG incs.toList breaks.toList ds st.2.1) ?hF2]
      case hF2 =>
        intro i hi s1
        have hil : i < incs.size := hi.upper
        obtain ⟨cur, low, cb⟩ := s1
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        rw [sim_exc_forIn_constF (fun (s : Nat × F64) => match breaks.toList[s.1]? with
          | some b => if b.2 ≤ incs[i].1 then ForInStep.yield (s.1 + 1, incs[i].1) else ForInStep.done (s.1, s.2)
          | none => ForInStep.done (s.1, s.2)) _ ?hF3]
        case hF3 =>
          intro j x
          simp only [Array.getElem?_toList]
          cases hb : breaks[x.1]? with
          | none => rfl
          | some b => dsimp only; split_ifs <;> rfl
        simp only [List.length_range', sim_scanG_brk, simPassG]
        have hl : (if hp : 0 < i then incs[i - 1].1 else ds) =
            (if 0 < i then ((incs.toList[i - 1]?).map (·.1)).getD 0 else ds) := by
          split <;> simp [*, Array.getElem?_toList, show i - 1 < incs.size by omega]
        have hg : incs.toList[i]? = some incs[i] := by simp [hil]
        have hrs : [:breaks.size].size = breaks.size := by simp [Std.Legacy.Range.size]
        rw [hl, hg, hrs]
        simp only [Option.map_some, Option.getD_some, Array.length_toList, Bind.bind, Except.bind]
        split_ifs <;> rfl
      simp only [Bind.bind, Except.bind, sim_iterR_pass, Array.length_toList]
      split_ifs
      · rfl
      · cases ((simPass incs.toList breaks.toList ds st.2.1 incs.size 0 (1, 1, 0)).2.1 - target).sign <;> rfl
    · rw [if_neg hc, if_neg hc]; rfl
  cases simCDRrun incs.toList breaks.toList ds target 100001 (1, 1, 100000) with
  | error e => rfl
  | ok s => simp only [Bind.bind, Except.bind]; split_ifs <;> rfl

theorem sim_mathops_f64_sign (value : F64) :
    net.mathops.f64_sign value = ok (exceptI i32I (F64.sign value)) := by
  have z : net.mathops.F64_ZERO = ok (0 : F64) := by simp [net.mathops.F64_ZERO]
  unfold net.mathops.f64_sign F64.sign
  by_cases h1 : value < 0 <;> by_cases h2 : 0 < value <;> by_cases h3 : (value == 0) = true <;>
    simp [z, h1, h2, h3, exceptI, exnI] <;> try rfl

def simI32 (x : I32) : Int32 := Int32.ofBitVec x.bv

theorem sim_i32_cast_i64 (x : I32) : (IScalar.cast .I64 x).val = x.val := by
  simp [IScalar.cast_val_eq]; try scalar_tac

theorem sim_i32_toInt (x : I32) : (simI32 x).toInt = x.val := by
  rfl

theorem sim_i32_pos (x : I32) : (0#i32 < x) ↔ (0 < simI32 x) := by
  rw [Int32.lt_iff_toInt_lt, sim_i32_toInt]; simp

theorem sim_i32_wmul (x : I32) : simI32 (core.num.I32.wrapping_mul x 2#i32) = simI32 x * 2 := by
  first | rfl | (apply Int32.toBitVec_inj.mp; simp [simI32, core.num.I32.wrapping_mul, IScalar.wrapping_mul]) | decide

def simCDRfin (s : Int32 × F64 × Nat) : Except String F64 :=
  if (s.2.2 == 0 && decide (0 < s.1)) = true then .error "internal: ComputeDrainRate fuel exhausted" else .ok s.2.1

theorem sim_cdr_fin_rust (incs : Slice sim.scoring.Inc) (breaks : Slice sim.playable.Period) (ds target : F64)
    (adj : I32) (res : F64) (fuel : U32) (stop : Bool) (hc : ¬ (0#i32 < adj ∧ fuel > 0#u32 ∧ stop = false)) :
    ∃ R, sim.scoring.compute_drain_rate_loop incs breaks ds target adj res fuel stop = ok R ∧
      simRel id R (simCDRfin (simI32 adj, res, fuel.val)) := by
  have hf : (fuel = 0#u32) ↔ fuel.val = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UScalar.eq_of_val_eq (by simpa using h)
  unfold sim.scoring.compute_drain_rate_loop; rw [loop_unfold]
  unfold simCDRfin
  by_cases h0 : fuel.val = 0 <;> by_cases ha : 0#i32 < adj
  · refine ⟨.Err (.Internal .DrainFuel), ?_, ⟨"internal: ComputeDrainRate fuel exhausted", ?_⟩⟩
    · have : ¬ fuel > 0#u32 := by scalar_tac
      simp [sim.scoring.compute_drain_rate_loop.body, ha, this, hf.mpr h0]
    · simp [h0, (sim_i32_pos adj).mp ha]
  · refine ⟨.Ok res, ?_, ?_⟩
    · simp [sim.scoring.compute_drain_rate_loop.body, ha, hf.mpr h0]
    · simp [simRel, h0, mt (sim_i32_pos adj).mpr ha]
  · have hfp : fuel > 0#u32 := by scalar_tac
    have hs : stop = true := by cases stop <;> simp_all
    refine ⟨.Ok res, ?_, ?_⟩
    · simp [sim.scoring.compute_drain_rate_loop.body, ha, hfp, hs, (hf.not).mpr h0]
    · simp [simRel, h0]
  · refine ⟨.Ok res, ?_, ?_⟩
    · simp [sim.scoring.compute_drain_rate_loop.body, ha, (hf.not).mpr h0]
    · simp [simRel, h0]

theorem sim_f64_one_lit : (1.0 : F64) = 1 := by decide

theorem sim_cdr_loop_rust (incs : Slice sim.scoring.Inc) (breaks : Slice sim.playable.Period) (ds target : F64) :
    ∀ n (adj : I32) (res : F64) (fuel : U32), fuel.val < n →
      ∃ R, sim.scoring.compute_drain_rate_loop incs breaks ds target adj res fuel false = ok R ∧
        simRel id R ((simCDRrun (simIncs incs) (simPS breaks) ds target n (simI32 adj, res, fuel.val)).bind simCDRfin) := by
  intro n
  induction n with
  | zero => intro adj res fuel h; omega
  | succ n ih =>
    intro adj res fuel hfu
    by_cases hc : 0#i32 < adj ∧ fuel > 0#u32
    · obtain ⟨ha, hfp⟩ := hc
      have hfv : 0 < fuel.val := hfp
      obtain ⟨f1, hf1, ef1⟩ : ∃ z, fuel - 1#u32 = ok z ∧ z.val = fuel.val - 1 := u32_sub_one fuel (by omega)
      have hstepS : (decide (0 < simI32 adj) && decide (fuel.val > 0)) = true := by
        simp [(sim_i32_pos adj).mp ha, hfv]
      set low := (simPass (simIncs incs) (simPS breaks) ds res (simIncs incs).length 0 (1, 1, 0)).2.1 with hlow
      have hdp := sim.scoring.drain_pass_refines incs breaks ds res
      simp only [simCDRrun, simCDRStep, hstepS, if_true, ← hlow]
      unfold sim.scoring.compute_drain_rate_loop; rw [loop_unfold]
      by_cases hab : (low - target).abs ≤ 1e-2
      · simp only [hab, if_true]
        obtain ⟨R, hR, eR⟩ := sim_cdr_fin_rust incs breaks ds target adj res f1 true (by simp)
        refine ⟨R, ?_, ?_⟩
        · rw [show sim.scoring.compute_drain_rate_loop.body incs breaks ds target adj res fuel false =
              ok (.cont (adj, res, f1, true)) by
            simp [sim.scoring.compute_drain_rate_loop.body, ha, hfp, hf1, hdp, ← hlow, float.F64.sub, float.F64.abs,
              float.F64.le, hab]]
          simp only [bind_ok]
          unfold sim.scoring.compute_drain_rate_loop at hR; exact hR
        · rw [ef1] at eR; exact eR
      · simp only [hab, if_false]
        cases hsg : (low - target).sign with
        | error e =>
          refine ⟨.Err (.SignDrain (exnI e)), ?_, ⟨_, rfl⟩⟩
          rw [show sim.scoring.compute_drain_rate_loop.body incs breaks ds target adj res fuel false =
              ok (.done (.Err (.SignDrain (exnI e)))) by
            simp [sim.scoring.compute_drain_rate_loop.body, ha, hfp, hf1, hdp, ← hlow, float.F64.sub, float.F64.abs,
              float.F64.le, hab, sim_mathops_f64_sign, hsg, exceptI, lift]]
          simp only [bind_ok]
        | ok v =>
          let adj1 := core.num.I32.wrapping_mul adj 2#i32
          let res1 := res + 1 / F64.ofInt adj1.val * F64.ofInt (i32I v).val
          obtain ⟨R, hR, eR⟩ := ih adj1 res1 f1 (by omega)
          refine ⟨R, ?_, ?_⟩
          · rw [show sim.scoring.compute_drain_rate_loop.body incs breaks ds target adj res fuel false =
                ok (.cont (adj1, res1, f1, false)) by
              simp [sim.scoring.compute_drain_rate_loop.body, ha, hfp, hf1, hdp, ← hlow, float.F64.sub,
                float.F64.abs, float.F64.le, hab, sim_mathops_f64_sign, hsg, exceptI, lift, sim_i32_cast_i64,
                float.F64.from_i64, float.F64.div, float.F64.mul, float.F64.add, adj1, res1]]
            simp only [bind_ok]
            unfold sim.scoring.compute_drain_rate_loop at hR; exact hR
          · have e1 : simI32 adj1 = simI32 adj * 2 := sim_i32_wmul adj
            have e2 : res1 = res + 1.0 / F64.ofInt32 (simI32 adj * 2) * F64.ofInt v.toInt := by
              simp only [res1, sim_f64_one_lit, F64.ofInt32, ← e1, sim_i32_toInt]; rfl
            rw [e1, e2, ef1] at eR
            exact eR
    · obtain ⟨R, hR, eR⟩ := sim_cdr_fin_rust incs breaks ds target adj res fuel false (by tauto)
      refine ⟨R, hR, ?_⟩
      have hstepS : (decide (0 < simI32 adj) && decide (fuel.val > 0)) = false := by
        by_cases ha : 0#i32 < adj
        · have : ¬ fuel > 0#u32 := fun h => hc ⟨ha, h⟩
          have : fuel.val = 0 := by scalar_tac
          simp [this]
        · simp [mt (sim_i32_pos adj).mpr ha]
      simp only [simCDRrun, simCDRStep, hstepS, Bool.false_eq_true, if_false, Except.bind]
      exact eR

theorem sim.scoring.compute_drain_rate_refines (incs : Slice sim.scoring.Inc) (breaks : Slice sim.playable.Period)
    (ds target : F64) :
    ∃ R, sim.scoring.compute_drain_rate incs breaks ds target = ok R ∧
      simRel id R (OsuModel.Sim.computeDrainRate (simIncs incs).toArray (simPS breaks).toArray ds target) := by
  have hlen : (simIncs incs).length = incs.val.length := by simp [simIncs]
  by_cases h1 : incs.val.length ≤ 1
  · have h1' : Slice.len incs <= 1#usize := by scalar_tac
    refine ⟨.Ok 0, by simp [sim.scoring.compute_drain_rate, h1', sim_scoring_F64_0], ?_⟩
    unfold OsuModel.Sim.computeDrainRate
    simp [simRel, hlen, h1]
  · have h1' : ¬ (Slice.len incs <= 1#usize) := by scalar_tac
    have h1s : ¬ (simIncs incs).toArray.size ≤ 1 := by simp [hlen]; omega
    obtain ⟨R, hR, eR⟩ := sim_cdr_loop_rust incs breaks ds target 100001 1#i32 1 100000#u32 (by simp)
    refine ⟨R, by simp [sim.scoring.compute_drain_rate, h1', sim_scoring_F64_1, hR], ?_⟩
    rw [simS_computeDrainRate _ _ _ _ h1s]
    have e1 : simI32 1#i32 = 1 := by decide
    simp only [List.toList_toArray, e1] at eR ⊢
    exact eR
end OsuProofs
