/-
(iii) A state machine with nested loops, `break`, fuel and signed indices:
`schedule::simulate_steps` refines `OsuModel.Sim.simulateSteps` (FSC step schedule, D9).

Assumptions (explicit hypotheses, not axioms):
* `System.Platform.numBits = 64` (we only run on x86-64; needed for the `i64 as usize` cast and
  for `Vec` capacity);
* `refs.val.length * 10^8 + 4 < 2^61`: the spec allows 10^8 steps per reference; this bound keeps every
  `i64`/`usize` operation of the impl in range (the impl would otherwise panic on overflow).
-/
import OsuProofs.Slider
import OsuProofs.Spec.Schedule
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Sim OsuProofs.SpecSched

namespace OsuProofs
open OsuImpl

theorem NEG_INF_eq : schedule.NEG_INF = ok F64.negInf := by
  unfold schedule.NEG_INF; exact from_bits_lit _ _ (by decide +kernel)
theorem POS_INF_eq : schedule.POS_INF = ok F64.posInf := by
  unfold schedule.POS_INF; exact from_bits_lit _ _ (by decide +kernel)
theorem K0_sched_eq : schedule.K0 = ok (0 : F64) := by
  unfold schedule.K0; exact from_bits_lit _ _ (by decide +kernel)
theorem SIXTY_eq : schedule.SIXTY_FRAME_TIME = ok sixtyFrameTime := by
  unfold schedule.SIXTY_FRAME_TIME; exact from_bits_lit _ _ (by decide +kernel)
theorem CATCHUP_eq : schedule.CATCHUP_THRESHOLD = ok catchupThreshold := by
  unfold schedule.CATCHUP_THRESHOLD; exact from_bits_lit _ _ (by decide +kernel)
theorem FUEL_val : schedule.FUEL.val = SpecSched.FUEL := by
  unfold schedule.FUEL SpecSched.FUEL; rfl

theorem usize_max_64 (h64 : System.Platform.numBits = 64) : Usize.max = 2^64 - 1 := by
  simp [Usize.max, Usize.numBits, h64]

theorem FUEL_lit : SpecSched.FUEL = 100000000 := rfl

/-- `frame_time` = the spec's `frameTime` closure. -/
theorem schedule.frame_time_refines (h64 : System.Platform.numBits = 64) (frames : Slice F64) (i : I64)
    (hi : i.val < 2^62) : schedule.frame_time frames i = ok (ft frames.val.toArray i.val) := by
  unfold schedule.frame_time ft
  by_cases hneg : i.val < 0
  · have h : i < 0#i64 := by simpa using hneg
    simp [h, hneg, NEG_INF_eq]
  · have h : ¬ (i < 0#i64) := by simpa using hneg
    have hc : (IScalar.hcast .Usize i).val = i.val.toNat := by
      rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
    simp only [h, hneg, if_false, lift, bind_tc_ok, bind_ok]
    by_cases hge : i.val ≥ (frames.val.length : Int)
    · have h2 : IScalar.hcast .Usize i >= Slice.len frames := by
        show Slice.len frames ≤ IScalar.hcast .Usize i
        simp only [UScalar.le_equiv, Slice.len_val, Slice.length, hc]; omega
      simp [h2, hge, POS_INF_eq]
    · have hlt : (IScalar.hcast .Usize i).val < frames.val.length := by rw [hc]; omega
      have h2 : ¬ (IScalar.hcast .Usize i >= Slice.len frames) := by
        show ¬ (Slice.len frames ≤ IScalar.hcast .Usize i)
        simp only [UScalar.le_equiv, Slice.len_val, Slice.length]; omega
      simp only [h2, if_false, List.size_toArray, hge]
      rw [index_eq frames _ hlt]
      have hlt2 : i.val.toNat < frames.val.length := by rw [← hc]; exact hlt
      simp [hc, List.getElem?_eq_getElem hlt2]

/-- Impl state ↦ spec tuple `(first, manual, idx, handlerTime)`. -/
def toT (st : schedule.SimState) : Bool × F64 × Int × F64 :=
  (st.first, st.manual, st.idx.val, st.handler_time)

set_option maxHeartbeats 4000000 in
/-- One FSC step. -/
theorem schedule.fsc_step_refines (h64 : System.Platform.numBits = 64) (st : schedule.SimState) (r : F64)
    (frames : Slice F64) (gst : F64) (hidx : -2^61 ≤ st.idx.val ∧ st.idx.val ≤ 2^61) :
    ∃ st', schedule.fsc_step st r frames gst = ok st' ∧
      toT st' = stepT frames.val.toArray gst r (toT st) := by
  obtain ⟨i1, hi1, hi1v⟩ := i64_add_one st.idx (by omega) (by omega)
  obtain ⟨i2, hi2, hi2v⟩ := i64_add_one i1 (by omega) (by omega)
  obtain ⟨d, hd, hdv⟩ := i64_sub_one st.idx (by omega) (by omega)
  obtain ⟨d1, hd1, hd1v⟩ := i64_add_one d (by omega) (by omega)
  have f0 := schedule.frame_time_refines h64 frames st.idx (by omega)
  have f1 := schedule.frame_time_refines h64 frames i1 (by omega)
  have f2 := schedule.frame_time_refines h64 frames i2 (by omega)
  have f3 := schedule.frame_time_refines h64 frames d (by omega)
  have f4 := schedule.frame_time_refines h64 frames d1 (by omega)
  rw [hi2v] at f2; rw [hi1v] at f1 f2; rw [hd1v] at f4; rw [hdv] at f3 f4
  unfold schedule.fsc_step
  simp only [hi1, hi2, hd, hd1, f0, f1, f2, f3, f4, CATCHUP_eq, SIXTY_eq, min_refines, max_refines,
    clamp_refines, float.F64.lt, float.F64.le, float.F64.eq, float.F64.sub, float.F64.add,
    float.F64.abs, bind_tc_ok, bind_ok, toT, stepT, propose]
  have hlen : (Slice.len frames = 0#usize) ↔ frames.val.length = 0 := by
    rw [UScalar.eq_equiv]; simp
  by_cases hfirst : st.first = true
  swap
  · simp only [hfirst, Bool.false_eq_true, ite_false, decide_eq_true_eq]
    by_cases h1 : st.manual < gst
    · simp only [h1, ite_true, decide_true, bind_tc_ok, bind_ok]
      repeat' split
      all_goals simp_all [exceptToOption]
    · simp only [h1, ite_false, decide_false, Bool.false_eq_true]
      by_cases h2 : catchupThreshold < F64.abs (st.manual - r)
      · simp only [h2, ite_true, decide_true]
        by_cases h3 : st.manual < r
        · simp only [h3, ite_true, decide_true, bind_tc_ok, bind_ok]
          repeat' split
          all_goals simp_all [exceptToOption]
        · simp only [h3, ite_false, decide_false, Bool.false_eq_true, bind_tc_ok, bind_ok]
          repeat' split
          all_goals simp_all [exceptToOption]
      · simp only [h2, ite_false, decide_false, Bool.false_eq_true, bind_tc_ok, bind_ok]
        repeat' split
        all_goals simp_all [exceptToOption]
  · simp only [hfirst, ite_true, bind_tc_ok, bind_ok]
    repeat' split
    all_goals simp_all [exceptToOption]

/-- Impl step record ↦ spec `Step`. -/
def stepSpec (s : schedule.Step) : Step := { time := s.time, frameIndex := s.frame_index.val }

theorem inner_loop_unfold (frames : Slice F64) (gst : F64) (steps : alloc.vec.Vec schedule.Step) (b : Bool)
    (f : F64) (i : I64) (f1 : F64) (r : F64) (fuel : U32) :
    schedule.simulate_steps_loop0_loop0 frames gst steps b f i f1 r fuel =
      (do
        let x ← schedule.simulate_steps_loop0_loop0.body frames gst r steps b f i f1 fuel
        match x with
        | .cont y => schedule.simulate_steps_loop0_loop0 frames gst y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 r y.2.2.2.2.2
        | .done y => ok y) := by
  unfold schedule.simulate_steps_loop0_loop0; rw [loop]
  simp only []
  congr 1; funext x; cases x <;> rfl

theorem outer_loop_unfold (refs frames : Slice F64) (gst : F64) (steps : alloc.vec.Vec schedule.Step) (b : Bool)
    (f : F64) (i : I64) (f1 : F64) (ri : Usize) :
    schedule.simulate_steps_loop0 refs frames gst steps b f i f1 ri =
      (do
        let x ← schedule.simulate_steps_loop0.body refs frames gst steps b f i f1 ri
        match x with
        | .cont y => schedule.simulate_steps_loop0 refs frames gst y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2
        | .done y => ok y) := by
  unfold schedule.simulate_steps_loop0; rw [loop]
  simp only []
  congr 1; funext x; cases x <;> rfl

/-- The inner `while fuel > 0` loop. -/
theorem inner_refines (h64 : System.Platform.numBits = 64) (frames : Slice F64) (gst r : F64) :
    ∀ (n : Nat) (fuel : U32) (steps : alloc.vec.Vec schedule.Step) (b : Bool) (f : F64) (i : I64) (f1 : F64),
      fuel.val = n → (if i.val < 0 then -i.val else i.val) ≤ 1 + steps.val.length →
      steps.val.length + n + 2 < 2^61 →
      ∃ steps' b' f' i' f1',
        schedule.simulate_steps_loop0_loop0 frames gst steps b f i f1 r fuel = ok (steps', b', f', i', f1') ∧
        ((steps'.val.map stepSpec).toArray, b', f', i'.val, f1') =
          (let o := inner frames.val.toArray gst r n (steps.val.map stepSpec).toArray b f i.val f1
           (o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1)) ∧
        (if i'.val < 0 then -i'.val else i'.val) ≤ 1 + steps'.val.length ∧ steps'.val.length ≤ steps.val.length + n := by
  intro n
  induction n with
  | zero =>
    intro fuel steps b f i f1 hfuel hinv hb
    refine ⟨steps, b, f, i, f1, ?_, ?_, hinv, by omega⟩
    · unfold schedule.simulate_steps_loop0_loop0
      rw [loop]
      have : ¬ (fuel > 0#u32) := by simp [hfuel]
      simp [schedule.simulate_steps_loop0_loop0.body, this]
    · simp [inner]
  | succ n ih =>
    intro fuel steps b f i f1 hfuel hinv hb
    have hpos : fuel > 0#u32 := by simp [hfuel]
    obtain ⟨fuel1, hf1, hf1v⟩ := u32_sub_one fuel (by omega)
    obtain ⟨st', hst, hst'⟩ := schedule.fsc_step_refines h64 { first := b, manual := f, idx := i, handler_time := f1 }
      r frames gst (by simp only; split at hinv <;> omega)
    have hU := usize_max_64 h64
    obtain ⟨steps1, hs1, hs1v⟩ := push_eq steps ({ time := st'.manual, frame_index := st'.idx } : schedule.Step)
      (by rw [hU]; omega)
    have hidx := stepT_idx frames.val.toArray gst r (b, f, i.val, f1)
    simp only [toT] at hst'
    rw [← hst'] at hidx
    simp only at hidx
    have hinv' : (if st'.idx.val < 0 then -st'.idx.val else st'.idx.val) ≤ 1 + steps1.val.length := by
      simp only [hs1v, List.length_append, List.length_singleton]
      split at hinv <;> split <;> omega
    have hinnerS : inner frames.val.toArray gst r (n + 1) (steps.val.map stepSpec).toArray b f i.val f1 =
        let steps' := ((steps.val.map stepSpec).toArray).push { time := st'.manual, frameIndex := st'.idx.val }
        if (st'.handler_time == r) = true then (steps', st'.first, st'.manual, st'.idx.val, st'.handler_time, n)
        else inner frames.val.toArray gst r n steps' st'.first st'.manual st'.idx.val st'.handler_time := by
      simp only [inner, ← hst']
    have hpushS : ((steps.val.map stepSpec).toArray).push { time := st'.manual, frameIndex := st'.idx.val } =
        (steps1.val.map stepSpec).toArray := by
      simp [hs1v, stepSpec]
    by_cases hbrk : (st'.handler_time == r) = true
    · refine ⟨steps1, st'.first, st'.manual, st'.idx, st'.handler_time, ?_, ?_, hinv', ?_⟩
      · unfold schedule.simulate_steps_loop0_loop0
        rw [loop]
        simp [schedule.simulate_steps_loop0_loop0.body, hpos, hf1, hst, hs1, float.F64.eq, hbrk]
      · rw [hinnerS]; simp only [hbrk, ite_true, hpushS]
      · simp only [hs1v, List.length_append, List.length_singleton]; omega
    · have hbrk' : (st'.handler_time == r) = false := by simpa using hbrk
      obtain ⟨steps', b', f', i', f1', hl, hr, hinv2, hlen2⟩ :=
        ih fuel1 steps1 st'.first st'.manual st'.idx st'.handler_time (by omega) hinv'
          (by simp only [hs1v, List.length_append, List.length_singleton] at *; omega)
      refine ⟨steps', b', f', i', f1', ?_, ?_, hinv2, ?_⟩
      · rw [inner_loop_unfold]
        simp only [schedule.simulate_steps_loop0_loop0.body, hpos, if_true, hf1, hst, hs1, float.F64.eq,
          hbrk', bind_tc_ok, bind_ok, Bool.false_eq_true, if_false]
        exact hl
      · rw [hinnerS]; simp only [hbrk, if_false, hpushS]; exact hr
      · simp only [hs1v, List.length_append, List.length_singleton] at *; omega

/-- The fold step of the spec's outer loop. -/
def outerStep (frames : Array F64) (gst : F64) (s : Array Step × Bool × F64 × Int × F64) (r : F64) :
    Array Step × Bool × F64 × Int × F64 :=
  let o := inner frames gst r FUEL s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
  (o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1)

/-- The outer `for r in refs` loop. -/
theorem outer_refines (h64 : System.Platform.numBits = 64) (refs frames : Slice F64) (gst : F64) :
    ∀ (k : Nat) (ri : Usize) (steps : alloc.vec.Vec schedule.Step) (b : Bool) (f : F64) (i : I64) (f1 : F64),
      refs.val.length - ri.val = k → ri.val ≤ refs.val.length →
      (if i.val < 0 then -i.val else i.val) ≤ 1 + steps.val.length →
      steps.val.length + (refs.val.length - ri.val) * FUEL + 4 < 2^61 →
      ∃ v, schedule.simulate_steps_loop0 refs frames gst steps b f i f1 ri = ok v ∧
        (v.val.map stepSpec).toArray =
          ((refs.val.drop ri.val).foldl (outerStep frames.val.toArray gst)
            ((steps.val.map stepSpec).toArray, b, f, i.val, f1)).1 := by
  intro k
  induction k with
  | zero =>
    intro ri steps b f i f1 hk hri hinv hb
    have hge : ¬ (ri < Slice.len refs) := by simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]; omega
    refine ⟨steps, ?_, ?_⟩
    · unfold schedule.simulate_steps_loop0
      rw [loop]
      simp [schedule.simulate_steps_loop0.body, hge]
    · have : refs.val.drop ri.val = [] := by simp; omega
      simp [this]
  | succ k ih =>
    intro ri steps b f i f1 hk hri hinv hb
    have hlt : ri.val < refs.val.length := by omega
    have hlt' : ri < Slice.len refs := by simp only [UScalar.lt_equiv, Slice.len_val, Slice.length]; omega
    have hFUEL : schedule.FUEL.val = FUEL := FUEL_val
    obtain ⟨steps1, b1, f2, i2, f3, hl, hr, hinv1, hlen1⟩ :=
      inner_refines h64 frames gst (refs.val[ri.val]'hlt) FUEL schedule.FUEL steps b f i f1 hFUEL hinv
        (by rw [FUEL_lit] at *; have : 1 ≤ refs.val.length - ri.val := by omega
            have : steps.val.length + 100000000 ≤ steps.val.length + (refs.val.length - ri.val) * 100000000 := by omega
            omega)
    have hU := usize_max_64 h64
    obtain ⟨ri1, hri1, hri1v⟩ := usize_add_one ri (by have := Slice.length_ineq refs; omega)
    obtain ⟨v, hv, hvv⟩ := ih ri1 steps1 b1 f2 i2 f3 (by omega) (by omega) hinv1
      (by rw [FUEL_lit] at *
          have e : refs.val.length - ri.val = (refs.val.length - ri1.val) + 1 := by omega
          rw [e] at hb; omega)
    refine ⟨v, ?_, ?_⟩
    · rw [outer_loop_unfold]
      simp only [schedule.simulate_steps_loop0.body, hlt', if_true, index_eq refs ri hlt, hl, hri1,
        bind_tc_ok, bind_ok]
      first
        | simpa using hv
        | (simp; exact hv)
        | (simp only [Bind.bind, bind_ok]; exact hv)
    · rw [hvv, List.drop_eq_getElem_cons hlt, List.foldl_cons, hri1v]
      congr 2

/-- **Refinement theorem**: whenever the spec's `simulateSteps` succeeds, the Rust `simulate_steps` returns
exactly its step list. (The Rust POC keeps the pre-totality semantics: on a `Math.Clamp` error it uses the
unclamped time and it does not reject on fuel exhaustion, so it is defined on more inputs than the spec; D28.) -/
theorem schedule.simulate_steps_refines (h64 : System.Platform.numBits = 64) (refs frames : Slice F64) (gst : F64)
    (hsz : refs.val.length * 100000000 + 4 < 2^61) (s : Array Step)
    (hs : simulateSteps refs.val.toArray frames.val.toArray gst = .ok s) :
    ∃ v, schedule.simulate_steps refs frames gst = ok v ∧ (v.val.map stepSpec).toArray = s := by
  obtain ⟨v, hv, hvv⟩ := outer_refines h64 refs frames gst refs.val.length 0#usize (alloc.vec.Vec.new schedule.Step)
    true 0 (-1)#i64 F64.negInf (by simp) (by simp) (by simp) (by rw [FUEL_lit]; simp; omega)
  refine ⟨v, ?_, ?_⟩
  · simp only [schedule.simulate_steps, K0_sched_eq, NEG_INF_eq, bind_tc_ok, bind_ok]
    exact hv
  · rw [hvv, simulateSteps_ok _ _ _ _ hs]
    simp [outer]
    rfl

end OsuProofs
