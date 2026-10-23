/-
`beatmap::control_points` (Rust) refines `OsuModel.Beatmap` control points
(`ControlPoints.lean`): clamps, defaults, redundancy checks, binary search, sorted insert,
`Add*` and `DeepClone`.
-/
import OsuProofs.Beatmap.DotNet
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

def tpS (p : beatmap.control_points.TimingPoint) : TimingPoint := ⟨p.time, p.beat_length, i32S p.time_signature⟩
def dpS (p : beatmap.control_points.DifficultyPoint) : DifficultyPoint := ⟨p.time, p.slider_velocity, p.generate_ticks⟩
def epS (p : beatmap.control_points.EffectPoint) : EffectPoint := ⟨p.time, p.kiai, p.scroll_speed⟩
def tpI (p : TimingPoint) : beatmap.control_points.TimingPoint := ⟨p.time, p.beatLength, i32I p.timeSignature⟩
def dpI (p : DifficultyPoint) : beatmap.control_points.DifficultyPoint := ⟨p.time, p.sliderVelocity, p.generateTicks⟩
def epI (p : EffectPoint) : beatmap.control_points.EffectPoint := ⟨p.time, p.kiai, p.scrollSpeed⟩

@[simp] theorem cp_K6 : beatmap.control_points.K6 = ok (6 : F64) := by
  simp [beatmap.control_points.K6] <;> decide
@[simp] theorem cp_K60000 : beatmap.control_points.K60000 = ok (60000 : F64) := by
  simp [beatmap.control_points.K60000] <;> decide
@[simp] theorem cp_K0_1 : beatmap.control_points.K0_1 = ok (0.1 : F64) := by
  simp [beatmap.control_points.K0_1] <;> decide
@[simp] theorem cp_K10 : beatmap.control_points.K10 = ok (10 : F64) := by
  simp [beatmap.control_points.K10] <;> decide
@[simp] theorem cp_K0_01 : beatmap.control_points.K0_01 = ok (0.01 : F64) := by
  simp [beatmap.control_points.K0_01] <;> decide
@[simp] theorem cp_K1 : beatmap.control_points.K1 = ok (1 : F64) := by
  simp [beatmap.control_points.K1] <;> decide
@[simp] theorem cp_K1000 : beatmap.control_points.K1000 = ok (1000 : F64) := by
  simp [beatmap.control_points.K1000] <;> decide
@[simp] theorem cp_K0 : beatmap.control_points.K0 = ok (0 : F64) := by
  simp [beatmap.control_points.K0] <;> decide

theorem beatmap.control_points.clamp_beat_length_refines (v : F64) :
    beatmap.control_points.clamp_beat_length v = ok (clampBeatLength v) := by
  simp [beatmap.control_points.clamp_beat_length, clampBeatLength]
theorem beatmap.control_points.clamp_sv_refines (v : F64) :
    beatmap.control_points.clamp_sv v = ok (clampSV v) := by
  simp [beatmap.control_points.clamp_sv, clampSV]
theorem beatmap.control_points.clamp_scroll_speed_refines (v : F64) :
    beatmap.control_points.clamp_scroll_speed v = ok (clampScrollSpeed v) := by
  simp [beatmap.control_points.clamp_scroll_speed, clampScrollSpeed]

theorem beatmap.control_points.TIMING_DEFAULT_refines :
    beatmap.control_points.TIMING_DEFAULT = ok (tpI TimingPoint.default) := by
  simp [beatmap.control_points.TIMING_DEFAULT, TimingPoint.default, tpI, i32I]; rfl
theorem beatmap.control_points.DIFFICULTY_DEFAULT_refines :
    beatmap.control_points.DIFFICULTY_DEFAULT = ok (dpI DifficultyPoint.default) := by
  simp [beatmap.control_points.DIFFICULTY_DEFAULT, DifficultyPoint.default, dpI]
theorem beatmap.control_points.EFFECT_DEFAULT_refines :
    beatmap.control_points.EFFECT_DEFAULT = ok (epI EffectPoint.default) := by
  simp [beatmap.control_points.EFFECT_DEFAULT, EffectPoint.default, epI]

theorem beatmap.control_points.difficulty_is_redundant_refines (p e : beatmap.control_points.DifficultyPoint) :
    beatmap.control_points.difficulty_is_redundant p e = ok ((dpS p).isRedundant (dpS e)) := by
  simp [beatmap.control_points.difficulty_is_redundant, DifficultyPoint.isRedundant, dpS]
  cases p.generate_ticks <;> cases e.generate_ticks <;> rfl
theorem beatmap.control_points.effect_is_redundant_refines (p e : beatmap.control_points.EffectPoint) :
    beatmap.control_points.effect_is_redundant p e = ok ((epS p).isRedundant (epS e)) := by
  simp [beatmap.control_points.effect_is_redundant, EffectPoint.isRedundant, epS]
  cases p.kiai <;> cases e.kiai <;> rfl

/-! ## binary search -/


def bsStep {α : Type} [Inhabited α] (A : _root_.Array α) (timeOf : α → F64) (time : F64) (s : Int × Int × Bool) :
    ForInStep (Int × Int × Bool) :=
  if s.1 ≤ s.2.1 then
    if timeOf A[(s.1 + (s.2.1 - s.1) / 2).toNat]! < time then ForInStep.yield (s.1 + (s.2.1 - s.1) / 2 + 1, s.2.1, s.2.2)
    else if time < timeOf A[(s.1 + (s.2.1 - s.1) / 2).toNat]! then ForInStep.yield (s.1, s.1 + (s.2.1 - s.1) / 2 - 1, s.2.2)
    else ForInStep.yield (s.1 + (s.2.1 - s.1) / 2 + 1, s.2.1, true)
  else ForInStep.yield (s.1, s.2.1, s.2.2)

theorem map_get! {T α : Type} [Inhabited α] (L : List T) (S : T → α) (i : Nat) (h : i < L.length) :
    (L.map S).toArray[i]! = S (L[i]'h) := by
  rw [getElem!_pos (L.map S).toArray i (by simpa using h)]; simp

theorem id_bind_eq' {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

theorem hcast_usize_val (x : I64) (h0 : 0 ≤ x.val) (h1 : x.val < 2^31) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have : (2:Int)^31 ≤ 2^UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
  rw [Int.emod_eq_of_lt h0 (by omega)]

theorem bs_loop {T α : Type} [Inhabited α] (H : beatmap.control_points.HasTime T) (tf : T → F64)
    (hH : ∀ x, H.time_of x = ok (tf x)) (S : T → α) (timeOf : α → F64) (hS : ∀ x, timeOf (S x) = tf x)
    (list : Slice T) (time : F64) (n : Usize) (hn : n.val = list.val.length) (hn62 : n.val < 2^31)
    (R : Int × Int × Bool) :
    ∀ (l r : I64) (eq : Bool) (k : Usize),
      (k.val ≤ n.val + 1 ∧ 0 ≤ l.val ∧ l.val ≤ n.val ∧ -1 ≤ r.val ∧ r.val ≤ n.val - 1 ∧
        iterId (bsStep (list.val.map S).toArray timeOf time) (n.val + 1 - k.val) (l.val, r.val, eq) = R) →
      ∃ y, beatmap.control_points.binary_search_idx_loop H list time n l r eq k = ok y ∧
        y.1.val = R.1 ∧ y.2 = R.2.2 ∧ 0 ≤ y.1.val ∧ y.1.val ≤ n.val := by
  intro l r eq k hx
  unfold beatmap.control_points.binary_search_idx_loop
  refine loop_ok _ (fun x => n.val + 1 - x.2.2.2.val) (fun (x : I64 × I64 × Bool × Usize) => x.2.2.2.val ≤ n.val + 1 ∧ 0 ≤ x.1.val ∧ x.1.val ≤ (n.val : Int) ∧ -1 ≤ x.2.1.val ∧ x.2.1.val ≤ (n.val : Int) - 1 ∧
        iterId (bsStep (list.val.map S).toArray timeOf time) (n.val + 1 - x.2.2.2.val) (x.1.val, x.2.1.val, x.2.2.1) = R)
    (fun (y : I64 × Bool) => y.1.val = R.1 ∧ y.2 = R.2.2 ∧ 0 ≤ y.1.val ∧ y.1.val ≤ (n.val : Int)) ?_ (l, r, eq, k) hx
  rintro ⟨l, r, eq, k⟩ ⟨hk, hl0, hln, hr0, hrn, hR⟩
  dsimp only at hk hl0 hln hr0 hrn hR ⊢
  have hnb := n.hBounds
  have hmax : n.val + 1 ≤ Usize.max := by
    have h32 := usize_ge_32
    omega
  obtain ⟨i, hi, hiv⟩ := usize_add_one n hmax
  by_cases hkn : k.val < n.val + 1
  · right
    have hkn' : k < i := by show k.val < i.val; omega
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    have e : n.val + 1 - k.val = (n.val + 1 - k1.val) + 1 := by omega
    rw [e] at hR
    simp only [iterId] at hR
    by_cases hlr : l.val ≤ r.val
    · have hlr' : l ≤ r := hlr
      obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (I64.sub_spec (x := r) (y := l)
        (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      obtain ⟨i2, hi2, hi2v⟩ := IScalar.div_spec (x := i1) (y := 2#i64) (by simp)
        (by simp)
      have hdiv : i2.val = (r.val - l.val) / 2 := by
        rw [hi2v, hi1v]; simp; rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
      obtain ⟨pv, hpv, hpvv⟩ := eq_ok_of_spec (I64.add_spec (x := l) (y := i2)
        (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      have hp0 : 0 ≤ pv.val := by omega
      have hpn : pv.val ≤ r.val := by omega
      have hc : (IScalar.hcast .Usize pv).val = pv.val.toNat := by
        rw [IScalar.hcast_val_eq]
        have hnb' : (n.val : Int) < 2^UScalarTy.Usize.numBits := by exact_mod_cast hnb
        have : pv.val < 2^UScalarTy.Usize.numBits := by omega
        rw [Int.emod_eq_of_lt hp0 (by exact_mod_cast this)]
      have hlt : (IScalar.hcast .Usize pv).val < list.val.length := by rw [hc]; omega
      have hlt2 : pv.val.toNat < list.val.length := by omega
      have hidx : Slice.index_usize list (IScalar.hcast .Usize pv) = ok (list.val[pv.val.toNat]'hlt2) := by
        rw [index_eq list _ hlt]; simp [hc]
      have hget := map_get! list.val S _ hlt2
      have hpe : (l.val + (r.val - l.val) / 2).toNat = pv.val.toNat := by rw [hpvv, hdiv]
      simp only [bsStep, hlr, ite_true, hpe, hget, hS] at hR
      rw [← hdiv, ← hpvv] at hR
      generalize hxx : list.val[pv.val.toNat]'hlt2 = xx at hidx hR
      obtain ⟨l2, hl2, hl2v⟩ := i64_add_one pv (by omega) (by omega)
      by_cases c1 : tf xx < time
      · refine ⟨(l2, r, eq, k1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · simp [beatmap.control_points.binary_search_idx_loop.body, hi, hkn', hiv, hkn, hlr, hlr', hi1, hi2, hpv, lift, hidx, hH, c1, hl2, hk1]
        · dsimp only; simp only [c1, ite_true] at hR; rw [hl2v]; exact hR
      · by_cases c2 : time < tf xx
        · obtain ⟨r2, hr2, hr2v⟩ := i64_sub_one pv (by omega) (by omega)
          refine ⟨(l, r2, eq, k1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          · simp [beatmap.control_points.binary_search_idx_loop.body, hi, hkn', hiv, hkn, hlr, hlr', hi1, hi2, hpv, lift, hidx, hH, c1, c2, hr2, hk1]
          · dsimp only; simp only [c1, c2, ite_true, ite_false] at hR; rw [hr2v]; exact hR
        · refine ⟨(l2, r, true, k1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          · simp [beatmap.control_points.binary_search_idx_loop.body, hi, hkn', hiv, hkn, hlr, hlr', hi1, hi2, hpv, lift, hidx, hH, c1, c2, hl2, hk1]
          · dsimp only; simp only [c1, c2, ite_false] at hR; rw [hl2v]; exact hR
    · have hlr' : ¬ l ≤ r := hlr
      refine ⟨(l, r, eq, k1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      · simp [beatmap.control_points.binary_search_idx_loop.body, hi, hkn', hiv, hkn, hlr, hlr', hk1]
      · dsimp only; simp only [bsStep, hlr, ite_false] at hR; exact hR
  · left
    have hkn' : ¬ k < i := by show ¬ k.val < i.val; omega
    refine ⟨(l, eq), by simp [beatmap.control_points.binary_search_idx_loop.body, hi, hkn', hiv, hkn], ?_⟩
    have : n.val + 1 - k.val = 0 := by omega
    rw [this] at hR; simp only [iterId] at hR
    rw [← hR]; exact ⟨rfl, rfl, hl0, hln⟩

/-- Guarded: fewer than `2^31` points (so all `usize`/`i64` index arithmetic is exact on any platform). -/
theorem beatmap.control_points.binary_search_idx_refines {T α : Type} [Inhabited α]
    (H : beatmap.control_points.HasTime T) (tf : T → F64)
    (hH : ∀ x, H.time_of x = ok (tf x)) (S : T → α) (timeOf : α → F64) (hS : ∀ x, timeOf (S x) = tf x)
    (list : Slice T) (time : F64) (hn : list.val.length < 2^31) :
    ∃ o, beatmap.control_points.binary_search_idx H list time = ok o ∧
      o.map (·.val) = binarySearchIdx (list.val.map S).toArray timeOf time ∧
      (∀ i, o = some i → i.val < list.val.length) := by
  unfold beatmap.control_points.binary_search_idx binarySearchIdx
  simp only [Id.run]
  rw [forIn_range_id' _ (fun _ _ => rfl)]
  generalize hG : iterId _ ((list.val.map S).toArray.size + 1) _ = R
  have hG' : iterId (bsStep (list.val.map S).toArray timeOf time) (list.val.length + 1)
      (0, (list.val.length : Int) - 1, false) = R := by
    rw [← hG]; simp only [List.size_toArray, List.length_map]; rfl
  simp only [List.size_toArray, List.length_map]
  by_cases h0 : list.val.length = 0
  · have h0' : Slice.len list = 0#usize := by rw [UScalar.eq_equiv_bv_eq, ← BitVec.toNat_inj]; simpa using h0
    exact ⟨none, by simp [h0'], by simp [h0]; rfl, by simp⟩
  · have h0' : ¬ Slice.len list = 0#usize := by rw [UScalar.eq_equiv_bv_eq, ← BitVec.toNat_inj]; simpa using h0
    have hl0 : 0 < list.val.length := by omega
    rw [index_eq list 0#usize (by simpa using hl0)]
    rw [map_get! list.val S 0 hl0]
    simp only [h0', h0, hH, hS, beq_iff_eq, ite_false]
    by_cases c1 : time < tf (list.val[0]'hl0)
    · exact ⟨none, by simp [c1], by simp [c1]; rfl, by simp⟩
    · obtain ⟨nm1, hnm1, hnm1v⟩ := eq_ok_of_spec (Usize.sub_spec (x := Slice.len list) (y := 1#usize) (by simp; omega))
      simp at hnm1v
      have hlt1 : nm1.val < list.val.length := by omega
      rw [map_get! list.val S _ (by omega), hS]
      have hidx1 : Slice.index_usize list nm1 = ok (list.val[list.val.length - 1]'(by omega)) := by
        rw [index_eq list nm1 hlt1]; simp [hnm1v]
      by_cases c2 : tf (list.val[list.val.length - 1]'(by omega)) < time
      · exact ⟨some nm1, by simp [c1, hnm1, hidx1, c2], by simp [c1, c2, hnm1v]; rfl, by intro i hi; cases hi; omega⟩
      · have hcI : (UScalar.hcast .I64 (Slice.len list)).val = (list.val.length : Int) := by
          rw [UScalar.hcast_val_eq]; simp; exact Int.bmod_eq_of_le (by omega) (by omega)
        obtain ⟨r0, hr0, hr0v⟩ := i64_sub_one (UScalar.hcast .I64 (Slice.len list)) (by omega) (by omega)
        rw [hcI] at hr0v
        obtain ⟨y, hy, hy1, hy2, hy0, hyn⟩ := bs_loop H tf hH S timeOf hS list time (Slice.len list) (by simp)
          (by simp; omega) R 0#i64 r0 false 0#usize
          ⟨by simp, by simp, by simp, by simp [hr0v], by simp [hr0v], by simpa [hr0v] using hG'⟩
        obtain ⟨yl, ye⟩ := y
        simp only at hy1 hy2 hy0 hyn
        have hyn' : yl.val ≤ list.val.length := by simpa using hyn
        clear hyn
        obtain ⟨R1, R2, R3⟩ := R
        simp only at hy1 hy2
        subst hy1 hy2
        simp only [c1, c2, hnm1, hidx1, hr0, hy, lift, bind_tc_ok, bind_ok, ite_false, hH, float.F64.lt, decide_false, Bool.false_eq_true]
        have c1' : ¬ time < tf (list.val[(0#usize : Usize).val]'(by simpa using hl0)) := by simpa using c1
        simp only [c1', decide_false, Bool.false_eq_true, ite_false]
        have hmin : ∀ z : I64, -2^31 ≤ z.val → z.val ≤ 2^31 → z ≠ IScalar.min .I64 := by
          intro z h1 h2 h; rw [h] at h1; simp [IScalar.min, I64.min_eq] at h1
        rw [id_bind_eq']
        cases ye with
        | true =>
          obtain ⟨i0, hi0, hi0v⟩ := i64_sub_one yl (by omega) (by omega)
          by_cases hz : yl.val - 1 < 0
          · have hz' : i0 < 0#i64 := by show i0.val < (0#i64).val; simp; omega
            have hzv : i0.val < 0 := by omega
            obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step i0 (hmin i0 (by omega) (by omega)))
            obtain ⟨q1, hq1, hq1v⟩ := i64_sub_one q (by omega) (by omega)
            obtain ⟨q2, hq2, hq2v⟩ := i64_sub_one q1 (by omega) (by omega)
            have hq2' : ¬ q2 ≥ 0#i64 := by show ¬ (0#i64).val ≤ q2.val; simp; omega
            have hq2n : q2.val < 0 := by omega
            have hs : ¬ (0 ≤ -(yl.val - 1) - 1 - 1) := by omega
            refine ⟨none, by simp [hi0, hz', hzv, HNeg.hNeg, hq, hq1, hq2, hq2', hq2n], ?_, by simp⟩
            simp [hz, hs]
            simp only [id_pure_eq]; split <;> first | rfl | omega
          · have hz' : ¬ i0 < 0#i64 := by show ¬ i0.val < (0#i64).val; simp; omega
            have hge : i0 ≥ 0#i64 := by show (0#i64).val ≤ i0.val; simp; omega
            have hzv : ¬ i0.val < 0 := by omega
            have hzv' : 0 ≤ i0.val := by omega
            have hs : 0 ≤ yl.val - 1 := by omega
            refine ⟨some (IScalar.hcast .Usize i0), by simp [hi0, hz', hge, hzv, hzv'], ?_,
              by intro i hi; cases hi; rw [hcast_usize_val i0 hzv' (by omega)]; omega⟩
            simp [hz, hs, hcast_usize_val i0 hzv' (by omega), hi0v]
            simp only [id_pure_eq]; split <;> first | rfl | omega
        | false =>
          obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step yl (hmin yl (by omega) (by omega)))
          obtain ⟨i0, hi0, hi0v⟩ := i64_sub_one q (by omega) (by omega)
          have hz' : i0 < 0#i64 := by show i0.val < (0#i64).val; simp; omega
          have hzv : i0.val < 0 := by omega
          obtain ⟨q', hq', hqv'⟩ := eq_ok_of_spec (IScalar.neg_step i0 (hmin i0 (by omega) (by omega)))
          obtain ⟨q1, hq1, hq1v⟩ := i64_sub_one q' (by omega) (by omega)
          obtain ⟨q2, hq2, hq2v⟩ := i64_sub_one q1 (by omega) (by omega)
          have hs0 : -yl.val - 1 < 0 := by omega
          by_cases hz : yl.val - 1 < 0
          · have hq2' : ¬ q2 ≥ 0#i64 := by show ¬ (0#i64).val ≤ q2.val; simp; omega
            have hq2n : q2.val < 0 := by omega
            have hs : ¬ (0 ≤ -(-yl.val - 1) - 1 - 1) := by omega
            refine ⟨none, by simp [HNeg.hNeg, hq, hi0, hz', hzv, hq', hq1, hq2, hq2', hq2n], ?_, by simp⟩
            simp [hs0, hs]
            simp only [id_pure_eq]; split <;> first | rfl | omega
          · have hge : q2 ≥ 0#i64 := by show (0#i64).val ≤ q2.val; simp; omega
            have hq2p : 0 ≤ q2.val := by omega
            have hs : 0 ≤ -(-yl.val - 1) - 1 - 1 := by omega
            refine ⟨some (IScalar.hcast .Usize q2), by simp [HNeg.hNeg, hq, hi0, hz', hzv, hq', hq1, hq2, hge, hq2p], ?_,
              by intro i hi; cases hi; rw [hcast_usize_val q2 hq2p (by omega)]; omega⟩
            simp [hs0, hs, hcast_usize_val q2 hq2p (by omega), hq2v, hq1v, hqv', hi0v, hqv]
            simp only [id_pure_eq]; split <;> first | rfl | omega

/-! ## point lookups -/

def cpS (c : beatmap.control_points.ControlPointInfo) : ControlPointInfo :=
  ⟨(c.timing_points.val.map tpS).toArray, (c.difficulty_points.val.map dpS).toArray,
   (c.effect_points.val.map epS).toArray⟩

@[simp] theorem i32I_S (x : I32) : i32I (i32S x) = x := by
  simp [i32I, i32S]
@[simp] theorem tpI_S (p : beatmap.control_points.TimingPoint) : tpI (tpS p) = p := by
  simp [tpI, tpS]
@[simp] theorem dpS_I' (p : DifficultyPoint) : dpS (dpI p) = p := rfl
@[simp] theorem epS_I' (p : EffectPoint) : epS (epI p) = p := rfl
@[simp] theorem dpI_S (p : beatmap.control_points.DifficultyPoint) : dpI (dpS p) = p := rfl
@[simp] theorem epI_S (p : beatmap.control_points.EffectPoint) : epI (epS p) = p := rfl

theorem vec_index_eq {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok (v.val[i.val]'h) := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (alloc.vec.Vec.index_usize_spec v i h)
  rw [hx, hx']

/-- Guarded: fewer than `2^31` timing points. -/
theorem beatmap.control_points.timing_point_at_refines (c : beatmap.control_points.ControlPointInfo) (time : F64)
    (h : c.timing_points.val.length < 2^31) :
    beatmap.control_points.timing_point_at c time = ok (tpI ((cpS c).timingPointAt time)) := by
  obtain ⟨o, ho, hov, hob⟩ := beatmap.control_points.binary_search_idx_refines
    beatmap.control_points.TimingPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time) (fun _ => rfl)
    tpS (·.time) (fun _ => rfl) (alloc.vec.Vec.deref c.timing_points) time (by simpa [alloc.vec.Vec.deref] using h)
  have hd : (alloc.vec.Vec.deref c.timing_points).val = c.timing_points.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hov hob
  unfold beatmap.control_points.timing_point_at ControlPointInfo.timingPointAt
  dsimp only
  rw [ho]; simp only [cpS, bind_ok]; rw [← hov]
  cases o with
  | none =>
    simp only [Option.map_none]
    by_cases hz : 0 < c.timing_points.val.length
    · have hz' : alloc.vec.Vec.len c.timing_points > 0#usize := by show (0#usize).val < _; simpa using hz
      rw [ite_cond_eq_true _ _ (eq_true hz'), vec_index_eq _ _ (by simpa using hz)]
      simp [cpS, hz, map_get! _ _ 0 hz]
    · have hz' : ¬ alloc.vec.Vec.len c.timing_points > 0#usize := by show ¬ (0#usize).val < _; simpa using hz
      rw [ite_cond_eq_false _ _ (eq_false hz')]
      simp [cpS, hz, beatmap.control_points.TIMING_DEFAULT_refines]
  | some i =>
    have hi := hob i rfl
    simp only [Option.map_some]
    rw [vec_index_eq _ _ hi]
    simp [cpS, map_get! _ _ _ hi]

/-- Guarded: fewer than `2^31` difficulty points. -/
theorem beatmap.control_points.difficulty_point_at_refines (c : beatmap.control_points.ControlPointInfo) (time : F64)
    (h : c.difficulty_points.val.length < 2^31) :
    beatmap.control_points.difficulty_point_at c time = ok (dpI ((cpS c).difficultyPointAt time)) := by
  obtain ⟨o, ho, hov, hob⟩ := beatmap.control_points.binary_search_idx_refines
    beatmap.control_points.DifficultyPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time) (fun _ => rfl)
    dpS (·.time) (fun _ => rfl) (alloc.vec.Vec.deref c.difficulty_points) time (by simpa [alloc.vec.Vec.deref] using h)
  have hd : (alloc.vec.Vec.deref c.difficulty_points).val = c.difficulty_points.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hov hob
  unfold beatmap.control_points.difficulty_point_at ControlPointInfo.difficultyPointAt
  dsimp only
  rw [ho]; simp only [cpS, bind_ok]; rw [← hov]
  cases o with
  | none => simp [cpS, beatmap.control_points.DIFFICULTY_DEFAULT_refines]
  | some i =>
    have hi := hob i rfl
    simp only [Option.map_some]
    rw [vec_index_eq _ _ hi]
    simp [cpS, map_get! _ _ _ hi]

/-- Guarded: fewer than `2^31` effect points. -/
theorem beatmap.control_points.effect_point_at_refines (c : beatmap.control_points.ControlPointInfo) (time : F64)
    (h : c.effect_points.val.length < 2^31) :
    beatmap.control_points.effect_point_at c time = ok (epI ((cpS c).effectPointAt time)) := by
  obtain ⟨o, ho, hov, hob⟩ := beatmap.control_points.binary_search_idx_refines
    beatmap.control_points.EffectPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time) (fun _ => rfl)
    epS (·.time) (fun _ => rfl) (alloc.vec.Vec.deref c.effect_points) time (by simpa [alloc.vec.Vec.deref] using h)
  have hd : (alloc.vec.Vec.deref c.effect_points).val = c.effect_points.val := by simp [alloc.vec.Vec.deref]
  rw [hd] at hov hob
  unfold beatmap.control_points.effect_point_at ControlPointInfo.effectPointAt
  dsimp only
  rw [ho]; simp only [cpS, bind_ok]; rw [← hov]
  cases o with
  | none => simp [cpS, beatmap.control_points.EFFECT_DEFAULT_refines]
  | some i =>
    have hi := hob i rfl
    simp only [Option.map_some]
    rw [vec_index_eq _ _ hi]
    simp [cpS, map_get! _ _ _ hi]

theorem beatmap.control_points.cpi_empty_refines :
    ∃ c, beatmap.control_points.cpi_empty = ok c ∧ cpS c = {} :=
  ⟨_, rfl, by simp [cpS, alloc.vec.Vec.new]⟩

/-! ## sorted insert -/

theorem i32_eq_zero_iff (r : I32) : r = 0#i32 ↔ r.val = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; apply IScalar.eq_of_val_eq; simp [h]

theorem is_loop0 {T : Type} (H : beatmap.control_points.HasTime T) (tf : T → F64)
    (hH : ∀ x, H.time_of x = ok (tf x)) (list : alloc.vec.Vec T) (t : F64) :
    ∀ i : Usize, i.val ≤ list.val.length →
      (∀ j (_ : j < i.val) (hjl : j < list.val.length), (compareF64 (tf (list.val[j]'hjl)) t == 0) = false) →
      ∃ r, beatmap.control_points.insert_sorted_loop0 H list t none i = ok r ∧
        r.map (·.val) = list.val.findIdx? (fun q => compareF64 (tf q) t == 0) := by
  intro i hi hpre
  unfold beatmap.control_points.insert_sorted_loop0
  refine loop_ok _ (fun (x : Option Usize × Usize) => list.val.length + 1 - x.2.val)
    (fun (x : Option Usize × Usize) =>
      (x.1 = none ∧ x.2.val ≤ list.val.length ∧
        ∀ j (hj : j < x.2.val) (hjl : j < list.val.length), (compareF64 (tf (list.val[j]'hjl)) t == 0) = false) ∨
      (∃ s, x.1 = some s ∧ list.val.findIdx? (fun q => compareF64 (tf q) t == 0) = some s.val))
    (fun (r : Option Usize) => r.map (·.val) = list.val.findIdx? (fun q => compareF64 (tf q) t == 0)) ?_
    (none, i) (Or.inl ⟨rfl, hi, hpre⟩)
  rintro ⟨same, i⟩ hx
  dsimp only at hx ⊢
  rcases hx with ⟨rfl, hi, hpre⟩ | ⟨s, rfl, hs⟩
  · by_cases hlt : i.val < list.val.length
    · right
      have hlt' : i < alloc.vec.Vec.len list := by show i.val < (alloc.vec.Vec.len list).val; simpa using hlt
      obtain ⟨c, hc, hcv⟩ := beatmap.dotnet.compare_f64_refines (tf (list.val[i.val]'hlt)) t
      obtain ⟨i3, hi3, hi3v⟩ := usize_add_one i (by have := list.property; have := usize_ge_32; omega)
      by_cases h0 : compareF64 (tf (list.val[i.val]'hlt)) t = 0
      · have hc0 : c = 0#i32 := (i32_eq_zero_iff c).mpr (by rw [hcv, h0])
        refine ⟨(some i, i3), by simp [beatmap.control_points.insert_sorted_loop0.body, hlt',
          vec_index_eq _ _ hlt, hH, hc, hc0, hi3], Or.inr ⟨i, rfl, ?_⟩, by dsimp only; omega⟩
        rw [List.findIdx?_eq_some_iff_getElem]
        exact ⟨hlt, by simp [h0], fun j hj => by simpa using hpre j hj (by omega)⟩
      · have hc0 : ¬ c = 0#i32 := by rw [i32_eq_zero_iff, hcv]; exact h0
        refine ⟨(none, i3), by simp [beatmap.control_points.insert_sorted_loop0.body, hlt',
          vec_index_eq _ _ hlt, hH, hc, hc0, hi3], Or.inl ⟨rfl, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        intro j hj hjl
        by_cases hji : j < i.val
        · exact hpre j hji hjl
        · have : j = i.val := by dsimp only at hj; omega
          subst this; simp [h0]
    · left
      have hlt' : ¬ i < alloc.vec.Vec.len list := by show ¬ i.val < (alloc.vec.Vec.len list).val; simpa using hlt
      refine ⟨none, by simp [beatmap.control_points.insert_sorted_loop0.body, hlt'], ?_⟩
      simp only [Option.map_none]
      symm; rw [List.findIdx?_eq_none_iff]
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      simpa using hpre j (by omega) hj
  · left
    exact ⟨some s, by simp [beatmap.control_points.insert_sorted_loop0.body], by simp [hs]⟩

theorem i32_lt_zero_iff (r : I32) : r < 0#i32 ↔ r.val < 0 := by
  show r.val < (0#i32).val ↔ _; simp

theorem is_loop1 {T : Type} (H : beatmap.control_points.HasTime T) (tf : T → F64)
    (hH : ∀ x, H.time_of x = ok (tf x)) (list : alloc.vec.Vec T) (t : F64) :
    ∃ r, beatmap.control_points.insert_sorted_loop1 H list t 0#usize false = ok r ∧
      r.val = (list.val.findIdx? (fun q => decide (compareF64 t (tf q) < 0))).getD list.val.length := by
  unfold beatmap.control_points.insert_sorted_loop1
  refine loop_ok _ (fun (x : Usize × Bool) => list.val.length + 1 - x.1.val + (if x.2 then 0 else 1))
    (fun (x : Usize × Bool) =>
      (x.2 = false ∧ x.1.val ≤ list.val.length ∧
        ∀ j (_ : j < x.1.val) (hjl : j < list.val.length), compareF64 t (tf (list.val[j]'hjl)) ≥ 0) ∨
      (x.2 = true ∧ list.val.findIdx? (fun q => decide (compareF64 t (tf q) < 0)) = some x.1.val))
    (fun (r : Usize) => r.val = (list.val.findIdx? (fun q => decide (compareF64 t (tf q) < 0))).getD list.val.length) ?_
    (0#usize, false) (Or.inl ⟨rfl, by simp, fun j hj => by simp at hj⟩)
  rintro ⟨k, found⟩ hx
  dsimp only at hx ⊢
  rcases hx with ⟨rfl, hk, hpre⟩ | ⟨rfl, hs⟩
  · by_cases hlt : k.val < list.val.length
    · right
      have hlt' : k < alloc.vec.Vec.len list := by show k.val < (alloc.vec.Vec.len list).val; simpa using hlt
      obtain ⟨c, hc, hcv⟩ := beatmap.dotnet.compare_f64_refines t (tf (list.val[k.val]'hlt))
      by_cases h0 : compareF64 t (tf (list.val[k.val]'hlt)) < 0
      · have hc0 : c < 0#i32 := (i32_lt_zero_iff c).mpr (by rw [hcv]; exact h0)
        have hcvl : c.val < 0 := by rw [hcv]; exact h0
        refine ⟨(k, true), by simp [beatmap.control_points.insert_sorted_loop1.body, hlt',
          vec_index_eq _ _ hlt, hH, hc, hc0, hcvl], Or.inr ⟨rfl, ?_⟩, by dsimp only; simp⟩
        rw [List.findIdx?_eq_some_iff_getElem]
        exact ⟨hlt, by simp [h0], fun j hj => by
          simp only at hj; have := hpre j hj (by omega); simp; omega⟩
      · have hc0 : ¬ c < 0#i32 := by rw [i32_lt_zero_iff, hcv]; exact h0
        have hcvl : 0 ≤ c.val := by rw [hcv]; omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := list.property; have := usize_ge_32; omega)
        refine ⟨(k1, false), by simp [beatmap.control_points.insert_sorted_loop1.body, hlt',
          vec_index_eq _ _ hlt, hH, hc, hc0, hk1, hcvl], Or.inl ⟨rfl, by dsimp only; omega, ?_⟩, by dsimp only; simp; omega⟩
        intro j hj hjl
        by_cases hji : j < k.val
        · exact hpre j hji hjl
        · have : j = k.val := by dsimp only at hj; omega
          subst this; omega
    · left
      have hlt' : ¬ k < alloc.vec.Vec.len list := by show ¬ k.val < (alloc.vec.Vec.len list).val; simpa using hlt
      refine ⟨k, by simp [beatmap.control_points.insert_sorted_loop1.body, hlt'], ?_⟩
      have : list.val.findIdx? (fun q => decide (compareF64 t (tf q) < 0)) = none := by
        rw [List.findIdx?_eq_none_iff]
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have := hpre j (by omega) hj; simp; omega
      rw [this]; simp; omega
  · left
    exact ⟨k, by simp [beatmap.control_points.insert_sorted_loop1.body], by simp [hs]⟩

/-- Guarded: the list can grow by one (`len < usize::MAX`). -/
theorem beatmap.control_points.insert_sorted_refines {T α : Type} [Inhabited α]
    (H : beatmap.control_points.HasTime T) (tf : T → F64) (wt : T → F64 → T)
    (hH : ∀ x, H.time_of x = ok (tf x)) (hW : ∀ x t, H.with_time x t = ok (wt x t))
    (C : core.clone.Clone T) (hC : ∀ x, C.clone x = ok x)
    (S : T → α) (timeOf : α → F64) (setTime : α → F64 → α)
    (hS : ∀ x, timeOf (S x) = tf x) (hSet : ∀ x t, setTime (S x) t = S (wt x t))
    (list : alloc.vec.Vec T) (p : T) (hl : list.val.length < Usize.max) :
    ∃ w, beatmap.control_points.insert_sorted H C list p = ok w ∧
      (w.val.map S).toArray = ControlPointInfo.insertSorted (list.val.map S).toArray timeOf setTime (S p) := by
  obtain ⟨r, hr, hrv⟩ := is_loop0 H tf hH list (tf p) 0#usize (by simp) (fun j hj => by simp at hj)
  unfold beatmap.control_points.insert_sorted ControlPointInfo.insertSorted
  simp only [hH, bind_ok, hr, hS]
  have hf1 : ((list.val.map S).toArray.findIdx? fun q => compareF64 (timeOf q) (tf p) == 0) =
      list.val.findIdx? (fun q => compareF64 (tf q) (tf p) == 0) := by
    simp [Function.comp_def, hS]
  rw [hf1, ← hrv]
  cases r with
  | some jj =>
    have hjl : jj.val < list.val.length := by
      have := hrv; simp at this
      exact (List.findIdx?_eq_some_iff_getElem.mp this.symm).1
    refine ⟨alloc.vec.Vec.set list jj (wt p (tf (list.val[jj.val]'hjl))), ?_, ?_⟩
    · simp only [vec_index_eq _ _ hjl, hH, hW, bind_ok, vec_index_mut_eq _ _ hjl]; rfl
    · simp only [Option.map_some, alloc.vec.Vec.set_val_eq]
      rw [map_get! _ _ _ hjl, hS, hSet]
      apply Array.ext'
      simp
  | none =>
    obtain ⟨k, hk, hkv⟩ := is_loop1 H tf hH list (tf p)
    have hkl : k.val ≤ list.val.length := by
      rw [hkv]
      cases h : (list.val.findIdx? (fun q => decide (compareF64 (tf p) (tf q) < 0))) with
      | none => simp
      | some i => simp; exact Nat.le_of_lt (List.findIdx?_eq_some_iff_getElem.mp h).1
    obtain ⟨w, hw, hwv⟩ := beatmap.dotnet.insert_at_refines C hC list k p hkl hl
    refine ⟨w, by simp only [hk, hw, bind_ok], ?_⟩
    have hf2 : ((list.val.map S).toArray.findIdx? fun q => decide (compareF64 (tf p) (timeOf q) < 0)) =
        list.val.findIdx? (fun q => decide (compareF64 (tf p) (tf q) < 0)) := by
      simp [Function.comp_def, hS]
    simp only [Option.map_none]
    rw [hf2, List.size_toArray, List.length_map, ← hkv, hwv]
    apply Array.ext'
    simp [Array.insertIdx!, hkl, List.map_insertIdx]

theorem insertSorted_size_le {α : Type} [Inhabited α] (list : _root_.Array α) (timeOf : α → F64)
    (setTime : α → F64 → α) (p : α) :
    (ControlPointInfo.insertSorted list timeOf setTime p).size ≤ list.size + 1 := by
  unfold ControlPointInfo.insertSorted
  dsimp only
  split
  · simp
  · simp only [Array.insertIdx!]
    split
    · simp
    · next hcond =>
      exfalso; apply hcond
      cases hh : Array.findIdx? (fun q => decide (compareF64 (timeOf p) (timeOf q) < 0)) list with
      | none => simp
      | some i => simp; exact Nat.le_of_lt (Array.findIdx?_eq_some_iff_getElem.mp hh).1

/-! ## `ControlPointInfo.Add` -/

theorem beatmap.control_points.add_timing_refines (c : beatmap.control_points.ControlPointInfo)
    (p : beatmap.control_points.TimingPoint) (h : c.timing_points.val.length < Usize.max) :
    ∃ c', beatmap.control_points.add_timing c p = ok c' ∧ cpS c' = (cpS c).addTiming (tpS p) ∧
      c'.difficulty_points = c.difficulty_points ∧ c'.effect_points = c.effect_points ∧
      c'.timing_points.val.length ≤ c.timing_points.val.length + 1 := by
  obtain ⟨w, hw, hwv⟩ := beatmap.control_points.insert_sorted_refines
    beatmap.control_points.TimingPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time)
    (fun p t => { p with time := t }) (fun _ => rfl) (fun _ _ => rfl)
    beatmap.control_points.TimingPoint.Insts.CoreCloneClone (fun _ => rfl)
    tpS (·.time) (fun p t => { p with time := t }) (fun _ => rfl) (fun _ _ => rfl) c.timing_points p h
  refine ⟨{ c with timing_points := w }, by simp [beatmap.control_points.add_timing, hw], ?_, rfl, rfl, ?_⟩
  · simp only [cpS, ControlPointInfo.addTiming, hwv]
  · have := congrArg Array.size hwv
    simp at this
    have h2 := insertSorted_size_le (c.timing_points.val.map tpS).toArray (·.time) (fun p t => { p with time := t }) (tpS p)
    simp at h2; dsimp only; omega

theorem beatmap.control_points.add_difficulty_refines (c : beatmap.control_points.ControlPointInfo)
    (p : beatmap.control_points.DifficultyPoint) (h : c.difficulty_points.val.length < 2^31) :
    ∃ c', beatmap.control_points.add_difficulty c p = ok c' ∧ cpS c' = (cpS c).addDifficulty (dpS p) ∧
      c'.timing_points = c.timing_points ∧ c'.effect_points = c.effect_points ∧
      c'.difficulty_points.val.length ≤ c.difficulty_points.val.length + 1 := by
  have hdp := beatmap.control_points.difficulty_point_at_refines c p.time h
  unfold beatmap.control_points.add_difficulty ControlPointInfo.addDifficulty
  simp only [hdp, bind_ok, beatmap.control_points.difficulty_is_redundant_refines]
  by_cases hr : (dpS p).isRedundant ((cpS c).difficultyPointAt (dpS p).time) = true
  · have hr' : (dpS p).isRedundant (dpS (dpI ((cpS c).difficultyPointAt p.time))) = true := hr
    exact ⟨c, by rw [if_pos hr'], by rw [if_pos hr], rfl, rfl, by omega⟩
  · have hr' : ¬ (dpS p).isRedundant (dpS (dpI ((cpS c).difficultyPointAt p.time))) = true := hr
    have hm : c.difficulty_points.val.length < Usize.max := by have := usize_ge_32; omega
    obtain ⟨w, hw, hwv⟩ := beatmap.control_points.insert_sorted_refines
      beatmap.control_points.DifficultyPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time)
      (fun p t => { p with time := t }) (fun _ => rfl) (fun _ _ => rfl)
      beatmap.control_points.DifficultyPoint.Insts.CoreCloneClone (fun _ => rfl)
      dpS (·.time) (fun p t => { p with time := t }) (fun _ => rfl) (fun _ _ => rfl) c.difficulty_points p hm
    refine ⟨{ c with difficulty_points := w }, by rw [if_neg hr']; simp only [hw, bind_ok], ?_, rfl, rfl, ?_⟩
    · rw [if_neg hr]; simp only [cpS, hwv]
    · have := congrArg Array.size hwv
      simp at this
      have h2 := insertSorted_size_le (c.difficulty_points.val.map dpS).toArray (·.time) (fun p t => { p with time := t }) (dpS p)
      simp at h2; dsimp only; omega

theorem beatmap.control_points.add_effect_refines (c : beatmap.control_points.ControlPointInfo)
    (p : beatmap.control_points.EffectPoint) (h : c.effect_points.val.length < 2^31) :
    ∃ c', beatmap.control_points.add_effect c p = ok c' ∧ cpS c' = (cpS c).addEffect (epS p) ∧
      c'.timing_points = c.timing_points ∧ c'.difficulty_points = c.difficulty_points ∧
      c'.effect_points.val.length ≤ c.effect_points.val.length + 1 := by
  have hdp := beatmap.control_points.effect_point_at_refines c p.time h
  unfold beatmap.control_points.add_effect ControlPointInfo.addEffect
  simp only [hdp, bind_ok, beatmap.control_points.effect_is_redundant_refines]
  by_cases hr : (epS p).isRedundant ((cpS c).effectPointAt (epS p).time) = true
  · have hr' : (epS p).isRedundant (epS (epI ((cpS c).effectPointAt p.time))) = true := hr
    exact ⟨c, by rw [if_pos hr'], by rw [if_pos hr], rfl, rfl, by omega⟩
  · have hr' : ¬ (epS p).isRedundant (epS (epI ((cpS c).effectPointAt p.time))) = true := hr
    have hm : c.effect_points.val.length < Usize.max := by have := usize_ge_32; omega
    obtain ⟨w, hw, hwv⟩ := beatmap.control_points.insert_sorted_refines
      beatmap.control_points.EffectPoint.Insts.Osu_eval_coreBeatmapControl_pointsHasTime (·.time)
      (fun p t => { p with time := t }) (fun _ => rfl) (fun _ _ => rfl)
      beatmap.control_points.EffectPoint.Insts.CoreCloneClone (fun _ => rfl)
      epS (·.time) (fun p t => { p with time := t }) (fun _ => rfl) (fun _ _ => rfl) c.effect_points p hm
    refine ⟨{ c with effect_points := w }, by rw [if_neg hr']; simp only [hw, bind_ok], ?_, rfl, rfl, ?_⟩
    · rw [if_neg hr]; simp only [cpS, hwv]
    · have := congrArg Array.size hwv
      simp at this
      have h2 := insertSorted_size_le (c.effect_points.val.map epS).toArray (·.time) (fun p t => { p with time := t }) (epS p)
      simp at h2; dsimp only; omega

/-! ## `DeepClone` -/

theorem take_succ_foldl {α β} (f : β → α → β) (b : β) (l : List α) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).foldl f b = f ((l.take i).foldl f b) (l[i]'h) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]; rfl

theorem dc_loop0 (c : beatmap.control_points.ControlPointInfo) (h : c.timing_points.val.length < 2^31) :
    ∀ (r : beatmap.control_points.ControlPointInfo) (i : Usize), i.val ≤ c.timing_points.val.length →
      cpS r = ((c.timing_points.val.map tpS).take i.val).foldl ControlPointInfo.addTiming {} →
      r.timing_points.val.length ≤ i.val → r.difficulty_points.val = [] → r.effect_points.val = [] →
      ∃ r1, beatmap.control_points.deep_clone_loop0 c r i = ok (c.difficulty_points, c.effect_points, r1) ∧
        cpS r1 = (c.timing_points.val.map tpS).foldl ControlPointInfo.addTiming {} ∧
        r1.difficulty_points.val = [] ∧ r1.effect_points.val = [] := by
  intro r i hi hr hrl hrd hre
  have := loop_ok (fun (x : beatmap.control_points.ControlPointInfo × Usize) =>
      beatmap.control_points.deep_clone_loop0.body c x.1 x.2)
    (fun (x : beatmap.control_points.ControlPointInfo × Usize) => c.timing_points.val.length - x.2.val)
    (fun (x : beatmap.control_points.ControlPointInfo × Usize) => x.2.val ≤ c.timing_points.val.length ∧
      cpS x.1 = ((c.timing_points.val.map tpS).take x.2.val).foldl ControlPointInfo.addTiming {} ∧
      x.1.timing_points.val.length ≤ x.2.val ∧ x.1.difficulty_points.val = [] ∧ x.1.effect_points.val = [])
    (fun y => y.1 = c.difficulty_points ∧ y.2.1 = c.effect_points ∧
      cpS y.2.2 = (c.timing_points.val.map tpS).foldl ControlPointInfo.addTiming {} ∧
      y.2.2.difficulty_points.val = [] ∧ y.2.2.effect_points.val = [])
    (by
      rintro ⟨r, i⟩ ⟨hi, hr, hrl, hrd, hre⟩
      dsimp only at hi hr hrl hrd hre ⊢
      by_cases hlt : i.val < c.timing_points.val.length
      · right
        have hlt' : i < alloc.vec.Vec.len c.timing_points := by
          show i.val < (alloc.vec.Vec.len c.timing_points).val; simpa using hlt
        obtain ⟨r1, hr1, hr1s, hr1d, hr1e, hr1l⟩ := beatmap.control_points.add_timing_refines r
          (c.timing_points.val[i.val]'hlt) (by have := usize_ge_32; omega)
        obtain ⟨i2, hi2, hi2v⟩ := usize_add_one i (by have := usize_ge_32; omega)
        refine ⟨(r1, i2), by simp [beatmap.control_points.deep_clone_loop0.body, hlt', vec_index_eq _ _ hlt, hr1, hi2],
          ⟨by dsimp only; omega, ?_, by dsimp only; omega, by dsimp only; rw [hr1d, hrd], by dsimp only; rw [hr1e, hre]⟩,
          by dsimp only; omega⟩
        dsimp only
        rw [hr1s, hr, hi2v, take_succ_foldl _ _ _ _ (by simpa using hlt)]
        simp
      · left
        have hlt' : ¬ i < alloc.vec.Vec.len c.timing_points := by
          show ¬ i.val < (alloc.vec.Vec.len c.timing_points).val; simpa using hlt
        refine ⟨(c.difficulty_points, c.effect_points, r), by simp [beatmap.control_points.deep_clone_loop0.body, hlt'],
          rfl, rfl, ?_, hrd, hre⟩
        dsimp only
        rw [hr]
        have : i.val = c.timing_points.val.length := by omega
        rw [this, ← List.length_map tpS, List.take_length])
    (r, i) ⟨hi, hr, hrl, hrd, hre⟩
  obtain ⟨⟨v, v1, r1⟩, hy, rfl, rfl, hs, hd, he⟩ := this
  exact ⟨r1, by unfold beatmap.control_points.deep_clone_loop0; exact hy, hs, hd, he⟩

theorem dc_loop1 (v : alloc.vec.Vec beatmap.control_points.DifficultyPoint) (h : v.val.length < 2^31) (init : ControlPointInfo) :
    ∀ (r : beatmap.control_points.ControlPointInfo) (i : Usize), i.val ≤ v.val.length →
      cpS r = ((v.val.map dpS).take i.val).foldl ControlPointInfo.addDifficulty init →
      r.difficulty_points.val.length ≤ i.val →
      ∃ r1, beatmap.control_points.deep_clone_loop1 v r i = ok r1 ∧
        cpS r1 = (v.val.map dpS).foldl ControlPointInfo.addDifficulty init ∧ r1.effect_points = r.effect_points := by
  intro r i hi hr hrl
  have := loop_ok (fun (x : beatmap.control_points.ControlPointInfo × Usize) =>
      beatmap.control_points.deep_clone_loop1.body v x.1 x.2)
    (fun (x : beatmap.control_points.ControlPointInfo × Usize) => v.val.length - x.2.val)
    (fun (x : beatmap.control_points.ControlPointInfo × Usize) => x.2.val ≤ v.val.length ∧
      cpS x.1 = ((v.val.map dpS).take x.2.val).foldl ControlPointInfo.addDifficulty init ∧
      x.1.difficulty_points.val.length ≤ x.2.val ∧ x.1.effect_points = r.effect_points)
    (fun r1 => cpS r1 = (v.val.map dpS).foldl ControlPointInfo.addDifficulty init ∧ r1.effect_points = r.effect_points)
    (by
      rintro ⟨r', i⟩ ⟨hi, hr, hrl, hro⟩
      dsimp only at hi hr hrl hro ⊢
      by_cases hlt : i.val < v.val.length
      · right
        have hlt' : i < alloc.vec.Vec.len v := by
          show i.val < (alloc.vec.Vec.len v).val; simpa using hlt
        obtain ⟨r1, hr1, hr1s, hr1t, hr1o, hr1l⟩ := beatmap.control_points.add_difficulty_refines r'
          (v.val[i.val]'hlt) (by omega)
        obtain ⟨i2, hi2, hi2v⟩ := usize_add_one i (by have := usize_ge_32; omega)
        refine ⟨(r1, i2), by simp [beatmap.control_points.deep_clone_loop1.body, hlt', vec_index_eq _ _ hlt, hr1, hi2],
          ⟨by dsimp only; omega, ?_, by dsimp only; omega, by dsimp only; rw [hr1o, hro]⟩,
          by dsimp only; omega⟩
        dsimp only
        rw [hr1s, hr, hi2v, take_succ_foldl _ _ _ _ (by simpa using hlt)]
        simp
      · left
        have hlt' : ¬ i < alloc.vec.Vec.len v := by
          show ¬ i.val < (alloc.vec.Vec.len v).val; simpa using hlt
        refine ⟨r', by simp [beatmap.control_points.deep_clone_loop1.body, hlt'], ?_, hro⟩
        rw [hr]
        have : i.val = v.val.length := by omega
        rw [this, ← List.length_map dpS, List.take_length])
    (r, i) ⟨hi, hr, hrl, rfl⟩
  obtain ⟨r1, hy, hs, ho⟩ := this
  exact ⟨r1, by unfold beatmap.control_points.deep_clone_loop1; exact hy, hs, by rw [ho]⟩

theorem dc_loop2 (v : alloc.vec.Vec beatmap.control_points.EffectPoint) (h : v.val.length < 2^31) (init : ControlPointInfo) :
    ∀ (r : beatmap.control_points.ControlPointInfo) (i : Usize), i.val ≤ v.val.length →
      cpS r = ((v.val.map epS).take i.val).foldl ControlPointInfo.addEffect init →
      r.effect_points.val.length ≤ i.val →
      ∃ r1, beatmap.control_points.deep_clone_loop2 v r i = ok r1 ∧
        cpS r1 = (v.val.map epS).foldl ControlPointInfo.addEffect init ∧ True := by
  intro r i hi hr hrl
  have := loop_ok (fun (x : beatmap.control_points.ControlPointInfo × Usize) =>
      beatmap.control_points.deep_clone_loop2.body v x.1 x.2)
    (fun (x : beatmap.control_points.ControlPointInfo × Usize) => v.val.length - x.2.val)
    (fun (x : beatmap.control_points.ControlPointInfo × Usize) => x.2.val ≤ v.val.length ∧
      cpS x.1 = ((v.val.map epS).take x.2.val).foldl ControlPointInfo.addEffect init ∧
      x.1.effect_points.val.length ≤ x.2.val ∧ x.1.timing_points = r.timing_points)
    (fun r1 => cpS r1 = (v.val.map epS).foldl ControlPointInfo.addEffect init ∧ r1.timing_points = r.timing_points)
    (by
      rintro ⟨r', i⟩ ⟨hi, hr, hrl, hro⟩
      dsimp only at hi hr hrl hro ⊢
      by_cases hlt : i.val < v.val.length
      · right
        have hlt' : i < alloc.vec.Vec.len v := by
          show i.val < (alloc.vec.Vec.len v).val; simpa using hlt
        obtain ⟨r1, hr1, hr1s, hr1t, hr1o, hr1l⟩ := beatmap.control_points.add_effect_refines r'
          (v.val[i.val]'hlt) (by omega)
        obtain ⟨i2, hi2, hi2v⟩ := usize_add_one i (by have := usize_ge_32; omega)
        refine ⟨(r1, i2), by simp [beatmap.control_points.deep_clone_loop2.body, hlt', vec_index_eq _ _ hlt, hr1, hi2],
          ⟨by dsimp only; omega, ?_, by dsimp only; omega, by dsimp only; rw [hr1t, hro]⟩,
          by dsimp only; omega⟩
        dsimp only
        rw [hr1s, hr, hi2v, take_succ_foldl _ _ _ _ (by simpa using hlt)]
        simp
      · left
        have hlt' : ¬ i < alloc.vec.Vec.len v := by
          show ¬ i.val < (alloc.vec.Vec.len v).val; simpa using hlt
        refine ⟨r', by simp [beatmap.control_points.deep_clone_loop2.body, hlt'], ?_, hro⟩
        rw [hr]
        have : i.val = v.val.length := by omega
        rw [this, ← List.length_map epS, List.take_length])
    (r, i) ⟨hi, hr, hrl, rfl⟩
  obtain ⟨r1, hy, hs, ho⟩ := this
  exact ⟨r1, by unfold beatmap.control_points.deep_clone_loop2; exact hy, hs, trivial⟩

/-- Guarded: each typed list has fewer than `2^31` points. -/
theorem beatmap.control_points.deep_clone_refines (c : beatmap.control_points.ControlPointInfo)
    (h1 : c.timing_points.val.length < 2^31) (h2 : c.difficulty_points.val.length < 2^31)
    (h3 : c.effect_points.val.length < 2^31) :
    ∃ r, beatmap.control_points.deep_clone c = ok r ∧ cpS r = (cpS c).deepClone := by
  obtain ⟨r0, hr0, hr0s⟩ := beatmap.control_points.cpi_empty_refines
  have hr0t : r0.timing_points.val = [] := by
    simp [beatmap.control_points.cpi_empty] at hr0; rw [← hr0]; rfl
  have hr0d : r0.difficulty_points.val = [] := by
    simp [beatmap.control_points.cpi_empty] at hr0; rw [← hr0]; rfl
  have hr0e : r0.effect_points.val = [] := by
    simp [beatmap.control_points.cpi_empty] at hr0; rw [← hr0]; rfl
  obtain ⟨r1, hl0, hr1s, hr1d, hr1e⟩ := dc_loop0 c h1 r0 0#usize (by simp) (by simp [hr0s]) (by simp [hr0t]) hr0d hr0e
  obtain ⟨r2, hl1, hr2s, hr2e⟩ := dc_loop1 c.difficulty_points h2 (cpS r1) r1 0#usize (by simp) (by simp) (by simp [hr1d])
  obtain ⟨r3, hl2, hr3s, -⟩ := dc_loop2 c.effect_points h3 (cpS r2) r2 0#usize (by simp) (by simp) (by simp [hr2e, hr1e])
  refine ⟨r3, by simp [beatmap.control_points.deep_clone, hr0, hl0, hl1, hl2], ?_⟩
  rw [hr3s, hr2s, hr1s]
  simp [ControlPointInfo.deepClone, cpS, List.foldl_toArray]

end OsuProofs
