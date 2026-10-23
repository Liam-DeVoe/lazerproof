/-
`net::framework` part C: `BindableNumber` decimal snapping (`snap_d`/`snap_f`) and the setters
and constructors built on it (`setValue`, `Precision`, `create`, `init`, `set_double/float`).
-/
import OsuProofs.Net.DecimalValid
import OsuProofs.Net.FrameworkB
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

theorem resRel_cases {α β : Type} {R : α → β → Prop} {r : core.result.Result α net.basic.NetExn}
    {e : Except NetExn β} (h : resRel R r e) :
    (∃ a b, r = .Ok a ∧ e = .ok b ∧ R a b) ∨ (∃ x, r = .Err x ∧ e = .error (exnS x)) := by
  cases r <;> cases e <;> simp [resRel] at h
  · exact Or.inl ⟨_, _, rfl, rfl, h⟩
  · exact Or.inr ⟨_, rfl, by rw [h]⟩

theorem net.framework.snap_d_refines (lo hi p v : F64) :
    ∃ r, net.framework.snap_d lo hi p v = ok r ∧ resRel (· = ·) r (Bindable.snapD lo hi p v) := by
  unfold net.framework.snap_d Bindable.snapD
  obtain ⟨r0, hr0, hrr0⟩ := net.decimal.create_truncating_f64_refines p
  rw [hr0, bind_ok]
  rcases resRel_cases hrr0 with ⟨v1, dp, rfl, hdp, hv1⟩ | ⟨x, rfl, hdp⟩
  · dsimp only; rw [hdp, except_bind_ok]
    have hdv := createTruncatingF64_valid p dp hdp
    simp only [decRel] at hv1
    rw [net.decimal.is_positive_refines, bind_ok, hv1]
    by_cases hpos : dp.isPositive = true
    · rw [if_pos hpos, if_pos hpos, net.framework.clamp_d_refines, bind_ok]
      cases hc : Bindable.clampD v lo hi with
      | error e => exact ⟨.Err (exnI e), by simp [exceptI], by simp [resRel, exnS_I]⟩
      | ok c =>
        simp only [exceptI, except_bind_ok, id]
        obtain ⟨r2, hr2, hrr2⟩ := net.decimal.create_truncating_f64_refines c
        rw [hr2, bind_ok]
        rcases resRel_cases hrr2 with ⟨v3, a, rfl, ha, hv3⟩ | ⟨x, rfl, ha⟩
        · dsimp only; rw [ha, except_bind_ok]
          have hav := createTruncatingF64_valid c a ha
          simp only [decRel] at hv3
          obtain ⟨r3, hr3, hrr3⟩ := net.decimal.div_refines v3 v1
            (by have := hav.1; rw [← hv3] at this; exact this) (by have := hdv.1; rw [← hv1] at this; exact this)
            (by have := hav.2; rw [← hv3] at this; exact this) (by have := hdv.2; rw [← hv1] at this; exact this)
          rw [hr3, bind_ok]
          rw [hv3, hv1] at hrr3
          rcases resRel_cases hrr3 with ⟨v4, q, rfl, hq, hv4⟩ | ⟨x, rfl, hq⟩
          · dsimp only; rw [hq, except_bind_ok]
            have hqv := div_valid a dp hav hdv q hq
            simp only [decRel] at hv4
            obtain ⟨nd, hnd, hndv⟩ := net.decimal.round_refines v4 (by have := hqv.2; rw [← hv4] at this; simp [decS] at this; omega)
            rw [hnd, bind_ok]
            rw [hv4] at hndv
            have hrv := round_valid q hqv
            obtain ⟨r4, hr4, hrr4⟩ := net.decimal.mul_refines nd v1
              (by have := hrv.1; rw [← hndv] at this; exact this) (by have := hdv.1; rw [← hv1] at this; exact this)
              (by have := hrv.2; rw [← hndv] at this; exact this) (by have := hdv.2; rw [← hv1] at this; exact this)
            rw [hr4, bind_ok]
            rw [hndv, hv1] at hrr4
            rcases resRel_cases hrr4 with ⟨v5, m, rfl, hm, hv5⟩ | ⟨x, rfl, hm⟩
            · dsimp only; rw [hm, except_bind_ok]
              have hms := mul_scale _ _ hrv hdv m hm
              simp only [decRel] at hv5
              rw [net.decimal.to_f64_refines v5 (by have := hms; rw [← hv5] at this; exact this), bind_ok, hv5]
              exact ⟨_, rfl, rfl⟩
            · dsimp only; rw [hm, except_bind_error]; exact ⟨_, rfl, rfl⟩
          · dsimp only; rw [hq, except_bind_error]; exact ⟨_, rfl, rfl⟩
        · dsimp only; rw [ha, except_bind_error]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg hpos, if_neg hpos]
      exact ⟨_, rfl, rfl⟩
  · dsimp only; rw [hdp, except_bind_error]; exact ⟨_, rfl, rfl⟩

theorem net.framework.snap_f_refines (lo hi p v : F32) :
    ∃ r, net.framework.snap_f lo hi p v = ok r ∧ resRel (· = ·) r (Bindable.snapF lo hi p v) := by
  unfold net.framework.snap_f Bindable.snapF
  obtain ⟨r0, hr0, hrr0⟩ := net.decimal.create_truncating_f32_refines p
  rw [hr0, bind_ok]
  rcases resRel_cases hrr0 with ⟨v1, dp, rfl, hdp, hv1⟩ | ⟨x, rfl, hdp⟩
  · dsimp only; rw [hdp, except_bind_ok]
    have hdv := createTruncatingF32_valid p dp hdp
    simp only [decRel] at hv1
    rw [net.decimal.is_positive_refines, bind_ok, hv1]
    by_cases hpos : dp.isPositive = true
    · rw [if_pos hpos, if_pos hpos, net.framework.clamp_f_refines, bind_ok]
      cases hc : Bindable.clampF v lo hi with
      | error e => exact ⟨.Err (exnI e), by simp [exceptI], by simp [resRel, exnS_I]⟩
      | ok c =>
        simp only [exceptI, except_bind_ok, id]
        obtain ⟨r2, hr2, hrr2⟩ := net.decimal.create_truncating_f32_refines c
        rw [hr2, bind_ok]
        rcases resRel_cases hrr2 with ⟨v3, a, rfl, ha, hv3⟩ | ⟨x, rfl, ha⟩
        · dsimp only; rw [ha, except_bind_ok]
          have hav := createTruncatingF32_valid c a ha
          simp only [decRel] at hv3
          obtain ⟨r3, hr3, hrr3⟩ := net.decimal.div_refines v3 v1
            (by have := hav.1; rw [← hv3] at this; exact this) (by have := hdv.1; rw [← hv1] at this; exact this)
            (by have := hav.2; rw [← hv3] at this; exact this) (by have := hdv.2; rw [← hv1] at this; exact this)
          rw [hr3, bind_ok]
          rw [hv3, hv1] at hrr3
          rcases resRel_cases hrr3 with ⟨v4, q, rfl, hq, hv4⟩ | ⟨x, rfl, hq⟩
          · dsimp only; rw [hq, except_bind_ok]
            have hqv := div_valid a dp hav hdv q hq
            simp only [decRel] at hv4
            obtain ⟨nd, hnd, hndv⟩ := net.decimal.round_refines v4 (by have := hqv.2; rw [← hv4] at this; simp [decS] at this; omega)
            rw [hnd, bind_ok]
            rw [hv4] at hndv
            have hrv := round_valid q hqv
            obtain ⟨r4, hr4, hrr4⟩ := net.decimal.mul_refines nd v1
              (by have := hrv.1; rw [← hndv] at this; exact this) (by have := hdv.1; rw [← hv1] at this; exact this)
              (by have := hrv.2; rw [← hndv] at this; exact this) (by have := hdv.2; rw [← hv1] at this; exact this)
            rw [hr4, bind_ok]
            rw [hndv, hv1] at hrr4
            rcases resRel_cases hrr4 with ⟨v5, m, rfl, hm, hv5⟩ | ⟨x, rfl, hm⟩
            · dsimp only; rw [hm, except_bind_ok]
              have hms := mul_scale _ _ hrv hdv m hm
              simp only [decRel] at hv5
              rw [net.decimal.to_f32_refines v5 (by have := hms; rw [← hv5] at this; exact this), bind_ok, hv5]
              exact ⟨_, rfl, rfl⟩
            · dsimp only; rw [hm, except_bind_error]; exact ⟨_, rfl, rfl⟩
          · dsimp only; rw [hq, except_bind_error]; exact ⟨_, rfl, rfl⟩
        · dsimp only; rw [ha, except_bind_error]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg hpos, if_neg hpos]
      exact ⟨_, rfl, rfl⟩
  · dsimp only; rw [hdp, except_bind_error]; exact ⟨_, rfl, rfl⟩

theorem net.framework.bd_set_value_refines (s : net.framework.BD) (v : F64) :
    ∃ r, net.framework.bd_set_value s v = ok r ∧ resRel bdRel r ((bdS s).setValue v) := by
  unfold net.framework.bd_set_value Bindable.BD.setValue
  obtain ⟨r, hr, hrr⟩ := net.framework.snap_d_refines s.min_v s.max_v s.prec v
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only
    rw [show (bdS s).minV = s.min_v from rfl, show (bdS s).maxV = s.max_v from rfl,
      show (bdS s).prec = s.prec from rfl, hw, except_bind_ok, ← hv]
    exact net.framework.bd_rc_set_refines s v1
  · dsimp only
    rw [show (bdS s).minV = s.min_v from rfl, show (bdS s).maxV = s.max_v from rfl,
      show (bdS s).prec = s.prec from rfl, hw, except_bind_error]
    exact ⟨_, rfl, rfl⟩

theorem net.framework.bd_set_precision_refines (s : net.framework.BD) (p : F64) :
    ∃ r, net.framework.bd_set_precision s p = ok r ∧ resRel bdRel r ((bdS s).setPrecision p) := by
  unfold net.framework.bd_set_precision Bindable.BD.setPrecision
  simp only [float.F64.eq, bind_ok, show (bdS s).prec = s.prec from rfl]
  by_cases h1 : (p == s.prec) = true
  · rw [if_pos h1, if_pos h1]; exact ⟨_, rfl, rfl⟩
  · rw [if_neg h1, if_neg h1]
    have h0 : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp [float.F64.from_bits] <;> decide
    rw [h0, bind_ok, float.F64.le, bind_ok]
    by_cases h2 : p ≤ 0
    · rw [if_pos (decide_eq_true h2), if_pos h2]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg (by simpa using h2), if_neg h2]
      exact net.framework.bd_set_value_refines { s with prec := p } s.value

theorem fw_DBL_MAX : net.framework.DBL_MAX = ok Bindable.dblMax := by
  unfold net.framework.DBL_MAX Bindable.dblMax; simp [float.F64.from_bits] <;> decide
theorem fw_DBL_EPS : net.framework.DBL_EPS = ok Bindable.dblEps := by
  unfold net.framework.DBL_EPS Bindable.dblEps; simp [float.F64.from_bits] <;> decide

theorem net.framework.bd_create_refines (d : F64) :
    ∃ r, net.framework.bd_create d = ok r ∧ resRel bdRel r (Bindable.BD.create d) := by
  unfold net.framework.bd_create Bindable.BD.create
  rw [fw_DBL_MAX, bind_ok, float.F64.neg, bind_ok, fw_DBL_EPS, bind_ok]
  obtain ⟨r, hr, hrr⟩ := net.framework.bd_rc_set_refines ⟨d, -Bindable.dblMax, Bindable.dblMax, Bindable.dblEps⟩ d
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only
    rw [show (⟨d, -Bindable.dblMax, Bindable.dblMax, Bindable.dblEps⟩ : Bindable.BD) =
      bdS ⟨d, -Bindable.dblMax, Bindable.dblMax, Bindable.dblEps⟩ from rfl, hw, except_bind_ok]
    simp only [bdRel] at hv
    rw [← hv]
    exact net.framework.bd_set_value_refines v1 v1.value
  · dsimp only
    rw [show (⟨d, -Bindable.dblMax, Bindable.dblMax, Bindable.dblEps⟩ : Bindable.BD) =
      bdS ⟨d, -Bindable.dblMax, Bindable.dblMax, Bindable.dblEps⟩ from rfl, hw, except_bind_error]
    exact ⟨_, rfl, rfl⟩

theorem net.framework.bd_init_refines (d lo hi p : F64) :
    ∃ r, net.framework.bd_init d lo hi p = ok r ∧ resRel bdRel r (Bindable.BD.init d lo hi p) := by
  unfold net.framework.bd_init Bindable.BD.init
  obtain ⟨r, hr, hrr⟩ := net.framework.bd_create_refines d
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only; rw [hw, except_bind_ok]; simp only [bdRel] at hv; rw [← hv]
    obtain ⟨r1, hr1, hrr1⟩ := net.framework.bd_set_min_refines v1 lo
    rw [hr1, bind_ok]
    rcases resRel_cases hrr1 with ⟨v2, w2, rfl, hw2, hv2⟩ | ⟨x, rfl, hw2⟩
    · dsimp only; rw [hw2, except_bind_ok]; simp only [bdRel] at hv2; rw [← hv2]
      obtain ⟨r2, hr2, hrr2⟩ := net.framework.bd_set_max_refines v2 hi
      rw [hr2, bind_ok]
      rcases resRel_cases hrr2 with ⟨v3, w3, rfl, hw3, hv3⟩ | ⟨x, rfl, hw3⟩
      · dsimp only; rw [hw3, except_bind_ok]; simp only [bdRel] at hv3; rw [← hv3]
        exact net.framework.bd_set_precision_refines v3 p
      · dsimp only; rw [hw3, except_bind_error]; exact ⟨_, rfl, rfl⟩
    · dsimp only; rw [hw2, except_bind_error]; exact ⟨_, rfl, rfl⟩
  · dsimp only; rw [hw, except_bind_error]; exact ⟨_, rfl, rfl⟩

theorem net.framework.set_double_refines (lo hi p v : F64) :
    ∃ r, net.framework.set_double lo hi p v = ok r ∧ resRel (· = ·) r (Bindable.setDouble lo hi p v) := by
  unfold net.framework.set_double Bindable.setDouble
  obtain ⟨r, hr, hrr⟩ := net.framework.snap_d_refines lo hi p v
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only; rw [hw, except_bind_ok, net.framework.clamp_d_refines, ← hv]
    cases Bindable.clampD v1 lo hi with
    | error e => exact ⟨_, rfl, by simp [exceptI, resRel, exnS_I]⟩
    | ok c => exact ⟨_, rfl, rfl⟩
  · dsimp only; rw [hw, except_bind_error]; exact ⟨_, rfl, rfl⟩

theorem net.framework.bf_set_value_refines (s : net.framework.BF) (v : F32) :
    ∃ r, net.framework.bf_set_value s v = ok r ∧ resRel bfRel r ((bfS s).setValue v) := by
  unfold net.framework.bf_set_value Bindable.BF.setValue
  obtain ⟨r, hr, hrr⟩ := net.framework.snap_f_refines s.min_v s.max_v s.prec v
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only
    rw [show (bfS s).minV = s.min_v from rfl, show (bfS s).maxV = s.max_v from rfl,
      show (bfS s).prec = s.prec from rfl, hw, except_bind_ok, ← hv]
    exact net.framework.bf_rc_set_refines s v1
  · dsimp only
    rw [show (bfS s).minV = s.min_v from rfl, show (bfS s).maxV = s.max_v from rfl,
      show (bfS s).prec = s.prec from rfl, hw, except_bind_error]
    exact ⟨_, rfl, rfl⟩

theorem net.framework.bf_set_precision_refines (s : net.framework.BF) (p : F32) :
    ∃ r, net.framework.bf_set_precision s p = ok r ∧ resRel bfRel r ((bfS s).setPrecision p) := by
  unfold net.framework.bf_set_precision Bindable.BF.setPrecision
  simp only [float.F32.eq, bind_ok, show (bfS s).prec = s.prec from rfl]
  by_cases h1 : (p == s.prec) = true
  · rw [if_pos h1, if_pos h1]; exact ⟨_, rfl, rfl⟩
  · rw [if_neg h1, if_neg h1]
    have h0 : float.F32.from_bits 0#u32 = ok (0 : F32) := by simp [float.F32.from_bits] <;> decide
    rw [h0, bind_ok, float.F32.le, bind_ok]
    by_cases h2 : p ≤ 0
    · rw [if_pos (decide_eq_true h2), if_pos h2]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg (by simpa using h2), if_neg h2]
      exact net.framework.bf_set_value_refines { s with prec := p } s.value

theorem fw_FLT_MAX : net.framework.FLT_MAX = ok Bindable.fltMax := by
  unfold net.framework.FLT_MAX Bindable.fltMax; simp [float.F32.from_bits] <;> decide
theorem fw_FLT_EPS : net.framework.FLT_EPS = ok Bindable.fltEps := by
  unfold net.framework.FLT_EPS Bindable.fltEps; simp [float.F32.from_bits] <;> decide

theorem net.framework.bf_create_refines (d : F32) :
    ∃ r, net.framework.bf_create d = ok r ∧ resRel bfRel r (Bindable.BF.create d) := by
  unfold net.framework.bf_create Bindable.BF.create
  rw [fw_FLT_MAX, bind_ok, float.F32.neg, bind_ok, fw_FLT_EPS, bind_ok]
  obtain ⟨r, hr, hrr⟩ := net.framework.bf_rc_set_refines ⟨d, -Bindable.fltMax, Bindable.fltMax, Bindable.fltEps⟩ d
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only
    rw [show (⟨d, -Bindable.fltMax, Bindable.fltMax, Bindable.fltEps⟩ : Bindable.BF) =
      bfS ⟨d, -Bindable.fltMax, Bindable.fltMax, Bindable.fltEps⟩ from rfl, hw, except_bind_ok]
    simp only [bfRel] at hv
    rw [← hv]
    exact net.framework.bf_set_value_refines v1 v1.value
  · dsimp only
    rw [show (⟨d, -Bindable.fltMax, Bindable.fltMax, Bindable.fltEps⟩ : Bindable.BF) =
      bfS ⟨d, -Bindable.fltMax, Bindable.fltMax, Bindable.fltEps⟩ from rfl, hw, except_bind_error]
    exact ⟨_, rfl, rfl⟩

theorem net.framework.bf_init_refines (d lo hi p : F32) :
    ∃ r, net.framework.bf_init d lo hi p = ok r ∧ resRel bfRel r (Bindable.BF.init d lo hi p) := by
  unfold net.framework.bf_init Bindable.BF.init
  obtain ⟨r, hr, hrr⟩ := net.framework.bf_create_refines d
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only; rw [hw, except_bind_ok]; simp only [bfRel] at hv; rw [← hv]
    obtain ⟨r1, hr1, hrr1⟩ := net.framework.bf_set_min_refines v1 lo
    rw [hr1, bind_ok]
    rcases resRel_cases hrr1 with ⟨v2, w2, rfl, hw2, hv2⟩ | ⟨x, rfl, hw2⟩
    · dsimp only; rw [hw2, except_bind_ok]; simp only [bfRel] at hv2; rw [← hv2]
      obtain ⟨r2, hr2, hrr2⟩ := net.framework.bf_set_max_refines v2 hi
      rw [hr2, bind_ok]
      rcases resRel_cases hrr2 with ⟨v3, w3, rfl, hw3, hv3⟩ | ⟨x, rfl, hw3⟩
      · dsimp only; rw [hw3, except_bind_ok]; simp only [bfRel] at hv3; rw [← hv3]
        exact net.framework.bf_set_precision_refines v3 p
      · dsimp only; rw [hw3, except_bind_error]; exact ⟨_, rfl, rfl⟩
    · dsimp only; rw [hw2, except_bind_error]; exact ⟨_, rfl, rfl⟩
  · dsimp only; rw [hw, except_bind_error]; exact ⟨_, rfl, rfl⟩

theorem net.framework.set_float_refines (lo hi p v : F32) :
    ∃ r, net.framework.set_float lo hi p v = ok r ∧ resRel (· = ·) r (Bindable.setFloat lo hi p v) := by
  unfold net.framework.set_float Bindable.setFloat
  obtain ⟨r, hr, hrr⟩ := net.framework.snap_f_refines lo hi p v
  rw [hr, bind_ok]
  rcases resRel_cases hrr with ⟨v1, w, rfl, hw, hv⟩ | ⟨x, rfl, hw⟩
  · dsimp only; rw [hw, except_bind_ok, net.framework.clamp_f_refines, ← hv]
    cases Bindable.clampF v1 lo hi with
    | error e => exact ⟨_, rfl, by simp [exceptI, resRel, exnS_I]⟩
    | ok c => exact ⟨_, rfl, rfl⟩
  · dsimp only; rw [hw, except_bind_error]; exact ⟨_, rfl, rfl⟩

end OsuProofs
