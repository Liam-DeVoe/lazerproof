/-
`net::framework` part B: the `BindableNumber` state machine pieces that do not snap to the
decimal precision (`Bindable.Value` store, `RangeConstrainedBindable` set, `MinValue`/`MaxValue`).
-/
import OsuProofs.Net.Decimal3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.Framework

namespace OsuProofs
open OsuImpl

def bdS (s : net.framework.BD) : Bindable.BD := ⟨s.value, s.min_v, s.max_v, s.prec⟩
def bfS (s : net.framework.BF) : Bindable.BF := ⟨s.value, s.min_v, s.max_v, s.prec⟩
def bdRel (a : net.framework.BD) (b : Bindable.BD) : Prop := bdS a = b
def bfRel (a : net.framework.BF) (b : Bindable.BF) : Prop := bfS a = b

theorem net.framework.bd_store_refines (s : net.framework.BD) (v : F64) :
    ∃ r, net.framework.bd_store s v = ok r ∧ bdS r = (bdS s).store v := by
  by_cases h : Bindable.equalsD s.value v = true
  · exact ⟨s, by simp [net.framework.bd_store, net.framework.equals_d_refines, h], by simp [Bindable.BD.store, bdS, h]⟩
  · exact ⟨{ s with value := v }, by simp [net.framework.bd_store, net.framework.equals_d_refines, h],
      by simp [Bindable.BD.store, bdS, h]⟩
theorem net.framework.bf_store_refines (s : net.framework.BF) (v : F32) :
    ∃ r, net.framework.bf_store s v = ok r ∧ bfS r = (bfS s).store v := by
  by_cases h : Bindable.equalsF s.value v = true
  · exact ⟨s, by simp [net.framework.bf_store, net.framework.equals_f_refines, h], by simp [Bindable.BF.store, bfS, h]⟩
  · exact ⟨{ s with value := v }, by simp [net.framework.bf_store, net.framework.equals_f_refines, h],
      by simp [Bindable.BF.store, bfS, h]⟩

theorem net.framework.bd_rc_set_refines (s : net.framework.BD) (v : F64) :
    ∃ r, net.framework.bd_rc_set s v = ok r ∧ resRel bdRel r ((bdS s).rcSet v) := by
  unfold net.framework.bd_rc_set Bindable.BD.rcSet
  rw [net.framework.clamp_d_refines]
  cases hc : Bindable.clampD v s.min_v s.max_v with
  | error e => exact ⟨.Err (exnI e), by simp [exceptI, hc, bdS], by cases e <;> simp [resRel, hc, bdS, exnS, exnI]⟩
  | ok c =>
    obtain ⟨r, hr, hrv⟩ := net.framework.bd_store_refines s c
    exact ⟨.Ok r, by simp [exceptI, hc, bdS, hr], by simp only [resRel, bdRel, show (bdS s).minV = s.min_v from rfl, show (bdS s).maxV = s.max_v from rfl, hc, except_bind_ok, except_pure]; exact hrv⟩
theorem net.framework.bf_rc_set_refines (s : net.framework.BF) (v : F32) :
    ∃ r, net.framework.bf_rc_set s v = ok r ∧ resRel bfRel r ((bfS s).rcSet v) := by
  unfold net.framework.bf_rc_set Bindable.BF.rcSet
  rw [net.framework.clamp_f_refines]
  cases hc : Bindable.clampF v s.min_v s.max_v with
  | error e => exact ⟨.Err (exnI e), by simp [exceptI, hc, bfS], by cases e <;> simp [resRel, hc, bfS, exnS, exnI]⟩
  | ok c =>
    obtain ⟨r, hr, hrv⟩ := net.framework.bf_store_refines s c
    exact ⟨.Ok r, by simp [exceptI, hc, bfS, hr], by simp only [resRel, bfRel, show (bfS s).minV = s.min_v from rfl, show (bfS s).maxV = s.max_v from rfl, hc, except_bind_ok, except_pure]; exact hrv⟩

theorem net.framework.bd_set_min_refines (s : net.framework.BD) (m : F64) :
    ∃ r, net.framework.bd_set_min s m = ok r ∧ resRel bdRel r ((bdS s).setMin m) := by
  unfold net.framework.bd_set_min Bindable.BD.setMin
  by_cases h : Bindable.equalsD m s.min_v = true
  · exact ⟨.Ok s, by simp [net.framework.equals_d_refines, h], by simp [resRel, bdRel, bdS, h]⟩
  · obtain ⟨r, hr, hrv⟩ := net.framework.bd_rc_set_refines { s with min_v := m } s.value
    exact ⟨r, by simp [net.framework.equals_d_refines, h, hr], by simpa [bdS, h] using hrv⟩
theorem net.framework.bd_set_max_refines (s : net.framework.BD) (m : F64) :
    ∃ r, net.framework.bd_set_max s m = ok r ∧ resRel bdRel r ((bdS s).setMax m) := by
  unfold net.framework.bd_set_max Bindable.BD.setMax
  by_cases h : Bindable.equalsD m s.max_v = true
  · exact ⟨.Ok s, by simp [net.framework.equals_d_refines, h], by simp [resRel, bdRel, bdS, h]⟩
  · obtain ⟨r, hr, hrv⟩ := net.framework.bd_rc_set_refines { s with max_v := m } s.value
    exact ⟨r, by simp [net.framework.equals_d_refines, h, hr], by simpa [bdS, h] using hrv⟩
theorem net.framework.bf_set_min_refines (s : net.framework.BF) (m : F32) :
    ∃ r, net.framework.bf_set_min s m = ok r ∧ resRel bfRel r ((bfS s).setMin m) := by
  unfold net.framework.bf_set_min Bindable.BF.setMin
  by_cases h : Bindable.equalsF m s.min_v = true
  · exact ⟨.Ok s, by simp [net.framework.equals_f_refines, h], by simp [resRel, bfRel, bfS, h]⟩
  · obtain ⟨r, hr, hrv⟩ := net.framework.bf_rc_set_refines { s with min_v := m } s.value
    exact ⟨r, by simp [net.framework.equals_f_refines, h, hr], by simpa [bfS, h] using hrv⟩
theorem net.framework.bf_set_max_refines (s : net.framework.BF) (m : F32) :
    ∃ r, net.framework.bf_set_max s m = ok r ∧ resRel bfRel r ((bfS s).setMax m) := by
  unfold net.framework.bf_set_max Bindable.BF.setMax
  by_cases h : Bindable.equalsF m s.max_v = true
  · exact ⟨.Ok s, by simp [net.framework.equals_f_refines, h], by simp [resRel, bfRel, bfS, h]⟩
  · obtain ⟨r, hr, hrv⟩ := net.framework.bf_rc_set_refines { s with max_v := m } s.value
    exact ⟨r, by simp [net.framework.equals_f_refines, h, hr], by simpa [bfS, h] using hrv⟩

end OsuProofs
