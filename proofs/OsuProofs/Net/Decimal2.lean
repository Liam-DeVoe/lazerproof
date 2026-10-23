/-
`net::decimal` part 2: decimal ↔ binary-float conversions, `CreateTruncating`, the 192-bit
product helpers, `ScaleResult`, multiplication and division.
-/
import OsuProofs.Net.Decimal
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- Guarded: `k ≤ 28` (the spec array has 29 entries; the Rust returns NaN beyond). -/
theorem net.decimal.double_powers10_refines (k : U32) (hk : k.val ≤ 28) :
    net.decimal.double_powers10 k = ok NetDecimal.doublePowers10[k.val]! := by
  unfold net.decimal.double_powers10
  split
  all_goals first
    | (simp only [float.F64.from_bits]; congr 1; decide +kernel)
    | skip
  exfalso
  simp only [UScalar.eq_equiv_bv_eq, ← BitVec.toNat_inj] at *
  have hv : k.val = k.bv.toNat := rfl
  simp at *
  omega

@[simp] theorem dec_DS2TO64 : net.decimal.DS2TO64 = ok NetDecimal.ds2to64 := by
  simp [net.decimal.DS2TO64, NetDecimal.ds2to64]

/-- Guarded: `scale ≤ 28`. -/
theorem net.decimal.to_f64_refines (d : net.decimal.NetDecimal) (hs : d.scale.val ≤ 28) :
    net.decimal.to_f64 d = ok (NetDecimal.toF64 (decS d)) := by
  have hm := u128_bounds d.mant
  obtain ⟨hi, hhi, hhiv⟩ := u128_shr64 d.mant
  have hlo := u128_and_mask64 d.mant
  have c1 : (UScalar.cast .U64 (d.mant &&& 18446744073709551615#u128)).val = d.mant.val % 2^64 := by
    rw [UScalar.cast_val_eq, hlo]; simp
  have c2 : (UScalar.cast .U64 hi).val = d.mant.val >>> 64 := by
    rw [UScalar.cast_val_eq, hhiv, Nat.shiftRight_eq_div_pow]; simp; omega
  have e1 : F64.ofUInt64 (UInt64.ofNat (d.mant.val % 2^64)) = F64.ofInt (d.mant.val % 2^64 : Nat) := by
    simp [F64.ofUInt64]
  unfold net.decimal.to_f64 NetDecimal.toF64
  simp only [lift, bind_ok, hhi, float.F64.from_u64, c1, c2, dec_DS2TO64, float.F64.mul, float.F64.add,
    net.decimal.double_powers10_refines _ hs, float.F64.div, decS, e1]
  cases d.neg <;> simp [float.F64.neg]

theorem net.decimal.to_f32_refines (d : net.decimal.NetDecimal) (hs : d.scale.val ≤ 28) :
    net.decimal.to_f32 d = ok (NetDecimal.toF32 (decS d)) := by
  simp [net.decimal.to_f32, NetDecimal.toF32, net.decimal.to_f64_refines d hs]

def ffStep (r : Nat × Nat × Nat) (k : Nat) : Nat × Nat × Nat :=
  if r.2.2 ≥ k && r.1 % 10 ^ k == 0 then (r.1 / 10 ^ k, r.2.1 - k, r.2.2 - k) else r

theorem ff_loop_spec (steps : Slice U32) (hst : ∀ k ∈ steps.val, k.val ≤ 9) (m : U128) (p lim : U32)
    (hlp : lim.val ≤ p.val) :
    ∃ m' p', net.decimal.finish_from_r_loop steps m p lim 0#usize = ok (m', p') ∧
      (m'.val, p'.val) = (((steps.val.map (·.val)).foldl ffStep (m.val, p.val, lim.val)).1,
        ((steps.val.map (·.val)).foldl ffStep (m.val, p.val, lim.val)).2.1) := by
  let T := (steps.val.map (·.val)).foldl ffStep (m.val, p.val, lim.val)
  have hl := Slice.length_ineq steps
  unfold net.decimal.finish_from_r_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : U128 × U32 × U32 × Usize) =>
      net.decimal.finish_from_r_loop.body steps x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x => steps.val.length - x.2.2.2.val)
    (fun x => x.2.2.1.val ≤ x.2.1.val ∧ x.2.2.2.val ≤ steps.val.length ∧
      ((steps.val.map (·.val)).drop x.2.2.2.val).foldl ffStep (x.1.val, x.2.1.val, x.2.2.1.val) = T)
    (fun y => (y.1.val, y.2.val) = (T.1, T.2.1))
    (by
      rintro ⟨m, p, lim, i⟩ ⟨hlp, hil, hT⟩
      dsimp only at hlp hil hT ⊢
      by_cases hlt : i < Slice.len steps
      · right
        have hlt' : i.val < steps.val.length := by simpa using hlt
        have hk := hst _ (List.getElem_mem hlt')
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have hd : (steps.val.map (·.val)).drop i.val = (steps.val[i.val]'hlt').val :: (steps.val.map (·.val)).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hlt')]; simp
        rw [hd, List.foldl_cons] at hT
        generalize hkk : steps.val[i.val]'hlt' = k at hk hT
        have hidx : Slice.index_usize steps i = ok k := by rw [← hkk]; exact index_eq steps i hlt'
        by_cases c1 : k.val ≤ lim.val
        · have c1' : lim >= k := c1
          obtain ⟨pw, hpw, hpwv⟩ := net.decimal.pow10_refines k (by omega)
          have hpos : 0 < pw.val := by rw [hpwv]; exact Nat.pow_pos (by decide)
          obtain ⟨rm, hrm, hrmv⟩ := eq_ok_of_spec (U128.rem_spec m (y := pw) (by omega))
          by_cases c2 : m.val % 10 ^ k.val = 0
          · have c2' : rm = 0#u128 := by rw [uscalar_eq_val]; simp [hrmv, hpwv, c2]
            obtain ⟨m2, hm2, hm2v⟩ := eq_ok_of_spec (U128.div_spec m (y := pw) (by omega))
            obtain ⟨p2, hp2, hp2v, _⟩ := eq_ok_of_spec (U32.sub_spec (x := p) (y := k) (by omega))
            obtain ⟨l2, hl2, hl2v, _⟩ := eq_ok_of_spec (U32.sub_spec (x := lim) (y := k) (by omega))
            refine ⟨(m2, p2, l2, i1), by simp [net.decimal.finish_from_r_loop.body, hlt, hidx, c1, c1', hpw, hrm, c2',
              hm2, hp2, hl2, hi1], ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
            dsimp only; rw [hi1v, ← hT]
            simp [ffStep, c1, c2, hm2v, hp2v, hl2v, hpwv]
          · have c2' : ¬ rm = 0#u128 := by rw [uscalar_eq_val]; simp [hrmv, hpwv, c2]
            refine ⟨(m, p, lim, i1), by simp [net.decimal.finish_from_r_loop.body, hlt, hidx, c1, c1', hpw, hrm, c2', hi1],
              ⟨hlp, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
            dsimp only; rw [hi1v, ← hT]
            simp [ffStep, c1, c2]
        · have c1' : ¬ lim >= k := c1
          refine ⟨(m, p, lim, i1), by simp [net.decimal.finish_from_r_loop.body, hlt, hidx, c1, c1', hi1],
            ⟨hlp, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          dsimp only; rw [hi1v, ← hT]
          simp [ffStep, c1]
      · left
        have : i.val = steps.val.length := by
          have : ¬ i.val < steps.val.length := by simpa using hlt
          omega
        refine ⟨(m, p), by simp [net.decimal.finish_from_r_loop.body, hlt], ?_⟩
        rw [this] at hT
        simp at hT
        rw [← hT])
    (m, p, lim, 0#usize) ⟨hlp, by simp, by simp [T]⟩
  obtain ⟨m', p'⟩ := y
  exact ⟨m', p', hy, hq⟩

def decRel (d : net.decimal.NetDecimal) (d' : NetDecimal) : Prop := decS d = d'

theorem net.decimal.finish_from_r_refines (neg : Bool) (mant : U128) (power : I64) (ms : U32) (steps : Slice U32)
    (hst : ∀ k ∈ steps.val, k.val ≤ 9) (hp : -38 ≤ power.val ∧ power.val < 2^31)
    (hm : power.val < 0 → mant.val * 10 ^ power.val.natAbs < 2^128) :
    ∃ r, net.decimal.finish_from_r neg mant power ms steps = ok r ∧
      resRel decRel r (NetDecimal.finishFromR neg mant.val power.val ms.val (steps.val.map (·.val))) := by
  unfold net.decimal.finish_from_r NetDecimal.finishFromR
  by_cases hneg : power.val < 0
  · have hneg' : power < 0#i64 := hneg
    obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step power (by simp [IScalar.min, I64.min_eq]; omega))
    have hc : (IScalar.hcast .U32 q).val = power.val.natAbs := by
      rw [IScalar.hcast_val_eq, hqv]; simp; omega
    obtain ⟨pw, hpw, hpwv⟩ := net.decimal.pow10_refines (IScalar.hcast .U32 q) (by rw [hc]; omega)
    rw [hc] at hpwv
    obtain ⟨v, hv, hvv⟩ := eq_ok_of_spec (U128.mul_spec (x := mant) (y := pw) (by
      simp [U128.max_eq]; rw [hpwv]; have := hm hneg; omega))
    try simp at hvv
    by_cases hov : mant.val * 10 ^ power.val.natAbs ≥ NetDecimal.two96
    · have hov' : v >= (⟨BitVec.ofNat 128 (2^96)⟩ : U128) := by
        show (⟨BitVec.ofNat 128 (2^96)⟩ : U128).val ≤ v.val; rw [TWO96_val, hvv, hpwv]; exact hov
      have h2 := hov'; simp at h2
      exact ⟨.Err .Overflow, by simp [hneg', HNeg.hNeg, hq, lift, hpw, hv, TWO96_eq, h2],
        by simp [hneg, hov, resRel, exnS]⟩
    · have hov' : ¬ v >= (⟨BitVec.ofNat 128 (2^96)⟩ : U128) := by
        show ¬ (⟨BitVec.ofNat 128 (2^96)⟩ : U128).val ≤ v.val; rw [TWO96_val, hvv, hpwv]; exact hov
      have h2 := hov'; simp at h2
      exact ⟨.Ok ⟨neg, v, 0#u32⟩, by simp [hneg', HNeg.hNeg, hq, lift, hpw, hv, TWO96_eq, h2],
        by simp [hneg, hov, resRel, decRel, decS, hvv, hpwv]⟩
  · have hneg' : ¬ power < 0#i64 := hneg
    have hc : (IScalar.hcast .U32 power).val = power.val.toNat := by
      rw [IScalar.hcast_val_eq]; simp; omega
    let p := IScalar.hcast .U32 power
    let lim : U32 := if p < ms then p else ms
    have hlim : lim.val = Nat.min p.val ms.val := by
      simp only [lim]; split
      · rename_i h; have : p.val < ms.val := h; simp [Nat.min_def]; omega
      · rename_i h; have : ¬ p.val < ms.val := h; simp [Nat.min_def]; omega
    obtain ⟨m', p', hl, hlv⟩ := ff_loop_spec steps hst mant p lim (by rw [hlim]; exact Nat.min_le_left _ _)
    have hlimE : (if IScalar.hcast .U32 power < ms then ok (IScalar.hcast .U32 power) else ok ms) = ok lim := by
      simp only [lim, p]; split <;> rfl
    have hl' : net.decimal.finish_from_r_loop steps mant (IScalar.hcast .U32 power) lim 0#usize = ok (m', p') := hl
    refine ⟨.Ok ⟨neg, m', p'⟩, by simp only [hneg', ite_false, lift, bind_ok, hlimE, hl']; rfl, ?_⟩
    have hf : (fun (x : Nat × Nat × Nat) (k : Nat) =>
        match x with
        | (m, p, lim) => if (decide (lim ≥ k) && m % 10 ^ k == 0) = true then (m / 10 ^ k, p - k, lim - k) else (m, p, lim))
        = ffStep := by
      funext x k; obtain ⟨a, b, c⟩ := x; rfl
    simp only [hneg, ite_false, resRel, decRel, decS]
    rw [hf]
    have hp' : p.val = power.val.toNat := hc
    rw [hlim, hp'] at hlv
    simp only [Prod.mk.injEq] at hlv
    rw [hlv.1, hlv.2]

@[simp] theorem dec_P1E15 : net.decimal.P1E15 = ok NetDecimal.p1e15 := by
  simp [net.decimal.P1E15, NetDecimal.p1e15] <;> decide
@[simp] theorem dec_P1E14 : net.decimal.P1E14 = ok NetDecimal.p1e14 := by
  simp [net.decimal.P1E14, NetDecimal.p1e14] <;> decide
@[simp] theorem dec_F64TEN : net.decimal.F64TEN = ok NetDecimal.f64ten := by
  simp [net.decimal.F64TEN, NetDecimal.f64ten] <;> decide
@[simp] theorem dec_F64_ZERO : net.decimal.F64_ZERO = ok (0 : F64) := by
  simp [net.decimal.F64_ZERO] <;> decide
@[simp] theorem dec_ZERO : decS net.decimal.ZERO = NetDecimal.zero := by
  simp [net.decimal.ZERO, decS, NetDecimal.zero]

theorem steps_r8 : ((Std.Array.to_slice net.decimal.STEPS_R8).val.map (·.val)) = [8, 4, 2, 1] := by
  simp [net.decimal.STEPS_R8, Std.Array.to_slice, Std.Array.make]
theorem steps_r8_le : ∀ k ∈ (Std.Array.to_slice net.decimal.STEPS_R8).val, k.val ≤ 9 := by
  simp [net.decimal.STEPS_R8, Std.Array.to_slice, Std.Array.make]

/-- The exponent field of a non-NaN double through the Rust bit ops. -/
theorem f64_exp_bits (input : F64) (h : input.isNaN = false) :
    ∃ e : I64, (∀ {β : Type} (f : I64 → Result β),
      (do let i ← float.F64.to_bits input
          let i1 ← i >>> 52#i32
          let i2 ← lift (i1 &&& 2047#u64)
          let e ← lift (UScalar.hcast .I64 i2)
          f e) = f e) ∧
      e.val = (((input.toBits >>> 52) &&& 0x7FF).toNat : Int) := by
  let b : U64 := ⟨input.toBits.toBitVec⟩
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec b (y := 52#i32) (by simp) (by simp))
  have hbv : b.val = input.toBits.toNat := by simp [b, UScalar.val]
  have hzv' : z.val = input.toBits.toNat >>> 52 := by rw [← hbv]; simpa using hzv.1
  have hand : (z &&& 2047#u64).val = (input.toBits.toNat >>> 52) &&& 2047 := by
    simp only [UScalar.val, UScalar.bv_and]; rw [BitVec.toNat_and]; rw [← UScalar.val, hzv']; rfl
  have hlt : (input.toBits.toNat >>> 52) &&& 2047 < 2048 := Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  refine ⟨UScalar.hcast .I64 (z &&& 2047#u64), ?_, ?_⟩
  · intro β f; simp [f64_to_bits_eq input h, lift, hz, b]
  · rw [UScalar.hcast_val_eq, hand]
    rw [Int.bmod_eq_of_le (by simp) (by simp; omega)]
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight]

open NetDecimal in
def specE (dbl : F64) (power : Int) : F64 × Int :=
  if power ≥ 0 then
    let power := if power > 28 then 28 else power
    (dbl * doublePowers10[power.toNat]!, power)
  else if power != -1 || p1e15 ≤ dbl then (dbl / doublePowers10[power.natAbs]!, power)
  else (dbl, 0)

open NetDecimal in
def specF (x : F64 × Int) : F64 × Int :=
  if x.1 < p1e14 && x.2 < 28 then (x.1 * f64ten, x.2 + 1) else x

open NetDecimal in
def ofF64' (input : F64) : Except NetExn NetDecimal :=
  let e : Int := ((input.toBits >>> 52) &&& 0x7FF).toNat
  let num := e - 1022
  if num < -94 then .ok zero
  else if num > 96 then .error .overflow
  else
    let neg := input < 0
    let dbl := if neg then -input else input
    let power : Int := 14 - sar (num * 19728) 16
    let r := specF (specE dbl power)
    let mant := (F64.toInt64 (F64.round r.1)).toInt.toNat
    if mant == 0 then .ok zero
    else finishFromR neg mant r.2 14 [8, 4, 2, 1]

theorem ofF64_eq (input : F64) : NetDecimal.ofF64 input = ofF64' input := by
  unfold NetDecimal.ofF64 ofF64' specE specF
  simp only

theorem eStep_impl (dbl : F64) (p0 : I64) (hp : -14 ≤ p0.val ∧ p0.val ≤ 43) :
    ∃ (d1 : F64) (p1 : I64), (∀ {β : Type} (f : F64 → I64 → Result β),
      (do
        let (dbl1, power) ←
          if p0 >= 0#i64
          then
            do
            let power1 ← if p0 > 28#i64 then ok 28#i64 else ok p0
            let i5 ← lift (IScalar.hcast .U32 power1)
            let f1 ← net.decimal.double_powers10 i5
            let dbl2 ← float.F64.mul dbl f1
            ok (dbl2, power1)
          else
            if p0 != (-1)#i64
            then
              do
              let i5 ← -. p0
              let i6 ← lift (IScalar.hcast .U32 i5)
              let f1 ← net.decimal.double_powers10 i6
              let dbl2 ← float.F64.div dbl f1
              ok (dbl2, p0)
            else
              do
              let f1 ← net.decimal.P1E15
              let b1 ← float.F64.le f1 dbl
              if b1
              then
                let i5 ← -. p0
                let i6 ← lift (IScalar.hcast .U32 i5)
                let f2 ← net.decimal.double_powers10 i6
                let dbl2 ← float.F64.div dbl f2
                ok (dbl2, p0)
              else ok (dbl, 0#i64)
        f dbl1 power) = f d1 p1) ∧
      (d1, p1.val) = specE dbl p0.val ∧ -14 ≤ p1.val ∧ p1.val ≤ 28 := by
  by_cases c1 : 0 ≤ p0.val
  · have c1' : p0 >= 0#i64 := c1
    by_cases c2 : p0.val > 28
    · have c2' : p0 > 28#i64 := c2
      have hc : (IScalar.hcast .U32 (28#i64 : I64)).val = 28 := by rfl
      refine ⟨dbl * NetDecimal.doublePowers10[28]!, 28#i64, ?_, ?_, by simp, by simp⟩
      · intro β f
        simp [c1', c2', lift, net.decimal.double_powers10_refines _ (by rw [hc] : (IScalar.hcast .U32 (28#i64 : I64)).val ≤ 28), hc]
      · simp [specE, c1, c2]
    · have c2' : ¬ p0 > 28#i64 := c2
      have hc : (IScalar.hcast .U32 p0).val = p0.val.toNat := by rw [IScalar.hcast_val_eq]; simp <;> omega
      refine ⟨dbl * NetDecimal.doublePowers10[p0.val.toNat]!, p0, ?_, ?_, by omega, by omega⟩
      · intro β f
        simp [c1', c2', lift, net.decimal.double_powers10_refines _ (by rw [hc]; omega : (IScalar.hcast .U32 p0).val ≤ 28), hc]
      · simp [specE, c1, c2]
  · have c1' : ¬ p0 >= 0#i64 := c1
    obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step p0 (by simp [IScalar.min, I64.min_eq]; omega))
    have hc : (IScalar.hcast .U32 q).val = p0.val.natAbs := by rw [IScalar.hcast_val_eq, hqv]; simp <;> omega
    have hdp := net.decimal.double_powers10_refines (IScalar.hcast .U32 q) (by rw [hc]; omega)
    rw [hc] at hdp
    by_cases c3 : p0.val ≠ -1
    · have c3' : (p0 != (-1)#i64) = true := by rw [bne_iff_ne]; intro h; apply c3; rw [h]; rfl
      refine ⟨dbl / NetDecimal.doublePowers10[p0.val.natAbs]!, p0, ?_, ?_, by omega, by omega⟩
      · intro β f; simp [c1', c3', HNeg.hNeg, hq, lift, hdp]
      · simp [specE, c1, c3]
    · have c3' : (p0 != (-1)#i64) = false := by
        have : p0 = (-1)#i64 := IScalar.eq_of_val_eq (by simp; omega)
        rw [this]; rfl
      have hp1 : p0.val = -1 := by omega
      by_cases c4 : NetDecimal.p1e15 ≤ dbl
      · refine ⟨dbl / NetDecimal.doublePowers10[p0.val.natAbs]!, p0, ?_, ?_, by omega, by omega⟩
        · intro β f; simp [c1', c3', HNeg.hNeg, hq, lift, hdp, c4]
        · simp [specE, c1, hp1, c4]
      · refine ⟨dbl, 0#i64, ?_, ?_, by simp, by simp⟩
        · intro β f; simp [c1', c3', c4]
        · simp [specE, c1, hp1, c4]

theorem fStep_impl (d : F64) (p : I64) (hp : -14 ≤ p.val ∧ p.val ≤ 28) :
    ∃ (d2 : F64) (p2 : I64), (∀ {β : Type} (f : F64 → I64 → Result β),
      (do
        let f1 ← net.decimal.P1E14
        let b1 ← float.F64.lt d f1
        let (dbl2, power1) ←
          if b1
          then
            if p < 28#i64
            then
              do
              let f2 ← net.decimal.F64TEN
              let dbl3 ← float.F64.mul d f2
              let power2 ← p + 1#i64
              ok (dbl3, power2)
            else ok (d, p)
          else ok (d, p)
        f dbl2 power1) = f d2 p2) ∧
      (d2, p2.val) = specF (d, p.val) ∧ -14 ≤ p2.val ∧ p2.val ≤ 28 := by
  by_cases c1 : d < NetDecimal.p1e14
  · by_cases c2 : p.val < 28
    · have c2' : p < 28#i64 := c2
      obtain ⟨p2, hp2, hp2v⟩ := eq_ok_of_spec (I64.add_spec (x := p) (y := 1#i64)
        (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      simp at hp2v
      refine ⟨d * NetDecimal.f64ten, p2, ?_, ?_, by omega, by omega⟩
      · intro β f; simp [c1, c2', hp2]
      · simp [specF, c1, c2, hp2v]
    · have c2' : ¬ p < 28#i64 := c2
      exact ⟨d, p, by intro β f; simp [c1, c2'], by simp [specF, c1, c2], hp.1, hp.2⟩
  · exact ⟨d, p, by intro β f; simp [c1], by simp [specF, c1], hp.1, hp.2⟩

theorem ofF64_nan : NetDecimal.ofF64 Float.nan = .error .overflow := by
  rw [ofF64_eq]; unfold ofF64'; decide +kernel

theorem net.decimal.of_f64_refines (input : F64) :
    ∃ r, net.decimal.of_f64 input = ok r ∧ resRel decRel r (NetDecimal.ofF64 input) := by
  cases hn : input.isNaN
  · obtain ⟨e, he, hev⟩ := f64_exp_bits input hn
    have he0 : 0 ≤ e.val ∧ e.val < 2048 := by
      rw [hev]; constructor
      · simp
      · have : ((input.toBits >>> 52) &&& 0x7FF).toNat < 2048 := by
          rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
        omega
    obtain ⟨num, hnum, hnumv⟩ := eq_ok_of_spec (I64.sub_spec (x := e) (y := 1022#i64)
      (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
    simp at hnumv
    rw [ofF64_eq]
    unfold net.decimal.of_f64 ofF64'
    simp only [hn, Bool.false_eq_true, ite_false]
    rw [he, hnum, bind_ok]
    rw [← hev]
    by_cases c1 : num.val < -94
    · have c1' : num < (-94)#i64 := c1
      have c1s : e.val - 1022 < -94 := by omega
      exact ⟨.Ok net.decimal.ZERO, by simp [c1', hn], by simp [c1s, resRel, decRel]⟩
    · have c1' : ¬ num < (-94)#i64 := c1
      have c1s : ¬ e.val - 1022 < -94 := by omega
      by_cases c2 : num.val > 96
      · have c2' : num > 96#i64 := c2
        have c2s : e.val - 1022 > 96 := by omega
        exact ⟨.Err .Overflow, by simp [c1', c2', hn], by simp [c1s, c2s, resRel, exnS]⟩
      · have c2' : ¬ num > 96#i64 := c2
        have c2s : ¬ e.val - 1022 > 96 := by omega
        simp only [c1', c2', c1s, c2s, ite_false, dec_F64_ZERO, bind_ok, float.F64.is_nan, hn,
          Bool.false_eq_true]
        have hdbl : (if decide (input < 0) = true then float.F64.neg input else ok input) =
            ok (if input < 0 then -input else input) := by
          by_cases h : input < 0 <;> simp [float.F64.neg, h]
        obtain ⟨i3, hi3, hi3v⟩ := eq_ok_of_spec (I64.mul_spec (x := num) (y := 19728#i64)
          (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
        simp at hi3v
        obtain ⟨i4, hi4, hi4v⟩ := net.decimal.sar_refines i3 16#u32 (by simp)
        have hi4b : -29 ≤ i4.val ∧ i4.val ≤ 28 := by
          rw [hi4v]; simp only [NetDecimal.sar, Int.fdiv_eq_ediv]; simp [hi3v]; omega
        obtain ⟨p0, hp0, hp0v⟩ := eq_ok_of_spec (I64.sub_spec (x := 14#i64) (y := i4)
          (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
        simp at hp0v
        obtain ⟨d1, p1, hE, hEv, hp1a, hp1b⟩ := eStep_impl (if input < 0 then -input else input) p0 ⟨by omega, by omega⟩
        obtain ⟨d2, p2, hF, hFv, hp2a, hp2b⟩ := fStep_impl d1 p1 ⟨hp1a, hp1b⟩
        simp only [float.F64.lt, bind_ok] at hF ⊢
        rw [hdbl, bind_ok, hi3, bind_ok, hi4, bind_ok, hp0, bind_ok, hE, hF]
        have hp0' : (14 - NetDecimal.sar ((e.val - 1022) * 19728) 16) = p0.val := by
          rw [hp0v, hi4v, hi3v, hnumv]; rfl
        rw [hp0', ← hEv, ← hFv]
        simp only [net.mathops.f64_round_refines, bind_ok, float.F64.to_i64_sat]
        generalize hR : F64.toInt64 (F64.round d2) = R
        have hRv : (⟨R.toBitVec⟩ : I64).val = R.toInt := rfl
        have hRb := (⟨R.toBitVec⟩ : I64).hmax
        simp [IScalar.max, I64.max_eq, hRv] at hRb
        by_cases hr0 : R.toInt < 0
        · have hr0' : (⟨R.toBitVec⟩ : I64) < 0#i64 := by show (⟨R.toBitVec⟩ : I64).val < 0; rw [hRv]; exact hr0
          have hz : R.toInt.toNat = 0 := by omega
          exact ⟨.Ok net.decimal.ZERO, by simp [hr0'], by simp [hz, resRel, decRel]⟩
        · have hr0' : ¬ (⟨R.toBitVec⟩ : I64) < 0#i64 := by show ¬ (⟨R.toBitVec⟩ : I64).val < 0; rw [hRv]; exact hr0
          have hcm : (IScalar.hcast .U128 (⟨R.toBitVec⟩ : I64)).val = R.toInt.toNat := by
            rw [IScalar.hcast_val_eq, hRv, Int.emod_eq_of_lt (by omega) (by simp; omega)]
          by_cases hz : R.toInt.toNat = 0
          · have hz' : IScalar.hcast .U128 (⟨R.toBitVec⟩ : I64) = 0#u128 := UScalar.eq_of_val_eq (by rw [hcm, hz]; rfl)
            exact ⟨.Ok net.decimal.ZERO, by simp [hr0', hz'], by simp [hz, resRel, decRel]⟩
          · have hz' : ¬ IScalar.hcast .U128 (⟨R.toBitVec⟩ : I64) = 0#u128 := fun h => hz (by rw [← hcm, h]; rfl)
            obtain ⟨r, hr, hrel⟩ := net.decimal.finish_from_r_refines (decide (input < 0))
              (IScalar.hcast .U128 (⟨R.toBitVec⟩ : I64)) p2 14#u32 (Std.Array.to_slice net.decimal.STEPS_R8)
              steps_r8_le ⟨by omega, by omega⟩ (by
                intro _; rw [hcm]
                have h1 : R.toInt.toNat < 2^63 := by omega
                have h2 : 10 ^ p2.val.natAbs ≤ 10 ^ 14 := Nat.pow_le_pow_right (by decide) (by omega)
                have h3 : R.toInt.toNat * 10 ^ p2.val.natAbs ≤ 2^63 * 10^14 := Nat.mul_le_mul (by omega) h2
                omega)
            refine ⟨r, by simp [hr0', hz', lift, hr], ?_⟩
            rw [hcm, steps_r8] at hrel
            simp only [hz, beq_iff_eq, Bool.false_eq_true, ite_false, decide_false]
            exact hrel
  · have := FloatFacts.f64_isNaN_eq input hn; subst this
    exact ⟨.Err .Overflow, by simp [net.decimal.of_f64, hn], by rw [ofF64_nan]; simp [resRel, exnS]⟩

@[simp] theorem dec_P1E7 : net.decimal.P1E7 = ok NetDecimal.p1e7 := by
  simp [net.decimal.P1E7, NetDecimal.p1e7] <;> decide
@[simp] theorem dec_P1E6 : net.decimal.P1E6 = ok NetDecimal.p1e6 := by
  simp [net.decimal.P1E6, NetDecimal.p1e6] <;> decide

open NetDecimal in
def specE32 (dbl : F64) (power : Int) : F64 × Int :=
  if power ≥ 0 then
    let power := if power > 28 then 28 else power
    (dbl * doublePowers10[power.toNat]!, power)
  else if power != -1 || p1e7 ≤ dbl then (dbl / doublePowers10[power.natAbs]!, power)
  else (dbl, 0)

open NetDecimal in
def specF32 (x : F64 × Int) : F64 × Int :=
  if x.1 < p1e6 && x.2 < 28 then (x.1 * f64ten, x.2 + 1) else x

theorem eStep_impl32 (dbl : F64) (p0 : I64) (hp : -22 ≤ p0.val ∧ p0.val ≤ 35) :
    ∃ (d1 : F64) (p1 : I64), (∀ {β : Type} (f : F64 → I64 → Result β),
      (do
        let (dbl1, power) ←
          if p0 >= 0#i64
          then
            do
            let power1 ← if p0 > 28#i64 then ok 28#i64 else ok p0
            let i5 ← lift (IScalar.hcast .U32 power1)
            let f1 ← net.decimal.double_powers10 i5
            let dbl2 ← float.F64.mul dbl f1
            ok (dbl2, power1)
          else
            if p0 != (-1)#i64
            then
              do
              let i5 ← -. p0
              let i6 ← lift (IScalar.hcast .U32 i5)
              let f1 ← net.decimal.double_powers10 i6
              let dbl2 ← float.F64.div dbl f1
              ok (dbl2, p0)
            else
              do
              let f1 ← net.decimal.P1E7
              let b1 ← float.F64.le f1 dbl
              if b1
              then
                let i5 ← -. p0
                let i6 ← lift (IScalar.hcast .U32 i5)
                let f2 ← net.decimal.double_powers10 i6
                let dbl2 ← float.F64.div dbl f2
                ok (dbl2, p0)
              else ok (dbl, 0#i64)
        f dbl1 power) = f d1 p1) ∧
      (d1, p1.val) = specE32 dbl p0.val ∧ -22 ≤ p1.val ∧ p1.val ≤ 28 := by
  by_cases c1 : 0 ≤ p0.val
  · have c1' : p0 >= 0#i64 := c1
    by_cases c2 : p0.val > 28
    · have c2' : p0 > 28#i64 := c2
      have hc : (IScalar.hcast .U32 (28#i64 : I64)).val = 28 := by rfl
      refine ⟨dbl * NetDecimal.doublePowers10[28]!, 28#i64, ?_, ?_, by simp, by simp⟩
      · intro β f
        simp [c1', c2', lift, net.decimal.double_powers10_refines _ (by rw [hc] : (IScalar.hcast .U32 (28#i64 : I64)).val ≤ 28), hc]
      · simp [specE32, c1, c2]
    · have c2' : ¬ p0 > 28#i64 := c2
      have hc : (IScalar.hcast .U32 p0).val = p0.val.toNat := by rw [IScalar.hcast_val_eq]; simp <;> omega
      refine ⟨dbl * NetDecimal.doublePowers10[p0.val.toNat]!, p0, ?_, ?_, by omega, by omega⟩
      · intro β f
        simp [c1', c2', lift, net.decimal.double_powers10_refines _ (by rw [hc]; omega : (IScalar.hcast .U32 p0).val ≤ 28), hc]
      · simp [specE32, c1, c2]
  · have c1' : ¬ p0 >= 0#i64 := c1
    obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step p0 (by simp [IScalar.min, I64.min_eq]; omega))
    have hc : (IScalar.hcast .U32 q).val = p0.val.natAbs := by rw [IScalar.hcast_val_eq, hqv]; simp <;> omega
    have hdp := net.decimal.double_powers10_refines (IScalar.hcast .U32 q) (by rw [hc]; omega)
    rw [hc] at hdp
    by_cases c3 : p0.val ≠ -1
    · have c3' : (p0 != (-1)#i64) = true := by rw [bne_iff_ne]; intro h; apply c3; rw [h]; rfl
      refine ⟨dbl / NetDecimal.doublePowers10[p0.val.natAbs]!, p0, ?_, ?_, by omega, by omega⟩
      · intro β f; simp [c1', c3', HNeg.hNeg, hq, lift, hdp]
      · simp [specE32, c1, c3]
    · have c3' : (p0 != (-1)#i64) = false := by
        have : p0 = (-1)#i64 := IScalar.eq_of_val_eq (by simp; omega)
        rw [this]; rfl
      have hp1 : p0.val = -1 := by omega
      by_cases c4 : NetDecimal.p1e7 ≤ dbl
      · refine ⟨dbl / NetDecimal.doublePowers10[p0.val.natAbs]!, p0, ?_, ?_, by omega, by omega⟩
        · intro β f; simp [c1', c3', HNeg.hNeg, hq, lift, hdp, c4]
        · simp [specE32, c1, hp1, c4]
      · refine ⟨dbl, 0#i64, ?_, ?_, by simp, by simp⟩
        · intro β f; simp [c1', c3', c4]
        · simp [specE32, c1, hp1, c4]

theorem fStep_impl32 (d : F64) (p : I64) (hp : -22 ≤ p.val ∧ p.val ≤ 28) :
    ∃ (d2 : F64) (p2 : I64), (∀ {β : Type} (f : F64 → I64 → Result β),
      (do
        let f1 ← net.decimal.P1E6
        let b1 ← float.F64.lt d f1
        let (dbl2, power1) ←
          if b1
          then
            if p < 28#i64
            then
              do
              let f2 ← net.decimal.F64TEN
              let dbl3 ← float.F64.mul d f2
              let power2 ← p + 1#i64
              ok (dbl3, power2)
            else ok (d, p)
          else ok (d, p)
        f dbl2 power1) = f d2 p2) ∧
      (d2, p2.val) = specF32 (d, p.val) ∧ -22 ≤ p2.val ∧ p2.val ≤ 28 := by
  by_cases c1 : d < NetDecimal.p1e6
  · by_cases c2 : p.val < 28
    · have c2' : p < 28#i64 := c2
      obtain ⟨p2, hp2, hp2v⟩ := eq_ok_of_spec (I64.add_spec (x := p) (y := 1#i64)
        (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      simp at hp2v
      refine ⟨d * NetDecimal.f64ten, p2, ?_, ?_, by omega, by omega⟩
      · intro β f; simp [c1, c2', hp2]
      · simp [specF32, c1, c2, hp2v]
    · have c2' : ¬ p < 28#i64 := c2
      exact ⟨d, p, by intro β f; simp [c1, c2'], by simp [specF32, c1, c2], hp.1, hp.2⟩
  · exact ⟨d, p, by intro β f; simp [c1], by simp [specF32, c1], hp.1, hp.2⟩


/-- The exponent field of a non-NaN single through the Rust bit ops. -/
theorem f32_exp_bits (input : F32) (h : input.isNaN = false) :
    ∃ e : I64, (∀ {β : Type} (f : I64 → Result β),
      (do let i ← float.F32.to_bits input
          let i1 ← i >>> 23#i32
          let i2 ← lift (i1 &&& 255#u32)
          let e ← lift (UScalar.hcast .I64 i2)
          f e) = f e) ∧
      e.val = (((input.toBits >>> 23) &&& 0xFF).toNat : Int) := by
  let b : U32 := ⟨input.toBits.toBitVec⟩
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (UScalar.ShiftRight_IScalar_spec b (y := 23#i32) (by simp) (by simp))
  have hbv : b.val = input.toBits.toNat := by simp [b, UScalar.val]
  have hzv' : z.val = input.toBits.toNat >>> 23 := by rw [← hbv]; simpa using hzv.1
  have hand : (z &&& 255#u32).val = (input.toBits.toNat >>> 23) &&& 255 := by
    simp only [UScalar.val, UScalar.bv_and]; rw [BitVec.toNat_and]; rw [← UScalar.val, hzv']; rfl
  have hlt : (input.toBits.toNat >>> 23) &&& 255 < 256 := Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  refine ⟨UScalar.hcast .I64 (z &&& 255#u32), ?_, ?_⟩
  · intro β f; simp [f32_to_bits_eq input h, lift, hz, b]
  · rw [UScalar.hcast_val_eq, hand]
    rw [Int.bmod_eq_of_le (by simp) (by simp; omega)]
    simp [UInt32.toNat_and, UInt32.toNat_shiftRight]

open NetDecimal in
def ofF32' (input : F32) : Except NetExn NetDecimal :=
  let e : Int := ((input.toBits >>> 23) &&& 0xFF).toNat
  let num := e - 126
  if num < -94 then .ok zero
  else if num > 96 then .error .overflow
  else
    let neg := input < 0
    let dbl := F32.toF64 (if neg then -input else input)
    let power : Int := 6 - sar (num * 19728) 16
    let r := specF32 (specE32 dbl power)
    let mant := (F64.toInt32 (F64.round r.1)).toInt.toNat
    if mant == 0 then .ok zero
    else finishFromR neg mant r.2 6 [4, 2, 1]

theorem ofF32_eq (input : F32) : NetDecimal.ofF32 input = ofF32' input := by
  unfold NetDecimal.ofF32 ofF32' specE32 specF32
  simp only

theorem ofF32_nan : NetDecimal.ofF32 Float32.nan = .error .overflow := by
  rw [ofF32_eq]; unfold ofF32'; decide +kernel

@[simp] theorem dec_F32_ZERO : net.decimal.F32_ZERO = ok (0 : F32) := by
  simp [net.decimal.F32_ZERO] <;> decide
theorem steps_r4 : ((Std.Array.to_slice net.decimal.STEPS_R4).val.map (·.val)) = [4, 2, 1] := by
  simp [net.decimal.STEPS_R4, Std.Array.to_slice, Std.Array.make]
theorem steps_r4_le : ∀ k ∈ (Std.Array.to_slice net.decimal.STEPS_R4).val, k.val ≤ 9 := by
  simp [net.decimal.STEPS_R4, Std.Array.to_slice, Std.Array.make]

theorem net.decimal.of_f32_refines (input : F32) :
    ∃ r, net.decimal.of_f32 input = ok r ∧ resRel decRel r (NetDecimal.ofF32 input) := by
  cases hn : input.isNaN
  · obtain ⟨e, he, hev⟩ := f32_exp_bits input hn
    have he0 : 0 ≤ e.val ∧ e.val < 256 := by
      rw [hev]; constructor
      · simp
      · have : ((input.toBits >>> 23) &&& 0xFF).toNat < 256 := by
          rw [UInt32.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
        omega
    obtain ⟨num, hnum, hnumv⟩ := eq_ok_of_spec (I64.sub_spec (x := e) (y := 126#i64)
      (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
    simp at hnumv
    rw [ofF32_eq]
    unfold net.decimal.of_f32 ofF32'
    simp only [hn, Bool.false_eq_true, ite_false]
    rw [he, hnum, bind_ok]
    rw [← hev]
    by_cases c1 : num.val < -94
    · have c1' : num < (-94)#i64 := c1
      have c1s : e.val - 126 < -94 := by omega
      exact ⟨.Ok net.decimal.ZERO, by simp [c1', hn], by simp [c1s, resRel, decRel]⟩
    · have c1' : ¬ num < (-94)#i64 := c1
      have c1s : ¬ e.val - 126 < -94 := by omega
      by_cases c2 : num.val > 96
      · have c2' : num > 96#i64 := c2
        have c2s : e.val - 126 > 96 := by omega
        exact ⟨.Err .Overflow, by simp [c1', c2', hn], by simp [c1s, c2s, resRel, exnS]⟩
      · have c2' : ¬ num > 96#i64 := c2
        have c2s : ¬ e.val - 126 > 96 := by omega
        simp only [c1', c2', c1s, c2s, ite_false, dec_F32_ZERO, bind_ok, float.F32.is_nan, hn,
          Bool.false_eq_true]
        have hdbl : (if decide (input < 0) = true then float.F32.neg input else ok input) =
            ok (if input < 0 then -input else input) := by
          by_cases h : input < 0 <;> simp [float.F32.neg, h]
        obtain ⟨i3, hi3, hi3v⟩ := eq_ok_of_spec (I64.mul_spec (x := num) (y := 19728#i64)
          (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
        simp at hi3v
        obtain ⟨i4, hi4, hi4v⟩ := net.decimal.sar_refines i3 16#u32 (by simp)
        have hi4b : -29 ≤ i4.val ∧ i4.val ≤ 28 := by
          rw [hi4v]; simp only [NetDecimal.sar, Int.fdiv_eq_ediv]; simp [hi3v]; omega
        obtain ⟨p0, hp0, hp0v⟩ := eq_ok_of_spec (I64.sub_spec (x := 6#i64) (y := i4)
          (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
        simp at hp0v
        obtain ⟨d1, p1, hE, hEv, hp1a, hp1b⟩ := eStep_impl32 (F32.toF64 (if input < 0 then -input else input)) p0
          ⟨by omega, by omega⟩
        obtain ⟨d2, p2, hF, hFv, hp2a, hp2b⟩ := fStep_impl32 d1 p1 ⟨hp1a, hp1b⟩
        simp only [float.F32.lt, float.F64.lt, bind_ok] at hF ⊢
        rw [hdbl, bind_ok, float.F32.to_f64, bind_ok, hi3, bind_ok, hi4, bind_ok, hp0, bind_ok, hE, hF]
        have hp0' : (6 - NetDecimal.sar ((e.val - 126) * 19728) 16) = p0.val := by
          rw [hp0v, hi4v, hi3v, hnumv]; rfl
        rw [hp0', ← hEv, ← hFv]
        simp only [net.mathops.f64_round_refines, bind_ok, float.F64.to_i32_sat]
        generalize hR : F64.toInt32 (F64.round d2) = R
        have hRv : (⟨R.toBitVec⟩ : I32).val = R.toInt := rfl
        have hRb := (⟨R.toBitVec⟩ : I32).hmax
        simp [IScalar.max, I32.max_eq, hRv] at hRb
        by_cases hr0 : R.toInt < 0
        · have hr0' : (⟨R.toBitVec⟩ : I32) < 0#i32 := by show (⟨R.toBitVec⟩ : I32).val < 0; rw [hRv]; exact hr0
          have hz : R.toInt.toNat = 0 := by omega
          exact ⟨.Ok net.decimal.ZERO, by simp [hr0'], by simp [hz, resRel, decRel]⟩
        · have hr0' : ¬ (⟨R.toBitVec⟩ : I32) < 0#i32 := by show ¬ (⟨R.toBitVec⟩ : I32).val < 0; rw [hRv]; exact hr0
          have hcm : (IScalar.hcast .U128 (⟨R.toBitVec⟩ : I32)).val = R.toInt.toNat := by
            rw [IScalar.hcast_val_eq, hRv, Int.emod_eq_of_lt (by omega) (by simp; omega)]
          by_cases hz : R.toInt.toNat = 0
          · have hz' : IScalar.hcast .U128 (⟨R.toBitVec⟩ : I32) = 0#u128 := UScalar.eq_of_val_eq (by rw [hcm, hz]; rfl)
            exact ⟨.Ok net.decimal.ZERO, by simp [hr0', hz'], by simp [hz, resRel, decRel]⟩
          · have hz' : ¬ IScalar.hcast .U128 (⟨R.toBitVec⟩ : I32) = 0#u128 := fun h => hz (by rw [← hcm, h]; rfl)
            obtain ⟨r, hr, hrel⟩ := net.decimal.finish_from_r_refines (decide (input < 0))
              (IScalar.hcast .U128 (⟨R.toBitVec⟩ : I32)) p2 6#u32 (Std.Array.to_slice net.decimal.STEPS_R4)
              steps_r4_le ⟨by omega, by omega⟩ (by
                intro _; rw [hcm]
                have h1 : R.toInt.toNat < 2^31 := by omega
                have h2 : 10 ^ p2.val.natAbs ≤ 10 ^ 22 := Nat.pow_le_pow_right (by decide) (by omega)
                have h3 : R.toInt.toNat * 10 ^ p2.val.natAbs ≤ 2^31 * 10^22 := Nat.mul_le_mul (by omega) h2
                omega)
            refine ⟨r, by simp [hr0', hz', lift, hr], ?_⟩
            rw [hcm, steps_r4] at hrel
            simp only [hz, beq_iff_eq, Bool.false_eq_true, ite_false, decide_false]
            exact hrel
  · have := FloatFacts.f32_isNaN_eq input hn; subst this
    exact ⟨.Err .Overflow, by simp [net.decimal.of_f32, hn], by rw [ofF32_nan]; simp [resRel, exnS]⟩

theorem dec_MAX_VALUE : ∃ d, net.decimal.MAX_VALUE = ok d ∧ decS d = NetDecimal.maxValue := by
  obtain ⟨t, ht, htv, _⟩ := eq_ok_of_spec (U128.sub_spec (x := ⟨BitVec.ofNat 128 (2^96)⟩) (y := 1#u128)
    (by rw [TWO96_val]; simp [NetDecimal.two96]))
  refine ⟨⟨false, t, 0#u32⟩, by unfold net.decimal.MAX_VALUE; rw [TWO96_eq, bind_ok, ht, bind_ok], ?_⟩
  simp only [decS, NetDecimal.maxValue]; rw [htv, TWO96_val]; rfl
theorem dec_MIN_VALUE : ∃ d, net.decimal.MIN_VALUE = ok d ∧ decS d = NetDecimal.minValue := by
  obtain ⟨t, ht, htv, _⟩ := eq_ok_of_spec (U128.sub_spec (x := ⟨BitVec.ofNat 128 (2^96)⟩) (y := 1#u128)
    (by rw [TWO96_val]; simp [NetDecimal.two96]))
  refine ⟨⟨true, t, 0#u32⟩, by unfold net.decimal.MIN_VALUE; rw [TWO96_eq, bind_ok, ht, bind_ok], ?_⟩
  simp only [decS, NetDecimal.minValue]; rw [htv, TWO96_val]; rfl

@[simp] theorem dec_F64_DEC_MAX : net.decimal.F64_DEC_MAX = ok NetDecimal.f64DecMax := by
  simp [net.decimal.F64_DEC_MAX, NetDecimal.f64DecMax]
@[simp] theorem dec_F32_DEC_MAX : net.decimal.F32_DEC_MAX = ok NetDecimal.f32DecMax := by
  simp [net.decimal.F32_DEC_MAX, NetDecimal.f32DecMax]

theorem net.decimal.create_truncating_f64_refines (x : F64) :
    ∃ r, net.decimal.create_truncating_f64 x = ok r ∧ resRel decRel r (NetDecimal.createTruncatingF64 x) := by
  obtain ⟨mx, hmx, hmxv⟩ := dec_MAX_VALUE
  obtain ⟨mn, hmn, hmnv⟩ := dec_MIN_VALUE
  unfold net.decimal.create_truncating_f64 NetDecimal.createTruncatingF64
  by_cases c1 : NetDecimal.f64DecMax ≤ x
  · exact ⟨.Ok mx, by simp [c1, hmx], by simp [c1, resRel, decRel, hmxv]⟩
  · by_cases c2 : x ≤ -NetDecimal.f64DecMax
    · exact ⟨.Ok mn, by simp [c1, c2, hmn], by simp [c1, c2, resRel, decRel, hmnv]⟩
    · by_cases c3 : x.isNaN = true
      · exact ⟨.Ok ⟨false, 0#u128, 1#u32⟩, by simp [c1, c2, c3], by simp [c1, c2, c3, resRel, decRel, decS]⟩
      · obtain ⟨r, hr, hrel⟩ := net.decimal.of_f64_refines x
        exact ⟨r, by simp [c1, c2, c3, hr], by simp [c1, c2, c3]; exact hrel⟩

theorem net.decimal.create_truncating_f32_refines (x : F32) :
    ∃ r, net.decimal.create_truncating_f32 x = ok r ∧ resRel decRel r (NetDecimal.createTruncatingF32 x) := by
  obtain ⟨mx, hmx, hmxv⟩ := dec_MAX_VALUE
  obtain ⟨mn, hmn, hmnv⟩ := dec_MIN_VALUE
  unfold net.decimal.create_truncating_f32 NetDecimal.createTruncatingF32
  by_cases c1 : NetDecimal.f32DecMax ≤ x
  · exact ⟨.Ok mx, by simp [c1, hmx], by simp [c1, resRel, decRel, hmxv]⟩
  · by_cases c2 : x ≤ -NetDecimal.f32DecMax
    · exact ⟨.Ok mn, by simp [c1, c2, hmn], by simp [c1, c2, resRel, decRel, hmnv]⟩
    · by_cases c3 : x.isNaN = true
      · exact ⟨.Ok ⟨false, 0#u128, 1#u32⟩, by simp [c1, c2, c3], by simp [c1, c2, c3, resRel, decRel, decS]⟩
      · obtain ⟨r, hr, hrel⟩ := net.decimal.of_f32_refines x
        exact ⟨r, by simp [c1, c2, c3, hr], by simp [c1, c2, c3]; exact hrel⟩

end OsuProofs
