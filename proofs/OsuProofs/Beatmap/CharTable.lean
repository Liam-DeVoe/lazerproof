/-
`beatmap::chartable` (Rust) refines `OsuModel.Beatmap.charIsLetter` (.NET `char.IsLetter`).
Both run the same 20-step binary search over the same range table (checked equal by kernel
evaluation, `letter_table`).
-/
import OsuProofs.Net.FrameworkB
import OsuProofs.SpecLoops
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem letter_table : (beatmap.chartable.LETTER_RANGES.val.map (fun p => (p.1.val, p.2.val))) = letterRanges.toList := by
  unfold beatmap.chartable.LETTER_RANGES
  decide +kernel

theorem letter_size : letterRanges.size = 380 := by decide +kernel

theorem letter_get (i : Nat) (h : i < 380) :
    ((beatmap.chartable.LETTER_RANGES.val[i]'(by simpa using h)).1.val,
     (beatmap.chartable.LETTER_RANGES.val[i]'(by simpa using h)).2.val) = letterRanges[i]! := by
  have hs : i < letterRanges.size := by rw [letter_size]; exact h
  have hl : i < (beatmap.chartable.LETTER_RANGES.val.map (fun p => (p.1.val, p.2.val))).length := by simpa using h
  have := List.getElem_of_eq letter_table hl
  rw [getElem!_pos letterRanges i hs]
  simp only [List.getElem_map] at this
  rw [this, Array.getElem_toList]

/-- The spec loop body (`charIsLetter`'s binary search step), as elaborated. -/
def clStep (n : Nat) (s : Option Bool × Nat × Nat) : ForInStep (Option Bool × Nat × Nat) :=
  if s.2.1 < s.2.2 then
    if n < letterRanges[(s.2.1 + s.2.2) / 2]!.1 then ForInStep.yield (none, s.2.1, (s.2.1 + s.2.2) / 2)
    else if letterRanges[(s.2.1 + s.2.2) / 2]!.2 < n then ForInStep.yield (none, (s.2.1 + s.2.2) / 2 + 1, s.2.2)
    else ForInStep.done (some true, s.2.1, s.2.2)
  else ForInStep.yield (none, s.2.1, s.2.2)

theorem cl_loop (nU : U32) :
    ∃ y, beatmap.chartable.char_is_letter_loop nU 0#usize 380#usize false 0#i32 = ok y ∧
      y = (match (iterId (clStep nU.val) 20 (none, 0, 380)).1 with | some r => r | none => false) := by
  let T := iterId (clStep nU.val) 20 (none, 0, 380)
  unfold beatmap.chartable.char_is_letter_loop
  apply loop_ok _ (fun x => (20 - x.2.2.2.val).toNat + (if x.2.2.1 then 0 else 1))
    (fun x => 0 ≤ x.2.2.2.val ∧ x.2.2.2.val ≤ 20 ∧ x.1.val ≤ x.2.1.val ∧ x.2.1.val ≤ 380 ∧
      (x.2.2.1 = false → iterId (clStep nU.val) (20 - x.2.2.2.val).toNat (none, x.1.val, x.2.1.val) = T) ∧
      (x.2.2.1 = true → T.1 = some true))
  · rintro ⟨lo, hi, found, it⟩ ⟨hi0, hi20, hlh, hh, hT, hF⟩
    dsimp only at hi0 hi20 hlh hh hT hF ⊢
    cases found with
    | true =>
      left; refine ⟨true, by simp [beatmap.chartable.char_is_letter_loop.body], ?_⟩
      have h1 := hF rfl; simp only [T] at h1; simp [h1]
    | false =>
      have hT' := hT rfl
      by_cases hit : it.val < 20
      · right
        have hit' : it < 20#i32 := hit
        obtain ⟨it1, hit1, hit1v⟩ := eq_ok_of_spec (I32.add_spec (x := it) (y := 1#i32)
          (by simp [I32.min_eq]; omega) (by simp [I32.max_eq]; omega))
        simp at hit1v
        have e : (20 - it.val).toNat = (20 - it1.val).toNat + 1 := by omega
        rw [e] at hT'
        simp only [iterId] at hT'
        by_cases hlt : lo.val < hi.val
        · have hlt' : lo < hi := hlt
          have hmax := usize_ge_32
          obtain ⟨sm, hsm, hsmv⟩ := eq_ok_of_spec (Usize.add_spec (x := lo) (y := hi) (by omega))
          obtain ⟨mid, hmid, hmidv⟩ := eq_ok_of_spec (Usize.div_spec sm (y := 2#usize) (by simp))
          simp at hsmv hmidv
          have hml : mid.val < 380 := by rw [hmidv, hsmv]; omega
          have hidx : Std.Array.index_usize beatmap.chartable.LETTER_RANGES mid =
              ok (beatmap.chartable.LETTER_RANGES.val[mid.val]'(by simpa using hml)) := by
            obtain ⟨x, hx, rfl⟩ := eq_ok_of_spec (Std.Array.index_usize_spec beatmap.chartable.LETTER_RANGES mid
              (by simpa using hml))
            exact hx
          have hget := letter_get mid.val hml
          generalize hpp : beatmap.chartable.LETTER_RANGES.val[mid.val]'(by simpa using hml) = pp at hidx hget
          obtain ⟨a, b⟩ := pp
          have hmid' : (lo.val + hi.val) / 2 = mid.val := by rw [hmidv, hsmv]
          simp only [clStep, hlt, ite_true, hmid'] at hT'
          rw [← hget] at hT'
          simp only at hT'
          by_cases c1 : nU.val < a.val
          · have c1' : nU < a := c1
            refine ⟨(lo, mid, false, it1), by simp [beatmap.chartable.char_is_letter_loop.body, hit', hlt', hsm, hmid,
              hidx, c1, c1', hit1], ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
              ?_, by simp⟩, by dsimp only; simp; omega⟩
            intro _; dsimp only; simp only [c1, ite_true] at hT'; exact hT'
          · have c1' : ¬ nU < a := c1
            by_cases c2 : b.val < nU.val
            · have c2' : b < nU := c2
              obtain ⟨l2, hl2, hl2v⟩ := eq_ok_of_spec (Usize.add_spec (x := mid) (y := 1#usize) (by simp; omega))
              simp at hl2v
              refine ⟨(l2, hi, false, it1), by simp [beatmap.chartable.char_is_letter_loop.body, hit', hlt', hsm, hmid,
                hidx, c1, c1', c2, c2', hl2, hit1], ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                by dsimp only; omega, ?_, by simp⟩, by dsimp only; simp; omega⟩
              intro _; dsimp only; simp only [c1, c2, ite_true, ite_false] at hT'; rw [hl2v]; exact hT'
            · have c2' : ¬ b < nU := c2
              refine ⟨(lo, hi, true, it1), by simp [beatmap.chartable.char_is_letter_loop.body, hit', hlt', hsm, hmid,
                hidx, c1, c1', c2, c2', hit1], ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                by dsimp only; omega, by simp, ?_⟩, by dsimp only; simp; omega⟩
              intro _; simp only [c1, c2, ite_false] at hT'; rw [← hT']
        · have hlt' : ¬ lo < hi := hlt
          refine ⟨(lo, hi, false, it1), by simp [beatmap.chartable.char_is_letter_loop.body, hit', hlt', hit1],
            ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_, by simp⟩,
            by dsimp only; simp; omega⟩
          intro _; simp only [clStep, hlt, ite_false] at hT'; exact hT'
      · left
        have hit' : ¬ it < 20#i32 := hit
        refine ⟨false, by simp [beatmap.chartable.char_is_letter_loop.body, hit'], ?_⟩
        have : (20 - it.val).toNat = 0 := by omega
        rw [this] at hT'; simp only [iterId] at hT'
        simp only [T] at hT'; rw [← hT']
  · exact ⟨by simp, by simp, by simp, by simp, fun _ => rfl, by simp⟩

theorem beatmap.chartable.char_is_letter_refines (nU : U32) (h : nU.val.isValidChar) :
    beatmap.chartable.char_is_letter nU = ok (charIsLetter (chOf nU)) := by
  have e := chOf_toNat nU h
  have le1 : ∀ k : Char, (k ≤ chOf nU ↔ k.toNat ≤ nU.val) := by
    intro k; rw [Char.le_def, UInt32.le_iff_toNat_le]; show k.toNat ≤ (chOf nU).toNat ↔ _; rw [e]
  have le2 : ∀ k : Char, (chOf nU ≤ k ↔ nU.val ≤ k.toNat) := by
    intro k; rw [Char.le_def, UInt32.le_iff_toNat_le]; show (chOf nU).toNat ≤ k.toNat ↔ _; rw [e]
  unfold beatmap.chartable.char_is_letter charIsLetter
  simp only [Id.run, e]
  by_cases h128 : nU.val < 128
  · have h128' : nU < 128#u32 := h128
    simp only [h128', h128, ite_true]
    simp only [le1, le2, show ('a' : Char).toNat = 97 from rfl, show ('z' : Char).toNat = 122 from rfl,
      show ('A' : Char).toNat = 65 from rfl, show ('Z' : Char).toNat = 90 from rfl]
    by_cases a1 : 97 ≤ nU.val <;> by_cases a2 : nU.val ≤ 122 <;> by_cases a3 : 65 ≤ nU.val <;>
      by_cases a4 : nU.val ≤ 90 <;> simp [a1, a2, a3, a4]
    all_goals first | rfl | omega
  · have h128' : ¬ nU < 128#u32 := h128
    simp only [h128', h128, ite_false]
    rw [forIn_range_id' _ (fun _ _ => rfl)]
    simp only [id_bind_eq, id_pure_eq]
    generalize hG : (iterId _ 20 (none, 0, letterRanges.size)) = T
    have hG' : iterId (clStep nU.val) 20 (none, 0, 380) = T := by rw [← hG, letter_size]; rfl
    obtain ⟨y, hy, hyv⟩ := cl_loop nU
    have hlen : Slice.len (Std.Array.to_slice beatmap.chartable.LETTER_RANGES) = 380#usize := by
      apply UScalar.eq_of_val_eq; simp
    simp only [lift, bind_ok, hlen, hy, hyv, hG']
    cases T.1 <;> rfl

end OsuProofs
