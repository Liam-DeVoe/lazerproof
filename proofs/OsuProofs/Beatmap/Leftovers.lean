/-
Standalone refinement theorems for three small `beatmap` functions that were only covered inside other proofs
(infra agent, orchestrator 18:45): `dotnet.intro_sort_iter` (the loop of `IntroSort`, previously a `have` inside
`dis_main`), `types.decoded_empty` (the initial `DecodedBeatmap`) and `types.path_type_eq` (`PathType ==`).
-/
import OsuProofs.Beatmap.DotNetIntro
import OsuProofs.Beatmap.Decoder3
import OsuProofs.Auto.Base
set_option maxHeartbeats 400000
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

/-- `IntroSort`'s `while (partitionSize > 1)` loop (`intro_sort_iter`, the body of `introSort` with fuel `F + 1`):
`steps` iterations from loop state `(none, a, ps, depth)` (see `disF`/`dis_spec`). -/
theorem beatmap.dotnet.intro_sort_iter_refines {T : Type} [Inhabited T] (cl : core.clone.Clone T)
    (hcl : ∀ x, cl.clone x = ok x)
    (sc : beatmap.dotnet.SortCmp T) (cmp : T → T → Int)
    (hsc : ∀ x y, ∃ r, sc.cmp3 x y = ok r ∧ r.val = cmp x y) (hrefl : ∀ x, ¬ cmp x x < 0)
    (N : Nat) (hN : N < 2^31) (F : Nat) (lo fuel : Usize) (hf : fuel.val = F + 1) :
    ∀ (steps : Nat) (j : Nat) (sV : Usize) (a : alloc.vec.Vec T) (ps depth : Usize), sV.val = steps →
        a.val.length = N → lo.val + ps.val ≤ N →
        ∃ r, beatmap.dotnet.intro_sort_iter cl sc a lo ps depth sV fuel = ok r ∧
          r.val.toArray = disRes (iterR (disF cmp lo.val F) j steps (none, a.val.toArray, ps.val, depth.val)) ∧
          r.val.length = N := by
  have hf0 : fuel ≠ 0#usize := by intro h; rw [h] at hf; simp at hf
  have ih := dis_main cl hcl sc cmp hsc hrefl N hN F
  intro steps
  induction steps with
  | zero =>
    intro j sV a ps depth hs ha hb
    have : sV = 0#usize := UScalar.eq_of_val_eq (by rw [hs]; rfl)
    subst this
    exact ⟨a, by unfold beatmap.dotnet.intro_sort_iter; simp, by simp [iterR, disRes], ha⟩
  | succ k ihk =>
    intro j sV a ps depth hs ha hb
    have hs0 : sV ≠ 0#usize := by intro h; rw [h] at hs; simp at hs
    simp only [iterR]
    by_cases h1 : ps.val ≤ 1
    · have h1' : ps ≤ 1#usize := by show ps.val ≤ (1#usize : Usize).val; simpa using h1
      refine ⟨a, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1'], ?_, ha⟩
      have : disF cmp lo.val F j (none, a.val.toArray, ps.val, depth.val) = .yield (none, a.val.toArray, ps.val, depth.val) := by
        simp only [disF]; rw [if_neg (by omega)]
      simp only [this, dis_small cmp lo.val F a.val.toArray ps.val depth.val h1, disRes]
    · have h1' : ¬ ps ≤ 1#usize := by show ¬ ps.val ≤ (1#usize : Usize).val; simpa using h1
      have hg1 : ps.val > 1 := by omega
      by_cases h16 : ps.val ≤ 16
      · have h16' : ps ≤ 16#usize := by show ps.val ≤ (16#usize : Usize).val; simpa using h16
        by_cases h2 : ps.val = 2
        · have h2' : ps = 2#usize := UScalar.eq_of_val_eq (by rw [h2]; rfl)
          obtain ⟨i, hi, hiv⟩ := usize_add_one lo (by have := dns_usize_max; omega)
          obtain ⟨r, hr, hrv⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a lo i (by omega) (by omega)
          refine ⟨r, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', h2', hi, hr], ?_, ?_⟩
          · simp only [disF, if_pos hg1, if_pos h16, h2, beq_self_eq_true, if_true, disRes]
            rw [hrv, hiv]; simp
          · have := congrArg List.length hrv; simp [dpp_sig_size] at this; omega
        · have h2' : ¬ ps = 2#usize := by intro h; apply h2; rw [h]; rfl
          have h2b : (ps.val == 2) = false := by simpa using h2
          by_cases h3 : ps.val = 3
          · have h3' : ps = 3#usize := UScalar.eq_of_val_eq (by rw [h3]; rfl)
            obtain ⟨i, hi, hiv⟩ := usize_add_one lo (by have := dns_usize_max; omega)
            obtain ⟨i1, hi1, hi1v⟩ := dns_usize_add lo 2#usize (by simp; omega)
            simp only [show ((2#usize : Usize).val) = 2 from rfl] at hi1v
            obtain ⟨r1, hr1, hr1v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc a lo i (by omega) (by omega)
            have hr1l : r1.val.length = N := by
              have := congrArg List.length hr1v; simp [dpp_sig_size] at this; omega
            obtain ⟨r2, hr2, hr2v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc r1 lo i1 (by omega) (by omega)
            have hr2l : r2.val.length = N := by
              have := congrArg List.length hr2v; simp [dpp_sig_size] at this; omega
            obtain ⟨r3, hr3, hr3v⟩ := beatmap.dotnet.swap_if_greater_refines cl hcl sc cmp hsc r2 i i1 (by omega) (by omega)
            refine ⟨r3, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', h2', h3', hi, hr1, hi1, hr2, hr3],
              ?_, ?_⟩
            · simp only [disF, if_pos hg1, if_pos h16, h2b, h3, beq_self_eq_true, if_true, disRes, Bool.false_eq_true,
                if_false]
              rw [hr3v, hr2v, hr1v, hiv, hi1v]; simp
            · have := congrArg List.length hr3v; simp [dpp_sig_size] at this; omega
          · have h3' : ¬ ps = 3#usize := by intro h; apply h3; rw [h]; rfl
            have h3b : (ps.val == 3) = false := by simpa using h3
            obtain ⟨r, hr, hrv, hrl⟩ := beatmap.dotnet.insertion_sort_refines cl hcl sc cmp hsc a lo ps (by omega) (by omega)
            refine ⟨r, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', h2', h3', hr], ?_, by omega⟩
            simp only [disF, if_pos hg1, if_pos h16, h2b, h3b, disRes, Bool.false_eq_true, if_false]
            exact hrv
      · have h16' : ¬ ps ≤ 16#usize := by show ¬ ps.val ≤ (16#usize : Usize).val; simpa using h16
        by_cases hd : depth.val = 0
        · have hd' : depth = 0#usize := UScalar.eq_of_val_eq (by rw [hd]; rfl)
          obtain ⟨r, hr, hrv, hrl⟩ := beatmap.dotnet.heap_sort_refines cl hcl sc cmp hsc a lo ps (by omega) (by omega)
          refine ⟨r, by unfold beatmap.dotnet.intro_sort_iter; simp [hs0, h1', h16', hd', hr], ?_, by omega⟩
          simp only [disF, if_pos hg1, if_neg h16, hd, beq_self_eq_true, if_true, disRes]
          exact hrv
        · have hd' : ¬ depth = 0#usize := by intro h; apply hd; rw [h]; rfl
          have hdb : (depth.val == 0) = false := by simpa using hd
          obtain ⟨p, a1, hpp, ha1v, hpv, ha1l, hpl⟩ := beatmap.dotnet.pick_pivot_and_partition_refines cl hcl sc cmp hsc
            hrefl a lo ps (by omega) (by omega) (by omega)
          obtain ⟨i, hi, hiv⟩ := dns_usize_add lo p (by omega)
          obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := dns_usize_max; omega)
          obtain ⟨i2, hi2, hi2v⟩ := usize_add_one p (by have := dns_usize_max; omega)
          obtain ⟨i3, hi3, hi3v⟩ := beatmap.dotnet.nat_sub_refines ps i2
          obtain ⟨i4, hi4, hi4v⟩ := dns_usize_sub1 depth (by omega)
          obtain ⟨i5, hi5, hi5v⟩ := dns_usize_sub1 fuel (by omega)
          obtain ⟨a2, ha2, ha2v, ha2l⟩ := ih a1 i1 i3 i4 i5 (by omega) (by omega) (by omega)
          obtain ⟨i6, hi6, hi6v⟩ := dns_usize_sub1 sV (by omega)
          obtain ⟨r, hr, hrv, hrl⟩ := ihk (j + 1) i6 a2 p i4 (by omega) ha2l (by omega)
          refine ⟨r, ?_, ?_, hrl⟩
          · unfold beatmap.dotnet.intro_sort_iter
            simp only [hs0, h1', h16', hd', if_false, hpp, bind_ok, uncurry_apply_pair, hi, hi1, hi2, hi3, hi4, hi5,
              ha2, hi6]
            exact hr
          · simp only [disF, if_pos hg1, if_neg h16, hdb, Bool.false_eq_true, if_false]
            rw [hrv, ha2v, ha1v, hpv, hi1v, hiv, hi3v, hi2v, hi4v, hpv]

/-- `decoded_empty(format_version)` is the spec's initial `DecodedBeatmap` (`{ formatVersion }`, all other fields
at their defaults: ruleset 0, default difficulty, stack leniency 0.7, no lead-in, empty control points/breaks/objects). -/
theorem beatmap.types.decoded_empty_refines (fv : I32) :
    ∃ d, beatmap.types.decoded_empty fv = ok d ∧ dec_dbS d = ({ formatVersion := i32S fv } : DecodedBeatmap) := by
  have hdd : ∃ d0, beatmap.types.DIFFICULTY_DEFAULT = ok d0 ∧ dec_diffS d0 = {} := by
    unfold beatmap.types.DIFFICULTY_DEFAULT
    simp only [float.F32.from_bits, float.F64.from_bits, bind_ok]
    exact ⟨_, rfl, by simp only [dec_diffS]; congr 1 <;> decide⟩
  obtain ⟨d0, hd0, hd0v⟩ := hdd
  obtain ⟨c, hc, hcv⟩ := beatmap.control_points.cpi_empty_refines
  have hsl : float.F32.from_bits 1060320051#u32 = ok (0.7 : F32) := by simp; decide
  have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp; decide
  unfold beatmap.types.decoded_empty
  simp only [hsl, hz, hc, hd0, bind_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [dec_dbS, hd0v, hcv]
  simp
  first | rfl | decide

/-- `path_type_eq(a, b)` is the spec's derived `PathType` `==` (`bspline` compares the optional degree). -/
theorem beatmap.types.path_type_eq_refines (a b : beatmap.types.PathType) :
    beatmap.types.path_type_eq a b = ok ((abs a : PathType) == abs b) := by
  unfold beatmap.types.path_type_eq
  exact hop_pt_eq a b

end OsuProofs
