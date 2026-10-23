/-
`replay::frames` text parser (Rust index scans over the code-point slice) refines `OsuModel.Replay`
`parseLegacyFrames` (`String.splitOn` on `,` and `|`), `fixupFrames`, `decode`. The U32 view of `text[i..b]` is
`s2_g`; `splitOn` on a single character is reduced to `List.splitOnP` and peeled with `s2_splitOnP_eq`.
-/
import OsuProofs.Sim2.Frames
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs

theorem s2_splitOnP_eq {α : Type} (p : α → Bool) : ∀ l : List α,
    l.splitOnP p = l.takeWhile (fun x => !p x) ::
      (if l.any p then (l.drop ((l.takeWhile (fun x => !p x)).length + 1)).splitOnP p else []) := by
  intro l
  induction l with
  | nil => simp [List.splitOnP_nil]
  | cons x xs ih =>
    rw [List.splitOnP_cons]
    by_cases hx : p x = true
    · simp [hx]
    · simp only [hx, Bool.false_eq_true, ite_false]
      rw [ih]
      simp [hx]
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- "not the code point `c`" -/
def s2_ne (c : Nat) (u : U32) : Bool := decide (u.val ≠ c)

theorem s2_cpipe : replay.frames.C_PIPE = 124#u32 := by unfold replay.frames.C_PIPE; rfl
theorem s2_ccomma : replay.frames.C_COMMA = 44#u32 := by unfold replay.frames.C_COMMA; rfl

theorem s2_ccomma_val : replay.frames.C_COMMA.val = 44 := by rw [s2_ccomma]; rfl
theorem s2_cpipe_val : replay.frames.C_PIPE.val = 124 := by rw [s2_cpipe]; rfl

theorem s2_segment_end (s : Slice U32) :
    ∀ (n : Nat) (a : Usize), s.val.length - a.val = n → a.val ≤ s.val.length →
      ∃ b, replay.frames.segment_end_loop s a = ok b ∧
        b.val = a.val + ((s.val.drop a.val).takeWhile (s2_ne 44)).length := by
  have hmax := s.property
  intro n
  induction n with
  | zero =>
    intro a hn ha
    refine ⟨a, ?_, ?_⟩
    · unfold replay.frames.segment_end_loop; rw [loop_unfold]
      simp [replay.frames.segment_end_loop.body, slice_lt_len_iff, show ¬ a.val < s.val.length by omega]
    · rw [List.drop_eq_nil_of_le (by omega)]; simp
  | succ n ih =>
    intro a hn ha
    have hl : a.val < s.val.length := by omega
    rw [List.drop_eq_getElem_cons hl, List.takeWhile_cons]
    by_cases hc : (s.val[a.val]'hl).val = 44
    · refine ⟨a, ?_, by simp [s2_ne, hc]⟩
      unfold replay.frames.segment_end_loop; rw [loop_unfold]
      have : s.val[a.val]'hl = replay.frames.C_COMMA := UScalar.eq_of_val_eq (by rw [s2_ccomma_val, hc])
      simp [replay.frames.segment_end_loop.body, slice_lt_len_iff, hl, index_eq s a hl, this]
    · obtain ⟨a1, ha1, ha1v⟩ := usize_add_one a (by omega)
      obtain ⟨b, hb, hbv⟩ := ih a1 (by omega) (by omega)
      refine ⟨b, ?_, ?_⟩
      · have hne : ¬ (s.val[a.val]'hl).val = replay.frames.C_COMMA.val := by rw [s2_ccomma_val]; exact hc
        have hb0 : replay.frames.segment_end_loop.body s a = ok (.cont a1) := by
          simp [replay.frames.segment_end_loop.body, slice_lt_len_iff, hl, index_eq s a hl, hne, ha1]
        unfold replay.frames.segment_end_loop; rw [loop_unfold]; simp only [hb0, bind_ok]
        unfold replay.frames.segment_end_loop at hb; exact hb
      · rw [hbv, ha1v]; simp [s2_ne, hc]; omega
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem s2_sf0_step (s : Slice U32) (b : Usize) (hb : b.val ≤ s.val.length) :
    ∀ (n : Nat) (ends : Std.Array Usize 4#usize) (k i : Usize), b.val - i.val = n → i.val ≤ b.val → k.val < 3 →
      ((i.val + (((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124)).length < b.val →
        ∃ (p k1 i1 : Usize), p.val = i.val + (((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124)).length ∧
          k1.val = k.val + 1 ∧ i1.val = p.val + 1 ∧
          replay.frames.split_fields_loop0 s b ends k i = replay.frames.split_fields_loop0 s b (Std.Array.set ends k p) k1 i1) ∧
      (b.val ≤ i.val + (((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124)).length →
        replay.frames.split_fields_loop0 s b ends k i = ok (ends, k, b))) := by
  have hmax := s.property
  intro n
  induction n with
  | zero =>
    intro ends k i hn hi hk
    have hib : i = b := UScalar.eq_of_val_eq (by omega)
    subst hib
    refine ⟨fun h => by simp at h, fun _ => ?_⟩
    unfold replay.frames.split_fields_loop0; rw [loop_unfold]
    simp [replay.frames.split_fields_loop0.body]
  | succ n ih =>
    intro ends k i hn hi hk
    have hl : i.val < s.val.length := by omega
    have hib : i.val < b.val := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have htk : (s.val.drop i.val).take (b.val - i.val) = (s.val[i.val]'hl) :: (s.val.drop (i.val + 1)).take (b.val - (i.val + 1)) := by
      rw [List.drop_eq_getElem_cons hl, show b.val - i.val = (b.val - (i.val + 1)) + 1 by omega, List.take_succ_cons]
    have hk3 : k < 3#usize := by scalar_tac
    have hib' : i < b := by scalar_tac
    by_cases hp : (s.val[i.val]'hl).val = 124
    · have hpipe : s.val[i.val]'hl = replay.frames.C_PIPE := UScalar.eq_of_val_eq (by rw [s2_cpipe_val, hp])
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by scalar_tac)
      have h0 : ((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124) = [] := by
        rw [htk]; simp [List.takeWhile_cons, s2_ne, hp]
      rw [h0]; simp only [List.length_nil, Nat.add_zero]
      refine ⟨fun _ => ⟨i, k1, i1, rfl, hk1v, hi1v, ?_⟩, fun h => by omega⟩
      have hupd : Std.Array.update ends k i = ok (Std.Array.set ends k i) := by
        obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (Std.Array.update_spec ends k i (by simp; omega))
        rw [hr, hrv]
      conv => lhs; unfold replay.frames.split_fields_loop0; rw [loop_unfold]
      simp [replay.frames.split_fields_loop0.body, hib', hk3, index_eq s i hl, hpipe, hupd, hk1, hi1]
      rfl
    · have hnp : ¬ (s.val[i.val]'hl).val = replay.frames.C_PIPE.val := by rw [s2_cpipe_val]; exact hp
      have hb0 : replay.frames.split_fields_loop0.body s b ends k i = ok (.cont (ends, k, i1)) := by
        simp [replay.frames.split_fields_loop0.body, hib', hk3, index_eq s i hl, hnp, hi1]
      have ih' := ih ends k i1 (by omega) (by omega) hk
      rw [hi1v] at ih'
      have heq : replay.frames.split_fields_loop0 s b ends k i = replay.frames.split_fields_loop0 s b ends k i1 := by
        conv => lhs; unfold replay.frames.split_fields_loop0; rw [loop_unfold]
        simp only [hb0, bind_ok]; rfl
      have h1 : ((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124) =
          (s.val[i.val]'hl) :: ((s.val.drop (i.val + 1)).take (b.val - (i.val + 1))).takeWhile (s2_ne 124) := by
        rw [htk]; simp [List.takeWhile_cons, s2_ne, hp]
      rw [h1, List.length_cons]
      obtain ⟨hA, hB⟩ := ih'
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨p, k1, i2, hp1, hk1, hi2, he⟩ := hA (by omega)
        exact ⟨p, k1, i2, by rw [hp1]; omega, hk1, hi2, by rw [heq, he]⟩
      · rw [heq]; exact hB (by omega)
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem s2_sf1 (s : Slice U32) (b : Usize) (hb : b.val ≤ s.val.length) :
    ∀ (n : Nat) (i : Usize), b.val - i.val = n → i.val ≤ b.val →
      ∃ j, replay.frames.split_fields_loop1 s b i false = ok j ∧
        j.val = i.val + (((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124)).length := by
  have hmax := s.property
  intro n
  induction n with
  | zero =>
    intro i hn hi
    refine ⟨i, ?_, ?_⟩
    · unfold replay.frames.split_fields_loop1; rw [loop_unfold]
      simp [replay.frames.split_fields_loop1.body, show ¬ i < b by scalar_tac]
    · simp [show b.val - i.val = 0 by omega]
  | succ n ih =>
    intro i hn hi
    have hl : i.val < s.val.length := by omega
    have hib' : i < b := by scalar_tac
    have htk : (s.val.drop i.val).take (b.val - i.val) = (s.val[i.val]'hl) :: (s.val.drop (i.val + 1)).take (b.val - (i.val + 1)) := by
      rw [List.drop_eq_getElem_cons hl, show b.val - i.val = (b.val - (i.val + 1)) + 1 by omega, List.take_succ_cons]
    by_cases hp : (s.val[i.val]'hl).val = 124
    · have hpipe : s.val[i.val]'hl = replay.frames.C_PIPE := UScalar.eq_of_val_eq (by rw [s2_cpipe_val, hp])
      have h0 : ((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124) = [] := by
        rw [htk]; simp [List.takeWhile_cons, s2_ne, hp]
      refine ⟨i, ?_, by rw [h0]; rfl⟩
      unfold replay.frames.split_fields_loop1; rw [loop_unfold]
      simp [replay.frames.split_fields_loop1.body, hib', index_eq s i hl, hpipe]
      rw [loop_unfold]
      simp [replay.frames.split_fields_loop1.body, hib']
    · have hnp : ¬ (s.val[i.val]'hl).val = replay.frames.C_PIPE.val := by rw [s2_cpipe_val]; exact hp
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      have h1 : ((s.val.drop i.val).take (b.val - i.val)).takeWhile (s2_ne 124) =
          (s.val[i.val]'hl) :: ((s.val.drop (i.val + 1)).take (b.val - (i.val + 1))).takeWhile (s2_ne 124) := by
        rw [htk]; simp [List.takeWhile_cons, s2_ne, hp]
      obtain ⟨j, hj, hjv⟩ := ih i1 (by omega) (by omega)
      refine ⟨j, ?_, ?_⟩
      · have hb0 : replay.frames.split_fields_loop1.body s b i false = ok (.cont (i1, false)) := by
          simp [replay.frames.split_fields_loop1.body, hib', index_eq s i hl, hnp, hi1]
        unfold replay.frames.split_fields_loop1; rw [loop_unfold]; simp only [hb0, bind_ok]
        unfold replay.frames.split_fields_loop1 at hj; exact hj
      · rw [hjv, h1, hi1v, List.length_cons]; omega
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- the U32 view of `s[i..b]` -/
def s2_g (s : Slice U32) (i b : Nat) : List U32 := (s.val.drop i).take (b - i)

theorem s2_takeWhile_self {α : Type} (p : α → Bool) : ∀ l : List α, (∀ x ∈ l, p x = true) → l.takeWhile p = l := by
  intro l; induction l with
  | nil => intro _; rfl
  | cons x xs ih => intro h; rw [List.takeWhile_cons_of_pos (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]

theorem s2_g_split (c : Nat) (s : Slice U32) (i b : Nat) (hib : i ≤ b) (hb : b ≤ s.val.length) :
    (s2_g s i b).splitOnP (fun u => !(s2_ne c u)) =
      (s2_g s i b).takeWhile (s2_ne c) ::
        (if i + ((s2_g s i b).takeWhile (s2_ne c)).length < b then
          (s2_g s (i + ((s2_g s i b).takeWhile (s2_ne c)).length + 1) b).splitOnP (fun u => !(s2_ne c u)) else []) := by
  rw [s2_splitOnP_eq]
  simp only [Bool.not_not, show (fun x => s2_ne c x) = s2_ne c from rfl]
  congr 1
  have hlen : (s2_g s i b).length = b - i := by simp [s2_g]; omega
  have hw : ((s2_g s i b).takeWhile (s2_ne c)).length ≤ (s2_g s i b).length := (List.takeWhile_prefix _).length_le
  by_cases h : i + ((s2_g s i b).takeWhile (s2_ne c)).length < b
  · rw [if_pos h]
    have hany : (s2_g s i b).any (fun u => !(s2_ne c u)) = true := by
      by_contra hn
      simp only [Bool.not_eq_true, List.any_eq_false, Bool.not_eq_false] at hn
      have : (s2_g s i b).takeWhile (s2_ne c) = s2_g s i b := s2_takeWhile_self _ _ (by
        intro x hx; simpa using hn x hx)
      rw [this] at h; omega
    rw [if_pos hany]
    congr 1
    simp only [s2_g, List.drop_take]
    rw [List.drop_drop]
    congr 1 <;> omega
  · rw [if_neg h]
    have hall : (s2_g s i b).takeWhile (s2_ne c) = s2_g s i b :=
      (List.takeWhile_prefix _).eq_of_length (by omega)
    have hany : (s2_g s i b).any (fun u => !(s2_ne c u)) = false := by
      simp only [List.any_eq_false, Bool.not_eq_true']
      intro x hx
      rw [← hall] at hx
      have := List.all_eq_true.mp (List.all_takeWhile (p := s2_ne c) (l := s2_g s i b)) x hx
      simpa using this
    rw [if_neg (by simp [hany])]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem s2_tw_g (c : Nat) (s : Slice U32) (i b : Nat) :
    (s2_g s i b).takeWhile (s2_ne c) = s2_g s i (i + ((s2_g s i b).takeWhile (s2_ne c)).length) := by
  obtain ⟨t, ht⟩ := List.takeWhile_prefix (p := s2_ne c) (l := s2_g s i b)
  generalize hw : (s2_g s i b).takeWhile (s2_ne c) = w at ht ⊢
  have hlen : w.length ≤ b - i := by
    have := congrArg List.length ht; simp [s2_g] at this; omega
  have h1 : w = (w ++ t).take w.length := by simp
  rw [h1, ht]
  simp only [s2_g, List.take_take, List.length_take, List.length_append]
  rw [Nat.add_sub_cancel_left, List.take_eq_take_iff]
  omega

theorem s2_sf0_k3 (s : Slice U32) (b : Usize) (ends : Std.Array Usize 4#usize) (i : Usize) :
    replay.frames.split_fields_loop0 s b ends 3#usize i = ok (ends, 3#usize, i) := by
  unfold replay.frames.split_fields_loop0; rw [loop_unfold]
  by_cases h : i < b <;> simp [replay.frames.split_fields_loop0.body, h]
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- the outcome of `split_fields` against the U32 `splitOnP '|'` of the frame -/
def s2_sfRel (s : Slice U32) (a b : Nat) : Option (Std.Array Usize 4#usize) → Prop
  | none => ∀ (f0 f1 f2 f3 : List U32) rest, (s2_g s a b).splitOnP (fun u => !(s2_ne 124 u)) ≠ f0 :: f1 :: f2 :: f3 :: rest
  | some e => ∃ (e0 e1 e2 e3 : Usize) (rest : List (List U32)), e.val = [e0, e1, e2, e3] ∧
      a ≤ e0.val ∧ e0.val < e1.val ∧ e1.val < e2.val ∧ e2.val < e3.val ∧ e3.val ≤ b ∧
      (s2_g s a b).splitOnP (fun u => !(s2_ne 124 u)) =
        s2_g s a e0.val :: s2_g s (e0.val + 1) e1.val :: s2_g s (e1.val + 1) e2.val :: s2_g s (e2.val + 1) e3.val :: rest

theorem s2_split_fields (s : Slice U32) (a b : Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ s.val.length) :
    ∃ r, replay.frames.split_fields s a b = ok r ∧ s2_sfRel s a.val b.val r := by
  have hmax := s.property
  have hspl := fun (i : Nat) (hi : i ≤ b.val) => s2_g_split 124 s i b.val hi hb
  have htw := fun (i : Nat) => s2_tw_g 124 s i b.val
  have hsfA := s2_sf0_step s b hb
  generalize hE0 : (Std.Array.make 4#usize [b, b, b, b] (by simp) : Std.Array Usize 4#usize) = E0
  have hsf : replay.frames.split_fields s a b = (do
      let (ends, k, i) ← replay.frames.split_fields_loop0 s b E0 0#usize a
      if k < 3#usize then ok none else do
        let j ← replay.frames.split_fields_loop1 s b i false
        let ends1 ← Std.Array.update ends 3#usize j
        ok (some ends1)) := by rw [← hE0]; rfl
  have hG : ∀ i, (s.val.drop i).take (b.val - i) = s2_g s i b.val := fun _ => rfl
  obtain ⟨A0, B0⟩ := hsfA _ E0 0#usize a rfl hab (by simp)
  simp only [hG] at A0 B0
  by_cases h0 : a.val + ((s2_g s a.val b.val).takeWhile (s2_ne 124)).length < b.val
  · obtain ⟨p0, k1, i1, hp0, hk1, hi1, e0⟩ := A0 h0
    simp only [show (0#usize : Usize).val = 0 from rfl] at hk1
    have hs0 := hspl a.val hab
    rw [if_pos h0, show a.val + ((s2_g s a.val b.val).takeWhile (s2_ne 124)).length + 1 = i1.val by omega,
      htw a.val, show a.val + ((s2_g s a.val b.val).takeWhile (s2_ne 124)).length = p0.val by omega] at hs0
    obtain ⟨A1, B1⟩ := hsfA _ (Std.Array.set E0 0#usize p0) k1 i1 rfl (by omega) (by omega)
    simp only [hG] at A1 B1
    by_cases h1 : i1.val + ((s2_g s i1.val b.val).takeWhile (s2_ne 124)).length < b.val
    · obtain ⟨p1, k2, i2, hp1, hk2, hi2, e1⟩ := A1 h1
      have hs1 := hspl i1.val (by omega)
      rw [if_pos h1, show i1.val + ((s2_g s i1.val b.val).takeWhile (s2_ne 124)).length + 1 = i2.val by omega,
        htw i1.val, show i1.val + ((s2_g s i1.val b.val).takeWhile (s2_ne 124)).length = p1.val by omega] at hs1
      obtain ⟨A2, B2⟩ := hsfA _ (Std.Array.set (Std.Array.set E0 0#usize p0) k1 p1) k2 i2 rfl (by omega) (by omega)
      simp only [hG] at A2 B2
      by_cases h2 : i2.val + ((s2_g s i2.val b.val).takeWhile (s2_ne 124)).length < b.val
      · obtain ⟨p2, k3, i3, hp2, hk3, hi3, e2⟩ := A2 h2
        have hs2 := hspl i2.val (by omega)
        rw [if_pos h2, show i2.val + ((s2_g s i2.val b.val).takeWhile (s2_ne 124)).length + 1 = i3.val by omega,
          htw i2.val, show i2.val + ((s2_g s i2.val b.val).takeWhile (s2_ne 124)).length = p2.val by omega] at hs2
        have hk3' : k3 = 3#usize := UScalar.eq_of_val_eq (by simp; omega)
        subst hk3'
        obtain ⟨j, hj, hjv⟩ := s2_sf1 s b hb _ i3 rfl (by omega)
        rw [hG] at hjv
        have hs3 := hspl i3.val (by omega)
        rw [htw i3.val, ← hjv] at hs3
        obtain ⟨rest, hs3⟩ : ∃ rest, (s2_g s i3.val b.val).splitOnP (fun u => !(s2_ne 124 u)) = s2_g s i3.val j.val :: rest :=
          ⟨_, hs3⟩
        let E3 := Std.Array.set (Std.Array.set (Std.Array.set E0 0#usize p0) k1 p1) k2 p2
        have hupd : Std.Array.update E3 3#usize j = ok (Std.Array.set E3 3#usize j) := by
          obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (Std.Array.update_spec E3 3#usize j (by simp))
          rw [hr, hrv]
        have hL3 : ((s2_g s i3.val b.val).takeWhile (s2_ne 124)).length ≤ b.val - i3.val := by
          have h2' : (s2_g s i3.val b.val).length = b.val - i3.val := by simp [s2_g]; omega
          exact le_trans (List.takeWhile_prefix (p := s2_ne 124) (l := s2_g s i3.val b.val)).length_le (le_of_eq h2')
        refine ⟨some (Std.Array.set E3 3#usize j), ?_, ?_⟩
        · rw [hsf, e0, e1, e2, s2_sf0_k3, bind_ok]
          show (if (3#usize : Usize) < 3#usize then ok none else (do
            let j ← replay.frames.split_fields_loop1 s b i3 false
            let ends1 ← Std.Array.update E3 3#usize j
            ok (some ends1))) = _
          rw [if_neg (by decide), hj]; simp only [bind_ok]; rw [hupd]; simp only [bind_ok]
        · refine ⟨p0, p1, p2, j, rest, ?_, by omega, by omega, by omega, by omega, by omega, ?_⟩
          · have hk1' : k1 = 1#usize := UScalar.eq_of_val_eq (by simp; omega)
            have hk2' : k2 = 2#usize := UScalar.eq_of_val_eq (by simp; omega)
            subst hk1' hk2'
            simp [E3, ← hE0, Std.Array.set, Std.Array.make]
          · rw [hs0, hs1, hs2, hs3, hi1, hi2, hi3]
      · have hl := B2 (by omega)
        refine ⟨none, ?_, ?_⟩
        · have hk2' : k2 = 2#usize := UScalar.eq_of_val_eq (by simp; omega)
          rw [hsf, e0, e1, hl, hk2']; simp
        · intro f0 f1 f2 f3 rest h
          have hs2 := hspl i2.val (by omega)
          rw [if_neg h2] at hs2
          rw [hs0, hs1, hs2] at h; simp at h
    · have hl := B1 (by omega)
      refine ⟨none, ?_, ?_⟩
      · have hk1' : k1 = 1#usize := UScalar.eq_of_val_eq (by simp; omega)
        rw [hsf, e0, hl, hk1']; simp
      · intro f0 f1 f2 f3 rest h
        have hs1 := hspl i1.val (by omega)
        rw [if_neg h1] at hs1
        rw [hs0, hs1] at h; simp at h
  · have hl := B0 (by omega)
    refine ⟨none, ?_, ?_⟩
    · rw [hsf, hl]; simp
    · intro f0 f1 f2 f3 rest h
      rw [hspl a.val hab, if_neg h0] at h
      simp at h
end OsuProofs

namespace OsuProofs
open OsuImpl

def s2_skL : List Nat := [45, 49, 50, 51, 52, 53]

theorem s2_skm_val : replay.frames.SKIP_MARKER.val.map (·.val) = s2_skL := by
  simp [replay.frames.SKIP_MARKER, s2_skL, Std.Array.make]

theorem s2_skm_loop (s : Slice U32) (a : Usize) (ha : a.val + 6 ≤ s.val.length) :
    ∀ (n : Nat) (i : Usize) (same : Bool), 6 - i.val = n → i.val ≤ 6 →
      replay.frames.is_skip_marker_loop s a i same =
        ok (same && ((List.range' i.val (6 - i.val)).all fun j => decide ((s.val[a.val + j]!).val = s2_skL[j]!))) := by
  have hmax := s.property
  intro n
  induction n with
  | zero =>
    intro i same hn hi
    unfold replay.frames.is_skip_marker_loop; rw [loop_unfold]
    simp [replay.frames.is_skip_marker_loop.body, show ¬ i < 6#usize by scalar_tac, show 6 - i.val = 0 by omega]
  | succ n ih =>
    intro i same hn hi
    have hi6 : i < 6#usize := by scalar_tac
    obtain ⟨ai, hai, haiv⟩ : ∃ z, a + i = ok z ∧ z.val = a.val + i.val := by
      obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (Usize.add_spec (x := a) (y := i) (by scalar_tac))
      exact ⟨z, hz, by simpa using hv⟩
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by scalar_tac)
    have hl : ai.val < s.val.length := by omega
    have hsk : replay.frames.SKIP_MARKER.index_usize i = ok (replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega)) := by
      obtain ⟨x, hx, hxv⟩ := eq_ok_of_spec (Std.Array.index_usize_spec replay.frames.SKIP_MARKER i (by simp; omega))
      rw [hx, hxv]
    have hskv : (replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega)).val = s2_skL[i.val]! := by
      rw [getElem!_pos s2_skL i.val (by simp [s2_skL]; omega)]
      obtain ⟨_, h2⟩ := List.ext_getElem_iff.mp s2_skm_val
      have := h2 i.val (by simp; omega) (by simp [s2_skL]; omega)
      simpa using this
    have hsv : (s.val[ai.val]'hl) = s.val[a.val + i.val]! := by rw [getElem!_pos _ _ (by omega)]; simp [haiv]
    have hb : replay.frames.is_skip_marker_loop.body s a i same =
        ok (.cont (i1, if (s.val[ai.val]'hl) != replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega) then false else same)) := by
      simp [replay.frames.is_skip_marker_loop.body, hi6, hai, index_eq s ai hl, hsk, hi1]
    unfold replay.frames.is_skip_marker_loop; rw [loop_unfold]; simp only [hb, bind_ok]
    have := ih i1 (if (s.val[ai.val]'hl) != replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega) then false else same) (by omega) (by omega)
    unfold replay.frames.is_skip_marker_loop at this; rw [this]
    rw [show 6 - i.val = (6 - i1.val) + 1 by omega, List.range'_succ, List.all_cons, hi1v]
    congr 1
    rw [← hsv]
    by_cases he : (s.val[ai.val]'hl) = replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega)
    · have : (s.val[ai.val]'hl).val = s2_skL[i.val]! := by rw [he, hskv]
      have h1 : ((s.val[ai.val]'hl) != replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega)) = false := by simp [he]
      have h2 : decide ((s.val[ai.val]'hl).val = s2_skL[i.val]!) = true := by simp only [decide_eq_true_eq]; exact this
      rw [h1, h2]; simp
    · have : ¬ (s.val[ai.val]'hl).val = s2_skL[i.val]! := by
        rw [← hskv]; intro h; exact he (UScalar.eq_of_val_eq h)
      have h1 : ((s.val[ai.val]'hl) != replay.frames.SKIP_MARKER.val[i.val]'(by simp; omega)) = true := by simp [he]
      have h2 : decide ((s.val[ai.val]'hl).val = s2_skL[i.val]!) = false := by simp only [decide_eq_false_iff_not]; exact this
      rw [h1, h2]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem s2_ofNat_eq (n : Nat) (c : Char) (hc : c.toNat ≠ 0) : Char.ofNat n = c ↔ n = c.toNat := by
  constructor
  · intro h
    by_cases hv : n.isValidChar
    · rw [← h]; simp [Char.ofNat, hv, Char.ofNatAux]
    · exfalso; apply hc; rw [← h]; simp [Char.ofNat, hv]
  · intro h; subst h; simp

theorem s2_chars_eq : ∀ (l : List Nat) (cs : List Char), (∀ c ∈ cs, c.toNat ≠ 0) →
    (l.map Char.ofNat = cs ↔ l = cs.map Char.toNat) := by
  intro l
  induction l with
  | nil => intro cs _; cases cs <;> simp
  | cons x xs ih =>
    intro cs hcs
    cases cs with
    | nil => simp
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq]
      rw [s2_ofNat_eq x c (hcs c (by simp)), ih cs (fun d hd => hcs d (by simp [hd]))]

theorem s2_skL_chars : s2_skL = "-12345".toList.map Char.toNat := by decide

theorem s2_str_skip (g : List U32) :
    (String.ofList (g.map chOf) == "-12345") = decide (g.map (·.val) = s2_skL) := by
  have e1 : (String.ofList (g.map chOf) == "-12345") = decide (g.map chOf = "-12345".toList) := by
    by_cases h : g.map chOf = "-12345".toList
    · rw [h]; simp
    · have : String.ofList (g.map chOf) ≠ "-12345" := by
        intro h'; apply h; rw [← h']; simp
      rw [beq_false_of_ne this]; exact (decide_eq_false h).symm
  rw [e1]
  congr 1
  have : g.map chOf = (g.map (·.val)).map Char.ofNat := by simp [chOf, Function.comp_def]
  rw [this, s2_chars_eq _ _ (by decide), ← s2_skL_chars]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem s2_is_skip (s : Slice U32) (a b : Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ s.val.length) :
    replay.frames.is_skip_marker s a b = ok (String.ofList ((s2_g s a.val b.val).map chOf) == "-12345") := by
  rw [s2_str_skip]
  obtain ⟨d, hd, hdv⟩ : ∃ z, b - a = ok z ∧ z.val = b.val - a.val := by
    obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := b) (y := a) (by scalar_tac))
    exact ⟨z, hz, by simpa using hv⟩
  have hlen : (s2_g s a.val b.val).length = b.val - a.val := by simp [s2_g]; omega
  by_cases h6 : d.val = 6
  · have hd6 : ¬ (d != 6#usize) = true := by
      have : d = 6#usize := UScalar.eq_of_val_eq (by simp [h6])
      simp [this]
    unfold replay.frames.is_skip_marker
    rw [hd, bind_ok, if_neg hd6, s2_skm_loop s a (by omega) 6 0#usize true rfl (by simp)]
    simp only [Bool.true_and, show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
    have hg : ∀ j (hj : j < 6), (s.val[a.val + j]!).val = ((s2_g s a.val b.val).map (·.val))[j]'(by simp; omega) := by
      intro j hj
      rw [getElem!_pos s.val (a.val + j) (by omega)]
      simp [s2_g]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_range'_1, decide_eq_true_eq]
    constructor
    · intro H
      apply List.ext_getElem (by simp [s2_skL]; omega)
      intro j h1 h2
      have hj : j < 6 := by simp [s2_skL] at h2; exact h2
      rw [← hg j hj, H j ⟨by omega, by omega⟩, getElem!_pos s2_skL j h2]
    · intro H j hj
      rw [hg j (by omega)]
      simp only [H]
      rw [getElem!_pos s2_skL j (by simp [s2_skL]; omega)]
  · have hd6 : (d != 6#usize) = true := by simp; intro h; apply h6; rw [h]
    unfold replay.frames.is_skip_marker
    rw [hd, bind_ok, if_pos hd6]
    congr 1
    symm; apply decide_eq_false
    intro h
    have := congrArg List.length h
    simp [s2_skL] at this; omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_sub (s : Slice U32) (a b : Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ s.val.length) :
    ∃ t : Slice U32, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U32) s
      { start := a, «end» := b } = ok t ∧ t.val = s2_g s a.val b.val := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index]
  rw [if_pos ⟨by scalar_tac, by scalar_tac⟩]
  exact ⟨_, rfl, by simp [s2_g, List.slice]⟩

theorem s2_g_valid (s : Slice U32) (hs : ValidStr s) (i b : Nat) : ∀ u ∈ s2_g s i b, u.val.isValidChar := by
  intro u hu; exact hs u (List.mem_of_mem_drop (List.mem_of_mem_take hu))

theorem s2_g_len (s : Slice U32) (i b : Nat) : (s2_g s i b).length ≤ s.val.length := by
  simp [s2_g]

/-- the spec's `diff` of one frame (`intTryParse`, else rounded `parseFloat`) -/
def s2_diffS (s0 : String) : Except NetExn Int32 :=
  match OsuModel.Replay.intTryParse s0 with
  | some d => pure d
  | none => do
    let f ← Parsing.parseFloat s0
    pure (F64.toInt32 (F64.round (F32.toF64 f)))

theorem replay.frames.int_try_parse_refines (s : Slice U32) (hs : ValidStr s) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ s.val.length) :
    replay.frames.int_try_parse s a b =
      ok ((OsuModel.Replay.intTryParse (String.ofList ((s2_g s a.val b.val).map chOf))).map i32I) := by
  obtain ⟨t, ht, htv⟩ := s2_sub s a b hab hb
  have hvt : ValidStr t := by intro u hu; rw [htv] at hu; exact s2_g_valid s hs _ _ u hu
  unfold replay.frames.int_try_parse OsuModel.Replay.intTryParse intParse
  rw [ht, bind_ok, net.parse.int_parse_refines t hvt, bind_ok]
  have : strS t = (s2_g s a.val b.val).map chOf := by simp [strS, htv]
  rw [this, String.toList_ofList]
  cases intParseChars ((s2_g s a.val b.val).map chOf) <;> rfl

theorem replay.frames.parse_diff_refines (s : Slice U32) (hs : ValidStr s) (hn : s.val.length < 2^62) (a b : Usize)
    (hab : a.val ≤ b.val) (hb : b.val ≤ s.val.length) :
    replay.frames.parse_diff s a b = ok (exceptI i32I (s2_diffS (String.ofList ((s2_g s a.val b.val).map chOf)))) := by
  obtain ⟨t, ht, htv⟩ := s2_sub s a b hab hb
  have hvt : ValidStr t := by intro u hu; rw [htv] at hu; exact s2_g_valid s hs _ _ u hu
  have htn : t.val.length < 2^62 := by rw [htv]; have := s2_g_len s a.val b.val; omega
  have hst : String.ofList (strS t) = String.ofList ((s2_g s a.val b.val).map chOf) := by simp [strS, htv]
  unfold replay.frames.parse_diff s2_diffS
  rw [replay.frames.int_try_parse_refines s hs a b hab hb, bind_ok]
  cases hit : OsuModel.Replay.intTryParse (String.ofList ((s2_g s a.val b.val).map chOf)) with
  | some d => rfl
  | none =>
    simp only [Option.map_none]
    rw [ht, bind_ok, net.parse.parse_float_default_refines t hvt htn, bind_ok, hst]
    cases Parsing.parseFloat (String.ofList ((s2_g s a.val b.val).map chOf)) with
    | error e => rfl
    | ok f =>
      simp [exceptI, float.F32.to_f64, sim.netx.f64_round, net.mathops.f64_round_refines, float.F64.to_i32_sat, i32I,
        Bind.bind, Except.bind, pure, Except.pure]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_splitOnP_map {α β : Type} (f : α → β) (p : β → Bool) : ∀ l : List α,
    (l.map f).splitOnP p = (l.splitOnP (p ∘ f)).map (List.map f) := by
  intro l
  induction l with
  | nil => simp [List.splitOnP_nil]
  | cons x xs ih =>
    rw [List.map_cons, List.splitOnP_cons, List.splitOnP_cons, ih]
    by_cases hx : p (f x) = true
    · simp [hx]
    · simp only [hx, Function.comp_apply, Bool.false_eq_true, ite_false]
      cases h : xs.splitOnP (p ∘ f) with
      | nil => simp [List.modifyHead]
      | cons y ys => simp [List.modifyHead]

theorem s2_splitOnP_congr {α : Type} (p q : α → Bool) : ∀ l : List α, (∀ x ∈ l, p x = q x) →
    l.splitOnP p = l.splitOnP q := by
  intro l
  induction l with
  | nil => intro _; simp [List.splitOnP_nil]
  | cons x xs ih =>
    intro h
    rw [List.splitOnP_cons, List.splitOnP_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem s2_chOf_pipe (u : U32) (hu : u.val.isValidChar) : (chOf u == '|') = !(s2_ne 124 u) := by
  have := chOf_toNat u hu
  by_cases h : u.val = 124
  · have : chOf u = '|' := by simp only [chOf, h]
    simp [this, s2_ne, h]
  · have : chOf u ≠ '|' := by intro e; apply h; rw [← chOf_toNat u hu, e]; rfl
    simp [this, s2_ne, h]

theorem s2_str_split_pipe (g : List U32) (hg : ∀ u ∈ g, u.val.isValidChar) :
    (String.ofList (g.map chOf)).splitOn "|" =
      ((g.splitOnP (fun u => !(s2_ne 124 u))).map (List.map chOf)).map String.ofList := by
  rw [show "|" = '|'.toString from rfl, splitOn_char]
  congr 1
  show (g.map chOf).splitOnP (· == '|') = _
  rw [s2_splitOnP_map]
  congr 1
  apply s2_splitOnP_congr
  intro x hx; exact s2_chOf_pipe x (hg x hx)
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net
theorem s2_maxc : replay.frames.MAX_COORDINATE_F32 = ok (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE) := by
  unfold replay.frames.MAX_COORDINATE_F32
  simp only [float.F32.from_bits]
  congr 1
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the spec loop body's parse of one frame (`none` = `continue`) -/
def s2_pofS (fr : String) : Except NetExn (Option (Int32 × F32 × F32 × Int32)) :=
  match fr.splitOn "|" with
  | s0 :: s1 :: s2 :: s3 :: _ =>
    if s0 == "-12345" then pure none else do
      let diff ← s2_diffS s0
      let mx ← Parsing.parseFloat s1 (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE)
      let my ← Parsing.parseFloat s2 (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE)
      let b ← Parsing.parseInt s3
      pure (some (diff, mx, my, b))
  | _ => pure none

def s2_rawI (x : Int32 × F32 × F32 × Int32) : replay.frames.RawFrame :=
  { diff := i32I x.1, mouse_x := x.2.1, mouse_y := x.2.2.1, buttons := i32I x.2.2.2 }

theorem s2_arr4_index (e : Std.Array Usize 4#usize) (e0 e1 e2 e3 : Usize) (he : e.val = [e0, e1, e2, e3]) :
    Std.Array.index_usize e 0#usize = ok e0 ∧ Std.Array.index_usize e 1#usize = ok e1 ∧
    Std.Array.index_usize e 2#usize = ok e2 ∧ Std.Array.index_usize e 3#usize = ok e3 := by
  have hidx : ∀ (i : Usize) (h : i.val < 4), Std.Array.index_usize e i = ok (e.val[i.val]'(by rw [he]; simp; omega)) := by
    intro i h
    obtain ⟨x, hx, hxv⟩ := eq_ok_of_spec (Std.Array.index_usize_spec e i (by simp; omega))
    rw [hx, hxv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hidx 0#usize (by decide)]; simp [he]
  · rw [hidx 1#usize (by decide)]; simp [he]
  · rw [hidx 2#usize (by decide)]; simp [he]
  · rw [hidx 3#usize (by decide)]; simp [he]

theorem replay.frames.parse_one_frame_refines (s : Slice U32) (hs : ValidStr s) (hn : s.val.length < 2^62)
    (a b : Usize) (hab : a.val ≤ b.val) (hb : b.val ≤ s.val.length) :
    replay.frames.parse_one_frame s a b =
      ok (exceptI (Option.map s2_rawI) (s2_pofS (String.ofList ((s2_g s a.val b.val).map chOf)))) := by
  obtain ⟨r, hr, hrel⟩ := s2_split_fields s a b hab hb
  unfold replay.frames.parse_one_frame s2_pofS
  rw [hr, bind_ok, s2_str_split_pipe _ (s2_g_valid s hs _ _)]
  cases r with
  | none =>
    simp only [s2_sfRel] at hrel
    rcases hL : (s2_g s a.val b.val).splitOnP (fun u => !(s2_ne 124 u)) with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, rest⟩⟩⟩⟩
    all_goals first | (exact absurd hL (hrel _ _ _ _ _)) | rfl
  | some e =>
    obtain ⟨e0, e1, e2, e3, rest, he, h0, h1, h2, h3, h4, hL⟩ := hrel
    obtain ⟨i0, i1, i2, i3⟩ := s2_arr4_index e e0 e1 e2 e3 he
    rw [hL]
    have hU : ∀ x : Usize, x.val < s.val.length → x.val + 1 ≤ Usize.max := by
      intro x hx; have := s.property; omega
    obtain ⟨s1, hs1, hs1v⟩ := usize_add_one e0 (hU e0 (by omega))
    obtain ⟨s2, hs2, hs2v⟩ := usize_add_one e1 (hU e1 (by omega))
    obtain ⟨s3, hs3, hs3v⟩ := usize_add_one e2 (hU e2 (by omega))
    have hsk := s2_is_skip s a e0 h0 (by omega)
    obtain ⟨t1, ht1, ht1v⟩ := s2_sub s s1 e1 (by omega) (by omega)
    obtain ⟨t2, ht2, ht2v⟩ := s2_sub s s2 e2 (by omega) (by omega)
    obtain ⟨t3, ht3, ht3v⟩ := s2_sub s s3 e3 (by omega) (by omega)
    have hv : ∀ (t : Slice U32) i j, t.val = s2_g s i j → ValidStr t := by
      intro t i j h u hu; rw [h] at hu; exact s2_g_valid s hs _ _ u hu
    have hl : ∀ (t : Slice U32) i j, t.val = s2_g s i j → t.val.length < 2^62 := by
      intro t i j h; rw [h]; have := s2_g_len s i j; omega
    have hst : ∀ (t : Slice U32) i j, t.val = s2_g s i j → String.ofList (strS t) = String.ofList ((s2_g s i j).map chOf) := by
      intro t i j h; simp [strS, h]
    simp only [i0, i1, i2, i3, hs1, hs2, hs3, bind_ok, hsk]
    simp only [List.map_cons]
    rw [hs1v] at ht1v; rw [hs2v] at ht2v; rw [hs3v] at ht3v
    by_cases hskip : (String.ofList (List.map chOf (s2_g s a.val e0.val)) == "-12345") = true
    · simp only [hskip, ite_true]; rfl
    · simp only [hskip, Bool.false_eq_true, ite_false]
      rw [replay.frames.parse_diff_refines s hs hn a e0 h0 (by omega)]
      cases hd : s2_diffS (String.ofList (List.map chOf (s2_g s a.val e0.val))) with
      | error e => simp [exceptI, Bind.bind, Except.bind]
      | ok d =>
        simp only [exceptI, bind_ok, ht1, s2_maxc, net.parse.parsing_parse_float_refines t1 (hv _ _ _ ht1v) (hl _ _ _ ht1v),
          hst _ _ _ ht1v]
        cases hx : Parsing.parseFloat (String.ofList (List.map chOf (s2_g s (e0.val + 1) e1.val))) (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE) false with
        | error e => simp [Bind.bind, Except.bind, exceptI]
        | ok mx =>
          simp only [id, ht2, bind_ok, net.parse.parsing_parse_float_refines t2 (hv _ _ _ ht2v) (hl _ _ _ ht2v), hst _ _ _ ht2v]
          cases hy : Parsing.parseFloat (String.ofList (List.map chOf (s2_g s (e1.val + 1) e2.val))) (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE) false with
          | error e => simp [Bind.bind, Except.bind, exceptI]
          | ok my =>
            simp only [id, ht3, bind_ok, net.parse.parse_int_default_refines t3 (hv _ _ _ ht3v), hst _ _ _ ht3v]
            cases hb2 : Parsing.parseInt (String.ofList (List.map chOf (s2_g s (e2.val + 1) e3.val))) with
            | error e => simp [Bind.bind, Except.bind, exceptI]
            | ok bt => simp [Bind.bind, Except.bind, pure, Except.pure, s2_rawI, exceptI]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_forIn_yield_ex {α S ε : Type} (F : α → S → Except ε (ForInStep S)) (g : S → α → Except ε S)
    (hF : ∀ x s, F x s = ForInStep.yield <$> g s x) : ∀ (l : List α) (s : S), forIn l s F = l.foldlM g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    rw [List.forIn_cons, List.foldlM_cons, hF]
    cases g s x with
    | error e => rfl
    | ok s' => exact ih s'

/-- one step of the spec's frame loop -/
def s2_plfStep (st : Int64 × Array OsuModel.Replay.LegacyFrame) (fr : String) :
    Except NetExn (Int64 × Array OsuModel.Replay.LegacyFrame) := do
  match ← s2_pofS fr with
  | none => pure st
  | some (d, mx, my, b) => pure (st.1 + d.toInt64,
      st.2.push { time := F64.ofInt64 (st.1 + d.toInt64), mouseX := mx, mouseY := my, buttons := b })

theorem s2_PLF_eq (t : String) (o : Int64) :
    OsuModel.Replay.parseLegacyFrames t o = (fun st => st.2) <$> (t.splitOn ",").foldlM s2_plfStep (o, #[]) := by
  unfold OsuModel.Replay.parseLegacyFrames
  simp only []
  rw [s2_forIn_yield_ex _ s2_plfStep ?hF]
  · cases (t.splitOn ",").foldlM s2_plfStep (o, #[]) <;> rfl
  · intro fr st
    unfold s2_plfStep s2_pofS s2_diffS
    rcases fr.splitOn "|" with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, tail⟩⟩⟩⟩
    all_goals try rfl
    by_cases hs : (s0 == "-12345") = true
    · simp only [hs, ite_true]; rfl
    · simp only [hs, Bool.false_eq_true, ite_false]
      cases OsuModel.Replay.intTryParse s0 <;>
      (try cases Parsing.parseFloat s0) <;>
      cases Parsing.parseFloat s1 (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE) <;>
      cases Parsing.parseFloat s2 (F32.ofInt32 Parsing.MAX_COORDINATE_VALUE) <;>
      cases Parsing.parseInt s3 <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_i64_toInt (x : I64) : (abs x : Int64).toInt = x.val := by
  show (Int64.ofBitVec x.bv).toInt = x.val
  simp [Int64.toInt_ofBitVec]

theorem s2_i64_wadd (a b : I64) : (abs (core.num.I64.wrapping_add a b) : Int64) = abs a + abs b := rfl

theorem s2_i32_cast (d : Int32) : (abs (IScalar.cast .I64 (i32I d)) : Int64) = d.toInt64 := by
  apply Int64.toInt_inj.mp
  rw [s2_i64_toInt, Int32.toInt_toInt64]
  simp [IScalar.cast_val_eq, i32I]

theorem s2_fromi64 (x : I64) : float.F64.from_i64 x = ok (F64.ofInt64 (abs x)) := by
  simp [float.F64.from_i64, F64.ofInt64, s2_i64_toInt]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_chOf_comma (u : U32) (hu : u.val.isValidChar) : (chOf u == ',') = !(s2_ne 44 u) := by
  by_cases h : u.val = 44
  · have : chOf u = ',' := by simp only [chOf, h]
    simp [this, s2_ne, h]
  · have : chOf u ≠ ',' := by intro e; apply h; rw [← chOf_toNat u hu, e]; rfl
    simp [this, s2_ne, h]

theorem s2_str_split_comma (g : List U32) (hg : ∀ u ∈ g, u.val.isValidChar) :
    (String.ofList (g.map chOf)).splitOn "," =
      ((g.splitOnP (fun u => !(s2_ne 44 u))).map (List.map chOf)).map String.ofList := by
  rw [show "," = ','.toString from rfl, splitOn_char]
  congr 1
  show (g.map chOf).splitOnP (· == ',') = _
  rw [s2_splitOnP_map]
  congr 1
  apply s2_splitOnP_congr
  intro x hx; exact s2_chOf_comma x (hg x hx)

theorem s2_splitOnP_len {α : Type} (p : α → Bool) : ∀ l : List α, (l.splitOnP p).length ≤ l.length + 1 := by
  intro l
  induction l with
  | nil => simp [List.splitOnP_nil]
  | cons x xs ih =>
    rw [List.splitOnP_cons]
    split
    · simp; omega
    · cases h : xs.splitOnP p with
      | nil => simp [List.modifyHead]
      | cons y ys => rw [h] at ih; simp [List.modifyHead] at ih ⊢; omega

theorem s2_pof_some_len (g : List U32) (hg : ∀ u ∈ g, u.val.isValidChar) (x : Int32 × F32 × F32 × Int32)
    (h : s2_pofS (String.ofList (g.map chOf)) = .ok (some x)) : 3 ≤ g.length := by
  unfold s2_pofS at h
  rw [s2_str_split_pipe g hg] at h
  have hl := s2_splitOnP_len (fun u => !(s2_ne 124 u)) g
  rcases hL : g.splitOnP (fun u => !(s2_ne 124 u)) with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, rest⟩⟩⟩⟩
  all_goals rw [hL] at h hl
  all_goals simp at h hl
  all_goals omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the spec's comma segments of `text[a..]` -/
def s2_segS (t : Slice U32) (a : Nat) : List String :=
  ((s2_g t a t.val.length).splitOnP (fun u => !(s2_ne 44 u))).map (fun g => String.ofList (g.map chOf))

def s2_plfRel (len : Nat) (res : alloc.vec.Vec replay.frames.LegacyFrame × Option net.basic.NetExn) :
    Except NetExn (Int64 × Array OsuModel.Replay.LegacyFrame) → Prop
  | .ok st => res.2 = none ∧ (res.1.val.map abs).toArray = st.2 ∧ res.1.val.length ≤ len
  | .error _ => res.2.isSome

theorem s2_plf_done (t : Slice U32) (lt : I64) (out : alloc.vec.Vec replay.frames.LegacyFrame)
    (err : Option net.basic.NetExn) (a : Usize) :
    replay.frames.parse_legacy_frames_loop t lt out err a false = ok (out, err) := by
  unfold replay.frames.parse_legacy_frames_loop; rw [loop_unfold]
  simp [replay.frames.parse_legacy_frames_loop.body]

theorem s2_plf_err (t : Slice U32) (lt : I64) (out : alloc.vec.Vec replay.frames.LegacyFrame)
    (e : net.basic.NetExn) (a : Usize) (more : Bool) :
    replay.frames.parse_legacy_frames_loop t lt out (some e) a more = ok (out, some e) := by
  unfold replay.frames.parse_legacy_frames_loop; rw [loop_unfold]
  cases more <;> simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none]

theorem s2_plf_unfold (t : Slice U32) (lt : I64) (out : alloc.vec.Vec replay.frames.LegacyFrame)
    (err : Option net.basic.NetExn) (a : Usize) (more : Bool) :
    replay.frames.parse_legacy_frames_loop t lt out err a more = (do
      let r ← replay.frames.parse_legacy_frames_loop.body t lt out err a more
      match r with
      | .cont x => replay.frames.parse_legacy_frames_loop t x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
      | .done y => ok y) := by
  conv => lhs; unfold replay.frames.parse_legacy_frames_loop; rw [loop_unfold]
  dsimp only
  congr 1; funext r
  cases r with
  | cont x => unfold replay.frames.parse_legacy_frames_loop; rfl
  | done y => rfl

theorem s2_plf_loop (t : Slice U32) (ht : ValidStr t) (hn : t.val.length < 2^62) :
    ∀ (n : Nat) (a : Usize) (lt : I64) (out : alloc.vec.Vec replay.frames.LegacyFrame)
      (st : Int64 × Array OsuModel.Replay.LegacyFrame),
      t.val.length - a.val = n → a.val ≤ t.val.length → (abs lt : Int64) = st.1 → (out.val.map abs).toArray = st.2 →
      out.val.length ≤ a.val →
      ∃ res, replay.frames.parse_legacy_frames_loop t lt out none a true = ok res ∧
        s2_plfRel t.val.length res ((s2_segS t a.val).foldlM s2_plfStep st) := by
  have hmax := t.property
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a lt out st hn' ha hlt hout hol
  obtain ⟨b, hb, hbv⟩ := s2_segment_end t _ a rfl ha
  have hw := s2_tw_g 44 t a.val t.val.length
  have hseg := s2_g_split 44 t a.val t.val.length ha (le_refl _)
  generalize hW : (s2_g t a.val t.val.length).takeWhile (s2_ne 44) = W at hw hseg
  have hbv' : b.val = a.val + W.length := by
    rw [hbv, ← hW]; congr 3; simp [s2_g]
  have hble : b.val ≤ t.val.length := by
    have := (List.takeWhile_prefix (p := s2_ne 44) (l := s2_g t a.val t.val.length)).length_le
    rw [hW] at this; simp [s2_g] at this; omega
  have hpo := replay.frames.parse_one_frame_refines t ht hn a b (by omega) hble
  rw [show s2_g t a.val b.val = W by rw [hw, hbv']] at hpo
  have hsegS : s2_segS t a.val = String.ofList (W.map chOf) ::
      (if a.val + W.length < t.val.length then s2_segS t (a.val + W.length + 1) else []) := by
    unfold s2_segS; rw [hseg]; split <;> rfl
  rw [hsegS, List.foldlM_cons]
  have hse : replay.frames.segment_end t a = ok b := by unfold replay.frames.segment_end; exact hb
  have hfin : ∀ (lt1 : I64) (out1 : alloc.vec.Vec replay.frames.LegacyFrame) (st1 : Int64 × Array OsuModel.Replay.LegacyFrame),
      (abs lt1 : Int64) = st1.1 → (out1.val.map abs).toArray = st1.2 → out1.val.length ≤ b.val + 1 →
      out1.val.length ≤ t.val.length →
      (∀ b1 : Usize, b1.val = b.val + 1 → b.val < t.val.length →
        replay.frames.parse_legacy_frames_loop.body t lt out none a true = ok (.cont (lt1, out1, none, b1, true))) →
      (¬ b.val < t.val.length →
        replay.frames.parse_legacy_frames_loop.body t lt out none a true = ok (.cont (lt1, out1, none, a, false))) →
      ∃ res, replay.frames.parse_legacy_frames_loop t lt out none a true = ok res ∧
        s2_plfRel t.val.length res ((if a.val + W.length < t.val.length then s2_segS t (a.val + W.length + 1) else []).foldlM
          s2_plfStep st1) := by
    intro lt1 out1 st1 h1 h2 h3 h4 hc hd
    by_cases hbl : b.val < t.val.length
    · obtain ⟨b1, hb1, hb1v⟩ := usize_add_one b (by omega)
      rw [if_pos (by omega)]
      obtain ⟨res, hres, hrel⟩ := ih (t.val.length - b1.val) (by omega) b1 lt1 out1 st1 rfl (by omega) h1 h2 (by omega)
      refine ⟨res, ?_, ?_⟩
      · rw [s2_plf_unfold, hc b1 hb1v hbl, bind_ok]; exact hres
      · rw [show a.val + W.length + 1 = b1.val by omega]; exact hrel
    · rw [if_neg (by omega)]
      refine ⟨(out1, none), ?_, ⟨rfl, h2, h4⟩⟩
      rw [s2_plf_unfold, hd hbl, bind_ok]; exact s2_plf_done t lt1 out1 none a
  cases hp : s2_pofS (String.ofList (W.map chOf)) with
  | error e =>
    have hr : replay.frames.parse_one_frame t a b = ok (.Err (exnI e)) := by rw [hpo, hp]; rfl
    refine ⟨(out, some (exnI e)), ?_, by simp [s2_plfRel, s2_plfStep, hp, Bind.bind, Except.bind]⟩
    by_cases hbl : b.val < t.val.length
    · obtain ⟨b1, hb1, hb1v⟩ := usize_add_one b (by omega)
      have hb0 : replay.frames.parse_legacy_frames_loop.body t lt out none a true =
          ok (.cont (lt, out, some (exnI e), b1, true)) := by
        simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none, hse, hr, slice_lt_len_iff, hbl, hb1]
      rw [s2_plf_unfold, hb0, bind_ok]
      exact s2_plf_err t lt out (exnI e) b1 true
    · have hb0 : replay.frames.parse_legacy_frames_loop.body t lt out none a true =
          ok (.cont (lt, out, some (exnI e), a, false)) := by
        simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none, hse, hr, slice_lt_len_iff, hbl]
      rw [s2_plf_unfold, hb0, bind_ok]
      exact s2_plf_err t lt out (exnI e) a false
  | ok o =>
    cases o with
    | none =>
      have hr : replay.frames.parse_one_frame t a b = ok (.Ok none) := by rw [hpo, hp]; rfl
      have hstep : s2_plfStep st (String.ofList (W.map chOf)) = .ok st := by simp [s2_plfStep, hp]
      rw [hstep]
      exact hfin lt out st hlt hout (by omega) (by omega)
        (fun b1 hb1v hbl => by
          obtain ⟨b2, hb2, hb2v⟩ := usize_add_one b (by omega)
          have : b2 = b1 := UScalar.eq_of_val_eq (by omega)
          subst this
          simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none, hse, hr, slice_lt_len_iff, hbl, hb2])
        (fun hbl => by
          simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none, hse, hr, slice_lt_len_iff, hbl])
    | some x =>
      have hr : replay.frames.parse_one_frame t a b = ok (.Ok (some (s2_rawI x))) := by rw [hpo, hp]; rfl
      have h3 := s2_pof_some_len W (fun u hu => by rw [hw] at hu; exact s2_g_valid t ht _ _ u hu) x hp
      obtain ⟨d, mx, my, bt⟩ := x
      have hpl : out.val.length < Usize.max := by omega
      have hlt2 : (abs (core.num.I64.wrapping_add lt (IScalar.cast .I64 (i32I d))) : Int64) = st.1 + d.toInt64 := by
        simp only [s2_i64_wadd, s2_i32_cast, hlt]
      have hstep : s2_plfStep st (String.ofList (W.map chOf)) = .ok (st.1 + d.toInt64,
          st.2.push { time := F64.ofInt64 (st.1 + d.toInt64), mouseX := mx, mouseY := my, buttons := bt }) := by
        simp [s2_plfStep, hp]
      rw [hstep]
      refine hfin (core.num.I64.wrapping_add lt (IScalar.cast .I64 (i32I d)))
        (vpush out ⟨OsuModel.Net.F64.ofInt64 (abs (core.num.I64.wrapping_add lt (IScalar.cast .I64 (i32I d)))), mx, my,
          i32I bt⟩ hpl) _ hlt2 ?_ (by simp [vpush_val]; omega) (by simp [vpush_val]; omega) ?_ ?_
      · simp only [vpush_val, List.map_append, List.map_cons, List.map_nil, ← hout]
        rw [← List.push_toArray, ← hlt2]; rfl
      · intro b1 hb1v hbl
        obtain ⟨b2, hb2, hb2v⟩ := usize_add_one b (by omega)
        have : b2 = b1 := UScalar.eq_of_val_eq (by omega)
        subst this
        simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none, hse, hr, slice_lt_len_iff, hbl, hb2,
          s2_rawI, lift, float.F64.from_i64, vec_push_ok _ _ hpl, F64.ofInt64, s2_i64_toInt]
      · intro hbl
        simp [replay.frames.parse_legacy_frames_loop.body, core.option.Option.is_none, hse, hr, slice_lt_len_iff, hbl,
          s2_rawI, lift, float.F64.from_i64, vec_push_ok _ _ hpl, F64.ofInt64, s2_i64_toInt]
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Replay

def s2_isSkipPos (f : LegacyFrame) : Bool := f.mouseX == (256 : F32) && f.mouseY == (-500 : F32)

def s2_fixS (fs : Array LegacyFrame) : Array LegacyFrame := Id.run do
  let mut fs := fs
  if h : 2 ≤ fs.size then
    let f0 := fs[0]
    let f1 := fs[1]
    if f1.time < f0.time then
      fs := #[{ f0 with time := 0 }, { f1 with time := f0.time }] ++ fs.extract 2 fs.size
  if h : 3 ≤ fs.size then
    let f0 := fs[0]
    let f1 := fs[1]
    let f2 := fs[2]
    if f2.time < f0.time then
      fs := #[{ f0 with time := f2.time }, { f1 with time := f2.time }, f2] ++ fs.extract 3 fs.size
  if h : 2 ≤ fs.size then
    if s2_isSkipPos fs[1] then fs := fs.eraseIdx 1
  if h : 1 ≤ fs.size then
    if s2_isSkipPos fs[0] then fs := fs.eraseIdx 0
  let mut out : Array LegacyFrame := #[]
  for f in fs do
    match out.back? with
    | some cur => if f.time < cur.time then continue
    | none => pure ()
    out := out.push f
  return out

theorem s2_fix_eq (fs : Array LegacyFrame) : fixupFrames fs = s2_fixS fs := rfl
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Replay

def s2_dbS' (out : Array LegacyFrame) (f : LegacyFrame) : Array LegacyFrame :=
  match out.back? with
  | some cur => if f.time < cur.time then out else out.push f
  | none => out.push f

def s2_fx1 : List LegacyFrame → List LegacyFrame
  | f0 :: f1 :: rest => if f1.time < f0.time then { f0 with time := 0 } :: { f1 with time := f0.time } :: rest
      else f0 :: f1 :: rest
  | l => l
def s2_fx2 : List LegacyFrame → List LegacyFrame
  | f0 :: f1 :: f2 :: rest => if f2.time < f0.time then
      { f0 with time := f2.time } :: { f1 with time := f2.time } :: f2 :: rest else f0 :: f1 :: f2 :: rest
  | l => l
def s2_fx3 : List LegacyFrame → List LegacyFrame
  | f0 :: f1 :: rest => if s2_isSkipPos f1 then f0 :: rest else f0 :: f1 :: rest
  | l => l
def s2_fx4 : List LegacyFrame → List LegacyFrame
  | f0 :: rest => if s2_isSkipPos f0 then rest else f0 :: rest
  | l => l

theorem s2_forIn_yield_foldlA {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) : ∀ (l : List X) (s : S), forIn (m := Id) l s G = l.foldl g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x t ih => intro s; rw [List.forIn_cons, hG]; exact ih _

def s2_fa1 (fs : Array LegacyFrame) : Array LegacyFrame :=
  if h : 2 ≤ fs.size then
    if fs[1].time < fs[0].time then #[{ fs[0] with time := 0 }, { fs[1] with time := fs[0].time }] ++ fs.extract 2 fs.size
    else fs
  else fs
def s2_fa2 (fs : Array LegacyFrame) : Array LegacyFrame :=
  if h : 3 ≤ fs.size then
    if fs[2].time < fs[0].time then
      #[{ fs[0] with time := fs[2].time }, { fs[1] with time := fs[2].time }, fs[2]] ++ fs.extract 3 fs.size
    else fs
  else fs
def s2_fa3 (fs : Array LegacyFrame) : Array LegacyFrame :=
  if h : 2 ≤ fs.size then (if s2_isSkipPos fs[1] then fs.eraseIdx 1 else fs) else fs
def s2_fa4 (fs : Array LegacyFrame) : Array LegacyFrame :=
  if h : 1 ≤ fs.size then (if s2_isSkipPos fs[0] then fs.eraseIdx 0 else fs) else fs

theorem s2_forIn_arr {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) (a : Array X) (s : S) : forIn (m := Id) a s G = a.foldl g s := by
  rw [← Array.forIn_toList, s2_forIn_yield_foldlA G g hG, Array.foldl_toList]

set_option maxHeartbeats 200000 in
theorem s2_fixS_l3 (f0 f1 f2 : LegacyFrame) (rest : List LegacyFrame) :
    s2_fixS (f0 :: f1 :: f2 :: rest).toArray =
      (s2_fx4 (s2_fx3 (s2_fx2 (s2_fx1 (f0 :: f1 :: f2 :: rest))))).toArray.foldl s2_dbS' #[] := by
  have hF := s2_forIn_yield_foldlA (fun (f : LegacyFrame) (s : Array LegacyFrame) => (match s.back? with
      | some cur => if f.time < cur.time then pure (ForInStep.yield s) else pure (ForInStep.yield (s.push f))
      | none => pure (ForInStep.yield (s.push f)) : Id (ForInStep (Array LegacyFrame)))) s2_dbS'
    (by intro x s; unfold s2_dbS'; split <;> (try split) <;> rfl)
  unfold s2_fixS
  by_cases c1 : f1.time < f0.time
  all_goals simp [c1, s2_fx1, s2_fx2, s2_fx3, s2_fx4, List.extract_toArray, List.append_toArray, hF, s2_dbS']
  all_goals split_ifs <;> simp [*, s2_dbS']


end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Replay

theorem s2_fixS_list (l : List LegacyFrame) :
    s2_fixS l.toArray = (s2_fx4 (s2_fx3 (s2_fx2 (s2_fx1 l)))).toArray.foldl s2_dbS' #[] := by
  have hF := s2_forIn_yield_foldlA (fun (f : LegacyFrame) (s : Array LegacyFrame) => (match s.back? with
      | some cur => if f.time < cur.time then pure (ForInStep.yield s) else pure (ForInStep.yield (s.push f))
      | none => pure (ForInStep.yield (s.push f)) : Id (ForInStep (Array LegacyFrame)))) s2_dbS'
    (by intro x s; unfold s2_dbS'; split <;> (try split) <;> rfl)
  rcases l with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, rest⟩⟩⟩
  · rfl
  · unfold s2_fixS
    simp [s2_fx1, s2_fx2, s2_fx3, s2_fx4, List.extract_toArray, List.append_toArray, hF, s2_dbS']
    split_ifs <;> simp [*, s2_dbS']
  · unfold s2_fixS
    by_cases c1 : f1.time < f0.time
    all_goals simp [c1, s2_fx1, s2_fx2, s2_fx3, s2_fx4, List.extract_toArray, List.append_toArray, hF, s2_dbS']
    all_goals split_ifs <;> simp [*, s2_dbS']
  · exact s2_fixS_l3 f0 f1 f2 rest
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

def s2_rst1 (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) : Result (alloc.vec.Vec replay.frames.LegacyFrame) := do
  let i := alloc.vec.Vec.len fs0
  if i >= 2#usize
  then
    do
    let lf ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        replay.frames.LegacyFrame) fs0 1#usize
    let lf1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        replay.frames.LegacyFrame) fs0 0#usize
    let b ← float.F64.lt lf.time lf1.time
    if b
    then
      let (lf2, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          replay.frames.LegacyFrame) fs0 1#usize
      let f ← float.F64.from_bits 0#u64
      let fs01 := index_mut_back { lf2 with time := lf1.time }
      let (lf3, index_mut_back1) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          replay.frames.LegacyFrame) fs01 0#usize
      ok (index_mut_back1 { lf3 with time := f })
    else ok fs0
  else ok fs0

def s2_rst2 (fs : alloc.vec.Vec replay.frames.LegacyFrame) : Result (alloc.vec.Vec replay.frames.LegacyFrame) := do
  let i1 := alloc.vec.Vec.len fs
  if i1 >= 3#usize
  then
    do
    let lf ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        replay.frames.LegacyFrame) fs 2#usize
    let lf1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        replay.frames.LegacyFrame) fs 0#usize
    let b ← float.F64.lt lf.time lf1.time
    if b
    then
      let (lf2, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          replay.frames.LegacyFrame) fs 0#usize
      let fs2 := index_mut_back { lf2 with time := lf.time }
      let (lf3, index_mut_back1) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
          replay.frames.LegacyFrame) fs2 1#usize
      ok (index_mut_back1 { lf3 with time := lf.time })
    else ok fs
  else ok fs

def s2_rst3 (fs1 : alloc.vec.Vec replay.frames.LegacyFrame) : Result (alloc.vec.Vec replay.frames.LegacyFrame) := do
  let i2 := alloc.vec.Vec.len fs1
  if i2 >= 2#usize
  then
    do
    let lf ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        replay.frames.LegacyFrame) fs1 1#usize
    let b ← replay.frames.is_skip_pos lf
    if b
    then let s := alloc.vec.Vec.deref fs1
         replay.frames.erase_idx s 1#usize
    else ok fs1
  else ok fs1

def s2_rst4 (fs2 : alloc.vec.Vec replay.frames.LegacyFrame) : Result (alloc.vec.Vec replay.frames.LegacyFrame) := do
  let i3 := alloc.vec.Vec.len fs2
  if i3 >= 1#usize
  then
    do
    let lf ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        replay.frames.LegacyFrame) fs2 0#usize
    let b ← replay.frames.is_skip_pos lf
    if b
    then let s := alloc.vec.Vec.deref fs2
         replay.frames.erase_idx s 0#usize
    else ok fs2
  else ok fs2

theorem s2_fixup_eq (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) : replay.frames.fixup_frames fs0 = (do
    let fs ← s2_rst1 fs0
    let fs1 ← s2_rst2 fs
    let fs2 ← s2_rst3 fs1
    let fs3 ← s2_rst4 fs2
    replay.frames.drop_backwards (alloc.vec.Vec.deref fs3)) := rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_ob0 : Float.ofBits 0 = (0 : F64) := by decide
@[simp] theorem s2_absLF_time (f : replay.frames.LegacyFrame) : (abs f : OsuModel.Replay.LegacyFrame).time = f.time := rfl
@[simp] theorem s2_absLF_upd (f : replay.frames.LegacyFrame) (t : F64) :
    (abs ({ f with time := t } : replay.frames.LegacyFrame) : OsuModel.Replay.LegacyFrame) =
      { (abs f : OsuModel.Replay.LegacyFrame) with time := t } := rfl

theorem s2_rst1_ok (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) :
    ∃ fs, s2_rst1 fs0 = ok fs ∧ fs.val.map abs = s2_fx1 (fs0.val.map abs) ∧ fs.val.length = fs0.val.length := by
  rcases h : fs0.val with _ | ⟨f0, _ | ⟨f1, rest⟩⟩
  · refine ⟨fs0, ?_, by simp [h, s2_fx1], by simp [h]⟩
    simp [s2_rst1, show ¬ (alloc.vec.Vec.len fs0 >= 2#usize) by simp [h]]
  · refine ⟨fs0, ?_, by simp [h, s2_fx1], by simp [h]⟩
    simp [s2_rst1, show ¬ (alloc.vec.Vec.len fs0 >= 2#usize) by simp [h]]
  · have hl : fs0.val.length = rest.length + 2 := by simp [h]
    have h2 : alloc.vec.Vec.len fs0 >= 2#usize := by simp [hl]
    have e1 := vec_index_eq fs0 1#usize (by simp [hl])
    have e0 := vec_index_eq fs0 0#usize (by simp [hl])
    have m1 := vec_index_mut_eq fs0 1#usize (by simp [hl])
    simp only [h] at e1 e0 m1
    have hz : float.F64.from_bits 0#u64 = ok (0 : F64) := by simp [float.F64.from_bits] <;> decide
    by_cases c : f1.time < f0.time
    · let fs01 := alloc.vec.Vec.set fs0 1#usize { f1 with time := f0.time }
      have m0 := vec_index_mut_eq fs01 0#usize (by simp [fs01, vec_set_val', hl])
      refine ⟨alloc.vec.Vec.set fs01 0#usize { f0 with time := 0 }, ?_, ?_, ?_⟩
      · have m0' := vec_index_mut_usize_ok fs01 0#usize (by simp [fs01, vec_set_val', hl])
        simp [s2_rst1, h2, e1, e0, m1, float.F64.lt, c, hz, m0, fs01, s2_ob0]
        simp only [fs01] at m0'
        rw [m0']; simp [vec_set_val', h]
      · simp [fs01, vec_set_val', h, s2_fx1, c]
      · simp [fs01, vec_set_val', hl]
    · refine ⟨fs0, ?_, by simp [h, s2_fx1, c, abs], by simp [h]⟩
      simp [s2_rst1, h2, e1, e0, float.F64.lt, c]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_rst2_ok (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) :
    ∃ fs, s2_rst2 fs0 = ok fs ∧ fs.val.map abs = s2_fx2 (fs0.val.map abs) ∧ fs.val.length = fs0.val.length := by
  have triv : fs0.val.length < 3 → ∃ fs, s2_rst2 fs0 = ok fs ∧ fs.val.map abs = s2_fx2 (fs0.val.map abs) ∧
      fs.val.length = fs0.val.length := by
    intro hlt
    refine ⟨fs0, ?_, ?_, rfl⟩
    · simp [s2_rst2, show ¬ (alloc.vec.Vec.len fs0 >= 3#usize) by simp; omega]
    · rcases h : fs0.val with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, rest⟩⟩⟩
      · simp [s2_fx2]
      · simp [s2_fx2]
      · simp [s2_fx2]
      · exfalso; have := congrArg List.length h; simp at this; omega
  rcases h : fs0.val with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, rest⟩⟩⟩
  · rw [← h]; exact triv (by simp [h])
  · rw [← h]; exact triv (by simp [h])
  · rw [← h]; exact triv (by simp [h])
  have hl : fs0.val.length = rest.length + 3 := by simp [h]
  have h3 : alloc.vec.Vec.len fs0 >= 3#usize := by simp [hl]
  have e2 := vec_index_eq fs0 2#usize (by simp [hl])
  have e0 := vec_index_eq fs0 0#usize (by simp [hl])
  have m0 := vec_index_mut_eq fs0 0#usize (by simp [hl])
  simp only [h] at e2 e0 m0
  by_cases c : f2.time < f0.time
  · let fs01 := alloc.vec.Vec.set fs0 0#usize { f0 with time := f2.time }
    have m1' := vec_index_mut_usize_ok fs01 1#usize (by simp [fs01, vec_set_val', hl])
    refine ⟨alloc.vec.Vec.set fs01 1#usize { f1 with time := f2.time }, ?_, ?_, ?_⟩
    · simp [s2_rst2, h3, e2, e0, m0, float.F64.lt, c, fs01]
      simp only [fs01] at m1'
      rw [m1']; simp [vec_set_val', h]
    · simp [fs01, vec_set_val', h, s2_fx2, c]
    · simp [fs01, vec_set_val', hl]
  · refine ⟨fs0, ?_, by simp [h, s2_fx2, c], by simp [h]⟩
    simp [s2_rst2, h3, e2, e0, float.F64.lt, c]

theorem s2_isSkip_abs (f : replay.frames.LegacyFrame) :
    replay.frames.is_skip_pos f = ok (s2_isSkipPos (abs f)) := by
  rw [replay.frames.is_skip_pos_refines]; rfl

theorem s2_rst3_ok (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) :
    ∃ fs, s2_rst3 fs0 = ok fs ∧ fs.val.map abs = s2_fx3 (fs0.val.map abs) ∧ fs.val.length ≤ fs0.val.length := by
  have triv : fs0.val.length < 2 → ∃ fs, s2_rst3 fs0 = ok fs ∧ fs.val.map abs = s2_fx3 (fs0.val.map abs) ∧
      fs.val.length ≤ fs0.val.length := by
    intro hlt
    refine ⟨fs0, ?_, ?_, le_refl _⟩
    · simp [s2_rst3, show ¬ (alloc.vec.Vec.len fs0 >= 2#usize) by simp; omega]
    · rcases h : fs0.val with _ | ⟨f0, _ | ⟨f1, rest⟩⟩
      · simp [s2_fx3]
      · simp [s2_fx3]
      · exfalso; have := congrArg List.length h; simp at this; omega
  rcases h : fs0.val with _ | ⟨f0, _ | ⟨f1, rest⟩⟩
  · rw [← h]; exact triv (by simp [h])
  · rw [← h]; exact triv (by simp [h])
  have hl : fs0.val.length = rest.length + 2 := by simp [h]
  have h2 : alloc.vec.Vec.len fs0 >= 2#usize := by simp [hl]
  have e1 := vec_index_eq fs0 1#usize (by simp [hl])
  simp only [h] at e1
  by_cases c : s2_isSkipPos (abs f1) = true
  · obtain ⟨r, hr, hrv⟩ := replay.frames.erase_idx_refines (alloc.vec.Vec.deref fs0) 1#usize
    refine ⟨r, ?_, ?_, ?_⟩
    · simp [s2_rst3, h2, e1, s2_isSkip_abs, c, hr]
    · rw [hrv]; simp [ms_deref_val, h, s2_fx3, c]
    · rw [hrv]; simp [ms_deref_val, h]
  · refine ⟨fs0, ?_, by simp [h, s2_fx3, c], by simp [h]⟩
    simp [s2_rst3, h2, e1, s2_isSkip_abs, c]

theorem s2_rst4_ok (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) :
    ∃ fs, s2_rst4 fs0 = ok fs ∧ fs.val.map abs = s2_fx4 (fs0.val.map abs) ∧ fs.val.length ≤ fs0.val.length := by
  rcases h : fs0.val with _ | ⟨f0, rest⟩
  · refine ⟨fs0, ?_, by simp [h, s2_fx4], by simp [h]⟩
    simp [s2_rst4, show ¬ (alloc.vec.Vec.len fs0 >= 1#usize) by simp [h]]
  have hl : fs0.val.length = rest.length + 1 := by simp [h]
  have h1 : alloc.vec.Vec.len fs0 >= 1#usize := by simp [hl]
  have e0 := vec_index_eq fs0 0#usize (by simp [hl])
  simp only [h] at e0
  by_cases c : s2_isSkipPos (abs f0) = true
  · obtain ⟨r, hr, hrv⟩ := replay.frames.erase_idx_refines (alloc.vec.Vec.deref fs0) 0#usize
    refine ⟨r, ?_, ?_, ?_⟩
    · simp [s2_rst4, h1, e0, s2_isSkip_abs, c, hr]
    · rw [hrv]; simp [ms_deref_val, h, s2_fx4, c]
    · rw [hrv]; simp [ms_deref_val, h]
  · refine ⟨fs0, ?_, by simp [h, s2_fx4, c], by simp [h]⟩
    simp [s2_rst4, h1, e0, s2_isSkip_abs, c]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_dbS_size : ∀ (l : List OsuModel.Replay.LegacyFrame) (acc : Array OsuModel.Replay.LegacyFrame),
    (l.foldl s2_dbS acc).size ≤ acc.size + l.length := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    have := ih (s2_dbS acc x)
    have h2 : (s2_dbS acc x).size ≤ acc.size + 1 := by
      unfold s2_dbS; split <;> (try split) <;> simp
    omega

theorem replay.frames.fixup_frames_refines (fs0 : alloc.vec.Vec replay.frames.LegacyFrame) :
    ∃ r, replay.frames.fixup_frames fs0 = ok r ∧ OsuModel.Replay.fixupFrames (abs fs0) = abs r ∧
      r.val.length ≤ fs0.val.length := by
  obtain ⟨fs1, h1, e1, l1⟩ := s2_rst1_ok fs0
  obtain ⟨fs2, h2, e2, l2⟩ := s2_rst2_ok fs1
  obtain ⟨fs3, h3, e3, l3⟩ := s2_rst3_ok fs2
  obtain ⟨fs4, h4, e4, l4⟩ := s2_rst4_ok fs3
  obtain ⟨r, hr, er⟩ := replay.frames.drop_backwards_refines (alloc.vec.Vec.deref fs4)
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [s2_fixup_eq, h1, bind_ok, h2, bind_ok, h3, bind_ok, h4, bind_ok, hr]
  · rw [s2_fix_eq, show (abs fs0 : Array OsuModel.Replay.LegacyFrame) = (fs0.val.map abs).toArray from rfl, s2_fixS_list,
      ← e1, ← e2, ← e3, ← e4, ← er]
    show (fs4.val.map abs).toArray.foldl s2_dbS' #[] = ((alloc.vec.Vec.deref fs4).val.map abs).toArray.foldl s2_dbS #[]
    simp [ms_deref_val]; rfl
  · have hs : (abs r : Array OsuModel.Replay.LegacyFrame).size = r.val.length := by
      show (r.val.map abs).toArray.size = _; simp
    have := s2_dbS_size ((alloc.vec.Vec.deref fs4).val.map abs) #[]
    rw [← Array.foldl_toList] at er
    have ht : (abs (alloc.vec.Vec.deref fs4) : Array OsuModel.Replay.LegacyFrame).toList =
        (alloc.vec.Vec.deref fs4).val.map abs := by
      show ((alloc.vec.Vec.deref fs4).val.map abs).toArray.toList = _; simp
    rw [ht] at er; rw [er, hs] at this
    simp [ms_deref_val] at this
    omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- both succeed with related values, or both reject (= the eval slice's `ev_eRel`) -/
def s2_eR {α β ε ε'} (f : α → β) : core.result.Result α ε → Except ε' β → Prop
  | .Ok a, .ok b => f a = b
  | .Err _, .error _ => True
  | _, _ => False

theorem s2_segS_all (t : Slice U32) (ht : ValidStr t) :
    (String.ofList (strS t)).splitOn "," = s2_segS t 0 := by
  rw [show strS t = t.val.map chOf from rfl, s2_str_split_comma _ ht]
  unfold s2_segS
  rw [show s2_g t 0 t.val.length = t.val by simp [s2_g]]
  simp [Function.comp_def]

theorem replay.frames.parse_legacy_frames_refines (t : Slice U32) (ht : ValidStr t) (hn : t.val.length < 2^62)
    (off : I64) :
    ∃ r, replay.frames.parse_legacy_frames t off = ok r ∧
      s2_eR (fun v => (v.val.map abs).toArray) r (OsuModel.Replay.parseLegacyFrames (String.ofList (strS t)) (abs off)) ∧
      (∀ v, r = .Ok v → v.val.length ≤ t.val.length) := by
  obtain ⟨res, hres, hrel⟩ := s2_plf_loop t ht hn _ 0#usize off (alloc.vec.Vec.new _) ((abs off : Int64), #[]) rfl
    (by simp) rfl (by simp) (by simp)
  rw [s2_PLF_eq, s2_segS_all t ht]
  simp only [show (0#usize : Usize).val = 0 from rfl] at hrel
  obtain ⟨out, err⟩ := res
  cases hf : (s2_segS t 0).foldlM s2_plfStep ((abs off : Int64), #[]) with
  | error e =>
    rw [hf] at hrel
    simp only [s2_plfRel] at hrel
    cases err with
    | none => simp at hrel
    | some e' =>
      refine ⟨.Err e', ?_, ?_, ?_⟩
      · simp [replay.frames.parse_legacy_frames, hres]
      · simp [s2_eR, Functor.map, Except.map]
      · intro v hv; cases hv
  | ok st =>
    rw [hf] at hrel
    obtain ⟨h1, h2, h3⟩ := hrel
    simp only at h1 h2 h3
    subst h1
    refine ⟨.Ok out, ?_, ?_, ?_⟩
    · simp [replay.frames.parse_legacy_frames, hres]
    · simp [s2_eR, Functor.map, Except.map, h2]
    · intro v hv; cases hv; exact h3
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

noncomputable def s2_cf (f : replay.frames.LegacyFrame) : replay.frames.Frame :=
  (replay.frames.convert_frame_refines f).choose

theorem s2_cf_spec (f : replay.frames.LegacyFrame) : replay.frames.convert_frame f = ok (s2_cf f) ∧
    OsuModel.Replay.convertFrame (abs f) = abs (s2_cf f) :=
  ⟨(replay.frames.convert_frame_refines f).choose_spec.1, (replay.frames.convert_frame_refines f).choose_spec.2.1⟩

theorem s2_decode_loop (fixed : alloc.vec.Vec replay.frames.LegacyFrame) :
    ∀ (n : Nat) (out : alloc.vec.Vec replay.frames.Frame) (i : Usize), fixed.val.length - i.val = n →
      i.val ≤ fixed.val.length → out.val.length + (fixed.val.length - i.val) ≤ fixed.val.length →
      ∃ r, replay.frames.decode_loop fixed out i = ok r ∧ r.val = out.val ++ (fixed.val.drop i.val).map s2_cf := by
  have hmax := fixed.property
  intro n
  induction n with
  | zero =>
    intro out i hn hi ho
    refine ⟨out, ?_, by rw [List.drop_eq_nil_of_le (by omega)]; simp⟩
    unfold replay.frames.decode_loop; rw [loop_unfold]
    simp [replay.frames.decode_loop.body, vec_lt_len_iff, show ¬ i.val < fixed.val.length by omega]
  | succ n ih =>
    intro out i hn hi ho
    have hl : i.val < fixed.val.length := by omega
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hp : out.val.length < Usize.max := by omega
    obtain ⟨r, hr, hrv⟩ := ih (vpush out (s2_cf (fixed.val[i.val]'hl)) hp) i1 (by omega) (by omega)
      (by simp [vpush_val]; omega)
    refine ⟨r, ?_, ?_⟩
    · have hb : replay.frames.decode_loop.body fixed out i = ok (.cont (vpush out (s2_cf (fixed.val[i.val]'hl)) hp, i1)) := by
        simp [replay.frames.decode_loop.body, vec_lt_len_iff, hl, vec_index_eq fixed i hl, (s2_cf_spec _).1,
          vec_push_ok _ _ hp, hi1]
      unfold replay.frames.decode_loop; rw [loop_unfold]; simp only [hb, bind_ok]
      unfold replay.frames.decode_loop at hr; exact hr
    · rw [hrv, vpush_val, hi1v, List.drop_eq_getElem_cons hl, List.map_cons, List.append_assoc, List.singleton_append]

theorem replay.frames.decode_refines (t : Slice U32) (v : I64) (ht : ValidStr t) (hn : t.val.length < 2^62) :
    ∃ r, replay.frames.decode t v = ok r ∧
      s2_eR (fun fs => (fs.val.map abs).toArray) r (OsuModel.Replay.decode (String.ofList (strS t)) v.val) ∧
      ∀ fs, r = .Ok fs → fs.val.length ≤ t.val.length := by
  have hoff : ∃ off : I64, (if v < 5#i64 then ok 24#i64 else ok 0#i64 : Result I64) = ok off ∧
      (abs off : Int64) = (if v.val < 5 then 24 else 0) := by
    by_cases h : v.val < 5
    · exact ⟨24#i64, by simp [show v < 5#i64 by scalar_tac], by simp [h]; rfl⟩
    · exact ⟨0#i64, by simp [show ¬ v < 5#i64 by scalar_tac], by simp [h]; rfl⟩
  obtain ⟨off, hoff1, hoff2⟩ := hoff
  obtain ⟨r, hr, er, lr⟩ := replay.frames.parse_legacy_frames_refines t ht hn off
  unfold OsuModel.Replay.decode
  simp only [← hoff2]
  cases r with
  | Err e =>
    refine ⟨.Err e, by unfold replay.frames.decode; rw [hoff1, bind_ok, hr, bind_ok], ?_, fun fs h => by cases h⟩
    simp only [s2_eR] at er
    cases hp : OsuModel.Replay.parseLegacyFrames (String.ofList (strS t)) (abs off) with
    | error e' => simp [s2_eR, Bind.bind, Except.bind]
    | ok x => rw [hp] at er; exact er.elim
  | Ok fs =>
    obtain ⟨fixed, hfx, efx, lfx⟩ := replay.frames.fixup_frames_refines fs
    obtain ⟨out, hout, eout⟩ := s2_decode_loop fixed _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    refine ⟨.Ok out, by unfold replay.frames.decode; rw [hoff1, bind_ok, hr, bind_ok]; simp [hfx, hout], ?_, ?_⟩
    · cases hp : OsuModel.Replay.parseLegacyFrames (String.ofList (strS t)) (abs off) with
      | error e' => rw [hp] at er; exact er.elim
      | ok x =>
        rw [hp] at er
        simp only [s2_eR] at er
        show (out.val.map abs).toArray = (OsuModel.Replay.fixupFrames x).map OsuModel.Replay.convertFrame
        rw [← er, show ((fs.val.map abs).toArray : Array OsuModel.Replay.LegacyFrame) = abs fs from rfl, efx, eout]
        show _ = ((fixed.val.map abs).toArray).map OsuModel.Replay.convertFrame
        simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.nil_append,
          List.map_map, List.map_toArray]
        congr 1
        rw [show ((alloc.vec.Vec.from ([] : List replay.frames.Frame) (by simp)) : alloc.vec.Vec replay.frames.Frame).val = [] from rfl,
          List.nil_append, List.map_map]
        apply List.map_congr_left
        intro f _
        exact ((s2_cf_spec f).2).symm
    · intro fs' h; cases h
      rw [eout]; simp
      have := lr fs rfl; omega
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- FRAGMENT-OF: replay.frames.parse_one_frame (spec side: one `,`-separated segment of `splitOn ","`, as
`takeWhile (· ≠ ',')` on the code-point slice) -/
theorem replay.frames.segment_end_refines (s : Slice U32) (a : Usize) (ha : a.val ≤ s.val.length) :
    ∃ b, replay.frames.segment_end s a = ok b ∧ b.val = a.val + ((s.val.drop a.val).takeWhile (s2_ne 44)).length :=
  s2_segment_end s _ a rfl ha

/-- FRAGMENT-OF: replay.frames.parse_one_frame (spec side: `fr.splitOn "|"` restricted to the frame's four fields,
relation `s2_sfRel`) -/
theorem replay.frames.split_fields_refines : type_of% @s2_split_fields := @s2_split_fields
end OsuProofs
