/-
`beatmap::mod_settings`, part 2: `Convert.ChangeType` conversions (`convertToInt32`, `longToInt32`,
`boolParse`, `toInt32`, `toF64`, `toF32`, `toBool`) and `enumString`.
-/
import OsuProofs.Beatmap.ModSettings
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem ms_D0 : beatmap.mod_settings.D0 = ok (0 : F64) := by
  simp [beatmap.mod_settings.D0, float.F64.from_bits] <;> decide
theorem ms_D_HALF : beatmap.mod_settings.D_HALF = ok (0.5 : F64) := by
  simp [beatmap.mod_settings.D_HALF, float.F64.from_bits] <;> decide
theorem ms_D_MHALF : beatmap.mod_settings.D_MHALF = ok (-0.5 : F64) := by
  simp [beatmap.mod_settings.D_MHALF, float.F64.from_bits] <;> decide
theorem ms_D_I32_HI : beatmap.mod_settings.D_I32_HI = ok (2147483647.5 : F64) := by
  simp [beatmap.mod_settings.D_I32_HI, float.F64.from_bits] <;> decide
theorem ms_D_I32_LO : beatmap.mod_settings.D_I32_LO = ok (-2147483648.5 : F64) := by
  simp [beatmap.mod_settings.D_I32_LO, float.F64.from_bits] <;> decide

theorem i32S_wadd1 (r : I32) : i32S (core.num.I32.wrapping_add r 1#i32) = i32S r + 1 := rfl
theorem i32S_wsub1 (r : I32) : i32S (core.num.I32.wrapping_sub r 1#i32) = i32S r - 1 := rfl
theorem i32S_and1 (r : I32) : i32S (r &&& 1#i32) = i32S r &&& 1 := rfl
theorem i32_bne0 (x : I32) : (x != 0#i32) = (i32S x != 0) := by
  have h := i32S_beq x 0#i32
  rw [show i32S 0#i32 = 0 from rfl] at h
  simp only [bne, h]
  by_cases hx : x = 0#i32 <;> simp [hx]
theorem cast64_val (r : I32) : (IScalar.cast .I64 r).val = r.val := by
  rw [IScalar.cast_val_eq]; have := r.hBounds; simp [IScalar.min, IScalar.max] at *
theorem ofInt_cast64 (b : BitVec 32) :
    F64.ofInt ↑(IScalar.cast IScalarTy.I64 (b#iscalar : I32)) = F64.ofInt32 (Int32.ofBitVec b) := by
  rw [cast64_val, F64.ofInt32, ← i32S_toInt]; rfl

theorem beatmap.mod_settings.convert_to_int32_refines (v : F64) :
    beatmap.mod_settings.convert_to_int32 v = ok (exceptI i32I (Settings.convertToInt32 v)) := by
  unfold beatmap.mod_settings.convert_to_int32 Settings.convertToInt32
  simp only [ms_D0, ms_D_HALF, ms_D_MHALF, ms_D_I32_HI, ms_D_I32_LO, float.F64.le, float.F64.lt, float.F64.eq,
    float.F64.sub, float.F64.to_i32_sat, float.F64.from_i64, bind_ok, lift]
  simp only [ofInt_cast64, i32_bne0]
  rw [show Int32.ofBitVec v.toInt32.toBitVec = v.toInt32 from rfl]
  generalize hr : (IScalar.mk (ty := .I32) v.toInt32.toBitVec) = r
  have hrS : v.toInt32 = i32S r := by rw [← hr]; rfl
  rw [hrS, i32S_and1]
  generalize v - F64.ofInt32 (i32S r) = dif
  have ea : core.num.I32.wrapping_add r 1#i32 = i32I (i32S r + 1) := rfl
  have es : core.num.I32.wrapping_sub r 1#i32 = i32I (i32S r - 1) := rfl
  rw [ea, es]
  split_ifs <;> simp_all [exceptI, exnI] <;> rfl

theorem beatmap.mod_settings.long_to_int32_refines (v : I64) :
    beatmap.mod_settings.long_to_int32 v = ok (exceptI i32I (Settings.longToInt32 v.val)) := by
  unfold beatmap.mod_settings.long_to_int32 Settings.longToInt32
  by_cases h1 : -2147483648 ≤ v.val <;> by_cases h2 : v.val ≤ 2147483647
  · have h1' : (-2147483648)#i64 ≤ v := by show (-2147483648 : Int) ≤ v.val; exact h1
    have h2' : v ≤ 2147483647#i64 := by show v.val ≤ (2147483647 : Int); exact h2
    simp only [h1', h2', ite_true, lift, bind_ok, h1, h2, decide_true, Bool.and_self, exceptI]
    congr 2
  all_goals
    have h1' : ((-2147483648)#i64 ≤ v) ↔ -2147483648 ≤ v.val := Iff.rfl
    have h2' : (v ≤ 2147483647#i64) ↔ v.val ≤ 2147483647 := Iff.rfl
    simp [h1', h2', h1, h2, exceptI, exnI]

/-! ## `bool.Parse` -/

/-- the trim predicate of `bool.Parse` (white space or NUL) on a scalar value -/
def trU (u : U32) : Bool := isWhiteSpace (chOf u) || decide (u.val = 0)

theorem beatmap.mod_settings.is_trim_refines (c : U32) (h : c.val.isValidChar) :
    beatmap.mod_settings.is_trim c = ok (trU c) := by
  unfold beatmap.mod_settings.is_trim trU
  rw [beatmap.dotnet.is_white_space_refines c h, bind_ok]
  cases isWhiteSpace (chOf c) <;> simp [names_u32_eq_iff]

theorem tr_eq (s : Slice U32) (hs : ValidStr s) (i : Nat) (hi : i < s.val.length) :
    beatmap.mod_settings.is_trim (s.val[i]'hi) = ok (trU (s.val[i]'hi)) :=
  beatmap.mod_settings.is_trim_refines _ (hs _ (List.getElem_mem hi))

theorem bp_loop0 (s : Slice U32) (hs : ValidStr s) :
    ∀ lo : Usize, lo.val ≤ s.val.length → ∃ lo', beatmap.mod_settings.bool_parse_loop0 s lo = ok lo' ∧
      lo.val ≤ lo'.val ∧ lo'.val ≤ s.val.length ∧ s.val.drop lo'.val = (s.val.drop lo.val).dropWhile trU := by
  intro lo hlo
  unfold beatmap.mod_settings.bool_parse_loop0
  refine loop_ok _ (fun (x : Usize) => s.val.length - x.val)
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ s.val.length ∧ (s.val.drop x.val).dropWhile trU = (s.val.drop lo.val).dropWhile trU)
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ s.val.length ∧ s.val.drop x.val = (s.val.drop lo.val).dropWhile trU) ?_ lo
    ⟨le_refl _, hlo, rfl⟩
  intro x ⟨h1, h2, h3⟩
  by_cases hlt : x.val < s.val.length
  · have hlt' : x < Slice.len s := by show x.val < (Slice.len s).val; simpa using hlt
    have e2 : s.val.drop x.val = (s.val[x.val]'hlt) :: s.val.drop (x.val + 1) := List.drop_eq_getElem_cons hlt
    by_cases hw : trU (s.val[x.val]'hlt) = true
    · right
      obtain ⟨x1, hx1, hx1v⟩ := usize_add_one x (by have := s.property; omega)
      refine ⟨x1, by simp [beatmap.mod_settings.bool_parse_loop0.body, hlt', index_eq s x hlt, tr_eq s hs _ hlt, hw, hx1],
        ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [← h3, e2, List.dropWhile_cons_of_pos hw, hx1v]
    · left
      refine ⟨x, by simp [beatmap.mod_settings.bool_parse_loop0.body, hlt', index_eq s x hlt, tr_eq s hs _ hlt, hw],
        ⟨h1, h2, ?_⟩⟩
      rw [← h3, e2, List.dropWhile_cons_of_neg hw]
  · left
    have hlt' : ¬ x < Slice.len s := by show ¬ x.val < (Slice.len s).val; simpa using hlt
    refine ⟨x, by simp [beatmap.mod_settings.bool_parse_loop0.body, hlt'], ⟨h1, h2, ?_⟩⟩
    rw [← h3]
    have : s.val.drop x.val = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; rfl

/-- `TrimEnd` with the `bool.Parse` trim predicate -/
def rtrimT (l : List U32) : List U32 := (l.reverse.dropWhile trU).reverse

theorem rtrimT_append (l : List U32) (a : U32) : rtrimT (l ++ [a]) = if trU a then rtrimT l else l ++ [a] := by
  unfold rtrimT
  split
  · rename_i h; simp [List.dropWhile_cons_of_pos h]
  · rename_i h; simp [List.dropWhile_cons_of_neg h]

theorem bp_loop1 (s : Slice U32) (hs : ValidStr s) (lo : Usize) :
    ∀ hi : Usize, lo.val ≤ hi.val → hi.val ≤ s.val.length → ∃ hi', beatmap.mod_settings.bool_parse_loop1 s lo hi = ok hi' ∧
      lo.val ≤ hi'.val ∧ hi'.val ≤ hi.val ∧ segU s lo.val hi'.val = rtrimT (segU s lo.val hi.val) := by
  intro hi h0 hhi
  unfold beatmap.mod_settings.bool_parse_loop1
  refine loop_ok _ (fun (x : Usize) => x.val)
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ hi.val ∧ rtrimT (segU s lo.val x.val) = rtrimT (segU s lo.val hi.val))
    (fun (x : Usize) => lo.val ≤ x.val ∧ x.val ≤ hi.val ∧ segU s lo.val x.val = rtrimT (segU s lo.val hi.val)) ?_ hi
    ⟨h0, le_refl _, rfl⟩
  intro x ⟨h1, h2, h3⟩
  by_cases hgt : lo.val < x.val
  · have hgt' : x > lo := hgt
    obtain ⟨x1, hx1, hx1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := x) (y := 1#usize) (by simp; omega))
    simp at hx1v
    have hl : x1.val < s.val.length := by omega
    have hsn := segU_snoc s lo.val x.val hgt (by omega)
    by_cases hw : trU (s.val[x1.val]'hl) = true
    · right
      refine ⟨x1, by simp [beatmap.mod_settings.bool_parse_loop1.body, hgt', hx1, index_eq s x1 hl, tr_eq s hs _ hl, hw],
        ⟨by omega, by omega, ?_⟩, by omega⟩
      rw [← h3, hsn, rtrimT_append, hx1v]
      have : s.val[x.val - 1]'(by omega) = s.val[x1.val]'hl := by simp [hx1v]
      rw [this, if_pos hw]
    · left
      refine ⟨x, by simp [beatmap.mod_settings.bool_parse_loop1.body, hgt', hx1, index_eq s x1 hl, tr_eq s hs _ hl, hw],
        ⟨h1, h2, ?_⟩⟩
      rw [← h3, hsn, rtrimT_append]
      have : s.val[x.val - 1]'(by omega) = s.val[x1.val]'hl := by simp [hx1v]
      rw [this, if_neg hw]
  · left
    have hgt' : ¬ x > lo := hgt
    refine ⟨x, by simp [beatmap.mod_settings.bool_parse_loop1.body, hgt'], ⟨h1, h2, ?_⟩⟩
    rw [← h3]
    have : segU s lo.val x.val = [] := by unfold segU; simp; omega
    rw [this]; rfl

/-- `ascii_lower` as a function -/
def lowU (u : U32) : U32 := ⟨BitVec.ofNat 32 (if 65 ≤ u.val ∧ u.val ≤ 90 then u.val + 32 else u.val)⟩

theorem ascii_lower_eq (c : U32) : net.parse.ascii_lower c = ok (lowU c) := by
  obtain ⟨r, hr, hv⟩ := net.parse.ascii_lower_refines c
  rw [hr]; congr 1
  apply UScalar.eq_of_val_eq
  rw [hv]
  have := c.hBounds
  simp only [lowU, UScalar.val, BitVec.toNat_ofNat]
  split <;> simp at * <;> omega

theorem bp_loop2 (s : Slice U32) (hi : Usize) (hh : hi.val ≤ s.val.length) :
    ∀ (out : alloc.vec.Vec U32) (i : Usize), i.val ≤ hi.val → out.val.length + (hi.val - i.val) ≤ s.val.length →
      ∃ v, beatmap.mod_settings.bool_parse_loop2 s hi out i = ok v ∧
        v.val = out.val ++ ((s.val.drop i.val).take (hi.val - i.val)).map lowU := by
  intro out i hi0 hlen
  unfold beatmap.mod_settings.bool_parse_loop2
  refine loop_ok _ (fun (x : alloc.vec.Vec U32 × Usize) => hi.val - x.2.val)
    (fun (x : alloc.vec.Vec U32 × Usize) => x.2.val ≤ hi.val ∧ x.1.val.length + (hi.val - x.2.val) ≤ s.val.length ∧
      x.1.val ++ ((s.val.drop x.2.val).take (hi.val - x.2.val)).map lowU =
        out.val ++ ((s.val.drop i.val).take (hi.val - i.val)).map lowU)
    (fun (v : alloc.vec.Vec U32) => v.val = out.val ++ ((s.val.drop i.val).take (hi.val - i.val)).map lowU) ?_ (out, i)
    ⟨hi0, hlen, rfl⟩
  rintro ⟨o, j⟩ ⟨hj, hol, heq⟩
  dsimp only at hj hol heq ⊢
  by_cases hlt : j.val < hi.val
  · right
    have hlt' : j < hi := hlt
    have hjl : j.val < s.val.length := by omega
    obtain ⟨o1, ho1, ho1v⟩ := push_eq o (lowU (s.val[j.val]'hjl)) (by have := s.property; have := usize_ge_32; omega)
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := s.property; omega)
    refine ⟨(o1, j1), by simp [beatmap.mod_settings.bool_parse_loop2.body, hlt', index_eq s j hjl, ascii_lower_eq,
      ho1, hj1], ?_, by dsimp only; omega⟩
    refine ⟨by dsimp only; omega, by dsimp only; rw [ho1v]; simp; omega, ?_⟩
    dsimp only
    rw [ho1v, hj1v, ← heq]
    have e : hi.val - j.val = (hi.val - (j.val + 1)) + 1 := by omega
    have e2 : s.val.drop j.val = s.val[j.val] :: s.val.drop (j.val + 1) := List.drop_eq_getElem_cons hjl
    rw [e, e2, List.take_succ_cons]; simp only [List.map_cons, List.append_assoc, List.singleton_append]
  · left
    have hlt' : ¬ j < hi := hlt
    refine ⟨o, by simp [beatmap.mod_settings.bool_parse_loop2.body, hlt'], ?_⟩
    rw [← heq]
    have : hi.val - j.val = 0 := by omega
    simp [this]

theorem chOf_nul (u : U32) (h : u.val.isValidChar) : (chOf u == '\x00') = decide (u.val = 0) := by
  have := chOf_toNat u h
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e; rw [e] at this; simp at this; omega
  · intro e; apply Char.toNat_inj.mp; rw [this, e]; rfl

theorem lowU_val (u : U32) : (lowU u).val = if 65 ≤ u.val ∧ u.val ≤ 90 then u.val + 32 else u.val := by
  unfold lowU
  split
  · rename_i hA; show (BitVec.ofNat 32 (u.val + 32)).toNat = _; rw [BitVec.toNat_ofNat]; omega
  · show (BitVec.ofNat 32 u.val).toNat = _; rw [BitVec.toNat_ofNat]; have := u.hBounds; simp at this; omega

theorem lowU_valid (u : U32) (h : u.val.isValidChar) : (lowU u).val.isValidChar := by
  rw [lowU_val]; split
  · unfold Nat.isValidChar; omega
  · exact h

theorem chOf_lowU (u : U32) (h : u.val.isValidChar) : chOf (lowU u) = (chOf u).toLower := by
  have h1 := chOf_toNat u h
  have h1' : (chOf u).val.toNat = u.val := h1
  apply Char.toNat_inj.mp
  rw [chOf_toNat _ (lowU_valid u h), lowU_val]
  have hc : ((chOf u).val ≥ 'A'.val ∧ (chOf u).val ≤ 'Z'.val) ↔ (65 ≤ u.val ∧ u.val ≤ 90) := by
    rw [ge_iff_le, UInt32.le_iff_toNat_le, UInt32.le_iff_toNat_le, h1', show 'A'.val.toNat = 65 from rfl,
      show 'Z'.val.toNat = 90 from rfl]
  unfold Char.toLower
  by_cases hA : 65 ≤ u.val ∧ u.val ≤ 90
  · rw [if_pos hA, dif_pos (hc.mpr hA)]
    show u.val + 32 = ((chOf u).val + ('a'.val - 'A'.val)).toNat
    rw [UInt32.toNat_add, h1']; simp; omega
  · rw [if_neg hA, dif_neg (fun h' => hA (hc.mp h')), h1]

theorem dropWhile_trim_map (l : List U32) (hl : ∀ u ∈ l, u.val.isValidChar) :
    (l.map chOf).dropWhile (fun c => isWhiteSpace c || c == '\x00') = (l.dropWhile trU).map chOf := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := hl a (by simp)
    have e : (isWhiteSpace (chOf a) || chOf a == '\x00') = trU a := by rw [chOf_nul a ha]; rfl
    simp only [List.map_cons, List.dropWhile_cons, e]
    split
    · exact ih (fun u hu => hl u (by simp [hu]))
    · rfl

theorem rtrim_trim_map (l : List U32) (hl : ∀ u ∈ l, u.val.isValidChar) :
    ((l.map chOf).reverse.dropWhile (fun c => isWhiteSpace c || c == '\x00')).reverse = (rtrimT l).map chOf := by
  unfold rtrimT
  rw [← List.map_reverse, dropWhile_trim_map _ (fun u hu => hl u (List.mem_reverse.mp hu)), List.map_reverse]

theorem str_true : "true".toList = [Char.ofNat 116, Char.ofNat 114, Char.ofNat 117, Char.ofNat 101] := by decide
theorem str_false : "false".toList = [Char.ofNat 102, Char.ofNat 97, Char.ofNat 108, Char.ofNat 115, Char.ofNat 101] := by
  decide

theorem beatmap.mod_settings.bool_parse_refines (s : Slice U32) (hs : ValidStr s) :
    beatmap.mod_settings.bool_parse s = ok (exceptI id (Settings.boolParse (String.ofList (strS s)))) := by
  obtain ⟨lo, hlo, h01, h02, h03⟩ := bp_loop0 s hs 0#usize (by simp)
  have hlen : (Slice.len s).val = s.val.length := by simp
  obtain ⟨hi, hhi, g1, g2, g3⟩ := bp_loop1 s hs lo (Slice.len s) (by rw [hlen]; exact h02) (by rw [hlen])
  rw [hlen] at g2
  obtain ⟨v, hv, hvv⟩ := bp_loop2 s hi g2 (alloc.vec.Vec.new U32) lo g1 (by simp; omega)
  have h03' : s.val.drop lo.val = s.val.dropWhile trU := by simpa using h03
  have hseg : (s.val.drop lo.val).take (hi.val - lo.val) = rtrimT (s.val.dropWhile trU) := by
    have := g3; unfold segU at this; rw [this, hlen, ← segU, segU_full, h03']
  have hvv' : v.val = (rtrimT (s.val.dropWhile trU)).map lowU := by rw [hvv, hseg]; simp
  have hvalid : ∀ u ∈ rtrimT (s.val.dropWhile trU), u.val.isValidChar := by
    intro u hu
    unfold rtrimT at hu
    have := (List.dropWhile_sublist _).subset (List.mem_reverse.mp hu)
    rw [List.mem_reverse] at this
    exact hs u ((List.dropWhile_sublist _).subset this)
  have hvs : ValidStr (alloc.vec.Vec.deref v) := by
    intro u hu
    rw [ms_deref_val, hvv'] at hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact lowU_valid w (hvalid w hw)
  have hstr : strS (alloc.vec.Vec.deref v) =
      (String.ofList (((strS s).dropWhile (fun c => isWhiteSpace c || c == '\x00')).reverse.dropWhile
        (fun c => isWhiteSpace c || c == '\x00')).reverse).toList.map Char.toLower := by
    rw [String.toList_ofList]
    unfold strS
    rw [dropWhile_trim_map _ hs, rtrim_trim_map _ (fun u hu => hs u ((List.dropWhile_sublist _).subset hu)), ms_deref_val,
      hvv', List.map_map, List.map_map]
    apply List.map_congr_left
    intro u hu
    exact chOf_lowU u (hvalid u hu)
  unfold beatmap.mod_settings.bool_parse Settings.boolParse
  simp only [hlo, bind_ok, hhi, hv, lift, Array.to_slice, Array.make, beatmap.dotnet.str_eq_refines _ hvs]
  simp only [String.toList_ofList] at hstr ⊢
  simp only [← hstr]
  generalize strS (alloc.vec.Vec.deref v) = L
  simp only [litS, str_true, str_false, beq_iff_eq]
  simp
  split_ifs <;> simp_all [exceptI, exnI]


/-! ## `Convert.ChangeType` -/

theorem vvalid_deref (s : alloc.vec.Vec U32) (h : VValid s) : ValidStr (alloc.vec.Vec.deref s) := by
  intro u hu; rw [ms_deref_val] at hu; exact h u hu

theorem strS_deref (s : alloc.vec.Vec U32) : strS (alloc.vec.Vec.deref s) = (vstrS s).toList := by
  simp [strS, vstrS]

theorem beatmap.mod_settings.to_int32_refines (j : beatmap.mod_settings.JsonVal) (hj : JOk j) :
    beatmap.mod_settings.to_int32 j = ok (exceptI i32I (Settings.toInt32 (jvS j))) := by
  cases j with
  | Long v => simp [beatmap.mod_settings.to_int32, Settings.toInt32, jvS, beatmap.mod_settings.long_to_int32_refines]
  | Big => simp [beatmap.mod_settings.to_int32, Settings.toInt32, jvS, exceptI, exnI]
  | Double v =>
    simp [beatmap.mod_settings.to_int32, Settings.toInt32, jvS, beatmap.mod_settings.convert_to_int32_refines]
  | Bool b => cases b <;> simp [beatmap.mod_settings.to_int32, Settings.toInt32, jvS, exceptI] <;> rfl
  | Str s =>
    simp only [beatmap.mod_settings.to_int32, Settings.toInt32, jvS]
    rw [net.parse.int_parse_refines _ (vvalid_deref s hj.1), strS_deref]; rfl
  | Null => simp [beatmap.mod_settings.to_int32, Settings.toInt32, jvS, exceptI, exnI]

theorem f64_one_bits : float.F64.from_bits 4607182418800017408#u64 = ok (1 : F64) := by
  simp [float.F64.from_bits] <;> decide
theorem f32_one_bits : float.F32.from_bits 1065353216#u32 = ok (1 : F32) := by
  simp [float.F32.from_bits] <;> decide

theorem beatmap.mod_settings.to_f64_refines (j : beatmap.mod_settings.JsonVal) (hj : JOk j) :
    beatmap.mod_settings.to_f64 j = ok (exceptI id (Settings.toF64 (jvS j))) := by
  cases j with
  | Long v => simp [beatmap.mod_settings.to_f64, Settings.toF64, jvS, float.F64.from_i64, exceptI]
  | Big => simp [beatmap.mod_settings.to_f64, Settings.toF64, jvS, exceptI, exnI]
  | Double v => simp [beatmap.mod_settings.to_f64, Settings.toF64, jvS, exceptI]
  | Bool b => cases b <;> simp [beatmap.mod_settings.to_f64, Settings.toF64, jvS, exceptI, f64_one_bits, ms_D0] <;> decide
  | Str s =>
    simp only [beatmap.mod_settings.to_f64, Settings.toF64, jvS]
    rw [net.parse.double_parse_refines _ (vvalid_deref s hj.1) (by simpa using hj.2), strS_deref]; rfl
  | Null => simp [beatmap.mod_settings.to_f64, Settings.toF64, jvS, exceptI, exnI]

theorem beatmap.mod_settings.to_f32_refines (j : beatmap.mod_settings.JsonVal) (hj : JOk j) :
    beatmap.mod_settings.to_f32 j = ok (exceptI id (Settings.toF32 (jvS j))) := by
  cases j with
  | Long v => simp [beatmap.mod_settings.to_f32, Settings.toF32, jvS, float.F32.from_i64, exceptI]
  | Big => simp [beatmap.mod_settings.to_f32, Settings.toF32, jvS, exceptI, exnI]
  | Double v => simp [beatmap.mod_settings.to_f32, Settings.toF32, jvS, float.F64.to_f32, exceptI]
  | Bool b =>
    cases b <;> simp [beatmap.mod_settings.to_f32, Settings.toF32, jvS, exceptI, f32_one_bits, f32_from_bits_zero] <;> decide
  | Str s =>
    simp only [beatmap.mod_settings.to_f32, Settings.toF32, jvS]
    rw [net.parse.float_parse_refines _ (vvalid_deref s hj.1) (by simpa using hj.2), strS_deref]; rfl
  | Null => simp [beatmap.mod_settings.to_f32, Settings.toF32, jvS, exceptI, exnI]

theorem vstrS_eq_lit (s : alloc.vec.Vec U32) (hs : VValid s) (lit : String) (h) (hl : litS h = lit.toList) :
    decide (strS (alloc.vec.Vec.deref s) = litS h) = decide (vstrS s = lit) := by
  rw [strS_deref, hl]
  congr 1; apply propext; constructor
  · intro e; rw [← String.ofList_toList (s := vstrS s), e, String.ofList_toList]
  · intro e; rw [e]

theorem beatmap.mod_settings.to_bool_refines (bb : Bool) (j : beatmap.mod_settings.JsonVal) (hj : JOk j) :
    beatmap.mod_settings.to_bool bb j = ok (exceptI id (Settings.toBool bb (jvS j))) := by
  cases j with
  | Long v =>
    simp [beatmap.mod_settings.to_bool, Settings.toBool, jvS, exceptI]
    by_cases hv : v = 0#i64
    · subst hv; rfl
    · have : v.val ≠ 0 := fun h => hv (IScalar.eq_of_val_eq (by simpa using h))
      rw [bne_iff_ne.mpr hv, bne_iff_ne.mpr this]
  | Big => simp [beatmap.mod_settings.to_bool, Settings.toBool, jvS, exceptI, exnI]
  | Double v => simp [beatmap.mod_settings.to_bool, Settings.toBool, jvS, exceptI, ms_D0, float.F64.eq]
  | Bool b => simp [beatmap.mod_settings.to_bool, Settings.toBool, jvS, exceptI]
  | Str s =>
    have hv := vvalid_deref s hj.1
    simp only [beatmap.mod_settings.to_bool, Settings.toBool, jvS, lift, Array.to_slice, Array.make,
      beatmap.dotnet.str_eq_refines _ hv, bind_ok]
    rw [vstrS_eq_lit s hj.1 "1" _ (by simp [litS]), vstrS_eq_lit s hj.1 "0" _ (by simp [litS]),
      beatmap.mod_settings.bool_parse_refines _ hv, strS_deref, String.ofList_toList]
    generalize vstrS s = t
    by_cases h1 : t = "1"
    · subst h1; cases bb <;> simp [exceptI]
    · by_cases h0 : t = "0"
      · subst h0; cases bb <;> simp [exceptI]
      · simp only [h1, h0, decide_false, Bool.false_eq_true, ite_false]
  | Null => simp [beatmap.mod_settings.to_bool, Settings.toBool, jvS, exceptI, exnI]

end OsuProofs
