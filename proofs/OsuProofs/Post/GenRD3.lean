/-
Generator mods, part 4 (gen agent): Except-monad index loops (`gen_iterE`, lockstep `gen_loop_iterE`) and
`beatmap::mod_random::apply_decreasing_shift` (both loops; spec normal form `gen_adsS`).
-/
import OsuProofs.Post.GenRD2
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

/-- `k` iterations of an index-dependent `Except`-loop body starting at index `j` (early exit / error). -/
def gen_iterE {ε S : Type} (f : Nat → S → Except ε (ForInStep S)) : Nat → Nat → S → Except ε S
  | _, 0, s => .ok s
  | j, k+1, s => match f j s with
    | .error e => .error e
    | .ok (.done c) => .ok c
    | .ok (.yield c) => gen_iterE f (j + 1) k c

theorem gen_forIn_range'_iterE {ε S : Type} (f : Nat → S → Except ε (ForInStep S)) :
    ∀ (k j : Nat) (s : S), forIn (m := Except ε) (List.range' j k) s f = gen_iterE f j k s := by
  intro k
  induction k with
  | zero => intro j s; rfl
  | succ k ih =>
    intro j s
    rw [List.range'_succ, List.forIn_cons]
    simp only [gen_iterE]
    cases h : f j s with
    | error e => rfl
    | ok r =>
      cases r with
      | done c => rfl
      | yield c => exact ih (j + 1) c

theorem gen_forIn_range_iterE {ε S : Type} (f : Nat → S → Except ε (ForInStep S)) (lo hi : Nat) (s : S) :
    forIn (m := Except ε) [lo:hi] s f = gen_iterE f lo (hi - lo) s := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.div_one]
  rw [show hi - lo + 1 - 1 = hi - lo by omega]
  exact gen_forIn_range'_iterE f (hi - lo) lo s

/-- Lockstep: an Aeneas index loop (with an error flag) refines `gen_iterE`. -/
theorem gen_loop_iterE {T Y S ε : Type} (body : T → Result (ControlFlow T Y)) (f : Nat → S → Except ε (ForInStep S))
    (n : Nat) (idx : T → Nat) (R : T → S → Prop) (Q : Y → Except ε S → Prop)
    (hstep : ∀ t s, R t s → idx t < n →
      (∀ s', f (idx t) s = .ok (.yield s') → ∃ t', body t = ok (.cont t') ∧ idx t' = idx t + 1 ∧ R t' s') ∧
      (∀ s', f (idx t) s = .ok (.done s') → ∃ y, (body t = ok (.done y) ∨
        ∃ t', body t = ok (.cont t') ∧ body t' = ok (.done y)) ∧ Q y (.ok s')) ∧
      (∀ e, f (idx t) s = .error e → ∃ y, (body t = ok (.done y) ∨
        ∃ t', body t = ok (.cont t') ∧ body t' = ok (.done y)) ∧ Q y (.error e)))
    (hend : ∀ t s, R t s → n ≤ idx t → ∃ y, body t = ok (.done y) ∧ Q y (.ok s)) :
    ∀ t s, R t s → idx t ≤ n → ∃ y, loop body t = ok y ∧ Q y (gen_iterE f (idx t) (n - idx t) s) := by
  intro t
  induction hk : n - idx t using Nat.strong_induction_on generalizing t with
  | _ k ih =>
    intro s hR hle
    have fin : ∀ y q, (body t = ok (.done y) ∨ ∃ t', body t = ok (.cont t') ∧ body t' = ok (.done y)) →
        Q y q → ∃ y', loop body t = ok y' ∧ Q y' q := by
      intro y q hb hq
      refine ⟨y, ?_, hq⟩
      rcases hb with hb | ⟨t', hb, hb'⟩
      · rw [loop_unfold, hb]; simp only [bind_ok]
      · rw [loop_unfold, hb]; simp only [bind_ok]; rw [loop_unfold, hb']; simp only [bind_ok]
    by_cases hlt : idx t < n
    · obtain ⟨hy, hd, he⟩ := hstep t s hR hlt
      have e : n - idx t = (n - (idx t + 1)) + 1 := by omega
      rw [← hk, e]; simp only [gen_iterE]
      cases hf : f (idx t) s with
      | error er => obtain ⟨y, hb, hq⟩ := he er hf; exact fin y _ hb hq
      | ok r =>
        cases r with
        | done s' => obtain ⟨y, hb, hq⟩ := hd s' hf; exact fin y _ hb hq
        | yield s' =>
          obtain ⟨t', hb, hi, hR'⟩ := hy s' hf
          obtain ⟨y, hl, hq⟩ := ih (n - idx t') (by omega) t' rfl s' hR' (by omega)
          refine ⟨y, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
          rw [hi] at hq; exact hq
    · obtain ⟨y, hb, hq⟩ := hend t s hR (by omega)
      refine ⟨y, by rw [loop_unfold, hb]; simp only [bind_ok], ?_⟩
      rw [← hk, show n - idx t = 0 by omega]; exact hq
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

/-- the (up to 10) consecutive preceding hit circles of `i`, nearest first (`repositionHitObjects`) -/
def gen_tbsS (hos : Array OsuHitObject) (i : Nat) : Array Nat := Id.run do
  let mut toBeShifted : Array Nat := #[]
  for k in [1:11] do
    if k > i then break
    if !hos[i - k]!.isCircle then break
    toBeShifted := toBeShifted.push (i - k)
  return toBeShifted

def gen_tbsF (hos : Array OsuHitObject) (i : Nat) (k : Nat) (s : Array Nat) : ForInStep (Array Nat) :=
  if k > i then .done s else if !hos[i - k]!.isCircle then .done s else .yield (s.push (i - k))

theorem gen_tbs_eq (hos : Array OsuHitObject) (i : Nat) : gen_tbsS hos i = iterR (gen_tbsF hos i) 1 10 #[] := by
  unfold gen_tbsS
  simp only [Id.run]
  rw [forIn_range_iterR]
  refine congrArg (fun F => iterR F 1 (11 - 1) #[]) ?_
  funext k s
  unfold gen_tbsF
  split_ifs <;> rfl

theorem gen_ads_loop0 (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (i : Usize) (hi : i.val < hos.val.length) :
    ∃ y, beatmap.mod_random.apply_decreasing_shift_loop0 hos i (alloc.vec.Vec.new Usize) 1#usize true = ok y ∧
      y.val.map (·.val) = (gen_tbsS (abs hos) i.val).toList ∧ (∀ x ∈ y.val, x.val < i.val) ∧ y.val.length ≤ 10 := by
  rw [gen_tbs_eq]
  have := loop_iterR (fun t : alloc.vec.Vec Usize × Usize × Bool =>
      beatmap.mod_random.apply_decreasing_shift_loop0.body hos i t.1 t.2.1 t.2.2)
    (gen_tbsF (abs hos) i.val) 11 (fun t => t.2.1.val)
    (fun t s => t.2.2 = true ∧ t.1.val.map (·.val) = s.toList ∧ 1 ≤ t.2.1.val ∧ (∀ x ∈ t.1.val, x.val < i.val) ∧
      t.1.val.length + 1 = t.2.1.val ∧ t.2.1.val ≤ 11)
    (fun y s => y.val.map (·.val) = s.toList ∧ (∀ x ∈ y.val, x.val < i.val) ∧ y.val.length ≤ 10)
    (by
      rintro ⟨tb, k, go⟩ s ⟨hgo, hs, hk1, hx, hl, hk11'⟩ hlt
      simp only at hgo hs hk1 hx hl hk11' hlt ⊢
      subst hgo
      have hk11 : k < 11#usize := by scalar_tac
      by_cases hki : k.val > i.val
      · have hki' : k > i := hki
        have hF : gen_tbsF (abs hos) i.val k.val s = .done s := by simp [gen_tbsF, hki]
        rw [hF]
        refine ⟨(fun s' h => by cases h), fun s' h => ?_⟩
        cases h
        refine ⟨tb, Or.inr ⟨(tb, k, false), ?_, ?_⟩, hs, hx, by omega⟩
        · simp only [beatmap.mod_random.apply_decreasing_shift_loop0.body, hk11, hki', if_true]
        · simp only [beatmap.mod_random.apply_decreasing_shift_loop0.body, Bool.false_eq_true, if_false]
      · have hki' : ¬ k > i := hki
        obtain ⟨i1, hi1, hi1v⟩ : ∃ i1 : Usize, i - k = ok i1 ∧ i1.val = i.val - k.val := by
          obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := k) (by scalar_tac))
          exact ⟨z, hz, by have := hzv; scalar_tac⟩
        have hil : i1.val < hos.val.length := by omega
        have hc := beatmap.objects.is_circle_refines (hos.val[i1.val]'hil)
        have hga : (abs hos : Array OsuHitObject)[i.val - k.val]! = abs (hos.val[i1.val]'hil) := by
          rw [gen_abs_get hos _ (by omega)]; simp only [hi1v]
        by_cases hci : (abs (hos.val[i1.val]'hil) : OsuHitObject).isCircle
        · have hF : gen_tbsF (abs hos) i.val k.val s = .yield (s.push (i.val - k.val)) := by
            simp [gen_tbsF, hki, hga, hci]
          rw [hF]
          refine ⟨fun s' h => ?_, (fun s' h => by cases h)⟩
          cases h
          have hpush : tb.val.length < Usize.max := by scalar_tac
          obtain ⟨k1, hk1', hk1v⟩ := usize_add_one k (by scalar_tac)
          refine ⟨(vpush tb i1 hpush, k1, true), ?_, by simp only; omega, rfl, ?_, by simp only; omega, ?_, ?_, by simp only; omega⟩
          · simp only [beatmap.mod_random.apply_decreasing_shift_loop0.body, hk11, hki', if_true, if_false, hi1,
              bind_ok, vec_index_eq _ _ hil, hc, hci, vec_push_ok _ _ hpush, hk1']
          · simp [hs, hi1v]
          · intro x hxm
            simp only [vpush_val, List.mem_append, List.mem_singleton] at hxm
            rcases hxm with hxm | hxm
            · exact hx x hxm
            · subst hxm; omega
          · simp only [vpush_val, List.length_append, List.length_singleton]; omega
        · have hF : gen_tbsF (abs hos) i.val k.val s = .done s := by
            simp [gen_tbsF, hki, hga, hci]
          rw [hF]
          refine ⟨(fun s' h => by cases h), fun s' h => ?_⟩
          cases h
          refine ⟨tb, Or.inr ⟨(tb, k, false), ?_, ?_⟩, hs, hx, by omega⟩
          · simp only [beatmap.mod_random.apply_decreasing_shift_loop0.body, hk11, hki', if_true, if_false, hi1,
              bind_ok, vec_index_eq _ _ hil, hc, hci, Bool.false_eq_true]
          · simp only [beatmap.mod_random.apply_decreasing_shift_loop0.body, Bool.false_eq_true, if_false])
    (by
      rintro ⟨tb, k, go⟩ s ⟨hgo, hs, hk1, hx, hl, hk11'⟩ hge
      simp only at hgo hs hk1 hx hl hk11' hge ⊢
      subst hgo
      have hk11 : ¬ k < 11#usize := by scalar_tac
      exact ⟨tb, by simp only [beatmap.mod_random.apply_decreasing_shift_loop0.body, hk11, if_true, if_false], hs, hx,
        by omega⟩)
    (alloc.vec.Vec.new Usize, 1#usize, true) #[] ⟨rfl, rfl, by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new], by simp⟩
    (by simp)
  obtain ⟨y, hl, hq⟩ := this
  exact ⟨y, by unfold beatmap.mod_random.apply_decreasing_shift_loop0; exact hl, hq⟩
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

open Mods.Reposition in
/-- `applyDecreasingShift` of `repositionHitObjects` on object `i` -/
def gen_adsS (hos0 : Array OsuHitObject) (i : Nat) (shift : Vec2) : DecodeM (Array OsuHitObject) := do
  let toBeShifted := gen_tbsS hos0 i
  let mut hos := hos0
  let count := toBeShifted.size
  for idx in [0:count] do
    let j := toBeShifted[idx]!
    let hj := hos[j]!
    let f : F32 := F32.ofInt (count - idx : Nat) / F32.ofInt (count + 1 : Nat)
    let position := hj.position + ⟨shift.x * f, shift.y * f⟩
    let p ← clampWithPadding position (F64.toF32 hj.radius)
    hos := hos.set! j (Mods.setPosition hj p)
  return hos

open Mods.Reposition in
def gen_adsF (tbs : Array Nat) (shift : Vec2) (idx : Nat) (hos : Array OsuHitObject) :
    Except String (ForInStep (Array OsuHitObject)) :=
  let j := tbs[idx]!
  let hj := hos[j]!
  let f : F32 := F32.ofInt (tbs.size - idx : Nat) / F32.ofInt (tbs.size + 1 : Nat)
  match clampWithPadding (hj.position + ⟨shift.x * f, shift.y * f⟩) (F64.toF32 hj.radius) with
  | .error e => .error e
  | .ok p => .ok (.yield (hos.set! j (Mods.setPosition hj p)))

theorem gen_ads_eq (hos : Array OsuHitObject) (i : Nat) (shift : Vec2) :
    gen_adsS hos i shift = gen_iterE (gen_adsF (gen_tbsS hos i) shift) 0 (gen_tbsS hos i).size hos := by
  unfold gen_adsS
  simp only []
  rw [gen_forIn_range_iterE, bind_pure, Nat.sub_zero]
  refine congrArg (fun F => gen_iterE F 0 (gen_tbsS hos i).size hos) ?_
  funext idx s
  unfold gen_adsF
  simp only []
  split <;> next heq => rw [heq]; rfl

open Classical in
/-- the value of a `Result` known to be `ok` (opaque to `simp`, unlike `Exists.choose` of a refinement) -/
noncomputable def gen_val {α} [Inhabited α] (m : Result α) : α := if h : ∃ a, m = ok a then h.choose else default
theorem gen_val_eq {α} [Inhabited α] (m : Result α) (h : ∃ a, m = ok a) : m = ok (gen_val m) := by
  unfold gen_val; rw [dif_pos h]; exact h.choose_spec

instance : Inhabited (core.result.Result net.osutk.Vector2 beatmap.hit_object_parser.DecodeError) := ⟨.Ok ⟨0, 0⟩⟩

noncomputable def gen_cwpR (p : net.osutk.Vector2) (pad : F32) : core.result.Result net.osutk.Vector2 beatmap.hit_object_parser.DecodeError :=
  gen_val (beatmap.mod_random.clamp_with_padding p pad)
theorem gen_cwp_ok (p : net.osutk.Vector2) (pad : F32) :
    beatmap.mod_random.clamp_with_padding p pad = ok (gen_cwpR p pad) := by
  obtain ⟨r, hr, -⟩ := beatmap.mod_random.clamp_with_padding_refines p pad
  exact gen_val_eq _ ⟨r, hr⟩
theorem gen_cwp_rel (p : net.osutk.Vector2) (pad : F32) :
    hRel bv2S (gen_cwpR p pad) (Mods.Reposition.clampWithPadding (bv2S p) pad) := by
  obtain ⟨r, hr, hrel⟩ := beatmap.mod_random.clamp_with_padding_refines p pad
  have := gen_cwp_ok p pad; rw [hr] at this; rw [← Result.ok_injective this]; exact hrel

noncomputable def gen_radR (h : beatmap.objects.OsuHitObject) : F64 := gen_val (beatmap.objects.radius h)
theorem gen_rad_ok (h : beatmap.objects.OsuHitObject) : beatmap.objects.radius h = ok (gen_radR h) := by
  obtain ⟨r, hr, -⟩ := beatmap.objects.radius_refines h
  exact gen_val_eq _ ⟨r, hr⟩
theorem gen_rad_abs (h : beatmap.objects.OsuHitObject) : gen_radR h = (abs h : OsuHitObject).radius := by
  obtain ⟨r, hr, hrv⟩ := beatmap.objects.radius_refines h
  have := gen_rad_ok h; rw [hr] at this; rw [← Result.ok_injective this]; exact hrv.symm

theorem gen_cwp_split (r : core.result.Result net.osutk.Vector2 beatmap.hit_object_parser.DecodeError)
    (p : net.osutk.Vector2) (pad : F32) (h : gen_cwpR p pad = r) :
    hRel bv2S r (Mods.Reposition.clampWithPadding (bv2S p) pad) := h ▸ gen_cwp_rel p pad

theorem gen_hrel_ok {α β} {f : α → β} {a : α} {x : Except String β} (h : hRel f (.Ok a) x) : x = .ok (f a) := by
  cases x with
  | ok b => simp only [hRel] at h; rw [h]
  | error e => simp [hRel] at h
theorem gen_hrel_err {α β} {f : α → β} {e} {x : Except String β} (h : hRel f (.Err e) x) : ∃ e', x = .error e' := by
  cases x with
  | ok b => simp [hRel] at h
  | error e => exact ⟨e, rfl⟩

theorem gen_cast_u64 (x : Usize) (h : x.val < 2^64) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]; simp; omega

theorem gen_ads_loop1 (hos0 : alloc.vec.Vec beatmap.objects.OsuHitObject) (shift : net.osutk.Vector2)
    (tb : alloc.vec.Vec Usize) (htb : ∀ x ∈ tb.val, x.val < hos0.val.length) (htl : tb.val.length ≤ 10)
    (hg : GenOkL hos0.val) (h64 : System.Platform.numBits = 64) :
    ∃ y, beatmap.mod_random.apply_decreasing_shift_loop1 hos0 shift tb (alloc.vec.Vec.len tb) 0#usize none = ok y ∧
      GenOkL y.1.val ∧ y.1.val.length = hos0.val.length ∧
      (match gen_iterE (gen_adsF (tb.val.map (·.val)).toArray (bv2S shift)) 0 tb.val.length (abs hos0) with
       | .ok s => y.2 = none ∧ (abs y.1 : Array OsuHitObject) = s
       | .error _ => y.2.isSome) := by
  have := gen_loop_iterE (fun t : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × Option beatmap.hit_object_parser.DecodeError =>
      beatmap.mod_random.apply_decreasing_shift_loop1.body shift tb (alloc.vec.Vec.len tb) t.1 t.2.1 t.2.2)
    (gen_adsF (tb.val.map (·.val)).toArray (bv2S shift)) tb.val.length (fun t => t.2.1.val)
    (fun t s => t.2.2 = none ∧ (abs t.1 : Array OsuHitObject) = s ∧ GenOkL t.1.val ∧ t.1.val.length = hos0.val.length)
    (fun y q => GenOkL y.1.val ∧ y.1.val.length = hos0.val.length ∧
      (match q with
       | .ok s => y.2 = none ∧ (abs y.1 : Array OsuHitObject) = s
       | .error _ => y.2.isSome))
    (by
      rintro ⟨hs, idx, err⟩ s ⟨herr, habs, hgl, hlen⟩ hlt
      simp only at herr habs hgl hlen hlt ⊢
      subst herr habs
      have hi : idx.val < tb.val.length := hlt
      have hj : (tb.val[idx.val]'hi).val < hs.val.length := by rw [hlen]; exact htb _ (List.getElem_mem hi)
      obtain ⟨d, hd, hdv⟩ : ∃ d : Usize, alloc.vec.Vec.len tb - idx = ok d ∧ d.val = tb.val.length - idx.val := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := alloc.vec.Vec.len tb) (y := idx) (by scalar_tac))
        exact ⟨z, hz, by have := hzv; scalar_tac⟩
      obtain ⟨c1, hc1, hc1v⟩ := usize_add_one (alloc.vec.Vec.len tb) (by scalar_tac)
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one idx (by scalar_tac)
      have hcd : (UScalar.cast .U64 d).val = tb.val.length - idx.val := by rw [gen_cast_u64 d (by scalar_tac), hdv]
      have hcc : (UScalar.cast .U64 c1).val = tb.val.length + 1 := by rw [gen_cast_u64 c1 (by scalar_tac), hc1v]; simp
      have hpj := gen_okl_paths _ hgl _ hj
      have hgj := gen_okl_get _ hgl _ hj
      simp only [beatmap.mod_random.apply_decreasing_shift_loop1.body, core.option.Option.is_none, vec_lt_len_iff, hi,
        if_true, vec_index_eq _ _ hi, bind_ok, hd, hc1, lift, float.F32.from_u64, hcd, hcc, float.F32.div,
        vec_index_eq _ _ hj, float.F32.mul, beatmap.vector2.add_refines, gen_rad_ok, float.F64.to_f32,
        gen_cwp_ok, bm_vector2_ZERO]
      unfold gen_adsF
      have hmi : (List.map (fun x : Usize => x.val) tb.val)[idx.val]! = (tb.val[idx.val]'hi).val := by
        rw [getElem!_pos _ _ (by simpa using hi)]; simp
      simp only [List.size_toArray, List.length_map, List.getElem!_toArray, hmi, gen_abs_get hs _ hj,
        Option.isNone_none, if_true]
      generalize hR : gen_cwpR _ _ = R
      have hrel := gen_cwp_split _ _ _ hR
      rw [gen_rad_abs] at hrel
      generalize hS : Mods.Reposition.clampWithPadding _ _ = S
      have hSR : hRel bv2S R S := by rw [← hS]; exact hrel
      cases R with
      | Ok q =>
        have hSq := gen_hrel_ok hSR
        subst hSq
        obtain ⟨h2, e2, v2⟩ := beatmap.mods.set_position_refines _ q hpj h64
        simp only [bind_ok, uncurry_apply_pair, Option.isNone_none, if_true, vec_index_mut_eq _ _ hj, e2, hi1]
        refine ⟨?_, (fun s' h => by cases h), (fun e h => by cases h)⟩
        intro s' hs'
        cases hs'
        refine ⟨_, rfl, hi1v, rfl, ?_, ?_, by simp [vec_set_val', hlen]⟩
        · rw [gen_abs_set, ← v2]
        · rw [vec_set_val']
          exact gen_okl_set _ hgl _ _ (by rw [← v2, gen_ok_setpos]; exact hgj)
      | Err e =>
        obtain ⟨e', he'⟩ := gen_hrel_err hSR
        subst he'
        simp only [bind_ok, uncurry_apply_pair, Option.isNone_some, Bool.false_eq_true, if_false, hi1]
        refine ⟨(fun s' h => by cases h), (fun s' h => by cases h), fun e2 h => ?_⟩
        refine ⟨(hs, some e), Or.inr ⟨_, rfl, ?_⟩, hgl, hlen, rfl⟩
        simp [beatmap.mod_random.apply_decreasing_shift_loop1.body])
    (by
      rintro ⟨hs, idx, err⟩ s ⟨herr, habs, hgl, hlen⟩ hge
      simp only at herr habs hgl hlen hge ⊢
      subst herr habs
      have : ¬ idx < alloc.vec.Vec.len tb := by rw [vec_lt_len_iff]; omega
      exact ⟨(hs, none), by simp [beatmap.mod_random.apply_decreasing_shift_loop1.body, this], hgl, hlen, rfl, rfl⟩)
    (hos0, 0#usize, none) (abs hos0) ⟨rfl, rfl, hg, rfl⟩ (by simp)
  obtain ⟨y, hl, hq1, hq2, hq3⟩ := this
  exact ⟨y, by unfold beatmap.mod_random.apply_decreasing_shift_loop1; exact hl, hq1, hq2, hq3⟩

theorem beatmap.mod_random.apply_decreasing_shift_refines (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (i : Usize) (shift : net.osutk.Vector2) (hi : i.val < hos.val.length) (hg : GenOkL hos.val)
    (h64 : System.Platform.numBits = 64) :
    ∃ e hos', beatmap.mod_random.apply_decreasing_shift hos i shift = ok (e, hos') ∧ GenOkL hos'.val ∧
      hos'.val.length = hos.val.length ∧
      hRel (fun _ => (abs hos' : Array OsuHitObject)) e (gen_adsS (abs hos) i.val (bv2S shift)) := by
  obtain ⟨tb, h0, htb, hx, hl⟩ := gen_ads_loop0 hos i hi
  obtain ⟨y, h1, hg1, hl1, hq⟩ := gen_ads_loop1 hos shift tb (fun x hx' => by have := hx x hx'; omega) hl hg h64
  have hT : gen_tbsS (abs hos) i.val = (tb.val.map (·.val)).toArray := by
    rw [htb]
  unfold beatmap.mod_random.apply_decreasing_shift
  simp only [h0, bind_ok, h1]
  rw [gen_ads_eq, hT]
  simp only [List.size_toArray, List.length_map]
  obtain ⟨hos', err⟩ := y
  simp only at hg1 hl1 hq ⊢
  revert hq
  generalize gen_iterE _ _ _ _ = q
  intro hq
  cases q with
  | ok s =>
    obtain ⟨he, hs⟩ := hq
    subst he
    exact ⟨_, _, rfl, hg1, hl1, hs⟩
  | error e =>
    cases err with
    | none => simp at hq
    | some e' => exact ⟨_, _, rfl, hg1, hl1, trivial⟩
end OsuProofs

