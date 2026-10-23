/-
`net::random` (Rust) refines `OsuModel.Net.NetRandom` (`System.Random(int seed)`, Knuth's
subtractive generator). Representation: the Rust `[i32; 56]` seed array ↦ the spec `Array Int`
(values), indices `usize` ↦ `Nat`. Theorems are stated for valid states (`inext, inextp < 56`).
-/
import OsuProofs.Net.FrameworkA
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

def arrS {n : Usize} (a : Std.Array I32 n) : Array Int := (a.val.map (·.val)).toArray
def stS (s : net.random.State) : NetRandom.State := ⟨arrS s.a, s.inext.val, s.inextp.val⟩
def stOk (s : net.random.State) : Prop := s.inext.val < 56 ∧ s.inextp.val < 56

theorem arr56_len (a : Std.Array I32 56#usize) : a.val.length = 56 := by
  simp

theorem arr_update {α} (a : Std.Array α 56#usize) (i : Usize) (x : α) (h : i.val < 56) :
    Std.Array.update a i x = ok (a.set i x) := by
  obtain ⟨y, hy, rfl⟩ := eq_ok_of_spec (Std.Array.update_spec a i x (by simpa using h))
  exact hy

theorem arr_index (a : Std.Array I32 56#usize) (i : Usize) (h : i.val < 56) :
    Std.Array.index_usize a i = ok (a.val[i.val]'(by rw [arr56_len]; exact h)) := by
  obtain ⟨y, hy, rfl⟩ := eq_ok_of_spec (Std.Array.index_usize_spec a i (by simpa using h))
  exact hy

theorem arrS_set (a : Std.Array I32 56#usize) (i : Usize) (x : I32) :
    arrS (a.set i x) = (arrS a).set! i.val x.val := by
  simp [arrS, List.map_set]

theorem arrS_get (a : Std.Array I32 56#usize) (i : Nat) (h : i < 56) :
    (arrS a)[i]! = (a.val[i]'(by rw [arr56_len]; exact h)).val := by
  have h' : i < a.val.length := by rw [arr56_len]; exact h
  simp [arrS, h', List.getElem?_eq_getElem h']

theorem arr_index' (a : Std.Array I32 56#usize) (i : Usize) (h : i.val < 56) :
    ∃ x, Std.Array.index_usize a i = ok x ∧ (arrS a)[i.val]! = x.val :=
  ⟨_, arr_index a i h, arrS_get a i.val h⟩

theorem wrap32_eq (x : Int) : NetRandom.wrap32 x = Int.bmod x (2^32) := by
  simp [NetRandom.wrap32, Int32.toInt_ofInt]

theorem MBIG_val : net.random.MBIG.val = 2147483647 := by unfold net.random.MBIG; rfl

theorem idx_step (x : Usize) (hx : x.val < 56) : ∃ k : Usize,
    (∀ {β : Type} (f : Usize → Result β),
      (do let i ← x + 1#usize; let k ← (if i >= 56#usize then ok 1#usize else ok i); f k) = f k) ∧
    k.val = (if x.val + 1 ≥ 56 then 1 else x.val + 1) ∧ k.val < 56 := by
  obtain ⟨i, hi, hiv⟩ := usize_add_one x (by have := Usize.bounds_eq; simp [U32.max_eq, U64.max_eq] at this; omega)
  by_cases h : x.val + 1 ≥ 56
  · have : i >= 56#usize := by show (56#usize).val ≤ i.val; simp; omega
    have h56 : 56 ≤ i.val := by omega
    exact ⟨1#usize, by intro β f; simp [hi, h56], by simp [h], by simp⟩
  · have : ¬ (i >= 56#usize) := by show ¬ (56#usize).val ≤ i.val; simp; omega
    have h56 : ¬ 56 ≤ i.val := by omega
    exact ⟨i, by intro β f; simp [hi, h56], by simp [h, hiv], by omega⟩

theorem i32_eq_iff (a b : I32) : a = b ↔ a.val = b.val := by
  constructor
  · rintro rfl; rfl
  · intro h; exact IScalar.eq_of_val_eq h

theorem net.random.internal_sample_refines (st : net.random.State) (hs : stOk st) :
    ∃ n st', net.random.internal_sample st = ok (n, st') ∧ stOk st' ∧
      (n.val, stS st') = NetRandom.internalSample (stS st) := by
  obtain ⟨h1, h2⟩ := hs
  obtain ⟨k1, hk1, hk1v, hk1l⟩ := idx_step st.inext h1
  obtain ⟨k2, hk2, hk2v, hk2l⟩ := idx_step st.inextp h2
  unfold net.random.internal_sample
  obtain ⟨x, hxe, hx⟩ := arr_index' st.a k1 hk1l
  obtain ⟨y, hye, hy⟩ := arr_index' st.a k2 hk2l
  rw [hk1, hk2, hxe, hye]
  simp only [lift, bind_ok]
  have hM := MBIG_val
  by_cases hm : core.num.I32.wrapping_sub x y = net.random.MBIG
  · obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (I32.sub_spec (x := core.num.I32.wrapping_sub x y) (y := 1#i32)
      (by rw [hm]; simp [hM, I32.min_eq]) (by rw [hm]; simp [hM, I32.max_eq]))
    rw [hm] at hz hzv
    have hz0 : ¬ z.val < 0 := by rw [hzv, hM]; simp
    refine ⟨z, ⟨st.a.set k1 z, k1, k2⟩, ?_, ⟨hk1l, hk2l⟩, ?_⟩
    · simp [hm, hz, hz0, arr_update _ _ _ hk1l]
    · have hmv := congrArg IScalar.val hm
      simp at hmv
      simp only [NetRandom.internalSample, stS]
      by_cases c1 : st.inext.val + 1 ≥ 56 <;> by_cases c2 : st.inextp.val + 1 ≥ 56 <;>
        simp only [c1, c2, ite_true, ite_false] at hk1v hk2v ⊢ <;> rw [hk1v] at hx <;> rw [hk2v] at hy <;>
        simp [hx, hy, wrap32_eq, hmv, hM, hzv, hm, arrS_set, NetRandom.MBIG, hk1v, hk2v]
      all_goals (have hxy : x.val = y.val := by rw [← hx, ← hy]
                 simp [hxy, hM] at hmv)
  · have hmv : ¬ (Int.bmod (x.val - y.val) 4294967296 = 2147483647) := by
      intro h; apply hm; rw [i32_eq_iff]; simp [h, hM]
    let w := core.num.I32.wrapping_sub x y
    let n2 := if w.val < 0 then core.num.I32.wrapping_add w net.random.MBIG else w
    refine ⟨n2, ⟨st.a.set k1 n2, k1, k2⟩, ?_, ⟨hk1l, hk2l⟩, ?_⟩
    · simp [hm, arr_update _ _ _ hk1l, n2, w]
    · simp only [NetRandom.internalSample, stS]
      by_cases c1 : st.inext.val + 1 ≥ 56 <;> by_cases c2 : st.inextp.val + 1 ≥ 56 <;>
        simp only [c1, c2, ite_true, ite_false] at hk1v hk2v ⊢ <;> rw [hk1v] at hx <;> rw [hk2v] at hy <;>
        by_cases hneg : Int.bmod (x.val - y.val) 4294967296 < 0 <;>
        simp [n2, w, hx, hy, wrap32_eq, hmv, hM, arrS_set, NetRandom.MBIG, hk1v, hk2v, hneg]
      all_goals (have hxy : x.val = y.val := by rw [← hx, ← hy]
                 simp_all)

@[simp] theorem random_INV_MBIG : net.random.INV_MBIG = ok NetRandom.invMBIG := by
  simp [net.random.INV_MBIG, NetRandom.invMBIG]

theorem net.random.sample_refines (st : net.random.State) (hs : stOk st) :
    ∃ f st', net.random.sample st = ok (f, st') ∧ stOk st' ∧ (f, stS st') = NetRandom.sample (stS st) := by
  obtain ⟨n, st', h, hok, heq⟩ := net.random.internal_sample_refines st hs
  refine ⟨F64.ofInt n.val * NetRandom.invMBIG, st', ?_, hok, ?_⟩
  · simp [net.random.sample, h, lift]
  · simp only [NetRandom.sample, ← heq]

theorem net.random.next_double_refines (st : net.random.State) (hs : stOk st) :
    ∃ f st', net.random.next_double st = ok (f, st') ∧ stOk st' ∧
      (f, stS st') = NetRandom.nextDouble (stS st) :=
  net.random.sample_refines st hs

theorem i32S_ofInt (n : I32) : Int32.ofInt n.val = i32S n := by
  apply Int32.toInt_inj.mp
  rw [i32S_toInt, Int32.toInt_ofInt]
  have h1 := n.hmin; have h2 := n.hmax
  simp [I32.min, I32.max, IScalar.min, IScalar.max] at h1 h2
  exact Int.bmod_eq_of_le (by simp [Int32.size]; omega) (by simp [Int32.size]; omega)

theorem net.random.next_refines (st : net.random.State) (hs : stOk st) :
    ∃ n st', net.random.next st = ok (n, st') ∧ stOk st' ∧ (i32S n, stS st') = NetRandom.next (stS st) := by
  obtain ⟨n, st', h, hok, heq⟩ := net.random.internal_sample_refines st hs
  refine ⟨n, st', by simp [net.random.next, h], hok, ?_⟩
  simp only [NetRandom.next, ← heq, i32S_ofInt]

/-- Rust `Result<T, NetExn>` vs spec `Except NetExn T'` under a value relation. -/
def resRel {α β} (R : α → β → Prop) : core.result.Result α net.basic.NetExn → Except NetExn β → Prop
  | .Ok a, .ok b => R a b
  | .Err e, .error e' => exnS e = e'
  | _, _ => False

def stRel (p : I32 × net.random.State) (q : Int32 × NetRandom.State) : Prop :=
  i32S p.1 = q.1 ∧ stS p.2 = q.2 ∧ stOk p.2

@[simp] theorem i32S_i32I (x : Int32) : i32S (i32I x) = x := rfl
@[simp] theorem i32S_mk (x : Int32) : i32S ⟨x.toBitVec⟩ = x := rfl

theorem i32S_lt (a b : I32) : i32S a < i32S b ↔ a.val < b.val := by
  rw [Int32.lt_iff_toInt_lt, i32S_toInt, i32S_toInt]

theorem net.random.next_max_refines (st : net.random.State) (hs : stOk st) (mv : I32) :
    ∃ r, net.random.next_max st mv = ok r ∧ resRel stRel r (NetRandom.nextMax (stS st) (i32S mv)) := by
  unfold net.random.next_max NetRandom.nextMax
  by_cases h : mv.val < 0
  · have h' : i32S mv < 0 := by rw [show (0 : Int32) = i32S 0#i32 by rfl, i32S_lt]; simpa using h
    have h'' : mv < 0#i32 := by simpa using h
    exact ⟨.Err .ArgumentOutOfRange, by simp [h''], by simp [h', resRel, exnS]⟩
  · have h' : ¬ i32S mv < 0 := by rw [show (0 : Int32) = i32S 0#i32 by rfl, i32S_lt]; simpa using h
    have h'' : ¬ mv < 0#i32 := by simpa using h
    obtain ⟨f, st', hsm, hok, heq⟩ := net.random.sample_refines st hs
    refine ⟨_, by simp [h'', hsm, lift]; rfl, ?_⟩
    simp only [h', ite_false, ← heq, resRel, stRel, i32S_i32I, F64.ofInt32, i32S_toInt]
    simp [hok]

theorem tmod2_iff (m : Int) : Int.tmod m 2 = 0 ↔ m % 2 = 0 := by
  rw [← Int.dvd_iff_tmod_eq_zero, Int.dvd_iff_emod_eq_zero]

theorem net.random.sample_for_large_range_refines (st : net.random.State) (hs : stOk st) :
    ∃ f st', net.random.sample_for_large_range st = ok (f, st') ∧ stOk st' ∧
      (f, stS st') = NetRandom.sampleForLargeRange (stS st) := by
  obtain ⟨n0, st1, h1, hok1, heq1⟩ := net.random.internal_sample_refines st hs
  obtain ⟨m, st2, h2, hok2, heq2⟩ := net.random.internal_sample_refines st1 hok1
  obtain ⟨r, hr, hrv⟩ := eq_ok_of_spec (IScalar.rem_spec m (y := 2#i32) (by simp))
  have c1 : net.random.C2147483646 = ok NetRandom.sampleForLargeRange.c2147483646 := by
    simp [net.random.C2147483646, NetRandom.sampleForLargeRange.c2147483646]
  have c2 : net.random.C4294967293 = ok NetRandom.sampleForLargeRange.c4294967293 := by
    simp [net.random.C4294967293, NetRandom.sampleForLargeRange.c4294967293]
  have hn0 := n0.hmin; have hn0' := n0.hmax
  simp [I32.min, I32.max, IScalar.min, IScalar.max] at hn0 hn0'
  by_cases hm : m.val % 2 = 0
  · have hr0 : r = 0#i32 := by rw [i32_eq_iff]; simp [hrv, (tmod2_iff _).mpr hm]
    obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step (IScalar.cast .I64 n0)
      (by intro h; simp [IScalar.min, I64.min_eq] at h; omega))
    refine ⟨(F64.ofInt (-n0.val) + NetRandom.sampleForLargeRange.c2147483646) /
      NetRandom.sampleForLargeRange.c4294967293, st2, ?_, hok2, ?_⟩
    · simp [net.random.sample_for_large_range, h1, h2, hr, hr0, lift, c1, c2, HNeg.hNeg, hq, hqv]
    · simp only [NetRandom.sampleForLargeRange, ← heq1, ← heq2, hm]; simp
  · have hr0 : ¬ r = 0#i32 := by rw [i32_eq_iff]; simp [hrv]; rw [tmod2_iff]; exact hm
    refine ⟨(F64.ofInt n0.val + NetRandom.sampleForLargeRange.c2147483646) /
      NetRandom.sampleForLargeRange.c4294967293, st2, ?_, hok2, ?_⟩
    · simp [net.random.sample_for_large_range, h1, h2, hr, hr0, lift, c1, c2]
    · simp only [NetRandom.sampleForLargeRange, ← heq1, ← heq2, hm]; simp

@[simp] theorem i32mk_val (x : Int32) : IScalar.val (⟨x.toBitVec⟩ : I32) = x.toInt := rfl
@[simp] theorem i64mk_val (x : Int64) : IScalar.val (⟨x.toBitVec⟩ : I64) = x.toInt := rfl

theorem i32S_eq_ofInt (x : I32) (v : Int) (h : x.val = Int.bmod v (2^32)) : i32S x = Int32.ofInt v := by
  apply Int32.toInt_inj.mp
  rw [i32S_toInt, Int32.toInt_ofInt, h]; rfl

theorem net.random.next_range_refines (st : net.random.State) (hs : stOk st) (mn mx : I32) :
    ∃ r, net.random.next_range st mn mx = ok r ∧
      resRel stRel r (NetRandom.nextRange (stS st) (i32S mn) (i32S mx)) := by
  unfold net.random.next_range NetRandom.nextRange
  have b1 := mn.hmin; have b2 := mn.hmax; have b3 := mx.hmin; have b4 := mx.hmax
  simp [I32.min, I32.max, IScalar.min, IScalar.max] at b1 b2 b3 b4
  by_cases h : mx.val < mn.val
  · have h' : i32S mx < i32S mn := (i32S_lt _ _).mpr h
    have h'' : mx < mn := h
    exact ⟨.Err .ArgumentOutOfRange, by simp [h''], by simp [h', resRel, exnS]⟩
  · have h' : ¬ i32S mx < i32S mn := fun c => h ((i32S_lt _ _).mp c)
    have h'' : ¬ mx < mn := h
    obtain ⟨rg, hrg, hrgv⟩ := eq_ok_of_spec (I64.sub_spec (x := IScalar.cast .I64 mx) (y := IScalar.cast .I64 mn)
      (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
    simp at hrgv
    by_cases hl : rg.val > 2147483647
    · have hl' : rg > 2147483647#i64 := hl
      obtain ⟨f, st', hsm, hok, heq⟩ := net.random.sample_for_large_range_refines st hs
      refine ⟨_, by simp [h'', hrg, hl', hl, hsm, lift]; rfl, ?_⟩
      simp only [h', ite_false, i32S_toInt, ← hrgv, hl, ite_true, ← heq, resRel, stRel]
      refine ⟨?_, trivial, hok⟩
      apply i32S_eq_ofInt
      simp [Int.bmod_bmod_of_dvd]
    · have hl' : ¬ rg > 2147483647#i64 := hl
      obtain ⟨f, st', hsm, hok, heq⟩ := net.random.sample_refines st hs
      have c1 := (⟨(F64.toInt32 (f * F64.ofInt rg.val)).toBitVec⟩ : I32).hmin
      have c2 := (⟨(F64.toInt32 (f * F64.ofInt rg.val)).toBitVec⟩ : I32).hmax
      simp [I32.min, I32.max, IScalar.min, IScalar.max] at c1 c2
      obtain ⟨v, hv, hvv⟩ := eq_ok_of_spec (I64.add_spec
        (x := IScalar.cast .I64 (⟨(F64.toInt32 (f * F64.ofInt rg.val)).toBitVec⟩ : I32))
        (y := IScalar.cast .I64 mn) (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      refine ⟨_, by simp [h'', hrg, hl', hl, hsm, lift, hv]; rfl, ?_⟩
      simp only [h', ite_false, i32S_toInt, ← hrgv, hl, ite_false, ← heq, resRel, stRel]
      refine ⟨?_, trivial, hok⟩
      apply i32S_eq_ofInt
      simp at hvv
      simp [hvv]

def optRel : Option (F32 × net.random.State) → Option (F32 × NetRandom.State) → Prop
  | none, none => True
  | some (f, s), some (f', s') => f = f' ∧ stS s = s' ∧ stOk s
  | _, _ => False

theorem net.random.next_single_refines (fuel : U64) (st0 : net.random.State) (hs : stOk st0) :
    ∃ r, net.random.next_single fuel st0 = ok r ∧ optRel r (NetRandom.nextSingle fuel.val (stS st0)) := by
  have one : net.random.F32_ONE = ok (1 : F32) := by simp [net.random.F32_ONE]; decide
  let T := NetRandom.nextSingle fuel.val (stS st0)
  unfold net.random.next_single net.random.next_single_loop
  apply loop_ok _ (fun x => fuel.val - x.2.1.val)
    (fun x => x.2.1.val ≤ fuel.val ∧ stOk x.1 ∧
      match x.2.2 with
      | none => NetRandom.nextSingle (fuel.val - x.2.1.val) (stS x.1) = T
      | some (f, s) => stOk s ∧ T = some (f, stS s))
  · rintro ⟨st, k, res⟩ ⟨hk, hok, hres⟩
    dsimp only at hk hok hres ⊢
    cases res with
    | some p =>
      obtain ⟨f, s⟩ := p
      left
      refine ⟨some (f, s), by simp [net.random.next_single_loop.body], ?_⟩
      obtain ⟨hs', hT⟩ := hres
      have hT' : NetRandom.nextSingle fuel.val (stS st0) = some (f, stS s) := hT
      simp [optRel, hT', hs']
    | none =>
      by_cases hlt : k < fuel
      · right
        have hlt' : k.val < fuel.val := hlt
        obtain ⟨s, st2, hsm, hok2, heq⟩ := net.random.sample_refines st hok
        obtain ⟨k1, hk1, hk1v⟩ := eq_ok_of_spec (U64.add_spec (x := k) (y := 1#u64) (by simp [U64.max_eq]; scalar_tac))
        simp at hk1v
        have hfk : fuel.val - k.val = (fuel.val - k1.val) + 1 := by omega
        rw [hfk] at hres
        simp only [NetRandom.nextSingle, ← heq] at hres
        by_cases hf : F64.toF32 s < 1
        · refine ⟨(st2, k1, some (F64.toF32 s, st2)), ?_, ⟨by dsimp only; omega, hok2, hok2, ?_⟩, by dsimp only; omega⟩
          · simp [net.random.next_single_loop.body, hlt, hsm, one, hf, hk1]
          · simp [hf] at hres; exact hres.symm
        · refine ⟨(st2, k1, none), ?_, ⟨by dsimp only; omega, hok2, ?_⟩, by dsimp only; omega⟩
          · simp [net.random.next_single_loop.body, hlt, hsm, one, hf, hk1]
          · simp [hf] at hres; exact hres
      · left
        have : k.val = fuel.val := by have : ¬ k.val < fuel.val := hlt; omega
        refine ⟨none, by simp [net.random.next_single_loop.body, hlt], ?_⟩
        rw [this, Nat.sub_self] at hres
        simp [NetRandom.nextSingle] at hres
        have hres' : NetRandom.nextSingle fuel.val (stS st0) = none := hres.symm
        simp [optRel, hres']
  · exact ⟨by simp, hs, by simp [T]⟩

theorem usize_ge_32 : 2^32 - 1 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

theorem wrap55_21 (x : Usize) (hx : x.val < 56) : ∃ k : Usize,
    (∀ {β : Type} (f : Usize → Result β),
      (do let i ← x + 21#usize; let k ← (if i >= 55#usize then i - 55#usize else ok i); f k) = f k) ∧
    k.val = (if x.val + 21 ≥ 55 then x.val + 21 - 55 else x.val + 21) := by
  have hm := usize_ge_32
  obtain ⟨i, hi, hiv⟩ := eq_ok_of_spec (Usize.add_spec (x := x) (y := 21#usize) (by simp; omega))
  simp at hiv
  by_cases h : x.val + 21 ≥ 55
  · obtain ⟨j, hj, hjv⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 55#usize) (by simp; omega))
    simp at hjv
    have h55 : 55 ≤ i.val := by omega
    exact ⟨j, by intro β f; simp [hi, h55, hj], by simp [h]; omega⟩
  · have h55 : ¬ 55 ≤ i.val := by omega
    exact ⟨i, by intro β f; simp [hi, h55], by simp [h]; omega⟩

theorem wrap55_30 (x : Usize) (hx : x.val < 56) : ∃ k : Usize,
    (∀ {β : Type} (f : Usize → Result β),
      (do let i ← x + 30#usize; let k ← (if i >= 55#usize then i - 55#usize else ok i); f k) = f k) ∧
    k.val = (if x.val + 30 ≥ 55 then x.val + 30 - 55 else x.val + 30) := by
  have hm := usize_ge_32
  obtain ⟨i, hi, hiv⟩ := eq_ok_of_spec (Usize.add_spec (x := x) (y := 30#usize) (by simp; omega))
  simp at hiv
  by_cases h : x.val + 30 ≥ 55
  · obtain ⟨j, hj, hjv⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 55#usize) (by simp; omega))
    simp at hjv
    have h55 : 55 ≤ i.val := by omega
    exact ⟨j, by intro β f; simp [hi, h55, hj], by simp [h]; omega⟩
  · have h55 : ¬ 55 ≤ i.val := by omega
    exact ⟨i, by intro β f; simp [hi, h55], by simp [h]; omega⟩

theorem mk_step (mj mk : I32) : ∃ m2 : I32,
    (∀ {β : Type} (f : I32 → Result β),
      (do let mk1 ← lift (core.num.I32.wrapping_sub mj mk)
          let mk2 ← (if mk1 < 0#i32 then ok (core.num.I32.wrapping_add mk1 net.random.MBIG) else ok mk1)
          f mk2) = f m2) ∧
    m2.val = (let m := NetRandom.wrap32 (mj.val - mk.val); if m < 0 then NetRandom.wrap32 (m + NetRandom.MBIG) else m) := by
  by_cases h : (core.num.I32.wrapping_sub mj mk).val < 0
  · have h' : Int.bmod (mj.val - mk.val) 4294967296 < 0 := by simpa using h
    refine ⟨core.num.I32.wrapping_add (core.num.I32.wrapping_sub mj mk) net.random.MBIG, ?_, ?_⟩
    · intro β f; simp [lift, h']
    · simp [wrap32_eq, h', MBIG_val, NetRandom.MBIG]
  · have h' : ¬ Int.bmod (mj.val - mk.val) 4294967296 < 0 := by simpa using h
    refine ⟨core.num.I32.wrapping_sub mj mk, ?_, ?_⟩
    · intro β f; simp [lift, h']
    · simp [wrap32_eq, h']

theorem init_loop1_spec (a0 : Std.Array I32 56#usize) (mj0 : I32) :
    ∃ y, net.random.init_loop1 a0 mj0 = ok y ∧ arrS y = NetRandom.initLoop1 54 (arrS a0) mj0.val 1 0 := by
  let T := NetRandom.initLoop1 54 (arrS a0) mj0.val 1 0
  unfold net.random.init_loop1 net.random.init_loop1_loop
  have hm := usize_ge_32
  apply loop_ok _ (fun x => 54 - x.2.2.2.2.val)
    (fun x => x.2.2.2.2.val ≤ 54 ∧ x.2.2.2.1.val < 55 ∧
      NetRandom.initLoop1 (54 - x.2.2.2.2.val) (arrS x.1) x.2.1.val x.2.2.1.val x.2.2.2.1.val = T)
  · rintro ⟨a, mj, mk, ii, n⟩ ⟨hn, hii, hT⟩
    dsimp only at hn hii hT ⊢
    by_cases hlt : n < 54#usize
    · right
      have hlt' : n.val < 54 := hlt
      obtain ⟨k, hk, hkv⟩ := wrap55_21 ii (by omega)
      have hkl : k.val < 55 := by rw [hkv]; split <;> omega
      obtain ⟨m2, hm2, hm2v⟩ := mk_step mj mk
      obtain ⟨n1, hn1, hn1v⟩ := eq_ok_of_spec (Usize.add_spec (x := n) (y := 1#usize) (by simp; omega))
      simp at hn1v
      obtain ⟨x, hx, hxv⟩ := arr_index' (a.set k mk) k (by omega)
      refine ⟨(a.set k mk, x, m2, k, n1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      · simp only [net.random.init_loop1_loop.body, hlt, ite_true]
        rw [hk]; simp only [arr_update _ _ _ (by omega : k.val < 56), bind_ok]
        rw [hm2]; simp [hx, hn1]
      · have e : 54 - n.val = (54 - n1.val) + 1 := by omega
        rw [e] at hT
        simp only [NetRandom.initLoop1] at hT
        rw [← hT, ← hkv, ← hm2v, ← arrS_set, hxv]
    · left
      have : n.val = 54 := by have : ¬ n.val < 54 := hlt; omega
      refine ⟨a, by simp [net.random.init_loop1_loop.body, hlt], ?_⟩
      rw [this, Nat.sub_self] at hT; simp only [NetRandom.initLoop1] at hT; exact hT
  · refine ⟨by simp, by simp, ?_⟩
    have e1 : (0#usize).val = 0 := rfl
    have e2 : (1#i32).val = 1 := rfl
    simp only [e1, e2, Nat.sub_zero, T]

theorem init_loop2_inner_spec (a0 : Std.Array I32 56#usize) :
    ∃ y, net.random.init_loop2_inner a0 = ok y ∧ arrS y = NetRandom.initLoop2Inner 55 (arrS a0) 1 := by
  let T := NetRandom.initLoop2Inner 55 (arrS a0) 1
  unfold net.random.init_loop2_inner net.random.init_loop2_inner_loop
  have hm := usize_ge_32
  apply loop_ok _ (fun x => 56 - x.2.val)
    (fun x => 1 ≤ x.2.val ∧ x.2.val ≤ 56 ∧ NetRandom.initLoop2Inner (56 - x.2.val) (arrS x.1) x.2.val = T)
  · rintro ⟨a, k⟩ ⟨hk1, hk2, hT⟩
    dsimp only at hk1 hk2 hT ⊢
    by_cases hlt : k < 56#usize
    · right
      have hlt' : k.val < 56 := hlt
      obtain ⟨n, hn, hnv⟩ := wrap55_30 k hlt'
      have hnl : n.val < 55 := by rw [hnv]; split <;> omega
      obtain ⟨x, hx, hxv⟩ := arr_index' a k hlt'
      obtain ⟨i2, hi2, hi2v⟩ := eq_ok_of_spec (Usize.add_spec (x := 1#usize) (y := n) (by simp; omega))
      simp at hi2v
      obtain ⟨y, hy, hyv⟩ := arr_index' a i2 (by omega)
      obtain ⟨m2, hm2, hm2v⟩ := mk_step x y
      obtain ⟨k1, hk1', hk1v⟩ := eq_ok_of_spec (Usize.add_spec (x := k) (y := 1#usize) (by simp; omega))
      simp at hk1v
      refine ⟨(a.set k m2, k1), ?_, ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      · simp only [net.random.init_loop2_inner_loop.body, hlt, ite_true]
        rw [hn]; simp only [hx, hi2, hy, bind_ok]
        rw [hm2]; simp [arr_update _ _ _ hlt', hk1']
      · have e : 56 - k.val = (56 - k1.val) + 1 := by omega
        rw [e] at hT
        simp only [NetRandom.initLoop2Inner] at hT
        rw [← hT, ← hnv, hk1v, hxv, ← hi2v, hyv, arrS_set, hm2v]
    · left
      have : k.val = 56 := by have : ¬ k.val < 56 := hlt; omega
      refine ⟨a, by simp [net.random.init_loop2_inner_loop.body, hlt], ?_⟩
      rw [this, Nat.sub_self] at hT; simp only [NetRandom.initLoop2Inner] at hT; exact hT
  · refine ⟨by simp, by simp, ?_⟩
    have e1 : (1#usize).val = 1 := rfl
    simp only [e1, T]

theorem init_loop2_spec (a0 : Std.Array I32 56#usize) :
    ∃ y, net.random.init_loop2 a0 = ok y ∧ arrS y = NetRandom.initLoop2 4 (arrS a0) := by
  let T := NetRandom.initLoop2 4 (arrS a0)
  unfold net.random.init_loop2 net.random.init_loop2_loop
  apply loop_ok _ (fun x => (4 - x.2.val).toNat)
    (fun x => 0 ≤ x.2.val ∧ x.2.val ≤ 4 ∧ NetRandom.initLoop2 (4 - x.2.val).toNat (arrS x.1) = T)
  · rintro ⟨a, j⟩ ⟨hj1, hj2, hT⟩
    dsimp only at hj1 hj2 hT ⊢
    by_cases hlt : j < 4#i32
    · right
      have hlt' : j.val < 4 := hlt
      obtain ⟨a1, ha1, ha1v⟩ := init_loop2_inner_spec a
      obtain ⟨j1, hj1', hj1v⟩ := eq_ok_of_spec (I32.add_spec (x := j) (y := 1#i32)
        (by simp [I32.min_eq]; omega) (by simp [I32.max_eq]; omega))
      simp at hj1v
      refine ⟨(a1, j1), by simp [net.random.init_loop2_loop.body, hlt, ha1, hj1'],
        ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      have e : (4 - j.val).toNat = (4 - j1.val).toNat + 1 := by omega
      rw [e] at hT
      simp only [NetRandom.initLoop2] at hT
      rw [← hT, ha1v]
    · left
      have : j.val = 4 := by have : ¬ j.val < 4 := hlt; omega
      refine ⟨a, by simp [net.random.init_loop2_loop.body, hlt], ?_⟩
      rw [this] at hT; simp only [show ((4 : Int) - 4).toNat = 0 from rfl, NetRandom.initLoop2] at hT; exact hT
  · refine ⟨by simp, by simp, ?_⟩
    have e1 : (0#i32).val = 0 := rfl
    simp only [e1, T]; rfl

theorem MSEED_val : net.random.MSEED.val = 161803398 := by unfold net.random.MSEED; rfl

theorem net.random.create_refines (seed : I32) :
    ∃ st, net.random.create seed = ok st ∧ stOk st ∧ stS st = NetRandom.create (i32S seed) := by
  have b1 := seed.hmin; have b2 := seed.hmax
  simp [I32.min, I32.max, IScalar.min, IScalar.max] at b1 b2
  -- the `sub` value
  obtain ⟨sub, hsub, hsubv⟩ : ∃ sub : I32,
      (∀ {β : Type} (f : I32 → Result β),
        (do let sub ← (if seed = (-2147483648)#i32 then ok 2147483647#i32
                       else if seed < 0#i32 then -. seed else ok seed); f sub) = f sub) ∧
      sub.val = (if seed.val = -2147483648 then 2147483647 else (seed.val.natAbs : Int)) := by
    by_cases h1 : seed.val = -2147483648
    · have : seed = (-2147483648)#i32 := by rw [i32_eq_iff]; simp [h1]
      exact ⟨2147483647#i32, by intro β f; simp [this], by simp [h1]⟩
    · have h1' : ¬ seed = (-2147483648)#i32 := by rw [i32_eq_iff]; simpa using h1
      by_cases h2 : seed.val < 0
      · obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step seed (by simp [IScalar.min, I32.min_eq]; omega))
        exact ⟨q, by intro β f; simp [h1', h2, HNeg.hNeg, hq], by simp [h1, hqv]; rw [abs_of_neg (by omega)]⟩
      · exact ⟨seed, by intro β f; simp [h1', h2], by simp [h1]; rw [abs_of_nonneg (by omega)]⟩
  obtain ⟨a2, ha2, ha2v⟩ := init_loop1_spec
    ((Std.Array.repeat 56#usize 0#i32).set 55#usize (core.num.I32.wrapping_sub net.random.MSEED sub))
    (core.num.I32.wrapping_sub net.random.MSEED sub)
  obtain ⟨a3, ha3, ha3v⟩ := init_loop2_spec a2
  refine ⟨⟨a3, 0#usize, 21#usize⟩, ?_, ⟨by simp, by simp⟩, ?_⟩
  · unfold net.random.create
    rw [hsub]
    simp [lift, arr_update _ _ _ (by simp : (55#usize).val < 56), ha2, ha3]
  · simp only [stS, NetRandom.create, ha3v, ha2v, i32S_toInt, arrS_set]
    have r0 : arrS (Std.Array.repeat 56#usize 0#i32) = Array.replicate 56 (0 : Int) := by
      simp [arrS, Std.Array.repeat_val]; rfl
    have w : (core.num.I32.wrapping_sub net.random.MSEED sub).val =
        NetRandom.wrap32 (NetRandom.MSEED - if seed.val = -2147483648 then 2147483647 else (seed.val.natAbs : Int)) := by
      rw [wrap32_eq, core.num.I32.wrapping_sub_val_eq, MSEED_val, hsubv]; rfl
    rw [r0, w]; rfl

end OsuProofs
