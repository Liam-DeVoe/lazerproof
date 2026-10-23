/-
`sim::autogen` frame insertion: `find_insertion_index` (Rust binary search with a found flag + equal-time scan)
refines `OsuModel.Sim.AutoGen.findInsertionIndex` (`bsearch` + bounded scan), and `add_frame` refines `addFrame`
in the shape of sim3a's hypothesis `s3aAddFrameOk` (Sim3/SA_AutoSpin.lean) for frame lists below 2^62 on 64-bit.
-/
import OsuProofs.Sim2.AutoGen
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl
open OsuModel.Net

def s2_fiiR (lo : I64) : Option I64 → Int
  | some m => m.val
  | none => -lo.val - 1

theorem s2_fii_loop (h64 : System.Platform.numBits = 64) (fs : Slice sim.autogen.AFrame) (t : F64)
    (hn : fs.val.length < 2^62) :
    ∀ (k : Nat) (lo hi : I64) (fuel : U64) (hlo : 0 ≤ lo.val) (hhi : hi.val + 1 ≤ fs.val.length) (hle : lo.val ≤ hi.val + 1),
      (hi.val + 1 - lo.val).toNat = k → k + 1 ≤ fuel.val →
      ∃ lo' fd, sim.autogen.find_insertion_index_loop0 fs t lo hi none fuel = ok (lo', fd) ∧
        (∀ m, fd = some m → 0 ≤ m.val) ∧ (fd = none → 0 ≤ lo'.val) ∧
        s2_fiiR lo' fd = OsuModel.Sim.bsearchBy (abs fs : _root_.Array OsuModel.Sim.AFrame)
          (fun f => OsuModel.Sim.compareD f.time t) lo.val.toNat (hi.val + 1).toNat (by simp [abs]; omega) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro lo hi fuel hlo hhi hle hk hf
    unfold sim.autogen.find_insertion_index_loop0
    rw [loop_unfold]
    by_cases hc : lo.val ≤ hi.val
    · have hc' : lo ≤ hi := by scalar_tac
      have hfp : fuel > 0#u64 := by scalar_tac
      obtain ⟨fuel1, hf1, hf1v⟩ : ∃ z, fuel - 1#u64 = ok z ∧ z.val = fuel.val - 1 := by
        obtain ⟨z, hz, hv, _⟩ := eq_ok_of_spec (U64.sub_spec (x := fuel) (y := 1#u64) (by simp; omega))
        exact ⟨z, hz, by simpa using hv⟩
      obtain ⟨d, hd, hdv⟩ := eq_ok_of_spec (IScalar.sub_spec (x := hi) (y := lo) (by scalar_tac) (by scalar_tac))
      obtain ⟨q, hq, hqv⟩ := IScalar.div_spec (x := d) (y := 2#i64) (by simp) (by scalar_tac)
      have hq2 : q.val = (hi.val - lo.val) / 2 := by
        rw [hqv, hdv]; simp; rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
      obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (IScalar.add_spec (x := lo) (y := q) (by scalar_tac) (by scalar_tac))
      have hmc : (IScalar.hcast .Usize m).val = m.val.toNat := by
        rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
      have hml : (IScalar.hcast .Usize m).val < fs.val.length := by rw [hmc]; omega
      obtain ⟨c, hcmp, ec⟩ := sim.geometry.compare_d_refines (fs.val[(IScalar.hcast .Usize m).val]'hml).time t
      simp only [abs, id] at ec
      have hmid : (IScalar.hcast .Usize m).val = lo.val.toNat + ((hi.val + 1).toNat - 1 - lo.val.toNat) / 2 := by
        rw [hmc, hmv, hq2]; omega
      have hb : sim.autogen.find_insertion_index_loop0.body fs t lo hi none fuel =
          ((if c = 0#i32 then ok (ControlFlow.cont (lo, hi, some m, fuel1)) else if c < 0#i32 then (do let lo1 ← m + 1#i64; ok (ControlFlow.cont (lo1, hi, none, fuel1)))
            else (do let hi1 ← m - 1#i64; ok (ControlFlow.cont (lo, hi1, none, fuel1)))) : Result _) := by
        simp only [sim.autogen.find_insertion_index_loop0.body, hc', hfp, ite_true, hf1, hd, hq, hm, lift, bind_ok,
          index_eq fs _ hml, hcmp, core.option.Option.is_none, Option.isNone_none, ite_true]
      rw [OsuModel.Sim.bsearchBy, dif_pos (by omega)]
      dsimp only
      rw [hb]
      have eA : (abs fs : _root_.Array OsuModel.Sim.AFrame)[lo.val.toNat + ((hi.val + 1).toNat - 1 - lo.val.toNat) / 2]'(by simp [abs]; omega)
          = abs (fs.val[(IScalar.hcast .Usize m).val]'hml) := by simp [abs, hmid]
      rw [eA, show (abs (fs.val[(IScalar.hcast .Usize m).val]'hml) : OsuModel.Sim.AFrame).time
        = (fs.val[(IScalar.hcast .Usize m).val]'hml).time from rfl, ec]
      by_cases h0 : c.val = 0
      · have hc0 : c = 0#i32 := IScalar.eq_of_val_eq (by simp [h0])
        have hf1p : fuel1 > 0#u64 := by scalar_tac
        refine ⟨lo, some m, ?_, by intro m' hm'; simp at hm'; subst hm'; omega, by simp, ?_⟩
        · simp only [hc0, ite_true, bind_ok]
          rw [loop_unfold]
          simp [sim.autogen.find_insertion_index_loop0.body, hc', hf1p, core.option.Option.is_none]
        · simp [h0, s2_fiiR]; omega
      · have hc0 : ¬ c = 0#i32 := fun e => h0 (by simp [e])
        by_cases hneg : c.val < 0
        · have hcn : c < 0#i32 := by scalar_tac
          obtain ⟨m1, hm1, hm1v⟩ := i64_add_one m (by scalar_tac) (by scalar_tac)
          obtain ⟨lo', fd, hr, p1, p2, er⟩ := ih (hi.val + 1 - m1.val).toNat (by omega) m1 hi fuel1 (by omega) hhi (by omega) rfl (by omega)
          refine ⟨lo', fd, ?_, p1, p2, ?_⟩
          · simp only [hc0, hcn, ite_true, ite_false, hm1, bind_ok]
            unfold sim.autogen.find_insertion_index_loop0 at hr; exact hr
          · rw [er]; simp only [h0, hneg, beq_iff_eq, decide_true, ite_true, ite_false]
            congr 1; omega
        · have hcn : ¬ c < 0#i32 := by scalar_tac
          obtain ⟨m1, hm1, hm1v⟩ := i64_sub_one m (by scalar_tac) (by scalar_tac)
          obtain ⟨lo', fd, hr, p1, p2, er⟩ := ih (m1.val + 1 - lo.val).toNat (by omega) lo m1 fuel1 hlo (by omega) (by omega) rfl (by omega)
          refine ⟨lo', fd, ?_, p1, p2, ?_⟩
          · simp only [hc0, hcn, ite_false, hm1, bind_ok]
            unfold sim.autogen.find_insertion_index_loop0 at hr; exact hr
          · rw [er]; simp only [h0, hneg, beq_iff_eq, decide_false, ite_false, Bool.false_eq_true]
            congr 1; omega
    · have hc' : ¬ (lo ≤ hi) := by scalar_tac
      refine ⟨lo, none, ?_, by simp, fun _ => hlo, ?_⟩
      · simp [sim.autogen.find_insertion_index_loop0.body, hc']
      · rw [OsuModel.Sim.bsearchBy, dif_neg (by omega)]
        simp [s2_fiiR]; omega
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

def s2_scanB (fs : _root_.Array OsuModel.Sim.AFrame) (t : F64) (_j : Nat) (idx : Nat) : ForInStep Nat :=
  match fs[idx]? with
  | some f => if t == f.time then .yield (idx + 1) else .done idx
  | none => .done idx

theorem s2_fii_scan (fs : Slice sim.autogen.AFrame) (t : F64) :
    ∀ (c j : Nat) (idx : Usize), fs.val.length - idx.val ≤ c →
      ∃ r, sim.autogen.find_insertion_index_loop1 fs t idx = ok r ∧
        r.val = iterR (s2_scanB (abs fs) t) j c idx.val := by
  have hmax := fs.property
  intro c
  induction c with
  | zero =>
    intro j idx h
    refine ⟨idx, ?_, rfl⟩
    unfold sim.autogen.find_insertion_index_loop1; rw [loop_unfold]
    simp [sim.autogen.find_insertion_index_loop1.body, slice_lt_len_iff, show ¬ idx.val < fs.val.length by omega]
  | succ c ih =>
    intro j idx h
    by_cases hl : idx.val < fs.val.length
    · have hg : (abs fs : _root_.Array OsuModel.Sim.AFrame)[idx.val]? = some (abs (fs.val[idx.val]'hl)) := by
        simp [abs, hl]
      have et : (abs (fs.val[idx.val]'hl) : OsuModel.Sim.AFrame).time = (fs.val[idx.val]'hl).time := rfl
      by_cases he : (t == (fs.val[idx.val]'hl).time) = true
      · obtain ⟨i1, hi1, hi1v⟩ := usize_add_one idx (by omega)
        obtain ⟨r, hr, er⟩ := ih (j + 1) i1 (by omega)
        refine ⟨r, ?_, ?_⟩
        · have hb : sim.autogen.find_insertion_index_loop1.body fs t idx = ok (.cont i1) := by
            simp [sim.autogen.find_insertion_index_loop1.body, slice_lt_len_iff, hl, index_eq fs idx hl, float.F64.eq, he, hi1]
          unfold sim.autogen.find_insertion_index_loop1; rw [loop_unfold]; simp only [hb, bind_ok]
          unfold sim.autogen.find_insertion_index_loop1 at hr; exact hr
        · rw [er, iterR, s2_scanB, hg]; simp only [et, he, ite_true, hi1v]
      · refine ⟨idx, ?_, ?_⟩
        · unfold sim.autogen.find_insertion_index_loop1; rw [loop_unfold]
          simp [sim.autogen.find_insertion_index_loop1.body, slice_lt_len_iff, hl, index_eq fs idx hl, float.F64.eq, he]
        · rw [iterR, s2_scanB, hg]; simp only [et, he]; rfl
    · refine ⟨idx, ?_, ?_⟩
      · unfold sim.autogen.find_insertion_index_loop1; rw [loop_unfold]
        simp [sim.autogen.find_insertion_index_loop1.body, slice_lt_len_iff, hl]
      · rw [iterR, s2_scanB]
        have : (abs fs : _root_.Array OsuModel.Sim.AFrame)[idx.val]? = none := by simp [abs]; omega
        rw [this]
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem sim.autogen.find_insertion_index_refines (h64 : System.Platform.numBits = 64) (fs : Slice sim.autogen.AFrame)
    (t : F64) (hn : fs.val.length < 2^62) :
    ∃ r, sim.autogen.find_insertion_index fs t = ok r ∧
      OsuModel.Sim.AutoGen.findInsertionIndex (abs fs) t = r.val := by
  have hsz : (abs fs : _root_.Array OsuModel.Sim.AFrame).size = fs.val.length := by simp [abs]
  have hc1 : (UScalar.hcast .I64 (Slice.len fs)).val = fs.val.length := by
    rw [UScalar.hcast_val_eq]; simp only [Slice.len_val]
    rw [Int.bmod_def]
    have e : ((fs.val.length : Nat) : Int) % (2 ^ IScalarTy.I64.numBits : Nat) = fs.val.length :=
      Int.emod_eq_of_lt (by omega) (by simp; omega)
    rw [e]; split <;> simp at * <;> omega
  have hc2 : (UScalar.cast .U64 (Slice.len fs)).val = fs.val.length := by
    rw [UScalar.cast_val_eq]; simp; omega
  obtain ⟨hi, hhi, hhiv⟩ := i64_sub_one (UScalar.hcast .I64 (Slice.len fs)) (by scalar_tac) (by scalar_tac)
  obtain ⟨fu, hfu, hfuv⟩ : ∃ z, UScalar.cast .U64 (Slice.len fs) + 2#u64 = ok z ∧ z.val = fs.val.length + 2 := by
    obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.add_spec (x := UScalar.cast .U64 (Slice.len fs)) (y := 2#u64) (by scalar_tac))
    exact ⟨z, hz, by simp [hv, hc2]⟩
  obtain ⟨lo', fd, hl, p1, p2, er⟩ := s2_fii_loop h64 fs t hn fs.val.length 0#i64 hi fu (by simp)
    (by rw [hhiv, hc1]; omega) (by simp; rw [hhiv, hc1]; omega) (by simp; rw [hhiv, hc1]; omega) (by rw [hfuv]; omega)
  have hbs : OsuModel.Sim.bsearch (abs fs : _root_.Array OsuModel.Sim.AFrame) (fun f => OsuModel.Sim.compareD f.time t) =
      s2_fiiR lo' fd := by
    rw [er]; unfold OsuModel.Sim.bsearch; congr 1 <;> (try simp) <;> (try (rw [hhiv, hc1, hsz]; simp))
  unfold OsuModel.Sim.AutoGen.findInsertionIndex
  simp only [Id.run]
  rw [hbs]
  cases fd with
  | none =>
    have h0 := p2 rfl
    have hlb : lo'.val ≤ fs.val.length := by
      have := (s2_bsearchBy_bounds (abs fs : _root_.Array OsuModel.Sim.AFrame) (fun f => OsuModel.Sim.compareD f.time t)
        fs.val.length 0 (abs fs : _root_.Array OsuModel.Sim.AFrame).size (Nat.le_refl _) (by simp [hsz]) (by simp)).1
      have h2 : -((abs fs : _root_.Array OsuModel.Sim.AFrame).size : Int) - 1 ≤ OsuModel.Sim.bsearch (abs fs : _root_.Array OsuModel.Sim.AFrame) (fun f => OsuModel.Sim.compareD f.time t) := this
      rw [hbs, hsz] at h2; simp [s2_fiiR] at h2; omega
    refine ⟨IScalar.hcast .Usize lo', ?_, ?_⟩
    · simp only [sim.autogen.find_insertion_index, lift, bind_ok, hhi, hfu, hl]; rfl
    · simp only [s2_fiiR]
      have hneg : -lo'.val - 1 < 0 := by omega
      simp only [hneg, ↓reduceIte]
      show (-(-lo'.val - 1) - 1).toNat = _
      rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
  | some m =>
    have h0 := p1 m rfl
    have hmb : m.val < fs.val.length := by
      have := (s2_bsearchBy_bounds (abs fs : _root_.Array OsuModel.Sim.AFrame) (fun f => OsuModel.Sim.compareD f.time t)
        fs.val.length 0 (abs fs : _root_.Array OsuModel.Sim.AFrame).size (Nat.le_refl _) (by simp [hsz]) (by simp)).2
      have h2 : OsuModel.Sim.bsearch (abs fs : _root_.Array OsuModel.Sim.AFrame) (fun f => OsuModel.Sim.compareD f.time t) < (abs fs : _root_.Array OsuModel.Sim.AFrame).size := this
      rw [hbs, hsz] at h2; simpa [s2_fiiR] using h2
    have hmc : (IScalar.hcast .Usize m).val = m.val.toNat := by
      rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
    obtain ⟨r, hr, er2⟩ := s2_fii_scan fs t fs.val.length 0 (IScalar.hcast .Usize m) (by omega)
    refine ⟨r, ?_, ?_⟩
    · simp only [sim.autogen.find_insertion_index, lift, bind_ok, hhi, hfu, hl]; exact hr
    · simp only [s2_fiiR]
      have hneg : ¬ m.val < 0 := by omega
      simp only [hneg, ↓reduceIte]
      · show forIn (m := Id) [0:(abs fs : _root_.Array OsuModel.Sim.AFrame).size] m.val.toNat (fun _ idx => s2_scanB (abs fs) t 0 idx) = _
        rw [forIn_range_iterR, hsz, er2, hmc]
        rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_scan_le (fs : _root_.Array OsuModel.Sim.AFrame) (t : F64) :
    ∀ (c j idx : Nat), idx ≤ fs.size → iterR (s2_scanB fs t) j c idx ≤ fs.size := by
  intro c
  induction c with
  | zero => intro j idx h; exact h
  | succ c ih =>
    intro j idx h
    rw [iterR, s2_scanB]
    by_cases hl : idx < fs.size
    · rw [Array.getElem?_eq_getElem hl]
      dsimp only
      by_cases he : (t == (fs[idx]'hl).time) = true
      · simp only [he, ite_true]; exact ih _ _ (by omega)
      · simp only [he, Bool.false_eq_true, ite_false]; exact h
    · rw [Array.getElem?_eq_none (by omega)]; exact h

theorem s2_fii_le (fs : _root_.Array OsuModel.Sim.AFrame) (t : F64) :
    OsuModel.Sim.AutoGen.findInsertionIndex fs t ≤ fs.size := by
  have hb := s2_bsearchBy_bounds fs (fun f => OsuModel.Sim.compareD f.time t) fs.size 0 fs.size (Nat.le_refl _) (by simp) (by simp)
  have hb' : -(fs.size : Int) - 1 ≤ OsuModel.Sim.bsearch fs (fun f => OsuModel.Sim.compareD f.time t) ∧
      OsuModel.Sim.bsearch fs (fun f => OsuModel.Sim.compareD f.time t) < fs.size := hb
  unfold OsuModel.Sim.AutoGen.findInsertionIndex
  simp only [Id.run]
  generalize OsuModel.Sim.bsearch fs (fun f => OsuModel.Sim.compareD f.time t) = r at hb'
  by_cases hneg : r < 0
  · simp only [hneg, ↓reduceIte]; show (-r - 1).toNat ≤ _; omega
  · simp only [hneg, ↓reduceIte]
    show Id.run (forIn (m := Id) [0:fs.size] r.toNat (fun _ idx => s2_scanB fs t 0 idx)) ≤ fs.size
    rw [forIn_range_iterR]
    exact s2_scan_le fs t _ _ _ (by omega)

theorem sim.autogen.add_frame_refines (h64 : System.Platform.numBits = 64) (mods : Slice sim.mods.RateMod)
    (g : sim.autogen.G) (f : sim.autogen.AFrame) (h : g.frames.val.length < 2^62) :
    ∃ g', sim.autogen.add_frame g f = ok g' ∧
      OsuModel.Sim.AutoGen.addFrame (abs f) (abs mods) (abs g) = .ok ((), abs g') ∧ g'.heap = g.heap := by
  have hU := usize_max_64 h64
  obtain ⟨k, hk, ek⟩ := sim.autogen.find_insertion_index_refines h64 (alloc.vec.Vec.deref g.frames) f.time
    (by simpa [ms_deref_val] using h)
  have efs : (abs (alloc.vec.Vec.deref g.frames) : _root_.Array OsuModel.Sim.AFrame) = (abs g : OsuModel.Sim.AutoGen.G).frames := by
    show (List.map abs (alloc.vec.Vec.deref g.frames).val).toArray = (g.frames.val.map s2_aframeS).toArray
    simp [ms_deref_val]; intro a _; rfl
  rw [efs] at ek
  have hle := s2_fii_le (abs g : OsuModel.Sim.AutoGen.G).frames f.time
  rw [ek] at hle
  have hsz : (abs g : OsuModel.Sim.AutoGen.G).frames.size = g.frames.val.length := by
    show (g.frames.val.map s2_aframeS).toArray.size = _; simp
  obtain ⟨w, hw, ew⟩ := beatmap.dotnet.insert_at_refines sim.autogen.AFrame.Insts.CoreCloneClone (fun x => rfl)
    g.frames k f (by omega) (by omega)
  refine ⟨{ g with frames := w }, by simp [sim.autogen.add_frame, hk, hw], ?_, rfl⟩
  unfold OsuModel.Sim.AutoGen.addFrame
  simp only [s2_am_get_bind]
  rw [show (abs f : OsuModel.Sim.AFrame).time = f.time from rfl, ek, dif_pos (by omega)]
  simp only [s2_am_set]
  congr 2
  show _ = ({ frames := (w.val.map s2_aframeS).toArray, buttonIndex := g.button_index.val, heap := (g.heap.val.map s2_actListS).toArray } : OsuModel.Sim.AutoGen.G)
  rw [ew]
  congr 1
  apply Array.toList_inj.mp
  have e1 : (abs g : OsuModel.Sim.AutoGen.G).frames.toList = g.frames.val.map s2_aframeS := by
    show (g.frames.val.map s2_aframeS).toArray.toList = _; simp
  simp only [Array.toList_insertIdx, e1, List.toList_toArray]
  rw [insertIdx_take_drop _ _ _ (by simp; omega), insertIdx_take_drop _ _ _ (by omega)]
  simp [List.map_take, List.map_drop]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim.autogen.new_list_refines (g : sim.autogen.G) (xs : replay.frames.ActList) (mods : List OsuModel.Sim.RateMod)
    (hh : g.heap.val.length < Usize.max) :
    ∃ r, sim.autogen.new_list g xs = ok r ∧
      OsuModel.Sim.AutoGen.newList (s2_actListS xs) mods (abs g) = .ok (r.1.val, abs r.2) := by
  refine ⟨(alloc.vec.Vec.len g.heap, { g with heap := vpush g.heap xs hh }), by
    simp [sim.autogen.new_list, vec_push_ok _ _ hh], ?_⟩
  simp only [OsuModel.Sim.AutoGen.newList, s2_am_bind, s2_am_get_bind]
  show Except.ok _ = _
  simp [abs, s2_gS]

theorem sim.autogen.last_frame_refines (g : sim.autogen.G) (mods : List OsuModel.Sim.RateMod)
    (h : 0 < g.frames.val.length) :
    ∃ r, sim.autogen.last_frame g = ok r ∧ OsuModel.Sim.AutoGen.lastFrame mods (abs g) = .ok (abs r, abs g) := by
  obtain ⟨m, hm, hmv⟩ := usize_sub_one (alloc.vec.Vec.len g.frames) (by simp; omega)
  have hml : m.val < g.frames.val.length := by simp at hmv; omega
  refine ⟨g.frames.val[m.val]'hml, by simp [sim.autogen.last_frame, hm, vec_index_eq _ _ hml, vec_index_usize_ok _ _ hml], ?_⟩
  have hb : (abs g : OsuModel.Sim.AutoGen.G).frames.back? = some (abs (g.frames.val[m.val]'hml)) := by
    show (g.frames.val.map s2_aframeS).toArray.back? = _
    simp [Array.back?, List.getElem?_map, hmv]
    exact ⟨_, List.getElem?_eq_getElem (by omega), rfl⟩
  have hg : (get : OsuModel.Sim.AutoGen.M OsuModel.Sim.AutoGen.G) mods (abs g) = .ok (abs g, abs g) := rfl
  simp only [OsuModel.Sim.AutoGen.lastFrame, s2_am_bind, hg, Except.bind, hb]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- the `stackedEnd` expression of `addHitObjectReplay` -/
def s2_stackedEndS (o : OsuModel.Sim.TopObj) : OsuModel.Net.OsuTK.Vector2 :=
  match o.h.kind with
  | .slider => match o.nested.find? (·.kind == .tail) with
    | some t => OsuModel.Sim.AutoGen.ofVec t.stacked
    | none => OsuModel.Sim.AutoGen.ofVec o.h.stacked
  | _ => OsuModel.Sim.AutoGen.ofVec o.h.stacked

theorem s2_se_loop (v : alloc.vec.Vec sim.playable.HObj) :
    ∀ (n : Nat) (j : Usize), v.val.length - j.val = n → j.val ≤ v.val.length →
      sim.autogen.stacked_end_loop v j none =
        ok (((v.val.drop j.val).find? (fun h => kindS h.kind == OsuModel.Sim.Kind.tail)).map
          (fun h => (⟨h.stacked.x, h.stacked.y⟩ : net.osutk.Vector2))) := by
  have hmax := v.property
  intro n
  induction n with
  | zero =>
    intro j hn hj
    unfold sim.autogen.stacked_end_loop; rw [loop_unfold]
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [sim.autogen.stacked_end_loop.body, vec_lt_len_iff, show ¬ j.val < v.val.length by omega]
  | succ n ih =>
    intro j hn hj
    have hl : j.val < v.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    unfold sim.autogen.stacked_end_loop; rw [loop_unfold]
    rw [List.drop_eq_getElem_cons hl, List.find?_cons]
    have hk : kindS sim.playable.Kind.Tail = OsuModel.Sim.Kind.tail := rfl
    by_cases ht : (kindS (v.val[j.val]'hl).kind == OsuModel.Sim.Kind.tail) = true
    · have hb : sim.autogen.stacked_end_loop.body v j none =
          ok (.cont (j1, some ⟨(v.val[j.val]'hl).stacked.x, (v.val[j.val]'hl).stacked.y⟩)) := by
        simp [sim.autogen.stacked_end_loop.body, vec_lt_len_iff, hl, vec_index_eq v j hl, ht, sim.autogen.of_vec,
          net.osutk.v2, hj1, hk]
      dsimp only; rw [hb]; simp only [bind_ok, ht]
      rw [loop_unfold]
      simp [sim.autogen.stacked_end_loop.body, core.option.Option.is_none, vec_lt_len_iff]
    · have hb : sim.autogen.stacked_end_loop.body v j none = ok (.cont (j1, none)) := by
        simp [sim.autogen.stacked_end_loop.body, vec_lt_len_iff, hl, vec_index_eq v j hl, hj1, hk, ht]
      dsimp only; rw [hb]; simp only [bind_ok, ht]
      have := ih j1 (by omega) (by omega)
      unfold sim.autogen.stacked_end_loop at this; rw [this, hj1v]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim.autogen.stacked_end_refines (o : sim.playable.TopObj) :
    ∃ r, sim.autogen.stacked_end o = ok r ∧ s2_stackedEndS (abs o) = abs r := by
  obtain ⟨found, hf⟩ : ∃ f, sim.autogen.stacked_end_loop o.nested 0#usize none = ok f ∧
      f = ((o.nested.val.drop 0).find? (fun h => kindS h.kind == OsuModel.Sim.Kind.tail)).map
          (fun h => (⟨h.stacked.x, h.stacked.y⟩ : net.osutk.Vector2)) :=
    ⟨_, s2_se_loop o.nested _ 0#usize rfl (by simp), rfl⟩
  have hfind : (abs o : OsuModel.Sim.TopObj).nested.find? (·.kind == .tail) =
      (o.nested.val.find? (fun h => kindS h.kind == OsuModel.Sim.Kind.tail)).map (hobjS simTnDefault) := by
    show ((o.nested.val.map (hobjS simTnDefault)).toArray).find? _ = _
    rw [List.find?_toArray, List.find?_map]; rfl
  unfold s2_stackedEndS
  cases hk : o.h.kind
  case Slider =>
    have hk' : (abs o : OsuModel.Sim.TopObj).h.kind = .slider := by
      show kindS o.h.kind = _; rw [hk]; rfl
    simp only [hk', hfind]
    obtain ⟨hl, rfl⟩ := hf
    cases hfd : o.nested.val.find? (fun h => kindS h.kind == OsuModel.Sim.Kind.tail) with
    | none =>
      refine ⟨⟨o.h.stacked.x, o.h.stacked.y⟩, ?_, rfl⟩
      unfold sim.autogen.stacked_end; rw [kind_eq_ok, hk]; simp only [bind_ok]
      rw [if_pos (by decide), hl, List.drop_zero, hfd]; simp [sim.autogen.of_vec, net.osutk.v2]
    | some t =>
      refine ⟨⟨t.stacked.x, t.stacked.y⟩, ?_, rfl⟩
      unfold sim.autogen.stacked_end; rw [kind_eq_ok, hk]; simp only [bind_ok]
      rw [if_pos (by decide), hl, List.drop_zero, hfd]; simp
  all_goals
    have hk' : (abs o : OsuModel.Sim.TopObj).h.kind = kindS o.h.kind := rfl
    refine ⟨⟨o.h.stacked.x, o.h.stacked.y⟩, ?_, ?_⟩
    · unfold sim.autogen.stacked_end; rw [kind_eq_ok, hk]; simp only [bind_ok]
      rw [if_neg (by decide)]; simp [sim.autogen.of_vec, net.osutk.v2]
    · rw [hk']; simp only [hk, kindS]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_ag_f32 : sim.autogen.F32_0 = ok (0 : F32) ∧ sim.autogen.F32_1 = ok (1 : F32) ∧
    sim.autogen.SPIN_RADIUS = ok OsuModel.Sim.AutoGen.spinRadius := by
  simp [sim.autogen.F32_0, sim.autogen.F32_1, sim.autogen.SPIN_RADIUS, float.F32.from_bits, OsuModel.Sim.AutoGen.spinRadius]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

@[simp] theorem s2_v2SI (x : OsuModel.Net.OsuTK.Vector2) : v2S (v2I x) = x := rfl

theorem sim.autogen.calc_spinner_start_refines (p : net.osutk.Vector2) :
    ∃ r, sim.autogen.calc_spinner_start p = ok r ∧ OsuModel.Sim.AutoGen.calcSpinnerStart (abs p) = (abs r.1, r.2) := by
  obtain ⟨c, hc, ec⟩ := sim.autogen.spinner_centre_refines
  obtain ⟨h0, h1, hR⟩ := s2_ag_f32
  unfold sim.autogen.calc_spinner_start OsuModel.Sim.AutoGen.calcSpinnerStart
  simp only [hc, h0, h1, hR, bind_ok, net.osutk.v2_sub_refines, net.osutk.v2_length_refines, float.F32.mul,
    float.F32.sub, float.F32.sqrt, float.F32.lt, float.F32.div, float.F32.asin, float.F32.cos, float.F32.sin,
    float.F32.add, float.F32.neg, net.osutk.v2_refines, net.osutk.v2_normalized_refines, net.osutk.v2_scale_refines,
    net.osutk.v2_add_refines]
  simp only [decide_eq_true_eq]
  simp only [s2_v2SI]
  have ep : (abs p : OsuModel.Net.OsuTK.Vector2) = v2S p := rfl
  rw [ec, ep]
  simp only [show ∀ a b : OsuModel.Net.OsuTK.Vector2, a - b = a.sub b from fun _ _ => rfl,
    show (abs c : OsuModel.Net.OsuTK.Vector2) = v2S c from rfl,
    show ∀ (q : Prop) [Decidable q] (a b : F32), (if q then (ok a : Result F32) else ok b) = ok (if q then a else b)
      from fun q _ a b => by split <;> rfl, bind_ok]
  by_cases h1 : OsuModel.Sim.AutoGen.spinRadius < ((v2S c).sub (v2S p)).length
  · by_cases h2 : 0 < F32.asin (OsuModel.Sim.AutoGen.spinRadius / ((v2S c).sub (v2S p)).length)
    · simp only [h1, h2, ite_true, bind_ok]; exact ⟨_, rfl, rfl⟩
    · simp only [h1, h2, ite_true, ite_false, bind_ok]; exact ⟨_, rfl, rfl⟩
  · by_cases h3 : 0 < ((v2S c).sub (v2S p)).length
    · simp only [h1, h3, ite_true, ite_false, bind_ok]; exact ⟨_, rfl, rfl⟩
    · simp only [h1, h3, ite_false, bind_ok]; exact ⟨_, rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s2_ob64_0 : Float.ofBits 0 = (0 : OsuModel.Net.F64) := by decide
theorem s2_ob32_0 : Float32.ofBits 0 = (0 : OsuModel.Net.F32) := by decide
theorem s2_def64 : (default : OsuModel.Net.F64) = 0 := by decide

theorem sim.playable.slider_data_default_refines :
    ∃ r, sim.playable.slider_data_default = ok r ∧ (default : OsuModel.Sim.SliderData) = abs r := by
  refine ⟨_, by simp [sim.playable.slider_data_default, float.F64.from_bits]; rfl, ?_⟩
  show (⟨default, default, default, default, default, default, default, default⟩ : OsuModel.Sim.SliderData) = _
  simp [abs, s2_ob64_0, s2_def64]
  exact ⟨rfl, rfl⟩
end OsuProofs

