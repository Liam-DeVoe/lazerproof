/-
`beatmap::mods::adaptive_speed` (Rust) refines `Mods.adaptiveSpeed` (mods proof agent; abs-style).
The preceding-end-times pass: collect (object, end time) refs, sort the end times (`stable_sort_by`),
dedupe (`asE`) and binary-search each object's predecessor (`asQ`).
-/
import OsuProofs.Post.ModsB
import OsuProofs.Beatmap.DotNetSort
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


theorem as_forIn_yield_foldl {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) : ∀ (l : List X) (s : S), forIn (m := Id) l s G = l.foldl g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x t ih => intro s; rw [List.forIn_cons, hG]; exact ih _

def asHasW (n : NestedObject) : Bool := match n.hitWindows with | .empty => false | _ => true
def asHasWin (h : OsuHitObject) : Bool := match h.hitWindows with | some .empty => false | _ => true

/-- nested step of `Mods.adaptiveSpeed`'s object collection (object index `i`) -/
def asN (ep i : Nat) (s : Array (ObjRef × F64) × Nat) (n : NestedObject) : Array (ObjRef × F64) × Nat :=
  if asHasW n then (s.1.push ({ index := i, nested := some s.2, epoch := ep }, n.startTime), s.2 + 1) else (s.1, s.2 + 1)

/-- object step of `Mods.adaptiveSpeed`'s object collection -/
def asH (ep : Nat) (s : Array (ObjRef × F64) × Nat) (h : OsuHitObject) : Array (ObjRef × F64) × Nat :=
  let o0 := if asHasWin h then s.1.push ({ index := s.2, epoch := ep }, h.endTime) else s.1
  ((h.nested.toList.foldl (asN ep s.2) (o0, 0)).1, s.2 + 1)

def asE (et : Array F64) (t : F64) : Array F64 :=
  if (et.size == 0 || compareF64 et.back! t != 0) then et.push t else et

def asQ (et : Array F64) (en : Array (ObjRef × F64)) (x : ObjRef × F64) : Array (ObjRef × F64) :=
  let b := binarySearchF64 et x.2
  let index := (if b < 0 then -b - 1 else b) - 1
  if index ≥ 0 then en.push (x.1, et[index.toNat]!) else en

theorem as_spec (idx : Nat) (pb : PlayableBeatmap) :
    Mods.adaptiveSpeed idx pb =
      let objs := (pb.hitObjects.toList.foldl (asH pb.epoch) (#[], 0)).1
      let et := (stableSortBy id (objs.map (·.2))).toList.foldl asE #[]
      { pb with modStates := pb.modStates.push (idx, .precedingEndTimes (objs.toList.foldl (asQ et) #[])) } := by
  unfold Mods.adaptiveSpeed
  simp only [Id.run, id_bind_eq]
  simp only [← Array.forIn_toList]
  rw [as_forIn_yield_foldl _ (asH pb.epoch) ?h1, as_forIn_yield_foldl _ asE ?h2, as_forIn_yield_foldl _ (asQ _) ?h3]
  · rfl
  case h1 =>
    intro h s
    simp only [asH, asHasWin]
    split
    all_goals
      simp only [Bool.false_eq_true, ite_false, ite_true]
      rw [as_forIn_yield_foldl _ (asN pb.epoch s.2) (by
        intro n s'; simp only [asN, asHasW]
        cases n with
        | mk k st p sh sc tp tf hw pp si sst ri sd csb ki stt => cases hw <;> rfl)]
      simp_all; rfl
  case h2 => intro t s; simp only [asE, apply_ite ForInStep.yield]; rfl
  case h3 => intro x s; simp only [asQ, apply_ite ForInStep.yield]; rfl



theorem as_absvec_push {α β} [AbsTo α β] (v w : alloc.vec.Vec α) (x : α) (h : w.val = v.val ++ [x]) :
    (abs w : Array β) = (abs v : Array β).push (abs x) := by
  simp [abs, h]

theorem as_loop00 (ep idx : Usize) (v : alloc.vec.Vec beatmap.objects.NestedObject) :
    ∀ (j : Usize) (objs : alloc.vec.Vec (beatmap.playable.ObjRef × F64)), j.val ≤ v.val.length →
      objs.val.length + (v.val.length - j.val) < 2^31 →
      ∃ r, beatmap.mods.adaptive_speed_loop0_loop0 ep objs idx v j = ok r ∧
        (abs r : Array (ObjRef × F64)) = (((v.val.map (abs : _ → NestedObject)).drop j.val).foldl (asN ep.val idx.val)
          (abs objs, j.val)).1 ∧ r.val.length ≤ objs.val.length + (v.val.length - j.val) := by
  intro j
  induction hk : v.val.length - j.val using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    intro objs hle hb
    unfold beatmap.mods.adaptive_speed_loop0_loop0
    rw [loop_unfold]
    by_cases hlt : j.val < v.val.length
    · have hl : j < alloc.vec.Vec.len v := by show j.val < (alloc.vec.Vec.len v).val; simpa using hlt
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := v.property; omega)
      have hd : (v.val.map (abs : _ → NestedObject)).drop j.val =
          (abs (v.val[j.val]'hlt) : NestedObject) :: (v.val.map abs).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
      rw [hd, List.foldl_cons]
      have hw' : ∀ n : beatmap.objects.NestedObject, asHasW (abs n) = (match n.hit_windows with
          | .Empty => false | _ => true) := by
        intro n; simp only [asHasW]
        cases n with
        | mk k st p sh sc tp tf hw pp si sst ri sd csb ki stt => cases hw <;> rfl
      have hw := hw' (v.val[j.val]'hlt)
      cases hwc : (match (v.val[j.val]'hlt).hit_windows with | .Empty => false | _ => true)
      · obtain ⟨r, hr, hrv, hrl⟩ := ih (v.val.length - j1.val) (by omega) j1 rfl objs (by omega) (by omega)
        refine ⟨r, ?_, ?_, by omega⟩
        · have hb' : beatmap.mods.adaptive_speed_loop0_loop0.body ep idx v objs j = ok (.cont (objs, j1)) := by
            simp only [beatmap.mods.adaptive_speed_loop0_loop0.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok, hj1]
            revert hwc; cases (v.val[j.val]'hlt).hit_windows <;> simp
          simp only [hb', bind_ok]; unfold beatmap.mods.adaptive_speed_loop0_loop0 at hr; exact hr
        · rw [hrv, hj1v]; simp only [asN, hw, hwc]; rfl
      · obtain ⟨w, hpw, hwv⟩ := push_eq objs (({ index := idx, nested := some j, epoch := ep } : beatmap.playable.ObjRef),
          (v.val[j.val]'hlt).start_time) (by have := dns_usize_max; omega)
        obtain ⟨r, hr, hrv, hrl⟩ := ih (v.val.length - j1.val) (by omega) j1 rfl w (by omega) (by rw [hwv]; simp; omega)
        refine ⟨r, ?_, ?_, by rw [hwv] at hrl; simp at hrl; omega⟩
        · have hb' : beatmap.mods.adaptive_speed_loop0_loop0.body ep idx v objs j = ok (.cont (w, j1)) := by
            simp only [beatmap.mods.adaptive_speed_loop0_loop0.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok, hj1]
            revert hwc; cases (v.val[j.val]'hlt).hit_windows <;> simp [hpw]
          simp only [hb', bind_ok]; unfold beatmap.mods.adaptive_speed_loop0_loop0 at hr; exact hr
        · rw [hrv, hj1v, as_absvec_push objs w _ hwv]; simp only [asN, hw, hwc]; rfl
    · have hl : ¬ j < alloc.vec.Vec.len v := by show ¬ j.val < (alloc.vec.Vec.len v).val; simpa using hlt
      refine ⟨objs, by simp [beatmap.mods.adaptive_speed_loop0_loop0.body, hl], ?_, by omega⟩
      rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl



def asCnt (l : List beatmap.objects.OsuHitObject) : Nat := (l.map fun h => h.nested.val.length + 1).sum

theorem as_body0 (pb : beatmap.playable.PlayableBeatmap) (objs : alloc.vec.Vec (beatmap.playable.ObjRef × F64))
    (i : Usize) (hlt : i.val < pb.hit_objects.val.length)
    (hb : objs.val.length + (pb.hit_objects.val[i.val]'hlt).nested.val.length + 1 < 2^31) :
    ∃ objs1 i1, beatmap.mods.adaptive_speed_loop0.body pb objs i = ok (.cont (objs1, i1)) ∧ i1.val = i.val + 1 ∧
      (abs objs1 : Array (ObjRef × F64)) = (asH pb.epoch.val (abs objs, i.val) (abs (pb.hit_objects.val[i.val]'hlt))).1 ∧
      objs1.val.length ≤ objs.val.length + (pb.hit_objects.val[i.val]'hlt).nested.val.length + 1 := by
  have hl : i < alloc.vec.Vec.len pb.hit_objects := by show i.val < (alloc.vec.Vec.len pb.hit_objects).val; simpa using hlt
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by have := pb.hit_objects.property; omega)
  generalize hH : pb.hit_objects.val[i.val]'hlt = h at *
  have hix : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.objects.OsuHitObject) pb.hit_objects i = ok h := by
    rw [← hH]; exact vec_index_eq _ _ hlt
  have hn : (abs h : OsuHitObject).nested.toList = h.nested.val.map abs := by simp [abs]
  suffices H : ∃ o1, (abs o1 : Array (ObjRef × F64)) = (if asHasWin (abs h) then (abs objs : Array (ObjRef × F64)).push
          ({ index := i.val, epoch := pb.epoch.val }, (abs h : OsuHitObject).endTime) else abs objs) ∧
      o1.val.length ≤ objs.val.length + 1 ∧
      beatmap.mods.adaptive_speed_loop0.body pb objs i = (do
        let objs2 ← beatmap.mods.adaptive_speed_loop0_loop0 pb.epoch o1 i h.nested 0#usize
        let i2 ← i + 1#usize
        ok (ControlFlow.cont (objs2, i2))) by
    obtain ⟨o1, ho1v, ho1l, hbody⟩ := H
    obtain ⟨r, hr, hrv, hrl⟩ := as_loop00 pb.epoch i h.nested 0#usize o1 (by simp) (by simp; omega)
    refine ⟨r, i1, by rw [hbody, hr]; simp [hi1], hi1v, ?_, by simp at hrl; omega⟩
    rw [hrv]; simp only [asH, hn, ← ho1v]; simp
  obtain ⟨w, hw, hwv⟩ := push_eq objs (({ index := i, nested := none, epoch := pb.epoch } : beatmap.playable.ObjRef),
    (abs h : OsuHitObject).endTime) (by have := dns_usize_max; omega)
  have het : beatmap.objects.end_time h = ok (abs h : OsuHitObject).endTime := beatmap.objects.end_time_refines h
  cases hh : h.hit_windows with
  | none =>
    have : asHasWin (abs h) = true := by simp [asHasWin, abs, hh]
    refine ⟨w, by rw [this, if_pos rfl, as_absvec_push objs w _ hwv]; rfl, by rw [hwv]; simp, ?_⟩
    unfold beatmap.mods.adaptive_speed_loop0.body
    have het' : beatmap.objects.end_time { h with hit_windows := none } = ok (abs h : OsuHitObject).endTime := by
      rw [← hh]; exact het
    simp only [hl, if_true, hix, bind_ok, hh]
    simp [het', hw]
  | some hw0 =>
    cases hw0 with
    | Empty =>
      have : asHasWin (abs h) = false := by simp [asHasWin, abs, hh]
      refine ⟨objs, by rw [this]; rfl, by omega, ?_⟩
      unfold beatmap.mods.adaptive_speed_loop0.body
      simp only [hl, if_true, hix, bind_ok, hh]; simp
    | Osu a b c =>
      have : asHasWin (abs h) = true := by simp [asHasWin, abs, hh]
      refine ⟨w, by rw [this, if_pos rfl, as_absvec_push objs w _ hwv]; rfl, by rw [hwv]; simp, ?_⟩
      unfold beatmap.mods.adaptive_speed_loop0.body
      have het' : beatmap.objects.end_time { h with hit_windows := some (.Osu a b c) } = ok (abs h : OsuHitObject).endTime := by
        rw [← hh]; exact het
      simp only [hl, if_true, hix, bind_ok, hh]
      simp [het', hw]



theorem as_bs_iter (a : Array F64) (v : F64) : ∀ (k j : Nat) (lo hi : Int),
    0 ≤ lo → lo ≤ a.size → -1 ≤ hi → hi < a.size →
    (match (iterR (bsF a v) j k (none, lo, hi)).1 with
      | some r => 0 ≤ r ∧ r < a.size
      | none => 0 ≤ (iterR (bsF a v) j k (none, lo, hi)).2.1 ∧ (iterR (bsF a v) j k (none, lo, hi)).2.1 ≤ a.size) := by
  intro k
  induction k with
  | zero => intro j lo hi h1 h2 h3 h4; exact ⟨h1, h2⟩
  | succ k ih =>
    intro j lo hi h1 h2 h3 h4
    have hm1 : lo ≤ hi → lo ≤ lo + (hi - lo) / 2 := by clear ih; omega
    have hm2 : lo ≤ hi → lo + (hi - lo) / 2 ≤ hi := by clear ih; omega
    simp only [iterR]
    by_cases hle : lo ≤ hi
    · have e1 := hm1 hle; have e2 := hm2 hle
      by_cases hc : (compareF64 a[(lo + (hi - lo) / 2).toNat]! v == 0) = true
      · simp only [bsF, hle, hc, if_true]
        show 0 ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 < a.size
        clear ih; omega
      · by_cases hc2 : compareF64 a[(lo + (hi - lo) / 2).toNat]! v < 0
        · simp only [bsF, hle, hc, hc2, if_true, if_false]
          exact ih (j + 1) (lo + (hi - lo) / 2 + 1) hi (by clear ih; omega) (by clear ih; omega) h3 h4
        · simp only [bsF, hle, hc, hc2, if_true, if_false]
          exact ih (j + 1) lo (lo + (hi - lo) / 2 - 1) h1 h2 (by clear ih; omega) (by clear ih; omega)
    · simp only [bsF, hle, if_false]
      exact ih (j + 1) lo hi h1 h2 h3 h4

theorem as_bs_range (a : Array F64) (v : F64) :
    -((a.size : Int) + 1) ≤ binarySearchF64 a v ∧ binarySearchF64 a v < a.size := by
  rw [dns_bs_spec]
  have := as_bs_iter a v (a.size + 1) 0 0 ((a.size : Int) - 1) (le_refl _) (by omega) (by omega) (by omega)
  revert this
  cases (iterR (bsF a v) 0 (a.size + 1) (none, 0, (a.size : Int) - 1)).1 with
  | some r => intro h; simp only at h ⊢; omega
  | none => intro h; simp only at h ⊢; omega

theorem as_loop0 (pb : beatmap.playable.PlayableBeatmap) :
    ∀ (i : Usize) (objs : alloc.vec.Vec (beatmap.playable.ObjRef × F64)), i.val ≤ pb.hit_objects.val.length →
      objs.val.length + asCnt (pb.hit_objects.val.drop i.val) < 2^31 →
      ∃ r, beatmap.mods.adaptive_speed_loop0 pb objs i = ok (pb.format_version, pb.difficulty, pb.base_difficulty,
          pb.stack_leniency, pb.audio_lead_in, pb.control_points, pb.breaks, pb.hit_objects, pb.epoch, pb.mod_states, r) ∧
        (abs r : Array (ObjRef × F64)) = (((pb.hit_objects.val.map (abs : _ → OsuHitObject)).drop i.val).foldl
          (asH pb.epoch.val) (abs objs, i.val)).1 ∧
        r.val.length ≤ objs.val.length + asCnt (pb.hit_objects.val.drop i.val) := by
  intro i
  induction hk : pb.hit_objects.val.length - i.val using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    intro objs hle hb
    unfold beatmap.mods.adaptive_speed_loop0
    rw [loop_unfold]
    by_cases hlt : i.val < pb.hit_objects.val.length
    · have hdc : pb.hit_objects.val.drop i.val = (pb.hit_objects.val[i.val]'hlt) :: pb.hit_objects.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt]
      have hcnt : asCnt (pb.hit_objects.val.drop i.val) = (pb.hit_objects.val[i.val]'hlt).nested.val.length + 1 +
          asCnt (pb.hit_objects.val.drop (i.val + 1)) := by
        rw [hdc]; simp only [asCnt, List.map_cons, List.sum_cons]
      obtain ⟨o1, i1, hb1, hi1v, ho1v, ho1l⟩ := as_body0 pb objs i hlt (by omega)
      obtain ⟨r, hr, hrv, hrl⟩ := ih (pb.hit_objects.val.length - i1.val) (by omega) i1 rfl o1 (by omega) (by rw [hi1v]; omega)
      refine ⟨r, ?_, ?_, by rw [hi1v] at hrl; omega⟩
      · simp only [hb1, bind_ok]; unfold beatmap.mods.adaptive_speed_loop0 at hr; exact hr
      · have hd : (pb.hit_objects.val.map (abs : _ → OsuHitObject)).drop i.val =
            (abs (pb.hit_objects.val[i.val]'hlt) : OsuHitObject) :: (pb.hit_objects.val.map abs).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
        rw [hd, List.foldl_cons, hrv, hi1v, ho1v]
        simp only [asH]
    · have hl : ¬ i < alloc.vec.Vec.len pb.hit_objects := by
        show ¬ i.val < (alloc.vec.Vec.len pb.hit_objects).val; simpa using hlt
      refine ⟨objs, by simp [beatmap.mods.adaptive_speed_loop0.body, hl], ?_, by omega⟩
      rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl

theorem as_loop1 (objs : alloc.vec.Vec (beatmap.playable.ObjRef × F64)) :
    ∀ (k : Usize) (sorted : alloc.vec.Vec F64), k.val ≤ objs.val.length → sorted.val.length ≤ k.val →
      ∃ r, beatmap.mods.adaptive_speed_loop1 objs sorted k = ok r ∧
        r.val = sorted.val ++ (objs.val.drop k.val).map (·.2) := by
  intro k
  induction hk : objs.val.length - k.val using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    intro sorted hle hs
    unfold beatmap.mods.adaptive_speed_loop1
    rw [loop_unfold]
    by_cases hlt : k.val < objs.val.length
    · have hl : k < alloc.vec.Vec.len objs := by show k.val < (alloc.vec.Vec.len objs).val; simpa using hlt
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := objs.property; omega)
      obtain ⟨w, hw, hwv⟩ := push_eq sorted (objs.val[k.val]'hlt).2 (by have := objs.property; omega)
      obtain ⟨r, hr, hrv⟩ := ih (objs.val.length - k1.val) (by omega) k1 rfl w (by omega) (by rw [hwv]; simp; omega)
      refine ⟨r, ?_, ?_⟩
      · have hb : beatmap.mods.adaptive_speed_loop1.body objs sorted k = ok (.cont (w, k1)) := by
          simp only [beatmap.mods.adaptive_speed_loop1.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok]
          revert hw; generalize objs.val[k.val]'hlt = p; cases p; intro hw; simp [hw, hk1]
        simp only [hb, bind_ok]; unfold beatmap.mods.adaptive_speed_loop1 at hr; exact hr
      · rw [hrv, hwv, hk1v]; conv_rhs => rw [List.drop_eq_getElem_cons hlt]
        simp only [List.map_cons, List.append_assoc, List.singleton_append]
    · have hl : ¬ k < alloc.vec.Vec.len objs := by show ¬ k.val < (alloc.vec.Vec.len objs).val; simpa using hlt
      refine ⟨sorted, by simp [beatmap.mods.adaptive_speed_loop1.body, hl], ?_⟩
      rw [List.drop_eq_nil_of_le (by omega)]; simp



theorem as_cmp_ne (c : I32) (x : Int) (h : c.val = x) : (c != 0#i32) = (x != 0) := by
  by_cases hc : c = 0#i32
  · subst hc; have : x = 0 := by rw [← h]; decide
    subst this; decide
  · have : x ≠ 0 := by
      intro hx; apply hc; apply IScalar.eq_of_val_eq; rw [h, hx]; decide
    rw [(bne_iff_ne (a := c) (b := 0#i32)).mpr hc, (bne_iff_ne (a := x) (b := 0)).mpr this]

theorem as_body2 (sorted et : alloc.vec.Vec F64) (m : Usize) (hlt : m.val < sorted.val.length) (he : et.val.length ≤ m.val) :
    ∃ w m1, beatmap.mods.adaptive_speed_loop2.body sorted et m = ok (.cont (w, m1)) ∧ m1.val = m.val + 1 ∧
      w.val.toArray = asE et.val.toArray (sorted.val[m.val]'hlt) ∧ w.val.length ≤ et.val.length + 1 := by
  have hl : m < alloc.vec.Vec.len sorted := by show m.val < (alloc.vec.Vec.len sorted).val; simpa using hlt
  obtain ⟨m1, hm1, hm1v⟩ := usize_add_one m (by have := sorted.property; omega)
  obtain ⟨w, hw, hwv⟩ := push_eq et (sorted.val[m.val]'hlt) (by have := sorted.property; omega)
  by_cases h0 : et.val.length = 0
  · have h0' : alloc.vec.Vec.len et = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
    refine ⟨w, m1, ?_, hm1v, ?_, by rw [hwv]; simp⟩
    · simp only [beatmap.mods.adaptive_speed_loop2.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok, h0', hw, hm1]
    · simp [asE, h0, hwv]
  · have h0' : ¬ alloc.vec.Vec.len et = 0#usize := by
      intro h; apply h0; have := congrArg UScalar.val h; simpa using this
    obtain ⟨i3, hi3, hi3v⟩ := dns_usize_sub1 (alloc.vec.Vec.len et) (by simp; omega)
    have hi3l : i3.val < et.val.length := by rw [hi3v]; simp; omega
    obtain ⟨c, hc, hcv⟩ := beatmap.dotnet.compare_f64_refines (et.val[i3.val]'hi3l) (sorted.val[m.val]'hlt)
    have hback : et.val.toArray.back! = et.val[i3.val]'hi3l := by
      rw [Array.back!, getElem!_pos _ _ (by simp; omega)]; simp [hi3v]
    have hne := as_cmp_ne c _ hcv
    by_cases hz : (c != 0#i32) = true
    · refine ⟨w, m1, ?_, hm1v, ?_, by rw [hwv]; simp⟩
      · simp only [beatmap.mods.adaptive_speed_loop2.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok, h0', if_false,
          hi3, vec_index_eq _ _ hi3l, hc, hz, hw, hm1]
      · rw [hne] at hz; simp only [asE, hback, hz, Bool.or_true, if_true, hwv]; simp
    · refine ⟨et, m1, ?_, hm1v, ?_, by omega⟩
      · simp only [beatmap.mods.adaptive_speed_loop2.body, hl, if_true, vec_index_eq _ _ hlt, bind_ok, h0', if_false,
          hi3, vec_index_eq _ _ hi3l, hc, hz, Bool.false_eq_true, hm1]
      · rw [hne] at hz; simp only [Bool.not_eq_true] at hz
        simp only [asE, hback, hz, Bool.or_false]; simp [h0]

theorem as_loop2 (sorted : alloc.vec.Vec F64) :
    ∀ (m : Usize) (et : alloc.vec.Vec F64), m.val ≤ sorted.val.length → et.val.length ≤ m.val →
      ∃ r, beatmap.mods.adaptive_speed_loop2 sorted et m = ok r ∧
        r.val.toArray = (sorted.val.drop m.val).foldl asE et.val.toArray ∧ r.val.length ≤ sorted.val.length := by
  intro m
  induction hk : sorted.val.length - m.val using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    intro et hle he
    unfold beatmap.mods.adaptive_speed_loop2
    rw [loop_unfold]
    by_cases hlt : m.val < sorted.val.length
    · obtain ⟨w, m1, hb, hm1v, hwv, hwl⟩ := as_body2 sorted et m hlt he
      obtain ⟨r, hr, hrv, hrl⟩ := ih (sorted.val.length - m1.val) (by omega) m1 rfl w (by omega) (by omega)
      refine ⟨r, ?_, ?_, hrl⟩
      · simp only [hb, bind_ok]; unfold beatmap.mods.adaptive_speed_loop2 at hr; exact hr
      · rw [List.drop_eq_getElem_cons hlt, List.foldl_cons, ← hwv, hrv, hm1v]
    · have hl : ¬ m < alloc.vec.Vec.len sorted := by show ¬ m.val < (alloc.vec.Vec.len sorted).val; simpa using hlt
      refine ⟨et, by simp [beatmap.mods.adaptive_speed_loop2.body, hl], ?_, by omega⟩
      rw [List.drop_eq_nil_of_le (by omega)]; rfl



theorem as_body3 (objs : alloc.vec.Vec (beatmap.playable.ObjRef × F64)) (et : alloc.vec.Vec F64)
    (en : alloc.vec.Vec (beatmap.playable.ObjRef × F64)) (q : Usize) (hlt : q.val < objs.val.length)
    (he : en.val.length ≤ q.val) (hN : et.val.length < 2^31) :
    ∃ w q1, beatmap.mods.adaptive_speed_loop3.body objs et en q = ok (.cont (w, q1)) ∧ q1.val = q.val + 1 ∧
      (abs w : Array (ObjRef × F64)) = asQ et.val.toArray (abs en) (abs (objs.val[q.val]'hlt)) ∧
      w.val.length ≤ en.val.length + 1 := by
  have hl : q < alloc.vec.Vec.len objs := by show q.val < (alloc.vec.Vec.len objs).val; simpa using hlt
  obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by have := objs.property; omega)
  have hds : (alloc.vec.Vec.deref et).val = et.val := by simp [alloc.vec.Vec.deref]
  have hix := vec_index_eq objs q hlt
  generalize objs.val[q.val]'hlt = x at hix ⊢
  obtain ⟨r, t⟩ := x
  obtain ⟨b, hb, hbv⟩ := beatmap.dotnet.binary_search_f64_refines (alloc.vec.Vec.deref et) t (by rw [hds]; exact hN)
  rw [hds] at hbv
  have hrange := as_bs_range et.val.toArray t
  rw [← hbv] at hrange
  simp only [List.size_toArray] at hrange
  have hone : (1#i64 : I64).val = 1 := by decide
  -- b1 = if b < 0 then -b - 1 else b
  have hb1 : ∃ b1 : I64, (if b < 0#i64 then (do let i1 ← -. b; i1 - 1#i64) else ok b) = ok b1 ∧
      b1.val = (if b.val < 0 then -b.val - 1 else b.val) := by
    by_cases hneg : b.val < 0
    · have hne : b ≠ IScalar.min IScalarTy.I64 := by
        intro h; rw [h] at hrange
        have : IScalar.min IScalarTy.I64 = -9223372036854775808 := by simp [IScalar.min]; simp [I64.min_eq]
        rw [this] at hrange; omega
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (IScalar.neg_step b hne)
      obtain ⟨w, hw, hwv⟩ := dns_i64_sub z 1#i64 (by rw [hone, hzv]; omega) (by rw [hone, hzv]; omega)
      have hlt0 : b < 0#i64 := by show b.val < (0#i64 : I64).val; simpa using hneg
      refine ⟨w, ?_, by rw [hwv, hzv, hone]; simp [hneg]⟩
      simp only [hlt0, if_true]
      show (do let i1 ← IScalar.neg b; i1 - 1#i64) = ok w
      rw [hz]; simp only [bind_ok]; exact hw
    · have hlt0 : ¬ b < 0#i64 := by show ¬ b.val < (0#i64 : I64).val; simpa using hneg
      exact ⟨b, by simp only [hlt0, if_false], by simp [hneg]⟩
  obtain ⟨b1, hb1e, hb1v⟩ := hb1
  have hb1r : 0 ≤ b1.val ∧ b1.val ≤ et.val.length := by
    rw [hb1v]; split <;> omega
  obtain ⟨ix, hixe, hixv⟩ := dns_i64_sub b1 1#i64 (by rw [hone]; omega) (by rw [hone]; omega)
  rw [hone] at hixv
  have hasq : asQ et.val.toArray (abs en) (abs ((r, t) : beatmap.playable.ObjRef × F64)) =
      (if ix.val ≥ 0 then (abs en : Array (ObjRef × F64)).push (abs r, et.val.toArray[ix.val.toNat]!) else abs en) := by
    simp only [asQ]
    have e1 : (abs ((r, t) : beatmap.playable.ObjRef × F64) : ObjRef × F64).2 = t := rfl
    have e2 : (abs ((r, t) : beatmap.playable.ObjRef × F64) : ObjRef × F64).1 = abs r := rfl
    rw [e1, e2, ← hbv, hixv, hb1v]
  by_cases hge : 0 ≤ ix.val
  · have hge' : ix >= 0#i64 := by show (0#i64 : I64).val ≤ ix.val; simpa using hge
    obtain ⟨u, hu, huv⟩ := eq_ok_of_spec (IScalar.hcast_inBounds_spec .Usize ix
      (by have h1 := dns_usize_max; rw [UScalar.max_USize_eq]; constructor <;> omega))
    have hul : u.val < et.val.length := by omega
    have hu' : IScalar.hcast UScalarTy.Usize ix = u := by simpa [lift] using hu
    obtain ⟨w, hw, hwv⟩ := push_eq en (r, et.val[u.val]'hul) (by have := objs.property; omega)
    refine ⟨w, q1, ?_, hq1v, ?_, by rw [hwv]; simp⟩
    · simp only [beatmap.mods.adaptive_speed_loop3.body, hl, if_true, hix, bind_ok, hb, hb1e, hixe, hge', lift, hu',
        vec_index_eq _ _ hul, hw, hq1, uncurry_apply_pair]
    · rw [hasq, if_pos hge, as_absvec_push en w _ hwv]
      have : et.val.toArray[ix.val.toNat]! = et.val[u.val]'hul := by
        rw [getElem!_pos _ _ (by simp; omega)]; simp; congr 1; omega
      rw [this]; rfl
  · have hge' : ¬ ix >= 0#i64 := by show ¬ (0#i64 : I64).val ≤ ix.val; simpa using hge
    refine ⟨en, q1, ?_, hq1v, ?_, by omega⟩
    · simp only [beatmap.mods.adaptive_speed_loop3.body, hl, if_true, hix, bind_ok, hb, hb1e, hixe, hge', if_false, hq1, uncurry_apply_pair]
    · rw [hasq, if_neg (by omega)]



theorem as_loop3 (objs : alloc.vec.Vec (beatmap.playable.ObjRef × F64)) (et : alloc.vec.Vec F64)
    (hN : et.val.length < 2^31) :
    ∀ (q : Usize) (en : alloc.vec.Vec (beatmap.playable.ObjRef × F64)), q.val ≤ objs.val.length → en.val.length ≤ q.val →
      ∃ r, beatmap.mods.adaptive_speed_loop3 objs et en q = ok r ∧
        (abs r : Array (ObjRef × F64)) = ((objs.val.map (abs : _ → ObjRef × F64)).drop q.val).foldl (asQ et.val.toArray) (abs en) := by
  intro q
  induction hk : objs.val.length - q.val using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    intro en hle he
    unfold beatmap.mods.adaptive_speed_loop3
    rw [loop_unfold]
    by_cases hlt : q.val < objs.val.length
    · obtain ⟨w, q1, hb, hq1v, hwv, hwl⟩ := as_body3 objs et en q hlt he hN
      obtain ⟨r, hr, hrv⟩ := ih (objs.val.length - q1.val) (by omega) q1 rfl w (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · simp only [hb, bind_ok]; unfold beatmap.mods.adaptive_speed_loop3 at hr; exact hr
      · have hd : (objs.val.map (abs : _ → ObjRef × F64)).drop q.val =
            (abs (objs.val[q.val]'hlt) : ObjRef × F64) :: (objs.val.map abs).drop (q.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
        rw [hd, List.foldl_cons, ← hwv, hrv, hq1v]
    · have hl : ¬ q < alloc.vec.Vec.len objs := by show ¬ q.val < (alloc.vec.Vec.len objs).val; simpa using hlt
      refine ⟨en, by simp [beatmap.mods.adaptive_speed_loop3.body, hl], ?_⟩
      rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl

theorem beatmap.mods.adaptive_speed_refines (idx : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hm : pb.mod_states.val.length < Usize.max) (hC : asCnt pb.hit_objects.val < 2^31) :
    ∃ r, beatmap.mods.adaptive_speed idx pb = ok r ∧ Mods.adaptiveSpeed (abs idx) (abs pb) = abs r := by
  obtain ⟨o, ho, hov, hol⟩ := as_loop0 pb 0#usize (alloc.vec.Vec.new (beatmap.playable.ObjRef × F64)) (by simp)
    (by simpa using hC)
  have hov' : (abs o : Array (ObjRef × F64)) = (List.foldl (asH pb.epoch.val) (#[], 0) (pb.hit_objects.val.map abs)).1 := by
    rw [hov]; rfl
  have hol' : o.val.length ≤ asCnt pb.hit_objects.val := by simpa [alloc.vec.Vec.new] using hol
  obtain ⟨s1, hs1, hs1v⟩ := as_loop1 o 0#usize (alloc.vec.Vec.with_capacity F64 (alloc.vec.Vec.len o)) (by simp)
    (by simp [alloc.vec.Vec.with_capacity])
  have hs1n : s1.val.length < 2^31 := by
    rw [hs1v]; simp [alloc.vec.Vec.with_capacity]; omega
  obtain ⟨s2, hs2, hs2v⟩ := beatmap.dotnet.stable_sort_by_refines float.F64.Insts.CoreCloneClone (fun x => rfl)
    float.F64.Insts.Osu_eval_coreBeatmapDotnetSortKey id (fun x => rfl) s1 hs1n
  have hs2n : s2.val.length = s1.val.length := by
    have := congrArg Array.size hs2v
    simp only [List.size_toArray] at this
    rw [this]; unfold stableSortBy; simp [dns_sort_length]
  obtain ⟨et, het, hetv, hetl⟩ := as_loop2 s2 0#usize (alloc.vec.Vec.new F64) (by simp) (by simp)
  obtain ⟨en, hen, henv⟩ := as_loop3 o et (by omega) 0#usize (alloc.vec.Vec.new (beatmap.playable.ObjRef × F64)) (by simp) (by simp)
  obtain ⟨v3, hv3, hv3v⟩ := push_eq pb.mod_states (idx, beatmap.playable.ModState.PrecedingEndTimes en) hm
  refine ⟨{ pb with mod_states := v3 }, ?_, ?_⟩
  · unfold beatmap.mods.adaptive_speed
    simp only [ho, bind_ok, uncurry_apply_pair, hs1, hs2, het, hen, hv3]
  · rw [as_spec]
    have hho : (abs pb : PlayableBeatmap).hitObjects.toList = pb.hit_objects.val.map abs := by simp [abs]
    have hep : (abs pb : PlayableBeatmap).epoch = pb.epoch.val := rfl
    rw [hho, hep, ← hov']
    dsimp only
    have hsm : (abs o : Array (ObjRef × F64)).map (·.2) = s1.val.toArray := by
      rw [hs1v]; simp [abs, alloc.vec.Vec.with_capacity]
    rw [hsm, ← hs2v]
    have het' : s2.val.toArray.toList.foldl asE #[] = et.val.toArray := by
      rw [hetv]; simp [alloc.vec.Vec.new]
    rw [het']
    have hen' : (abs o : Array (ObjRef × F64)).toList.foldl (asQ et.val.toArray) #[] = abs en := by
      rw [henv]; simp [abs, alloc.vec.Vec.new]
    rw [hen']
    simp [abs, hv3v]


end OsuProofs
