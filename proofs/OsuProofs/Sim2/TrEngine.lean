/-
`sim::transforms` engine core (Rust) refines `OsuModel.Sim` Transforms: `tracker_rewind`/`tracker_catch_up`/the
`tracker_update` main loop against the spec's `trackerUpdate` (restated as `s2_TU` with named loop bodies, equal by
`rfl`), `update_transforms`, `add_transform`, `clear_state`, `transform_to`, `seq_append`, `fade_in_from_zero`.
Spec `for hk : k in [a:b]` (`forIn'`) loops become `iterR` via `s2_forIn'_range`.
-/
import OsuProofs.Sim2.Transforms
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
theorem s2_forIn'_range'_g {S : Type} (g : Nat → S → ForInStep S) :
    ∀ (k j : Nat) (s : S), forIn' (m := Id) (List.range' j k) s (fun a _ s => g a s) = iterR g j k s := by
  intro k
  induction k with
  | zero => intro j s; rfl
  | succ k ih =>
    intro j s
    simp only [List.range'_succ, List.forIn'_cons, iterR]
    cases g j s with
    | done c => rfl
    | yield c => exact ih (j + 1) c

theorem s2_mem_range (a lo hi : Nat) : a ∈ [lo:hi] ↔ lo ≤ a ∧ a < hi := by
  simp [Membership.mem]; intro _ _; omega

theorem s2_forIn'_list_g {S : Type} (l : List Nat) (j k : Nat) (hl : l = List.range' j k)
    (F : (a : Nat) → a ∈ l → S → Id (ForInStep S)) (G : Nat → S → ForInStep S) (hFG : ∀ a h s, F a h s = G a s) (s : S) :
    forIn' (m := Id) l s F = iterR G j k s := by
  subst hl
  rw [show F = (fun a _ s => G a s) from funext fun a => funext fun h => funext fun s => hFG a h s]
  exact s2_forIn'_range'_g G k j s

theorem s2_forIn'_range {S : Type} (lo hi : Nat) (f : (a : Nat) → a ∈ [lo:hi] → S → Id (ForInStep S)) (s : S) :
    forIn' (m := Id) [lo:hi] s f =
      iterR (fun a s => if h : lo ≤ a ∧ a < hi then f a ((s2_mem_range a lo hi).2 h) s else .yield s) lo (hi - lo) s := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine s2_forIn'_list_g _ lo (hi - lo) (by simp [Std.Legacy.Range.size]) _ _ ?_ s
  intro a h s
  have h' : lo ≤ a ∧ a < hi := by simp [List.mem_range', Std.Legacy.Range.size] at h; omega
  simp [h']
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Sim

def s2_rwB (time : F64) (n : Nat) (k : Nat) (hk : k ∈ [0:n]) (r : TObj × Vector Tr n × Bool) :
    Id (ForInStep (TObj × Vector Tr n × Bool)) := do
  let mut o := r.1
  let mut ts := r.2.1
  let mut reverted := r.2.2
  let i := n - 1 - k
  have hi : i < n := by have hu : k < n := hk.upper; omega
  let t := ts[i]
  if !t.applied then return .yield (o, ts, reverted)
  if t.start ≤ time then
    if !reverted then
      ts := ts.set i { t with appliedToEnd := false }
      reverted := true
  else
    let (o', t') := applyTr o t time
    o := o'
    ts := ts.set i { t' with applied := false, appliedToEnd := false }
  return .yield (o, ts, reverted)

def s2_cuB (n i : Nat) (hi : i < n) (last : Nat) (at_ : F64) (j : Nat) (hj : j ∈ [last:i]) (r : TObj × Vector Tr n) :
    Id (ForInStep (TObj × Vector Tr n)) := do
  let mut o := r.1
  let mut ts := r.2
  have : j < n := by have hu : j < i := hj.upper; omega
  let u := ts[j]
  let mut u' := u
  if !u.appliedToEnd then
    let (o', uu) := applyTr o u at_
    o := o'
    u' := uu
  ts := ts.set j { u' with appliedToEnd := true }
  return .yield (o, ts)

def s2_mainB (time : F64) (n : Nat) (_x : Nat) (r : TObj × Vector Tr n × Nat × Nat) :
    Id (ForInStep (TObj × Vector Tr n × Nat × Nat)) := do
  let mut o := r.1
  let mut ts := r.2.1
  let mut last := r.2.2.1
  let mut i := r.2.2.2
  if hi : i < n then
    let mut t := ts[i]
    if time < t.start then return .done (o, ts, last, i)
    if !t.applied then
      let (o', ts') := forIn' [last:i] (o, ts) (s2_cuB n i hi last t.start)
      o := o'
      ts := ts'
    if !t.hasStart then t := readStart o t
    if !t.appliedToEnd then
      let (o', tt) := applyTr o t time
      o := o'
      t := { tt with appliedToEnd := t.endT ≤ time }
    ts := ts.set i t
    if t.appliedToEnd then last := i + 1
    i := i + 1
    return .yield (o, ts, last, i)
  else return .done (o, ts, last, i)

def s2_TU (o : TObj) (tk : Tracker) (time : F64) (rewinding : Bool) : TObj × Tracker :=
  let n := tk.ts.size
  let ts0 : Vector Tr n := ⟨tk.ts, rfl⟩
  let r1 : TObj × Vector Tr n × Nat :=
    if rewinding then
      let r := forIn' [0:n] (o, ts0, false) (s2_rwB time n)
      (r.1, r.2.1, 0)
    else (o, ts0, tk.lastApplied)
  let r2 := forIn [0:n] (r1.1, r1.2.1, r1.2.2, r1.2.2) (s2_mainB time n)
  (r2.1, { tk with ts := r2.2.1.toArray, lastApplied := r2.2.2.1 })

theorem s2_TU_eq (o : TObj) (tk : Tracker) (time : F64) (rw : Bool) : trackerUpdate o tk time rw = s2_TU o tk time rw := by
  unfold trackerUpdate s2_TU
  cases rw <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_vec_get_abs {N : Nat} (tsV : Vector OsuModel.Sim.Tr N) (ts : List sim.transforms.Tr)
    (hV : tsV.toList = ts.map abs) (i : Nat) (hi : i < N) (hi' : i < ts.length) :
    tsV[i] = abs (ts[i]'hi') := by
  rw [← Vector.getElem_toList (h := by simpa using hi)]; simp [hV]

@[simp] theorem s2_absTr_f (t : sim.transforms.Tr) : (abs t : OsuModel.Sim.Tr).applied = t.applied ∧
    (abs t : OsuModel.Sim.Tr).appliedToEnd = t.applied_to_end ∧ (abs t : OsuModel.Sim.Tr).hasStart = t.has_start ∧
    (abs t : OsuModel.Sim.Tr).start = t.start ∧ (abs t : OsuModel.Sim.Tr).endT = t.end_t := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem s2_map_set_vec {N : Nat} (ts : alloc.vec.Vec sim.transforms.Tr) (sts : Vector OsuModel.Sim.Tr N)
    (h : ts.val.map abs = sts.toList) (i : Usize) (j : Nat) (hij : i.val = j) (hj : j < N) (x : sim.transforms.Tr)
    (y : OsuModel.Sim.Tr) (hxy : abs x = y) : (alloc.vec.Vec.set ts i x).val.map abs = (sts.set j y hj).toList := by
  subst hij hxy; simp [vec_set_val', List.map_set, h, Vector.toList_set]

theorem s2_tracker_rewind (o : sim.transforms.TObj) (ts : alloc.vec.Vec sim.transforms.Tr) (time : F64)
    (N : Nat) (tsV : Vector OsuModel.Sim.Tr N) (hN : ts.val.length = N) (hV : tsV.toList = ts.val.map abs) :
    ∃ o' ts', sim.transforms.tracker_rewind o ts time = ok (o', ts') ∧
      abs o' = (forIn' (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, false) (s2_rwB time N)).1 ∧
      ts'.val.map abs = (forIn' (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, false) (s2_rwB time N)).2.1.toList := by
  have hmax := ts.property
  rw [s2_forIn'_range]
  obtain ⟨y, hl, ⟨q1, q2⟩⟩ := loop_iterR
    (fun (x : sim.transforms.TObj × alloc.vec.Vec sim.transforms.Tr × Bool × Usize) =>
      sim.transforms.tracker_rewind_loop.body time (alloc.vec.Vec.len ts) x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun a s => if h : 0 ≤ a ∧ a < N then s2_rwB time N a ((s2_mem_range a 0 N).2 h) s else .yield s) N
    (fun x => x.2.2.2.val)
    (fun x s => abs x.1 = s.1 ∧ x.2.1.val.map abs = s.2.1.toList ∧ x.2.2.1 = s.2.2 ∧ x.2.1.val.length = N)
    (fun y s => abs y.1 = s.1 ∧ y.2.val.map abs = s.2.1.toList)
    (by
      rintro ⟨o1, ts1, rv, k⟩ ⟨so, sts, srv⟩ ⟨h1, h2, h3, h4⟩ hk
      simp only at h1 h2 h3 h4 hk ⊢
      subst h1 h3
      have hkN : k.val < (alloc.vec.Vec.len ts).val := by simp; omega
      obtain ⟨i0, hi0, hi0v⟩ : ∃ z, alloc.vec.Vec.len ts - 1#usize = ok z ∧ z.val = N - 1 := by
        have := Usize.sub_spec (x := alloc.vec.Vec.len ts) (y := 1#usize) (by simp; omega)
        obtain ⟨z, hz, hv⟩ := eq_ok_of_spec this; exact ⟨z, hz, by simp at hv; omega⟩
      obtain ⟨i1, hi1, hi1v⟩ : ∃ z, i0 - k = ok z ∧ z.val = N - 1 - k.val := by
        have := Usize.sub_spec (x := i0) (y := k) (by omega)
        obtain ⟨z, hz, hv⟩ := eq_ok_of_spec this; exact ⟨z, hz, by omega⟩
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
      have hiN : N - 1 - k.val < ts1.val.length := by omega
      have hiN' : i1.val < ts1.val.length := by omega
      have hget := s2_vec_get_abs sts ts1.val h2.symm (N - 1 - k.val) (by omega) hiN
      constructor
      have hti : ts1.val[N - 1 - k.val] = ts1.val[i1.val] := by simp only [hi1v]
      have e1 := vec_index_eq ts1 i1 hiN'
      have e2 := vec_index_mut_eq ts1 i1 hiN'
      · rintro ⟨so', sts', srv'⟩ hs'
        rw [dif_pos ⟨Nat.zero_le _, hk⟩] at hs'
        simp only [s2_rwB, hget, hti] at hs'
        generalize htt : ts1.val[i1.val] = tt at hs' e1 e2
        obtain ⟨⟨t2, o2⟩, hr, er⟩ := sim.transforms.apply_tr_refines o1 tt time
        have hbody : sim.transforms.tracker_rewind_loop.body time ts.len o1 ts1 rv k = (do
            let (o2, ts2, rv2) ← if tt.applied then (if tt.start ≤ time then
                (if rv then ok (o1, ts1, rv) else ok (o1, alloc.vec.Vec.set ts1 i1 { tt with applied_to_end := false }, true))
              else ok (o2, alloc.vec.Vec.set ts1 i1 { t2 with applied := false, applied_to_end := false }, rv))
              else ok (o1, ts1, rv)
            ok (ControlFlow.cont (o2, ts2, rv2, k1))) := by
          simp only [sim.transforms.tracker_rewind_loop.body, vec_lt_len_iff, show k.val < ts.val.length by omega,
            if_true, hi0, hi1, bind_ok, hk1, float.F64.le, hr, e1, e2]
          by_cases ha : tt.applied <;> by_cases hs : tt.start ≤ time <;> cases rv <;> simp [ha, hs]
        rw [hbody]
        by_cases ha : tt.applied
        · by_cases hs : tt.start ≤ time
          · cases rv
            · simp [ha, hs] at hs'; obtain ⟨rfl, rfl, rfl⟩ := hs'
              refine ⟨(o1, alloc.vec.Vec.set ts1 i1 { tt with applied_to_end := false }, true, k1), by simp [ha, hs],
                hk1v, rfl, ?_, rfl, by simp [vec_set_val', h4]⟩
              exact s2_map_set_vec ts1 sts h2 i1 _ hi1v (by omega) _ _ (by cases tt; simp_all [abs])
            · simp [ha, hs] at hs'; obtain ⟨rfl, rfl, rfl⟩ := hs'
              exact ⟨(o1, ts1, true, k1), by simp [ha, hs], hk1v, rfl, h2, rfl, h4⟩
          · simp [ha, hs, er] at hs'; obtain ⟨rfl, rfl, rfl⟩ := hs'
            refine ⟨(o2, alloc.vec.Vec.set ts1 i1 { t2 with applied := false, applied_to_end := false }, rv, k1),
              by simp [ha, hs], hk1v, rfl, ?_, rfl, by simp [vec_set_val', h4]⟩
            exact s2_map_set_vec ts1 sts h2 i1 _ hi1v (by omega) _ _ (by cases t2; simp_all [abs])
        · simp [ha] at hs'; obtain ⟨rfl, rfl, rfl⟩ := hs'
          exact ⟨(o1, ts1, rv, k1), by simp [ha], hk1v, rfl, h2, rfl, h4⟩
      · intro s' hs'
        rw [dif_pos ⟨Nat.zero_le _, hk⟩] at hs'
        simp only [s2_rwB] at hs'
        split at hs' <;> (try split at hs') <;> (try split at hs') <;> simp at hs')
    (by
      rintro ⟨o1, ts1, rv, k⟩ ⟨so, sts, srv⟩ ⟨h1, h2, h3, h4⟩ hk
      simp only at h1 h2 h3 h4 hk ⊢
      refine ⟨(o1, ts1), ?_, h1, h2⟩
      simp [sim.transforms.tracker_rewind_loop.body, show ¬ k < alloc.vec.Vec.len ts by
        intro h; have : k.val < ts.val.length := by simpa using h
        omega])
    (o, ts, false, 0#usize) ((abs o : OsuModel.Sim.TObj), tsV, false) ⟨rfl, hV.symm, rfl, hN⟩ (by simp)
  refine ⟨y.1, y.2, ?_, ?_, ?_⟩
  · unfold sim.transforms.tracker_rewind sim.transforms.tracker_rewind_loop; exact hl
  · simpa using q1
  · simpa using q2
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_catch_up (o : sim.transforms.TObj) (ts : alloc.vec.Vec sim.transforms.Tr) (last i : Usize) (at_ : F64)
    (N : Nat) (tsV : Vector OsuModel.Sim.Tr N) (hN : ts.val.length = N) (hV : tsV.toList = ts.val.map abs)
    (hi : i.val < N) :
    ∃ o' ts', sim.transforms.tracker_catch_up o ts last i at_ = ok (o', ts') ∧
      abs o' = (forIn' (m := Id) [last.val:i.val] ((abs o : OsuModel.Sim.TObj), tsV) (s2_cuB N i.val hi last.val at_)).1 ∧
      ts'.val.map abs = (forIn' (m := Id) [last.val:i.val] ((abs o : OsuModel.Sim.TObj), tsV) (s2_cuB N i.val hi last.val at_)).2.toList ∧
      ts'.val.length = N := by
  have hmax := ts.property
  rw [s2_forIn'_range]
  by_cases hli : i.val < last.val
  · refine ⟨o, ts, ?_, ?_⟩
    · unfold sim.transforms.tracker_catch_up sim.transforms.tracker_catch_up_loop
      rw [loop_unfold]; simp [sim.transforms.tracker_catch_up_loop.body, show ¬ last < i by scalar_tac]
    · rw [show i.val - last.val = 0 by omega]; simp [iterR, hV, hN]
  obtain ⟨y, hl, ⟨q1, q2, q3⟩⟩ := loop_iterR
    (fun (x : sim.transforms.TObj × alloc.vec.Vec sim.transforms.Tr × Usize) =>
      sim.transforms.tracker_catch_up_loop.body i at_ x.1 x.2.1 x.2.2)
    (fun a s => if h : last.val ≤ a ∧ a < i.val then s2_cuB N i.val hi last.val at_ a ((s2_mem_range a _ _).2 h) s else .yield s)
    i.val (fun x => x.2.2.val)
    (fun x s => abs x.1 = s.1 ∧ x.2.1.val.map abs = s.2.toList ∧ x.2.1.val.length = N ∧ last.val ≤ x.2.2.val)
    (fun y s => abs y.1 = s.1 ∧ y.2.val.map abs = s.2.toList ∧ y.2.val.length = N)
    (by
      rintro ⟨o1, ts1, j⟩ ⟨so, sts⟩ ⟨h1, h2, h4, h5⟩ hj
      simp only at h1 h2 h4 h5 hj ⊢
      subst h1
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
      have hjN : j.val < ts1.val.length := by omega
      have hget := s2_vec_get_abs sts ts1.val h2.symm j.val (by omega) hjN
      have e1 := vec_index_eq ts1 j hjN
      have e2 := vec_index_mut_eq ts1 j hjN
      have hlt : j < i := by scalar_tac
      refine ⟨?_, ?_⟩
      · rintro ⟨so', sts'⟩ hs'
        rw [dif_pos ⟨h5, hj⟩] at hs'
        simp only [s2_cuB, hget] at hs'
        generalize htt : ts1.val[j.val] = tt at hs' e1 e2
        obtain ⟨⟨t2, o2⟩, hr, er⟩ := sim.transforms.apply_tr_refines o1 tt at_
        by_cases ha : tt.applied_to_end
        · simp [ha] at hs'; obtain ⟨rfl, rfl⟩ := hs'
          refine ⟨(o1, alloc.vec.Vec.set ts1 j { tt with applied_to_end := true }, j1),
            by simp [sim.transforms.tracker_catch_up_loop.body, hlt, e1, e2, hj1, ha], hj1v, rfl, ?_,
            by simp [vec_set_val', h4], by simp [hj1v]; omega⟩
          exact s2_map_set_vec ts1 sts h2 j _ rfl (by omega) _ _ (by cases tt; simp_all [abs])
        · simp [ha, er] at hs'; obtain ⟨rfl, rfl⟩ := hs'
          refine ⟨(o2, alloc.vec.Vec.set ts1 j { t2 with applied_to_end := true }, j1),
            by simp [sim.transforms.tracker_catch_up_loop.body, hlt, e1, e2, hj1, ha, hr], hj1v, rfl, ?_,
            by simp [vec_set_val', h4], by simp [hj1v]; omega⟩
          exact s2_map_set_vec ts1 sts h2 j _ rfl (by omega) _ _ (by cases t2; simp_all [abs])
      · intro s' hs'
        rw [dif_pos ⟨h5, hj⟩] at hs'
        simp only [s2_cuB] at hs'
        split at hs' <;> simp at hs')
    (by
      rintro ⟨o1, ts1, j⟩ ⟨so, sts⟩ ⟨h1, h2, h4, h5⟩ hj
      simp only at h1 h2 h4 h5 hj ⊢
      exact ⟨(o1, ts1), by simp [sim.transforms.tracker_catch_up_loop.body, show ¬ j < i by scalar_tac], h1, h2, h4⟩)
    (o, ts, last) ((abs o : OsuModel.Sim.TObj), tsV) ⟨rfl, hV.symm, hN, le_refl _⟩ (by simp; omega)
  refine ⟨y.1, y.2, ?_, ?_, ?_, q3⟩
  · unfold sim.transforms.tracker_catch_up sim.transforms.tracker_catch_up_loop; exact hl
  · simpa using q1
  · simpa using q2
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_tu_loop (o : sim.transforms.TObj) (ts : alloc.vec.Vec sim.transforms.Tr) (time : F64) (last : Usize)
    (fuel : Usize) (N : Nat) (tsV : Vector OsuModel.Sim.Tr N) (hN : ts.val.length = N)
    (hV : tsV.toList = ts.val.map abs) (hf : fuel.val = N + 1) :
    ∃ o' ts' last', sim.transforms.tracker_update_loop o time ts last last fuel false = ok (o', ts', last') ∧
      abs o' = (forIn (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, last.val, last.val) (s2_mainB time N)).1 ∧
      ts'.val.map abs = (forIn (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, last.val, last.val) (s2_mainB time N)).2.1.toList ∧
      last'.val = (forIn (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, last.val, last.val) (s2_mainB time N)).2.2.1 := by
  have hmax := ts.property
  rw [forIn_range_iterR]
  obtain ⟨y, hl, ⟨q1, q2, q3⟩⟩ := loop_iterR
    (fun (x : sim.transforms.TObj × alloc.vec.Vec sim.transforms.Tr × Usize × Usize × Usize × Bool) =>
      sim.transforms.tracker_update_loop.body time x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun a s => s2_mainB time N a s) N (fun x => N + 1 - x.2.2.2.2.1.val)
    (fun x s => abs x.1 = s.1 ∧ x.2.1.val.map abs = s.2.1.toList ∧ x.2.2.1.val = s.2.2.1 ∧ x.2.2.2.1.val = s.2.2.2 ∧
      x.2.1.val.length = N ∧ x.2.2.2.2.2 = false ∧ x.2.2.2.2.1.val ≤ N + 1 ∧ N + 1 - x.2.2.2.2.1.val ≤ x.2.2.2.1.val)
    (fun y s => abs y.1 = s.1 ∧ y.2.1.val.map abs = s.2.1.toList ∧ y.2.2.val = s.2.2.1)
    (by
      rintro ⟨o1, ts1, lst, i, fu, stop⟩ ⟨so, sts, slast, si⟩ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hidx
      simp only at h1 h2 h3 h4 h5 h6 h7 h8 hidx ⊢
      subst h1 h3 h4 h6
      have hfu : 0 < fu.val := by omega
      obtain ⟨fu1, hfu1, hfu1v⟩ : ∃ z, fu - 1#usize = ok z ∧ z.val = fu.val - 1 := by
        have := Usize.sub_spec (x := fu) (y := 1#usize) (by simp; omega)
        obtain ⟨z, hz, hv⟩ := eq_ok_of_spec this; exact ⟨z, hz, by simp at hv; omega⟩
      by_cases hiN : i.val < N
      · have hiL : i.val < ts1.val.length := by omega
        have hget := s2_vec_get_abs sts ts1.val h2.symm i.val hiN hiL
        have e1 := vec_index_eq ts1 i hiL
        generalize htt : ts1.val[i.val] = tt at e1 hget
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have hpure : ∀ x : ForInStep (OsuModel.Sim.TObj × Vector OsuModel.Sim.Tr N × Nat × Nat), (pure x : Id _) = x :=
          fun _ => rfl
        by_cases hst : time < tt.start
        · refine ⟨fun s' hs' => ?_, fun s' hs' => ?_⟩
          · unfold s2_mainB at hs'; simp [hiN, hget, hst, hpure] at hs'
          · unfold s2_mainB at hs'; simp [hiN, hget, hst, hpure] at hs'
            subst hs'
            have hlt : i < alloc.vec.Vec.len ts1 := by scalar_tac
            have hfz : fu > 0#usize := by scalar_tac
            have hfz1 : fu1 > 0#usize := by scalar_tac
            refine ⟨(o1, ts1, lst), Or.inr ⟨(o1, ts1, lst, i, fu1, true), ?_, ?_⟩, rfl, h2, rfl⟩
            · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, float.F64.lt, hst]
            · simp [sim.transforms.tracker_update_loop.body, hlt, hfz1]
        · refine ⟨?_, fun s' hs' => ?_⟩
          · rintro ⟨so', sts', slast', si'⟩ hs'
            unfold s2_mainB at hs'; simp only [hiN, _root_.dite_true, hget, s2_absTr_f, hst, if_false] at hs'
            have hfz : fu > 0#usize := by scalar_tac
            have hlt : i < alloc.vec.Vec.len ts1 := by scalar_tac
            have e2 := vec_index_mut_eq ts1 i hiL
            have e3 := vec_index_mut_usize_ok ts1 i hiL
            rw [htt] at e2 e3
            by_cases ha : tt.applied
            · have hT0 : True := trivial
              have hiLc : i.val < ts1.val.length := by omega
              have e2c := vec_index_mut_eq ts1 i hiLc
              have e3c := vec_index_mut_usize_ok ts1 i hiLc
              by_cases hh : tt.has_start
              · have hT : True := trivial
                by_cases he : tt.applied_to_end
                · simp [ha, hh, he] at hs'
                  rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                  refine ⟨(o1, alloc.vec.Vec.set ts1 i tt, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                    by simp [hi1v], by simp [vec_set_val', h5], rfl, by simp; omega, by simp; omega⟩
                  · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hi1]
                    try (cases tt; simp_all)
                  · exact s2_map_set_vec ts1 sts h2 i _ rfl hiN _ _ rfl
                · obtain ⟨⟨t2, o2⟩, hr2, er2⟩ := sim.transforms.apply_tr_refines o1 tt time
                  by_cases hle : tt.end_t ≤ time
                  · simp [ha, hh, he, hle, er2] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set ts1 i { t2 with applied_to_end := true }, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', h5], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec ts1 sts h2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
                  · simp [ha, hh, he, hle, er2] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set ts1 i { t2 with applied_to_end := false }, lst, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', h5], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec ts1 sts h2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
              · obtain ⟨rs, hrs, ers⟩ := sim.transforms.read_start_refines o1 tt
                by_cases he : rs.applied_to_end
                · simp [ha, hh, he, hrs, ers] at hs'
                  rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                  refine ⟨(o1, alloc.vec.Vec.set ts1 i rs, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                    by simp [hi1v], by simp [vec_set_val', h5], rfl, by simp; omega, by simp; omega⟩
                  · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hi1, hrs, ers]
                    try (cases rs; simp_all)
                  · exact s2_map_set_vec ts1 sts h2 i _ rfl hiN _ _ rfl
                · obtain ⟨⟨t2, o2⟩, hr2, er2⟩ := sim.transforms.apply_tr_refines o1 rs time
                  by_cases hle : rs.end_t ≤ time
                  · simp [ha, hh, he, hle, er2, hrs, ers] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set ts1 i { t2 with applied_to_end := true }, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', h5], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2, hrs, ers]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec ts1 sts h2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
                  · simp [ha, hh, he, hle, er2, hrs, ers] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set ts1 i { t2 with applied_to_end := false }, lst, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', h5], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2, hrs, ers]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec ts1 sts h2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
            · obtain ⟨oc, tsc, hc, ec1, ec2, ec3⟩ := s2_catch_up o1 ts1 lst i tt.start N sts h5 h2.symm hiN
              generalize hF : forIn' (m := Id) [lst.val:i.val] ((abs o1 : OsuModel.Sim.TObj), sts)
                (s2_cuB N i.val hiN lst.val tt.start) = F at ec1 ec2 hs'
              obtain ⟨so2, V⟩ := F
              simp only at ec1 ec2
              subst ec1
              have hiLc : i.val < tsc.val.length := by omega
              have e2c := vec_index_mut_eq tsc i hiLc
              have e3c := vec_index_mut_usize_ok tsc i hiLc
              by_cases hh : tt.has_start
              · have hT : True := trivial
                by_cases he : tt.applied_to_end
                · simp [ha, hh, he] at hs'
                  rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                  refine ⟨(oc, alloc.vec.Vec.set tsc i tt, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                    by simp [hi1v], by simp [vec_set_val', ec3], rfl, by simp; omega, by simp; omega⟩
                  · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hi1, hc]
                    try (cases tt; simp_all)
                  · exact s2_map_set_vec tsc V ec2 i _ rfl hiN _ _ rfl
                · obtain ⟨⟨t2, o2⟩, hr2, er2⟩ := sim.transforms.apply_tr_refines oc tt time
                  by_cases hle : tt.end_t ≤ time
                  · simp [ha, hh, he, hle, er2] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set tsc i { t2 with applied_to_end := true }, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', ec3], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2, hc]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec tsc V ec2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
                  · simp [ha, hh, he, hle, er2] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set tsc i { t2 with applied_to_end := false }, lst, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', ec3], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2, hc]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec tsc V ec2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
              · obtain ⟨rs, hrs, ers⟩ := sim.transforms.read_start_refines oc tt
                by_cases he : rs.applied_to_end
                · simp [ha, hh, he, hrs, ers] at hs'
                  rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                  refine ⟨(oc, alloc.vec.Vec.set tsc i rs, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                    by simp [hi1v], by simp [vec_set_val', ec3], rfl, by simp; omega, by simp; omega⟩
                  · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hi1, hc, hrs, ers]
                    try (cases rs; simp_all)
                  · exact s2_map_set_vec tsc V ec2 i _ rfl hiN _ _ rfl
                · obtain ⟨⟨t2, o2⟩, hr2, er2⟩ := sim.transforms.apply_tr_refines oc rs time
                  by_cases hle : rs.end_t ≤ time
                  · simp [ha, hh, he, hle, er2, hrs, ers] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set tsc i { t2 with applied_to_end := true }, i1, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', ec3], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2, hc, hrs, ers]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec tsc V ec2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
                  · simp [ha, hh, he, hle, er2, hrs, ers] at hs'
                    rw [hpure] at hs'; simp only [ForInStep.yield.injEq, Prod.mk.injEq] at hs'
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
                    refine ⟨(o2, alloc.vec.Vec.set tsc i { t2 with applied_to_end := false }, lst, i1, fu1, false), ?_, by simp; omega, rfl, ?_, by simp [hi1v],
                      by simp [hi1v], by simp [vec_set_val', ec3], rfl, by simp; omega, by simp; omega⟩
                    · simp [sim.transforms.tracker_update_loop.body, hlt, hfz, hfu1, e1, e2c, e3c, float.F64.lt, hst, ha, hh, he, hle, hi1, hr2, hc, hrs, ers]
                      try (cases t2; simp_all)
                    · exact s2_map_set_vec tsc V ec2 i _ rfl hiN _ _ (by cases t2; simp_all [abs])
          · unfold s2_mainB at hs'; simp only [hiN, _root_.dite_true, hget, s2_absTr_f, hst, if_false] at hs'
            by_cases ha : tt.applied <;> simp [ha] at hs'
            all_goals (repeat' (split at hs'))
            all_goals simp [hpure] at hs'
      · refine ⟨fun s' hs' => ?_, fun s' hs' => ?_⟩
        · unfold s2_mainB at hs'; simp [hiN] at hs'
        · unfold s2_mainB at hs'; simp [hiN] at hs'
          change ForInStep.done (abs o1, sts, lst.val, i.val) = ForInStep.done s' at hs'
          injection hs' with hs'; subst hs'
          exact ⟨(o1, ts1, lst), Or.inl (by simp [sim.transforms.tracker_update_loop.body, vec_lt_len_iff, show ¬ i.val < ts1.val.length by omega]), rfl, h2, rfl⟩)
    (by
      rintro ⟨o1, ts1, lst, i, fu, stop⟩ ⟨so, sts, slast, si⟩ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hidx
      simp only at h1 h2 h3 h4 h5 h6 h7 h8 hidx ⊢
      exact ⟨(o1, ts1, lst), by simp [sim.transforms.tracker_update_loop.body, vec_lt_len_iff, show ¬ i.val < ts1.val.length by omega],
        h1, h2, h3⟩)
    (o, ts, last, last, fuel, false) ((abs o : OsuModel.Sim.TObj), tsV, last.val, last.val)
    ⟨rfl, hV.symm, rfl, rfl, hN, rfl, by simp; omega, by simp; omega⟩ (by simp; omega)
  refine ⟨y.1, y.2.1, y.2.2, ?_, ?_, ?_, ?_⟩
  · unfold sim.transforms.tracker_update_loop; simpa [hf] using hl
  · simpa [hf] using q1
  · simpa [hf] using q2
  · simpa [hf] using q3
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_vec_toArray {N : Nat} (V : Vector OsuModel.Sim.Tr N) (ts : alloc.vec.Vec sim.transforms.Tr)
    (h : ts.val.map abs = V.toList) : (abs ts : Array OsuModel.Sim.Tr) = V.toArray := by
  show (ts.val.map abs).toArray = V.toArray
  rw [h]; obtain ⟨a, ha⟩ := V; simp [Vector.toList]

theorem sim.transforms.tracker_update_refines (o : sim.transforms.TObj) (tk : sim.transforms.Tracker) (time : F64)
    (rewinding : Bool) (h : tk.ts.val.length < Usize.max) :
    ∃ r, sim.transforms.tracker_update o tk time rewinding = ok r ∧
      OsuModel.Sim.trackerUpdate (abs o) (abs tk) time rewinding = (abs r.2, abs r.1) := by
  rw [s2_TU_eq]
  have hN : tk.ts.val.length = (abs tk : OsuModel.Sim.Tracker).ts.size := by
    show _ = (tk.ts.val.map abs).toArray.size; simp
  have hV : (⟨(abs tk : OsuModel.Sim.Tracker).ts, rfl⟩ : Vector OsuModel.Sim.Tr (abs tk : OsuModel.Sim.Tracker).ts.size).toList =
      tk.ts.val.map abs := by
    show (tk.ts.val.map abs).toArray.toList = _; simp
  unfold s2_TU
  cases rewinding with
  | true =>
    obtain ⟨o', ts', hrw, e1, e2⟩ := s2_tracker_rewind o tk.ts time _ _ hN hV
    have hl' : ts'.val.length = (abs tk : OsuModel.Sim.Tracker).ts.size := by
      have := congrArg List.length e2; simpa using this
    obtain ⟨fu, hfu, hfuv⟩ := usize_add_one (alloc.vec.Vec.len ts') (by simp; omega)
    obtain ⟨o2, ts2, l2, hl, q1, q2, q3⟩ := s2_tu_loop o' ts' time 0#usize fu _ _ hl' e2.symm (by simp [hfuv, hl'])
    refine ⟨({ tk with ts := ts2, last_applied := l2 }, o2), ?_, ?_⟩
    · simp [sim.transforms.tracker_update, hrw, hfu, hl]
    · simp only [if_true, ← e1]
      rw [Prod.mk.injEq]
      refine ⟨q1.symm, ?_⟩
      show _ = ({ member := memberS tk.member, ts := abs ts2, counter := tk.counter.val, lastApplied := l2.val } : OsuModel.Sim.Tracker)
      rw [s2_vec_toArray _ ts2 q2, q3]; rfl
  | false =>
    obtain ⟨fu, hfu, hfuv⟩ := usize_add_one (alloc.vec.Vec.len tk.ts) (by simp; omega)
    obtain ⟨o2, ts2, l2, hl, q1, q2, q3⟩ := s2_tu_loop o tk.ts time tk.last_applied fu _ _ hN hV (by simp [hfuv, hN])
    refine ⟨({ tk with ts := ts2, last_applied := l2 }, o2), ?_, ?_⟩
    · simp [sim.transforms.tracker_update, hfu, hl]
    · simp only [Bool.false_eq_true, if_false]
      rw [Prod.mk.injEq]
      refine ⟨q1.symm, ?_⟩
      show _ = ({ member := memberS tk.member, ts := abs ts2, counter := tk.counter.val, lastApplied := l2.val } : OsuModel.Sim.Tracker)
      rw [s2_vec_toArray _ ts2 q2, q3]; rfl
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Sim

def s2_stepMap {S : Type} (φ : S → S) : ForInStep S → ForInStep S
  | .done c => .done (φ c)
  | .yield c => .yield (φ c)

theorem s2_iterR_hom {S : Type} (φ : S → S) (f : Nat → S → ForInStep S)
    (hf : ∀ k s, f k (φ s) = s2_stepMap φ (f k s)) : ∀ n j s, iterR f j n (φ s) = φ (iterR f j n s) := by
  intro n
  induction n with
  | zero => intro j s; rfl
  | succ n ih =>
    intro j s
    simp only [iterR, hf]
    cases f j s with
    | done c => rfl
    | yield c => exact ih (j + 1) c

theorem s2_set_frame (o : TObj) (X : Array Tracker) (m : Member) (v : Vec2) :
    ({ o with trackers := X } : TObj).set m v = { o.set m v with trackers := X } := by
  cases m <;> simp only [TObj.set] <;> split <;> rfl

theorem s2_get_frame (o : TObj) (X : Array Tracker) (m : Member) :
    ({ o with trackers := X } : TObj).get m = o.get m := by
  cases m <;> rfl

theorem s2_applyTr_frame (o : TObj) (X : Array Tracker) (t : Tr) (time : F64) :
    applyTr { o with trackers := X } t time = ({ (applyTr o t time).1 with trackers := X }, (applyTr o t time).2) := by
  simp only [applyTr, s2_set_frame]

theorem s2_readStart_frame (o : TObj) (X : Array Tracker) (t : Tr) :
    readStart { o with trackers := X } t = readStart o t := by
  simp only [readStart, s2_get_frame]

theorem s2_rwB_frame (X : Array Tracker) (time : F64) (n k : Nat) (hk : k ∈ [0:n]) (s : TObj × Vector Tr n × Bool) :
    s2_rwB time n k hk ({ s.1 with trackers := X }, s.2) =
      s2_stepMap (fun s => ({ s.1 with trackers := X }, s.2)) (s2_rwB time n k hk s) := by
  unfold s2_rwB
  simp only [s2_applyTr_frame]
  split <;> (try split) <;> (try split) <;> rfl

theorem s2_cuB_frame (X : Array Tracker) (n i : Nat) (hi : i < n) (last : Nat) (at_ : F64) (j : Nat) (hj : j ∈ [last:i])
    (s : TObj × Vector Tr n) :
    s2_cuB n i hi last at_ j hj ({ s.1 with trackers := X }, s.2) =
      s2_stepMap (fun s => ({ s.1 with trackers := X }, s.2)) (s2_cuB n i hi last at_ j hj s) := by
  unfold s2_cuB
  simp only [s2_applyTr_frame]
  split <;> rfl
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Sim

theorem s2_forIn'_hom {S : Type} (φ : S → S) (lo hi : Nat) (f : (a : Nat) → a ∈ [lo:hi] → S → Id (ForInStep S))
    (hf : ∀ a h s, f a h (φ s) = s2_stepMap φ (f a h s)) (s : S) :
    forIn' (m := Id) [lo:hi] (φ s) f = φ (forIn' (m := Id) [lo:hi] s f) := by
  rw [s2_forIn'_range, s2_forIn'_range]
  apply s2_iterR_hom
  intro k s
  split
  · exact hf _ _ _
  · rfl

theorem s2_forIn_hom {S : Type} (φ : S → S) (lo hi : Nat) (f : Nat → S → Id (ForInStep S))
    (hf : ∀ a s, f a (φ s) = s2_stepMap φ (f a s)) (s : S) :
    forIn (m := Id) [lo:hi] (φ s) f = φ (forIn (m := Id) [lo:hi] s f) := by
  rw [forIn_range_iterR, forIn_range_iterR]
  exact s2_iterR_hom φ f hf _ _ _

theorem s2_mainB_frame (X : Array Tracker) (time : F64) (n k : Nat) (s : TObj × Vector Tr n × Nat × Nat) :
    s2_mainB time n k ({ s.1 with trackers := X }, s.2) =
      s2_stepMap (fun s => ({ s.1 with trackers := X }, s.2)) (s2_mainB time n k s) := by
  have hcu : ∀ i hi last at_ (o : TObj) (ts : Vector Tr n),
      forIn' (m := Id) [last:i] ({ o with trackers := X }, ts) (s2_cuB n i hi last at_) =
        ({ (forIn' (m := Id) [last:i] (o, ts) (s2_cuB n i hi last at_)).1 with trackers := X },
         (forIn' (m := Id) [last:i] (o, ts) (s2_cuB n i hi last at_)).2) := by
    intro i hi last at_ o ts
    exact s2_forIn'_hom (fun s : TObj × Vector Tr n => ({ s.1 with trackers := X }, s.2)) last i _
      (s2_cuB_frame X n i hi last at_) (o, ts)
  obtain ⟨o, ts, last, i⟩ := s
  unfold s2_mainB
  simp only [hcu, s2_applyTr_frame, s2_readStart_frame]
  by_cases hi : i < n
  · simp only [hi, _root_.dite_true]
    by_cases hst : time < ts[i].start
    · simp only [hst, if_true]; rfl
    · simp only [hst, if_false]
      generalize hF : forIn' (m := Id) [last:i] (o, ts) (s2_cuB n i hi last ts[i].start) = F
      obtain ⟨oF, tsF⟩ := F
      cases ha : ts[i].applied <;> cases hh : ts[i].hasStart <;>
        simp only [Bool.not_true, Bool.not_false, if_true, if_false, Bool.false_eq_true, ha, hh] <;>
        split_ifs <;> rfl
  · simp only [hi, _root_.dite_false]; rfl

theorem s2_TU_frame (X : Array Tracker) (o : TObj) (tk : Tracker) (time : F64) (rw : Bool) :
    s2_TU { o with trackers := X } tk time rw = ({ (s2_TU o tk time rw).1 with trackers := X }, (s2_TU o tk time rw).2) := by
  unfold s2_TU
  have hrw := s2_forIn'_hom (fun s : TObj × Vector Tr tk.ts.size × Bool => ({ s.1 with trackers := X }, s.2)) 0 tk.ts.size
    (s2_rwB time tk.ts.size) (s2_rwB_frame X time tk.ts.size)
  have hm := s2_forIn_hom (fun s : TObj × Vector Tr tk.ts.size × Nat × Nat => ({ s.1 with trackers := X }, s.2)) 0 tk.ts.size
    (s2_mainB time tk.ts.size) (s2_mainB_frame X time tk.ts.size)
  cases rw
  · simp only [Bool.false_eq_true, if_false]
    rw [show (({ o with trackers := X } : TObj), (⟨tk.ts, rfl⟩ : Vector Tr tk.ts.size), tk.lastApplied, tk.lastApplied) =
      (fun s : TObj × Vector Tr tk.ts.size × Nat × Nat => ({ s.1 with trackers := X }, s.2)) (o, ⟨tk.ts, rfl⟩, tk.lastApplied, tk.lastApplied) from rfl, hm]
  · simp only [if_true]
    rw [show (({ o with trackers := X } : TObj), (⟨tk.ts, rfl⟩ : Vector Tr tk.ts.size), false) =
      (fun s : TObj × Vector Tr tk.ts.size × Bool => ({ s.1 with trackers := X }, s.2)) (o, ⟨tk.ts, rfl⟩, false) from rfl, hrw]
    simp only
    rw [show (({ (forIn' (m := Id) [0:tk.ts.size] (o, (⟨tk.ts, rfl⟩ : Vector Tr tk.ts.size), false) (s2_rwB time tk.ts.size)).1 with trackers := X } : TObj),
        (forIn' (m := Id) [0:tk.ts.size] (o, (⟨tk.ts, rfl⟩ : Vector Tr tk.ts.size), false) (s2_rwB time tk.ts.size)).2.1, 0, 0) =
      (fun s : TObj × Vector Tr tk.ts.size × Nat × Nat => ({ s.1 with trackers := X }, s.2))
        ((forIn' (m := Id) [0:tk.ts.size] (o, (⟨tk.ts, rfl⟩ : Vector Tr tk.ts.size), false) (s2_rwB time tk.ts.size)).1,
         (forIn' (m := Id) [0:tk.ts.size] (o, (⟨tk.ts, rfl⟩ : Vector Tr tk.ts.size), false) (s2_rwB time tk.ts.size)).2.1, 0, 0) from rfl, hm]
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Sim

def s2_utStep (time : F64) (rw : Bool) (s : TObj × List Tracker) (tk : Tracker) : TObj × List Tracker :=
  (s2_TU s.1 tk time rw).1 |> fun o' => (o', s.2 ++ [(s2_TU s.1 tk time rw).2])

theorem s2_mapM_run (time : F64) (rw : Bool) :
    ∀ (l : List Tracker) (o : TObj) (acc : List Tracker),
      (fun (r : List Tracker × TObj) => (r.2, acc ++ r.1)) ((l.mapM (fun (tk : Tracker) => (do
        let (o', tk') := trackerUpdate (← get) tk time rw
        set o'
        return tk' : StateM TObj Tracker))).run o) = l.foldl (s2_utStep time rw) (o, acc) := by
  intro l
  induction l with
  | nil => intro o acc; simp only [List.mapM_nil, List.foldl_nil]; change (o, acc ++ []) = (o, acc); simp
  | cons tk l ih =>
    intro o acc
    simp only [List.mapM_cons, List.foldl_cons]
    rw [← ih]
    simp only [s2_utStep, ← s2_TU_eq, List.append_assoc, List.singleton_append]
    rfl

theorem s2_UT_eq (o : TObj) (time : F64) (force : Bool) :
    updateTransforms o time force =
      let rw := time < o.lastUpdate || force
      let r := o.trackers.toList.foldl (s2_utStep time rw) ({ o with lastUpdate := time }, [])
      { r.1 with trackers := r.2.toArray } := by
  unfold updateTransforms
  simp only
  rw [Array.mapM_eq_mapM_toList]
  have := s2_mapM_run time (time < o.lastUpdate || force) o.trackers.toList { o with lastUpdate := time } []
  simp only [List.nil_append] at this
  rw [← this]
  rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_clone_vec {T : Type} (inst : core.clone.Clone T) (h : ∀ x, inst.clone x = ok x) (v : alloc.vec.Vec T) :
    alloc.vec.CloneVec.clone inst v = ok v := by
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := inst.clone) (s := v.slice) (by intro x _; exact h x))
  rw [alloc.vec.CloneVec.clone, hs, ← hss]; simp

theorem s2_tr_clone (t : sim.transforms.Tr) : sim.transforms.Tr.Insts.CoreCloneClone.clone t = ok t := by
  rcases t with ⟨a, m, b, c, d, e, f, g, h, i, j⟩
  cases m <;> cases g <;>
    simp [sim.transforms.Tr.Insts.CoreCloneClone.clone, sim.transforms.Member.Insts.CoreCloneClone.clone,
      sim.basic.Vec2.Insts.CoreCloneClone.clone, float.F64.Insts.CoreCloneClone.clone,
      float.F32.Insts.CoreCloneClone.clone, core.option.Option.Insts.CoreCloneClone.clone, lift]

theorem s2_tracker_clone (t : sim.transforms.Tracker) :
    sim.transforms.Tracker.Insts.CoreCloneClone.clone t = ok t := by
  rcases t with ⟨m, ts, c, l⟩
  cases m <;> simp [sim.transforms.Tracker.Insts.CoreCloneClone.clone, sim.transforms.Member.Insts.CoreCloneClone.clone,
    s2_clone_vec sim.transforms.Tr.Insts.CoreCloneClone s2_tr_clone, lift]

theorem s2_absTk_size (tk : sim.transforms.Tracker) : (abs tk : OsuModel.Sim.Tracker).ts.size = tk.ts.val.length := by
  show (tk.ts.val.map abs).toArray.size = _; simp

theorem s2_absVec_inj {α β : Type} [AbsTo α β] (a b : alloc.vec.Vec α)
    (h : (abs a : Array β) = abs b) : a.val.map (abs : α → β) = b.val.map abs := by
  have : (a.val.map (abs : α → β)).toArray = (b.val.map abs).toArray := h
  simpa using this

theorem sim.transforms.update_transforms_refines (o : sim.transforms.TObj) (time : F64) (force : Bool)
    (h : ∀ tk ∈ o.trackers.val, tk.ts.val.length < Usize.max) :
    ∃ o', sim.transforms.update_transforms o time force = ok o' ∧
      OsuModel.Sim.updateTransforms (abs o) time force = abs o' := by
  have hmax := o.trackers.property
  rw [s2_UT_eq]
  simp only
  generalize hrw : (decide (time < (abs o : OsuModel.Sim.TObj).lastUpdate) || force) = rw
  have hrw' : (decide (time < o.last_update) || force) = rw := hrw
  generalize hL : (abs o : OsuModel.Sim.TObj).trackers.toList = L
  have hL' : o.trackers.val.map abs = L := by rw [← hL]; show _ = (o.trackers.val.map abs).toArray.toList; simp
  have hLlen : L.length = o.trackers.val.length := by rw [← hL']; simp
  have hb : ∀ j (hj : j < L.length), (L[j]).ts.size < Usize.max := by
    intro j hj
    have : L[j] = abs (o.trackers.val[j]'(by omega)) := by simp [← hL']
    rw [this, s2_absTk_size]; exact h _ (List.getElem_mem _)
  rw [foldl_iterR]
  obtain ⟨y, hl, hq⟩ := loop_iterR
    (fun (x : sim.basic.Vec2 × sim.basic.Vec2 × F32 × F32 × alloc.vec.Vec sim.transforms.Tracker × F64 × F64 × Usize) =>
      sim.transforms.update_transforms_loop.body time rw x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
        x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2)
    (fun j acc => .yield (s2_utStep time rw acc L[j]!)) L.length (fun x => x.2.2.2.2.2.2.2.val)
    (fun x s => (abs (⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1⟩ : sim.transforms.TObj)
        : OsuModel.Sim.TObj) = { s.1 with trackers := abs x.2.2.2.2.1 } ∧
      x.2.2.2.2.1.val.map abs = s.2 ++ L.drop x.2.2.2.2.2.2.2.val ∧ s.2.length = x.2.2.2.2.2.2.2.val)
    (fun y s => (abs (⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1, y.2.2.2.2.2.2⟩ : sim.transforms.TObj)
        : OsuModel.Sim.TObj) = { s.1 with trackers := s.2.toArray })
    (by
      rintro ⟨v, v1, f, f1, v2, t1, f2, k⟩ ⟨so, acc⟩ ⟨h1, h2, h3⟩ hk
      simp only at h1 h2 h3 hk ⊢
      have hlen : v2.val.length = L.length := by
        have := congrArg List.length h2; simp at this; omega
      have hk2 : k.val < v2.val.length := by omega
      have htk : (abs (v2.val[k.val]'hk2) : OsuModel.Sim.Tracker) = L[k.val] := by
        have := congrArg (fun l => l[k.val]?) h2
        simp [List.getElem?_append_right, h3] at this
        rw [List.getElem?_eq_getElem hk2, List.getElem?_eq_getElem (by omega)] at this
        simpa using this
      have hbt : (v2.val[k.val]'hk2).ts.val.length < Usize.max := by
        rw [← s2_absTk_size, htk]; exact hb _ (by omega)
      obtain ⟨⟨tk2, o'⟩, hr, er⟩ := sim.transforms.tracker_update_refines
        ⟨v, v1, f, f1, v2, t1, f2⟩ (v2.val[k.val]'hk2) time rw hbt
      rw [h1, htk, s2_TU_eq, s2_TU_frame] at er
      simp only [Prod.mk.injEq] at er
      obtain ⟨eo, et⟩ := er
      have htr : o'.trackers.val.map (abs : sim.transforms.Tracker → OsuModel.Sim.Tracker) = v2.val.map abs := by
        have := congrArg OsuModel.Sim.TObj.trackers eo
        exact (s2_absVec_inj (β := OsuModel.Sim.Tracker) v2 o'.trackers this).symm
      have hlen' : o'.trackers.val.length = L.length := by
        have := congrArg List.length htr; simp at this; omega
      obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
      refine ⟨fun s' hs' => ?_, fun s' hs' => by simp at hs'⟩
      simp only [ForInStep.yield.injEq] at hs'
      subst hs'
      have hLk : L[k.val]! = L[k.val]'(by omega) := getElem!_pos L k.val (by omega)
      refine ⟨(o'.pos, o'.scale, o'.rot, o'.alpha, alloc.vec.Vec.set o'.trackers k tk2, o'.last_update, o'.delay, k1),
        ?_, hk1v, ?_, ?_, ?_⟩
      · simp [sim.transforms.update_transforms_loop.body, vec_lt_len_iff, hk2, vec_index_eq v2 k hk2, s2_tracker_clone, hr,
          vec_index_mut_eq o'.trackers k (by omega), vec_index_mut_usize_ok o'.trackers k (by omega), hk1]
      · show ({ (abs o' : OsuModel.Sim.TObj) with trackers := abs (alloc.vec.Vec.set o'.trackers k tk2) } : OsuModel.Sim.TObj) = _
        rw [← eo]; simp only [s2_utStep, hLk]
      · rw [vec_set_val', List.map_set, htr, h2, ← et]
        simp only [s2_utStep, hLk]
        rw [List.set_append_right _ _ (by omega), h3, Nat.sub_self]
        rw [List.drop_eq_getElem_cons (show k.val < L.length by omega), List.set_cons_zero, hk1v]
        simp
      · simp [s2_utStep, h3, hk1v])
    (by
      rintro ⟨v, v1, f, f1, v2, t1, f2, k⟩ ⟨so, acc⟩ ⟨h1, h2, h3⟩ hk
      simp only at h1 h2 h3 hk ⊢
      refine ⟨(v, v1, f, f1, v2, t1, f2), ?_, ?_⟩
      · have : ¬ k.val < v2.val.length := by
          have := congrArg List.length h2; simp at this; omega
        simp [sim.transforms.update_transforms_loop.body, vec_lt_len_iff, this]
      · simp only
        rw [h1]
        have : v2.val.map abs = acc := by rw [h2, List.drop_eq_nil_of_le (by omega)]; simp
        show ({ so with trackers := (v2.val.map abs).toArray } : OsuModel.Sim.TObj) = _
        rw [this])
    (o.pos, o.scale, o.rot, o.alpha, o.trackers, time, o.delay, 0#usize)
    (({ (abs o : OsuModel.Sim.TObj) with lastUpdate := time }), [])
    ⟨rfl, by simp [hL'], rfl⟩ (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero] at hq
  rcases y with ⟨a, b, c, d, e, g, i⟩
  refine ⟨_, ?_, hq.symm⟩
  unfold sim.transforms.update_transforms sim.transforms.update_transforms_loop
  simp only [float.F64.lt, bind_ok]
  rw [show (if decide (time < o.last_update) = true then ok true else ok force) = ok rw by
    rw [← hrw']; cases decide (time < o.last_update) <;> simp]
  simp only [bind_ok]
  rw [hl]; simp only [bind_ok]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

/-- the Rust `add_transform` after the tracker lookup -/
def s2_atTailR (o2 : sim.transforms.TObj) (k : Usize) (t0 : sim.transforms.Tr) (now : F64) : Result sim.transforms.TObj := do
  let t ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      sim.transforms.Tracker) o2.trackers k
  let i ← t.counter + 1#u64
  let s := alloc.vec.Vec.deref t.ts
  let ins ← sim.transforms.insertion_point s { t0 with id := i }
  let ts ←
    sim.transforms.add_transform_loop o2.trackers k ins (alloc.vec.Vec.new
      sim.transforms.Tr) 0#usize
  let ts1 ← alloc.vec.Vec.push ts { t0 with id := i }
  let i1 ← t.counter + 1#u64
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      sim.transforms.Tracker) o2.trackers k
  let b ← float.F64.lt t0.start now
  if b
  then
    let v :=
      index_mut_back
        {
          member := t0.member,
          ts := ts1,
          counter := i1,
          last_applied := 0#usize
        }
    let b1 ← float.F64.le t0.start now
    sim.transforms.update_transforms { o2 with trackers := v } now b1
  else
    let b1 ← float.F64.le t0.end_t now
    if b1
    then
      let v :=
        index_mut_back
          {
            member := t0.member,
            ts := ts1,
            counter := i1,
            last_applied := 0#usize
          }
      let b2 ← float.F64.le t0.start now
      sim.transforms.update_transforms { o2 with trackers := v } now b2
    else
      let v :=
        index_mut_back
          {
            member := t0.member,
            ts := ts1,
            counter := i1,
            last_applied := 0#usize
          }
      ok { o2 with trackers := v }

theorem s2_at_eq (o : sim.transforms.TObj) (t0 : sim.transforms.Tr) (now : F64) :
    sim.transforms.add_transform o t0 now = (do
      let o1 ← sim.transforms.tracker_index o t0.member
      let (o2, k) ←
        match o1 with
        | none =>
          do
          let v ←
            alloc.vec.Vec.push o.trackers
              ({
                 member := t0.member,
                 ts := (alloc.vec.Vec.new sim.transforms.Tr),
                 counter := 0#u64,
                 last_applied := 0#usize
               } : sim.transforms.Tracker)
          let i := alloc.vec.Vec.len v
          let k1 ← i - 1#usize
          ok ({ o with trackers := v }, k1)
        | some k1 => ok (o, k1)
      s2_atTailR o2 k t0 now) := rfl

open OsuModel.Sim in
/-- the spec's new tracker of `addTransform` -/
def s2_tkNew (tk : Tracker) (t0 : Tr) : Tracker :=
  let t := { t0 with id := tk.counter + 1 }
  let ins := (tk.ts.findIdx? (trLess t ·)).getD tk.ts.size
  { tk with ts := (tk.ts.extract 0 ins).push t, counter := tk.counter + 1, lastApplied := 0 }

open OsuModel.Sim in
theorem s2_AT_eq (o : TObj) (t0 : Tr) (now : F64) :
    addTransform o t0 now =
      (let found := o.trackers.findFinIdx? (·.member == t0.member)
       let o' : TObj := { o with trackers := match found with
         | some k => o.trackers.set k (s2_tkNew o.trackers[k] t0) k.isLt
         | none => o.trackers.push (s2_tkNew { member := t0.member } t0) }
       if t0.start < now || t0.endT ≤ now then updateTransforms o' now (t0.start ≤ now) else o') := by
  unfold addTransform s2_tkNew
  cases o.trackers.findFinIdx? (·.member == t0.member) <;> rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_range'_take {X : Type} (d : X) (l : List X) (n : Nat) (h : n ≤ l.length) :
    (List.range' 0 n).map (fun j => l.getD j d) = l.take n := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < l.length by omega)]

theorem s2_at_copy (v : alloc.vec.Vec sim.transforms.Tracker) (k : Usize) (hk : k.val < v.val.length) (ins : Usize) (d : sim.transforms.Tr)
    (hins : ins.val ≤ (v.val[k.val]'hk).ts.val.length) :
    ∃ ts, sim.transforms.add_transform_loop v k ins (alloc.vec.Vec.new sim.transforms.Tr) 0#usize = ok ts ∧
      ts.val = (v.val[k.val]'hk).ts.val.take ins.val := by
  have hmx := (v.val[k.val]'hk).ts.property
  obtain ⟨r, hl, hr⟩ := loop_push_map (fun x => sim.transforms.add_transform_loop.body v k ins x.1 x.2) ins.val
    (fun j => (v.val[k.val]'hk).ts.val.getD j d)
    (by
      intro ts i hi hb
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
      have hj : i.val < (v.val[k.val]'hk).ts.val.length := by omega
      refine ⟨vpush ts ((v.val[k.val]'hk).ts.val[i.val]'hj) (by omega), i1, ?_, by simp [vpush_val, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj], hi1v⟩
      simp [sim.transforms.add_transform_loop.body, show i < ins by scalar_tac, vec_index_eq v k hk,
        vec_index_usize_ok _ i hj, vec_push_ok _ _ (show ts.val.length < Usize.max by omega), hi1])
    (by intro ts i hi; simp [sim.transforms.add_transform_loop.body, show ¬ i < ins by scalar_tac])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp; omega)
  refine ⟨r, by unfold sim.transforms.add_transform_loop; exact hl, ?_⟩
  rw [hr]; have := s2_range'_take d _ _ hins; simp at this ⊢; exact this
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_absTrackers_size (o : sim.transforms.TObj) : (abs o : OsuModel.Sim.TObj).trackers.size = o.trackers.val.length := by
  show (o.trackers.val.map abs).toArray.size = _; simp

theorem s2_absTrackers_get (o : sim.transforms.TObj) (k : Nat) (hk : k < (abs o : OsuModel.Sim.TObj).trackers.size) :
    (abs o : OsuModel.Sim.TObj).trackers[k] = abs (o.trackers.val[k]'(by rw [← s2_absTrackers_size]; exact hk)) := by
  show (o.trackers.val.map abs).toArray[k]'(by simpa [← s2_absTrackers_size] using hk) = _; simp

theorem s2_at_tail (o2 : sim.transforms.TObj) (k : Usize) (t0 : sim.transforms.Tr) (now : F64)
    (hk : k.val < o2.trackers.val.length) (hm : (o2.trackers.val[k.val]'hk).member = t0.member)
    (hc : (o2.trackers.val[k.val]'hk).counter.val < U64.max)
    (hB : ∀ tk ∈ o2.trackers.val, tk.ts.val.length + 1 < Usize.max) :
    ∃ o', s2_atTailR o2 k t0 now = ok o' ∧
      (let oS : OsuModel.Sim.TObj := { (abs o2 : OsuModel.Sim.TObj) with trackers := ((abs o2 : OsuModel.Sim.TObj).trackers.set k.val (s2_tkNew (abs (o2.trackers.val[k.val]'hk)) (abs t0)) (by rw [s2_absTrackers_size]; exact hk)) }
       if (abs t0 : OsuModel.Sim.Tr).start < now || (abs t0 : OsuModel.Sim.Tr).endT ≤ now then
         OsuModel.Sim.updateTransforms oS now ((abs t0 : OsuModel.Sim.Tr).start ≤ now) else oS) = abs o' := by
  generalize htk : o2.trackers.val[k.val]'hk = tk at hm hc
  have e1 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.transforms.Tracker) o2.trackers k = ok tk := by
    rw [← htk]; exact vec_index_eq _ _ hk
  have htkm : tk ∈ o2.trackers.val := by rw [← htk]; exact List.getElem_mem _
  have hlen := hB tk htkm
  obtain ⟨i, hi, hiv⟩ := eq_ok_of_spec (U64.add_spec (x := tk.counter) (y := 1#u64) (by simp; omega))
  obtain ⟨ins, hins, eins⟩ := sim.transforms.insertion_point_refines (alloc.vec.Vec.deref tk.ts) { t0 with id := i }
  have ets : (abs (alloc.vec.Vec.deref tk.ts) : Array OsuModel.Sim.Tr) = (abs tk : OsuModel.Sim.Tracker).ts := by
    show (List.map abs (alloc.vec.Vec.deref tk.ts).val).toArray = (tk.ts.val.map abs).toArray; simp [ms_deref_val]
  have et : (abs ({ t0 with id := i } : sim.transforms.Tr) : OsuModel.Sim.Tr) =
      { (abs t0 : OsuModel.Sim.Tr) with id := (abs tk : OsuModel.Sim.Tracker).counter + 1 } := by
    show _ = { (abs t0 : OsuModel.Sim.Tr) with id := tk.counter.val + 1 }
    have hiv' : i.val = tk.counter.val + 1 := by simpa using hiv
    rw [← hiv']; rfl
  rw [ets, et] at eins
  have hsz : (abs tk : OsuModel.Sim.Tracker).ts.size = tk.ts.val.length := s2_absTk_size tk
  have hinsle : ins.val ≤ tk.ts.val.length := by
    rw [← eins, ← hsz]
    cases hf : ((abs tk : OsuModel.Sim.Tracker).ts.findIdx? _) with
    | none => simp
    | some x => simp only [Option.getD_some]; exact Nat.le_of_lt (Array.findIdx?_eq_some_iff_getElem.mp hf).1
  obtain ⟨ts, hts, ets'⟩ := s2_at_copy o2.trackers k hk ins t0 (by rw [htk]; exact hinsle)
  rw [htk] at ets'
  have hpush := vec_push_ok ts ({ t0 with id := i } : sim.transforms.Tr) (by rw [ets']; simp; omega)
  have e2 := vec_index_mut_eq o2.trackers k hk
  have hpl : ts.val.length < Usize.max := by rw [ets']; simp; omega
  let tkR : sim.transforms.Tracker := ⟨t0.member, vpush ts { t0 with id := i } hpl, i, 0#usize⟩
  have hiv' : i.val = tk.counter.val + 1 := by simpa using hiv
  have etkR : (abs tkR : OsuModel.Sim.Tracker) = s2_tkNew (abs tk) (abs t0) := by
    unfold s2_tkNew
    simp only [eins]
    show ({ member := memberS t0.member, ts := ((vpush ts _ hpl).val.map abs).toArray, counter := i.val, lastApplied := 0 } : OsuModel.Sim.Tracker) = _
    rw [vpush_val, ets', hiv']
    show _ = ({ member := memberS tk.member, ts := ((tk.ts.val.map abs).toArray.extract 0 ins.val).push _, counter := tk.counter.val + 1, lastApplied := 0 } : OsuModel.Sim.Tracker)
    rw [hm]
    congr 1
    rw [List.map_append, List.map_take]; simp only [List.map_cons, List.map_nil, et]
    simp
  have eoS : (abs ({ o2 with trackers := alloc.vec.Vec.set o2.trackers k tkR } : sim.transforms.TObj) : OsuModel.Sim.TObj) =
      { (abs o2 : OsuModel.Sim.TObj) with trackers := ((abs o2 : OsuModel.Sim.TObj).trackers.set k.val
        (s2_tkNew (abs tk) (abs t0)) (by rw [s2_absTrackers_size]; exact hk)) } := by
    show ({ (abs o2 : OsuModel.Sim.TObj) with trackers := ((alloc.vec.Vec.set o2.trackers k tkR).val.map abs).toArray } : OsuModel.Sim.TObj) = _
    rw [vec_set_val', List.map_set, etkR]
    congr 1
  have hb' : ∀ x ∈ (alloc.vec.Vec.set o2.trackers k tkR).val, x.ts.val.length < Usize.max := by
    intro x hx
    rw [vec_set_val'] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · have := hB x hx; omega
    · subst hx; simp [tkR, vpush_val, ets']; omega
  have hrust : s2_atTailR o2 k t0 now = (if t0.start < now || t0.end_t ≤ now then
      sim.transforms.update_transforms { o2 with trackers := alloc.vec.Vec.set o2.trackers k tkR } now (decide (t0.start ≤ now))
      else ok { o2 with trackers := alloc.vec.Vec.set o2.trackers k tkR }) := by
    simp only [s2_atTailR, e1, hi, hins, hts, hpush, e2, float.F64.lt, float.F64.le, bind_ok]
    by_cases h1 : t0.start < now <;> by_cases h2 : t0.end_t ≤ now <;> simp [h1, h2, tkR]
  rw [hrust]
  have ea : (abs t0 : OsuModel.Sim.Tr).start = t0.start ∧ (abs t0 : OsuModel.Sim.Tr).endT = t0.end_t := ⟨rfl, rfl⟩
  simp only [ea]
  rw [← eoS]
  by_cases hc2 : (decide (t0.start < now) || decide (t0.end_t ≤ now)) = true
  · obtain ⟨o', ho', eo'⟩ := sim.transforms.update_transforms_refines
      { o2 with trackers := alloc.vec.Vec.set o2.trackers k tkR } now (decide (t0.start ≤ now)) hb'
    refine ⟨o', ?_, ?_⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hc2; simp [hc2, ho']
    · simp only [hc2, if_true]; exact eo'
  · refine ⟨{ o2 with trackers := alloc.vec.Vec.set o2.trackers k tkR }, ?_, ?_⟩
    · simp only [Bool.not_eq_true] at hc2; simp only [hc2]; rfl
    · simp only [Bool.not_eq_true] at hc2; simp only [hc2]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_memberS_inj (a b : sim.transforms.Member) (h : memberS a = memberS b) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [memberS] at h)

theorem sim.transforms.add_transform_refines (o : sim.transforms.TObj) (t0 : sim.transforms.Tr) (now : F64)
    (hT : o.trackers.val.length < Usize.max)
    (hC : ∀ tk ∈ o.trackers.val, tk.counter.val < U64.max ∧ tk.ts.val.length + 1 < Usize.max) :
    ∃ o', sim.transforms.add_transform o t0 now = ok o' ∧
      OsuModel.Sim.addTransform (abs o) (abs t0) now = abs o' := by
  rw [s2_at_eq, s2_AT_eq]
  obtain ⟨r, hr, er⟩ := sim.transforms.tracker_index_refines o t0.member
  have hfi : ((abs o : OsuModel.Sim.TObj).trackers.findFinIdx? (·.member == (abs t0 : OsuModel.Sim.Tr).member)).map (·.val) =
      r.map (·.val) := by
    rw [← Array.findIdx?_eq_map_findFinIdx?_val, er]
    show ((o.trackers.val.map abs).toArray.findIdx? _) = _
    rw [List.findIdx?_toArray, List.findIdx?_map]; rfl
  cases hf : (abs o : OsuModel.Sim.TObj).trackers.findFinIdx? (·.member == (abs t0 : OsuModel.Sim.Tr).member) with
  | none =>
    rw [hf] at hfi
    cases r with
    | some _ => simp at hfi
    | none =>
    let newTk : sim.transforms.Tracker := ⟨t0.member, alloc.vec.Vec.new sim.transforms.Tr, 0#u64, 0#usize⟩
    have hpush := vec_push_ok o.trackers newTk hT
    obtain ⟨k1, hk1, hk1v⟩ : ∃ z, alloc.vec.Vec.len (vpush o.trackers newTk hT) - 1#usize = ok z ∧ z.val = o.trackers.val.length := by
      have := Usize.sub_spec (x := alloc.vec.Vec.len (vpush o.trackers newTk hT)) (y := 1#usize) (by simp [vpush_val])
      obtain ⟨z, hz, hv⟩ := eq_ok_of_spec this; exact ⟨z, hz, by simp [vpush_val] at hv; omega⟩
    let o2 : sim.transforms.TObj := { o with trackers := vpush o.trackers newTk hT }
    have hk : k1.val < o2.trackers.val.length := by simp [o2, vpush_val, hk1v]
    have hget : o2.trackers.val[k1.val]'hk = newTk := by simp [o2, vpush_val, hk1v]
    have hB : ∀ tk ∈ o2.trackers.val, tk.ts.val.length + 1 < Usize.max := by
      intro tk h
      simp only [o2, vpush_val, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact (hC tk h).2
      · subst h; simp [newTk]; scalar_tac
    obtain ⟨o', ho', eo'⟩ := s2_at_tail o2 k1 t0 now hk (by rw [hget]) (by rw [hget]; simp [newTk]; scalar_tac) hB
    have hpush' : alloc.vec.Vec.push o.trackers (⟨t0.member, alloc.vec.Vec.new sim.transforms.Tr, 0#u64, 0#usize⟩ : sim.transforms.Tracker) = ok (vpush o.trackers newTk hT) := hpush
    refine ⟨o', ?_, ?_⟩
    · simp only [hr, bind_ok]
      rw [hpush']; simp only [bind_ok]; rw [hk1]; simp only [bind_ok]; exact ho'
    have hA : ∀ hh, (abs o2 : OsuModel.Sim.TObj).trackers.set k1.val (s2_tkNew (abs (o2.trackers.val[k1.val]'hk)) (abs t0)) hh =
        (abs o : OsuModel.Sim.TObj).trackers.push (s2_tkNew { member := (abs t0 : OsuModel.Sim.Tr).member } (abs t0)) := by
      intro hh
      simp only [hget]
      show ((vpush o.trackers newTk hT).val.map abs).toArray.set k1.val _ hh = (o.trackers.val.map abs).toArray.push _
      apply Array.toList_inj.mp
      simp only [Array.toList_set, List.toList_toArray, Array.toList_push, vpush_val, List.map_append, List.map_cons,
        List.map_nil, hk1v]
      rw [List.set_append_right _ _ (by simp)]
      simp
      rfl
    rw [← eo']
    simp only []
    congr 2
    all_goals first | exact (hA _).symm | (congr 1; exact (hA _).symm)
  | some kk =>
    rw [hf] at hfi
    cases r with
    | none => simp at hfi
    | some k =>
    simp only [Option.map_some, Option.some.injEq] at hfi
    obtain ⟨kv, hkv⟩ := kk
    simp only at hfi
    subst hfi
    have hk : k.val < o.trackers.val.length := by rw [← s2_absTrackers_size]; exact hkv
    have hp := (Array.findFinIdx?_eq_some_iff.mp hf).1
    simp only [Fin.getElem_fin] at hp
    rw [s2_absTrackers_get o k.val hkv] at hp
    have hm : (o.trackers.val[k.val]'hk).member = t0.member := by
      apply s2_memberS_inj
      have : (memberS (o.trackers.val[k.val]'hk).member == memberS t0.member) = true := hp
      revert this
      cases (o.trackers.val[k.val]'hk).member <;> cases t0.member <;> decide
    have hmem : o.trackers.val[k.val]'hk ∈ o.trackers.val := List.getElem_mem _
    obtain ⟨o', ho', eo'⟩ := s2_at_tail o k t0 now hk hm (hC _ hmem).1 (fun tk h => (hC tk h).2)
    refine ⟨o', by simp [hr, ho'], ?_⟩
    rw [← eo']
    simp only [Fin.getElem_fin, s2_absTrackers_get o k.val hkv]
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem s2_dbl_min : sim.transforms.DBL_MIN_VALUE = ok OsuModel.Sim.dblMinValue := by
  unfold sim.transforms.DBL_MIN_VALUE OsuModel.Sim.dblMinValue
  simp only [float.F64.from_bits]; rfl

theorem s2_basic_f32_0 : sim.basic.F32_0 = ok (0 : F32) := by
  have := s2_tr_consts.1
  simp only [sim.transforms.F32_0] at this
  simpa [sim.basic.F32_0] using this

theorem sim.transforms.clear_state_refines (o : sim.transforms.TObj)
    (h : ∀ tk ∈ o.trackers.val, tk.ts.val.length < Usize.max) :
    ∃ o', sim.transforms.clear_state o = ok o' ∧ OsuModel.Sim.clearState (abs o) = abs o' := by
  obtain ⟨o1, h1, e1⟩ := sim.transforms.update_transforms_refines o OsuModel.Sim.dblMinValue false h
  obtain ⟨o2, h2, e2⟩ := sim.transforms.clear_transforms_after_refines o1 OsuModel.Sim.dblMinValue
  exact ⟨o2, by simp [sim.transforms.clear_state, s2_dbl_min, h1, h2], by simp only [OsuModel.Sim.clearState, e1, e2]⟩

theorem sim.transforms.transform_to_refines (o : sim.transforms.TObj) (now : F64) (m : sim.transforms.Member)
    (v : sim.basic.Vec2) (dur : F64) (e : net.framework.Easing) (off : Option sim.basic.Vec2)
    (hT : o.trackers.val.length < Usize.max)
    (hC : ∀ tk ∈ o.trackers.val, tk.counter.val < U64.max ∧ tk.ts.val.length + 1 < Usize.max) :
    ∃ sq o', sim.transforms.transform_to o now m v dur e off = ok (sq, o') ∧
      OsuModel.Sim.transformTo (abs o) now (abs m) (abs v) dur (abs e) (off.map abs) = (abs o', abs sq) := by
  obtain ⟨o', ho', eo'⟩ := sim.transforms.add_transform_refines o
    ⟨0#u64, m, now + o.delay, now + o.delay + dur, ⟨0, 0⟩, v, e, off, false, false, false⟩ now hT hC
  refine ⟨⟨now + o.delay, now + o.delay + dur, true⟩, o', ?_, ?_⟩
  · simp [sim.transforms.transform_to, sim.transforms.start_time, float.F64.add, sim.basic.VEC2_ZERO, s2_basic_f32_0, ho']
  · show (OsuModel.Sim.addTransform (abs o) (abs (⟨0#u64, m, now + o.delay, now + o.delay + dur, ⟨0, 0⟩, v, e, off, false, false, false⟩ : sim.transforms.Tr)) now, _) = _
    rw [eo']; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

theorem sim.transforms.seq_append_refines (s : sim.transforms.Seq) (o : sim.transforms.TObj) (now : F64)
    (m : sim.transforms.Member) (v : sim.basic.Vec2) (dur : F64) (e : net.framework.Easing) (off : Option sim.basic.Vec2)
    (hT : o.trackers.val.length < Usize.max)
    (hC : ∀ tk ∈ o.trackers.val, tk.counter.val < U64.max ∧ tk.ts.val.length + 1 < Usize.max) :
    ∃ sq o', sim.transforms.seq_append s o now m v dur e off = ok (sq, o') ∧
      OsuModel.Sim.Seq.append (abs s) (abs o) now (abs m) (abs v) dur (abs e) (off.map abs) = (abs o', abs sq) := by
  obtain ⟨sq, o2, h2, e2⟩ := sim.transforms.transform_to_refines { o with delay := s.current_time - now } now m v dur e off hT hC
  have hseq : OsuModel.Sim.absSeq (abs o) now (abs s : OsuModel.Sim.Seq).currentTime =
      abs ({ o with delay := s.current_time - now } : sim.transforms.TObj) := rfl
  unfold OsuModel.Sim.Seq.append
  rw [hseq, e2]
  have hc : sq.last_end_time = (abs sq : OsuModel.Sim.Seq).lastEndTime := rfl
  cases hl : s.has_last with
  | false =>
    refine ⟨{ s with last_end_time := sq.last_end_time, has_last := true }, { o2 with delay := o.delay }, ?_, ?_⟩
    · simp [sim.transforms.seq_append, sim.transforms.abs_seq, float.F64.sub, h2, hl]
    · simp only [show (abs s : OsuModel.Sim.Seq).hasLast = s.has_last from rfl, hl]; rfl
  | true =>
    by_cases hlt : s.last_end_time < sq.last_end_time
    · refine ⟨{ s with last_end_time := sq.last_end_time }, { o2 with delay := o.delay }, ?_, ?_⟩
      · simp [sim.transforms.seq_append, sim.transforms.abs_seq, float.F64.sub, float.F64.lt, h2, hl, hlt]
      · simp only [show (abs s : OsuModel.Sim.Seq).hasLast = s.has_last from rfl, hl,
          show (abs s : OsuModel.Sim.Seq).lastEndTime = s.last_end_time from rfl, ← hc, hlt]
        simp; exact ⟨rfl, rfl⟩
    · refine ⟨s, { o2 with delay := o.delay }, ?_, ?_⟩
      · simp [sim.transforms.seq_append, sim.transforms.abs_seq, float.F64.sub, float.F64.lt, h2, hl, hlt]
      · simp only [show (abs s : OsuModel.Sim.Seq).hasLast = s.has_last from rfl, hl,
          show (abs s : OsuModel.Sim.Seq).lastEndTime = s.last_end_time from rfl, ← hc, hlt]
        simp; exact ⟨rfl, by show _ = (⟨s.current_time, s.last_end_time, s.has_last⟩ : OsuModel.Sim.Seq); rw [hl]; rfl⟩
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Sim

/-- the transform engine's size budget: `b` more `addTransform`s cannot overflow the Rust `u64` counters or the
`usize` lengths (stated on the spec value; `s2_tfOk b o := s2_tfOkS b (abs o)`) -/
def s2_tfOkS (b : Nat) (a : TObj) : Prop :=
  a.trackers.size + b + 1 < Usize.max ∧ ∀ tk ∈ a.trackers, tk.counter + b < U64.max ∧ tk.ts.size + b + 1 < Usize.max

def s2_shp (tk : Tracker) : Nat × Nat := (tk.counter, tk.ts.size)

theorem s2_tfOkS_shp (b : Nat) (a a' : TObj) (h : a'.trackers.toList.map s2_shp = a.trackers.toList.map s2_shp)
    (ha : s2_tfOkS b a) : s2_tfOkS b a' := by
  obtain ⟨h1, h2⟩ := ha
  have hs : a'.trackers.size = a.trackers.size := by
    have := congrArg List.length h; simpa using this
  refine ⟨by omega, ?_⟩
  intro tk htk
  have : s2_shp tk ∈ a.trackers.toList.map s2_shp := by rw [← h]; exact List.mem_map_of_mem (Array.mem_toList_iff.mpr htk)
  obtain ⟨tk0, hm, he⟩ := List.mem_map.mp this
  have := h2 tk0 (Array.mem_toList_iff.mp hm)
  simp only [s2_shp, Prod.mk.injEq] at he
  omega

theorem s2_TU_shp (o : TObj) (tk : Tracker) (time : F64) (rw : Bool) : s2_shp (s2_TU o tk time rw).2 = s2_shp tk := by
  unfold s2_TU s2_shp; simp

theorem s2_ut_fold_shp (time : F64) (rw : Bool) :
    ∀ (l : List Tracker) (o : TObj) (acc : List Tracker),
      ((l.foldl (s2_utStep time rw) (o, acc)).2).map s2_shp = acc.map s2_shp ++ l.map s2_shp := by
  intro l
  induction l with
  | nil => intro o acc; simp
  | cons tk l ih =>
    intro o acc
    simp only [List.foldl_cons]
    rw [show s2_utStep time rw (o, acc) tk = ((s2_TU o tk time rw).1, acc ++ [(s2_TU o tk time rw).2]) from rfl, ih]
    simp [s2_TU_shp]

theorem s2_UT_shp (a : TObj) (time : F64) (f : Bool) :
    (updateTransforms a time f).trackers.toList.map s2_shp = a.trackers.toList.map s2_shp := by
  rw [s2_UT_eq]; simp only
  rw [s2_ut_fold_shp]; simp

theorem s2_tfOkS_UT (b : Nat) (a : TObj) (time : F64) (f : Bool) (h : s2_tfOkS b a) :
    s2_tfOkS b (updateTransforms a time f) := s2_tfOkS_shp b a _ (s2_UT_shp a time f) h

theorem s2_tfOkS_CTA (b : Nat) (a : TObj) (time : F64) (h : s2_tfOkS b a) :
    s2_tfOkS b (clearTransformsAfter a time) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa [clearTransformsAfter] using h1, ?_⟩
  intro tk htk
  simp only [clearTransformsAfter, Array.mem_map] at htk
  obtain ⟨tk0, hm, rfl⟩ := htk
  have := h2 tk0 hm
  have := Array.size_filter_le (p := fun t => decide (t.start < time)) (xs := tk0.ts)
  simp only; omega

theorem s2_tfOkS_clear (b : Nat) (a : TObj) (h : s2_tfOkS b a) : s2_tfOkS b (clearState a) :=
  s2_tfOkS_CTA b _ _ (s2_tfOkS_UT b a _ _ h)
end OsuProofs

namespace OsuProofs
open OsuModel.Net OsuModel.Sim

theorem s2_usize_le_u64 : Usize.max ≤ U64.max := by
  rw [Usize.max_def, Usize.numBits_def, UScalarTy.Usize_numBits_eq]
  have : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)
  rw [this]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem s2_tkNew_size (tk : Tracker) (t0 : Tr) : (s2_tkNew tk t0).ts.size ≤ tk.ts.size + 1 ∧
    (s2_tkNew tk t0).counter = tk.counter + 1 := by
  unfold s2_tkNew
  refine ⟨?_, rfl⟩
  simp only [Array.size_push, Array.size_extract]
  omega

theorem s2_tfOkS_AT (b : Nat) (a : TObj) (t0 : Tr) (now : F64) (h : s2_tfOkS (b + 1) a) :
    s2_tfOkS b (addTransform a t0 now) := by
  rw [s2_AT_eq]
  obtain ⟨h1, h2⟩ := h
  have hU := s2_usize_le_u64
  have hmid : s2_tfOkS b { a with trackers := match a.trackers.findFinIdx? (·.member == t0.member) with
      | some k => a.trackers.set k (s2_tkNew a.trackers[k] t0) k.isLt
      | none => a.trackers.push (s2_tkNew { member := t0.member } t0) } := by
    cases a.trackers.findFinIdx? (·.member == t0.member) with
    | some k =>
      refine ⟨by simp; omega, ?_⟩
      intro tk htk
      simp only at htk
      rcases Array.mem_or_eq_of_mem_set htk with htk | htk
      · have := h2 tk htk; omega
      · subst htk
        have := h2 _ (Array.getElem_mem k.isLt)
        have := s2_tkNew_size a.trackers[k] t0
        simp only [Fin.getElem_fin] at *
        omega
    | none =>
      refine ⟨by simp; omega, ?_⟩
      intro tk htk
      simp only [Array.mem_push] at htk
      rcases htk with htk | htk
      · have := h2 tk htk; omega
      · subst htk
        have := s2_tkNew_size { member := t0.member } t0
        simp at this
        omega
  simp only
  split
  · exact s2_tfOkS_UT b _ _ _ hmid
  · exact hmid
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

/-- the engine's size budget on the Rust value (see `s2_tfOkS`) -/
def s2_tfOk (b : Nat) (o : sim.transforms.TObj) : Prop := s2_tfOkS b (abs o)

theorem s2_tfOk_hyps (b : Nat) (o : sim.transforms.TObj) (h : s2_tfOk (b + 1) o) :
    o.trackers.val.length < Usize.max ∧
      ∀ tk ∈ o.trackers.val, tk.counter.val < U64.max ∧ tk.ts.val.length + 1 < Usize.max := by
  obtain ⟨h1, h2⟩ := h
  rw [s2_absTrackers_size] at h1
  refine ⟨by omega, fun tk htk => ?_⟩
  have hm : (abs tk : OsuModel.Sim.Tracker) ∈ (abs o : OsuModel.Sim.TObj).trackers := by
    show abs tk ∈ (o.trackers.val.map abs).toArray
    simp only [List.mem_toArray, List.mem_map]; exact ⟨tk, htk, rfl⟩
  have := h2 _ hm
  rw [s2_absTk_size] at this
  have hc : (abs tk : OsuModel.Sim.Tracker).counter = tk.counter.val := rfl
  omega

theorem s2_tfOk_ts (b : Nat) (o : sim.transforms.TObj) (h : s2_tfOk b o) :
    ∀ tk ∈ o.trackers.val, tk.ts.val.length < Usize.max := by
  obtain ⟨h1, h2⟩ := h
  intro tk htk
  have hm : (abs tk : OsuModel.Sim.Tracker) ∈ (abs o : OsuModel.Sim.TObj).trackers := by
    show abs tk ∈ (o.trackers.val.map abs).toArray
    simp only [List.mem_toArray, List.mem_map]; exact ⟨tk, htk, rfl⟩
  have := h2 _ hm
  rw [s2_absTk_size] at this
  omega

theorem s2_tfOkS_trackers (b : Nat) (a a' : OsuModel.Sim.TObj) (h : a'.trackers = a.trackers) (ha : s2_tfOkS b a) :
    s2_tfOkS b a' := by
  unfold s2_tfOkS; rw [h]; exact ha

theorem s2_tfOk_delay (b : Nat) (o : sim.transforms.TObj) (d : F64) (h : s2_tfOk b o) :
    s2_tfOk b { o with delay := d } := h

/-- `clear_state` (budget kept) -/
theorem s2_eng_clear (b : Nat) (o : sim.transforms.TObj) (h : s2_tfOk b o) :
    ∃ o', sim.transforms.clear_state o = ok o' ∧ OsuModel.Sim.clearState (abs o) = abs o' ∧ s2_tfOk b o' := by
  obtain ⟨o', h1, e1⟩ := sim.transforms.clear_state_refines o (s2_tfOk_ts b o h)
  exact ⟨o', h1, e1, by unfold s2_tfOk; rw [← e1]; exact s2_tfOkS_clear b _ h⟩

/-- `transform_to` (one `add_transform`: budget `b + 1 → b`) -/
theorem s2_eng_tto (b : Nat) (o : sim.transforms.TObj) (now : F64) (m : sim.transforms.Member) (v : sim.basic.Vec2)
    (dur : F64) (e : net.framework.Easing) (off : Option sim.basic.Vec2) (h : s2_tfOk (b + 1) o) :
    ∃ sq o', sim.transforms.transform_to o now m v dur e off = ok (sq, o') ∧
      OsuModel.Sim.transformTo (abs o) now (abs m) (abs v) dur (abs e) (off.map abs) = (abs o', abs sq) ∧ s2_tfOk b o' := by
  obtain ⟨hT, hC⟩ := s2_tfOk_hyps b o h
  obtain ⟨sq, o', h1, e1⟩ := sim.transforms.transform_to_refines o now m v dur e off hT hC
  refine ⟨sq, o', h1, e1, ?_⟩
  have hx : (abs o' : OsuModel.Sim.TObj) = (OsuModel.Sim.transformTo (abs o) now (abs m) (abs v) dur (abs e) (off.map abs)).1 := by
    rw [e1]
  unfold s2_tfOk; rw [hx]
  exact s2_tfOkS_AT b _ _ _ h

/-- `Seq.append` (one `add_transform`: budget `b + 1 → b`) -/
theorem s2_eng_app (b : Nat) (s : sim.transforms.Seq) (o : sim.transforms.TObj) (now : F64) (m : sim.transforms.Member)
    (v : sim.basic.Vec2) (dur : F64) (e : net.framework.Easing) (off : Option sim.basic.Vec2) (h : s2_tfOk (b + 1) o) :
    ∃ sq o', sim.transforms.seq_append s o now m v dur e off = ok (sq, o') ∧
      OsuModel.Sim.Seq.append (abs s) (abs o) now (abs m) (abs v) dur (abs e) (off.map abs) = (abs o', abs sq) ∧
      s2_tfOk b o' := by
  obtain ⟨hT, hC⟩ := s2_tfOk_hyps b o h
  obtain ⟨sq, o', h1, e1⟩ := sim.transforms.seq_append_refines s o now m v dur e off hT hC
  refine ⟨sq, o', h1, e1, ?_⟩
  have hx : (abs o' : OsuModel.Sim.TObj) = (OsuModel.Sim.Seq.append (abs s) (abs o) now (abs m) (abs v) dur (abs e) (off.map abs)).1 := by
    rw [e1]
  unfold s2_tfOk; rw [hx]
  unfold OsuModel.Sim.Seq.append OsuModel.Sim.transformTo
  apply s2_tfOkS_trackers b _ _ rfl
  exact s2_tfOkS_AT b _ _ _ h

/-- `fade_in_from_zero` (two `add_transform`s: budget `b + 2 → b`) -/
theorem s2_eng_fade (b : Nat) (o : sim.transforms.TObj) (now dur : F64) (e : net.framework.Easing) (h : s2_tfOk (b + 2) o) :
    ∃ o', sim.transforms.fade_in_from_zero o now dur e = ok o' ∧
      OsuModel.Sim.fadeInFromZero (abs o) now dur (abs e) = abs o' ∧ s2_tfOk b o' := by
  obtain ⟨sq, o1, h1, e1, p1⟩ := s2_eng_tto (b + 1) o now .Alpha ⟨0, 0⟩ 0 .None none h
  obtain ⟨sq2, o2, h2, e2, p2⟩ := s2_eng_app b sq o1 now .Alpha ⟨1, 0⟩ dur e none p1
  refine ⟨o2, ?_, ?_, p2⟩
  · simp [sim.transforms.fade_in_from_zero, s2_tr_consts, sim.transforms.vs, h1, h2]
  · unfold OsuModel.Sim.fadeInFromZero
    have ev0 : OsuModel.Sim.vs 0 = (abs (⟨0, 0⟩ : sim.basic.Vec2) : OsuModel.Sim.Vec2) := rfl
    have ev1 : OsuModel.Sim.vs 1 = (abs (⟨1, 0⟩ : sim.basic.Vec2) : OsuModel.Sim.Vec2) := rfl
    have em : OsuModel.Sim.Member.alpha = abs sim.transforms.Member.Alpha := rfl
    have ee : OsuModel.Net.Framework.Easing.none = abs net.framework.Easing.None := rfl
    have eo : (none : Option OsuModel.Sim.Vec2) = (none : Option sim.basic.Vec2).map abs := rfl
    rw [ev0, em, ee, eo, e1]
    dsimp only
    rw [ev1, e2]
end OsuProofs

namespace OsuProofs
open OsuImpl
open OsuModel.Net

/-- `tracker_rewind` refines the spec's rewind pass of `trackerUpdate` (`s2_rwB` loop). -/
theorem sim.transforms.tracker_rewind_refines (o : sim.transforms.TObj) (ts : alloc.vec.Vec sim.transforms.Tr) (time : F64)
    (N : Nat) (tsV : Vector OsuModel.Sim.Tr N) (hN : ts.val.length = N) (hV : tsV.toList = ts.val.map abs) :
    ∃ o' ts', sim.transforms.tracker_rewind o ts time = ok (o', ts') ∧
      abs o' = (forIn' (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, false) (s2_rwB time N)).1 ∧
      ts'.val.map abs = (forIn' (m := Id) [0:N] ((abs o : OsuModel.Sim.TObj), tsV, false) (s2_rwB time N)).2.1.toList :=
  s2_tracker_rewind o ts time N tsV hN hV

/-- `tracker_catch_up` refines the spec's catch-up loop of `trackerUpdate` (`s2_cuB` loop). -/
theorem sim.transforms.tracker_catch_up_refines (o : sim.transforms.TObj) (ts : alloc.vec.Vec sim.transforms.Tr)
    (last i : Usize) (at_ : F64) (N : Nat) (tsV : Vector OsuModel.Sim.Tr N) (hN : ts.val.length = N)
    (hV : tsV.toList = ts.val.map abs) (hi : i.val < N) :
    ∃ o' ts', sim.transforms.tracker_catch_up o ts last i at_ = ok (o', ts') ∧
      abs o' = (forIn' (m := Id) [last.val:i.val] ((abs o : OsuModel.Sim.TObj), tsV) (s2_cuB N i.val hi last.val at_)).1 ∧
      ts'.val.map abs = (forIn' (m := Id) [last.val:i.val] ((abs o : OsuModel.Sim.TObj), tsV) (s2_cuB N i.val hi last.val at_)).2.toList ∧
      ts'.val.length = N :=
  s2_catch_up o ts last i at_ N tsV hN hV hi

/-- `fade_in_from_zero` (two `add_transform`s; size budget 2). -/
theorem sim.transforms.fade_in_from_zero_refines (o : sim.transforms.TObj) (now dur : F64) (e : net.framework.Easing)
    (h : s2_tfOk 2 o) :
    ∃ o', sim.transforms.fade_in_from_zero o now dur e = ok o' ∧
      OsuModel.Sim.fadeInFromZero (abs o) now dur (abs e) = abs o' := by
  obtain ⟨o', h1, e1, _⟩ := s2_eng_fade 0 o now dur e h
  exact ⟨o', h1, e1⟩
end OsuProofs
