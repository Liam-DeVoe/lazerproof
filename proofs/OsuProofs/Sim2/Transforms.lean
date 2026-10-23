/-
`sim::transforms` (Rust) refines `OsuModel.Sim` Transforms (osu-framework transform engine). Uses the sim agent's
AbsTo maps for `Member`/`Tr`/`Tracker`/`TObj` (Sim/AbsState.lean); `Seq` ↦ `s2_seqS`.
-/
import OsuProofs.Sim2.Mods
import OsuProofs.Sim.AbsState
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

@[simp] theorem s2_tr_consts : sim.transforms.F32_0 = ok (0 : F32) ∧ sim.transforms.F32_1 = ok (1 : F32) ∧
    sim.transforms.F64_0 = ok (0 : F64) := by
  simp [sim.transforms.F32_0, sim.transforms.F32_1, sim.transforms.F64_0]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem sim.transforms.member_is_scalar_refines (m : sim.transforms.Member) :
    sim.transforms.member_is_scalar m = ok (OsuModel.Sim.Member.isScalar (abs m)) := by
  cases m <;> rfl

theorem sim.transforms.tobj_new_refines (a : F32) :
    ∃ r, sim.transforms.tobj_new a = ok r ∧ ({ alpha := a } : OsuModel.Sim.TObj) = abs r := by
  refine ⟨⟨⟨0, 0⟩, ⟨1, 1⟩, 0, a, alloc.vec.Vec.new _, 0, 0⟩, by simp [sim.transforms.tobj_new], ?_⟩
  rfl

theorem sim.transforms.tobj_get_refines (o : sim.transforms.TObj) (m : sim.transforms.Member) :
    ∃ r, sim.transforms.tobj_get o m = ok r ∧ OsuModel.Sim.TObj.get (abs o) (abs m) = abs r := by
  cases m <;> simp [sim.transforms.tobj_get, OsuModel.Sim.TObj.get, abs, memberS]

theorem sim.transforms.tobj_set_refines (o : sim.transforms.TObj) (m : sim.transforms.Member) (v : sim.basic.Vec2) :
    ∃ r, sim.transforms.tobj_set o m v = ok r ∧ OsuModel.Sim.TObj.set (abs o) (abs m) (abs v) = abs r := by
  cases m
  · by_cases hb : (o.pos.x == v.x && o.pos.y == v.y) = true
    · refine ⟨o, by simp [sim.transforms.tobj_set, sim.basic.Vec2.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .position (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_pos (show (abs o : OsuModel.Sim.TObj).pos.eq (abs v) = true from hb)]
    · refine ⟨{ o with pos := v }, by simp [sim.transforms.tobj_set, sim.basic.Vec2.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .position (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_neg (show ¬ (abs o : OsuModel.Sim.TObj).pos.eq (abs v) = true from hb)]; rfl
  · by_cases hb : (o.scale.x == v.x && o.scale.y == v.y) = true
    · refine ⟨o, by simp [sim.transforms.tobj_set, sim.basic.Vec2.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .scale (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_pos (show (abs o : OsuModel.Sim.TObj).scale.eq (abs v) = true from hb)]
    · refine ⟨{ o with scale := v }, by simp [sim.transforms.tobj_set, sim.basic.Vec2.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .scale (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_neg (show ¬ (abs o : OsuModel.Sim.TObj).scale.eq (abs v) = true from hb)]; rfl
  · by_cases hb : (o.rot == v.x) = true
    · refine ⟨o, by simp [sim.transforms.tobj_set, float.F32.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .rotation (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_pos (show ((abs o : OsuModel.Sim.TObj).rot == (abs v : OsuModel.Sim.Vec2).x) = true from hb)]
    · refine ⟨{ o with rot := v.x }, by simp [sim.transforms.tobj_set, float.F32.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .rotation (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_neg (show ¬ ((abs o : OsuModel.Sim.TObj).rot == (abs v : OsuModel.Sim.Vec2).x) = true from hb)]; rfl
  · by_cases hb : (o.alpha == v.x) = true
    · refine ⟨o, by simp [sim.transforms.tobj_set, float.F32.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .alpha (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_pos (show ((abs o : OsuModel.Sim.TObj).alpha == (abs v : OsuModel.Sim.Vec2).x) = true from hb)]
    · refine ⟨{ o with alpha := v.x }, by simp [sim.transforms.tobj_set, float.F32.eq, hb], ?_⟩
      change OsuModel.Sim.TObj.set (abs o) .alpha (abs v) = _; simp only [OsuModel.Sim.TObj.set]
      rw [if_neg (show ¬ ((abs o : OsuModel.Sim.TObj).alpha == (abs v : OsuModel.Sim.Vec2).x) = true from hb)]; rfl

theorem sim.transforms.to_tk_refines (v : sim.basic.Vec2) :
    ∃ r, sim.transforms.to_tk v = ok r ∧ OsuModel.Sim.toTK (abs v) = abs r := by
  simp [sim.transforms.to_tk, OsuModel.Sim.toTK, net.osutk.v2, abs, v2S]

theorem sim.transforms.of_tk_refines (v : net.osutk.Vector2) :
    ∃ r, sim.transforms.of_tk v = ok r ∧ OsuModel.Sim.ofTK (abs v) = abs r := by
  simp [sim.transforms.of_tk, OsuModel.Sim.ofTK, abs, v2S]

theorem sim.transforms.start_time_refines (o : sim.transforms.TObj) (now : F64) :
    sim.transforms.start_time o now = ok (OsuModel.Sim.startTime (abs o) now) := by
  simp [sim.transforms.start_time, OsuModel.Sim.startTime, abs, float.F64.add]

theorem sim.transforms.vs_refines (x : F32) :
    ∃ r, sim.transforms.vs x = ok r ∧ OsuModel.Sim.vs x = abs r := by
  simp [sim.transforms.vs, OsuModel.Sim.vs, abs]

def s2_seqS (s : sim.transforms.Seq) : OsuModel.Sim.Seq := ⟨s.current_time, s.last_end_time, s.has_last⟩
instance s2_absSeq : AbsTo sim.transforms.Seq OsuModel.Sim.Seq := ⟨s2_seqS⟩

theorem sim.transforms.tr_value_at_refines (t : sim.transforms.Tr) (time : F64) :
    ∃ r, sim.transforms.tr_value_at t time = ok r ∧ OsuModel.Sim.Tr.valueAt (abs t) time = abs r := by
  unfold sim.transforms.tr_value_at OsuModel.Sim.Tr.valueAt
  by_cases h1 : time < t.start
  · simp [float.F64.lt, h1, abs]
  · by_cases h2 : t.end_t ≤ time
    · simp [float.F64.lt, float.F64.le, h1, h2, abs]
    · cases hm : t.member <;> simp [hm, float.F64.lt, float.F64.le, h1, h2, abs, sim.transforms.member_is_scalar_refines,
        net.framework.value_at_f_refines, net.framework.value_at_v_refines, memberS, OsuModel.Sim.Member.isScalar,
        sim.transforms.to_tk, sim.transforms.of_tk, net.osutk.v2, OsuModel.Sim.toTK, OsuModel.Sim.ofTK, v2S, v2I]

theorem sim.transforms.apply_tr_refines (o : sim.transforms.TObj) (t : sim.transforms.Tr) (time : F64) :
    ∃ r, sim.transforms.apply_tr o t time = ok r ∧ OsuModel.Sim.applyTr (abs o) (abs t) time = (abs r.2, abs r.1) := by
  obtain ⟨v, hv, ev⟩ := sim.transforms.tr_value_at_refines t time
  obtain ⟨o', ho, eo⟩ := sim.transforms.tobj_set_refines o t.member v
  refine ⟨({ t with applied := true }, o'), by simp [sim.transforms.apply_tr, hv, ho], ?_⟩
  simp only [OsuModel.Sim.applyTr, ev]
  rw [show (abs t : OsuModel.Sim.Tr).member = abs t.member from rfl, eo]; rfl

theorem sim.transforms.read_start_refines (o : sim.transforms.TObj) (t : sim.transforms.Tr) :
    ∃ r, sim.transforms.read_start o t = ok r ∧ OsuModel.Sim.readStart (abs o) (abs t) = abs r := by
  obtain ⟨c, hc, ec⟩ := sim.transforms.tobj_get_refines o t.member
  unfold sim.transforms.read_start OsuModel.Sim.readStart
  rw [show (abs t : OsuModel.Sim.Tr).member = abs t.member from rfl, ec]
  cases ho : t.offset with
  | none =>
    refine ⟨{ t with sv := c, has_start := true }, by simp [hc, ho], ?_⟩
    simp only [show (abs t : OsuModel.Sim.Tr).offset = t.offset.map abs from rfl, ho, Option.map_none]; rfl
  | some off =>
    refine ⟨{ t with sv := c, ev := ⟨c.x + off.x, c.y + off.y⟩, has_start := true }, by simp [hc, ho, sim.basic.Vec2.add], ?_⟩
    simp only [show (abs t : OsuModel.Sim.Tr).offset = t.offset.map abs from rfl, ho, Option.map_some]; rfl

theorem sim.transforms.tr_less_refines (a b : sim.transforms.Tr) :
    sim.transforms.tr_less a b = ok (OsuModel.Sim.trLess (abs a) (abs b)) := by
  obtain ⟨c, hc, ec⟩ := sim.geometry.compare_d_refines a.start b.start
  simp only [abs_id] at ec
  unfold sim.transforms.tr_less OsuModel.Sim.trLess
  simp only [hc, bind_ok, show (abs a : OsuModel.Sim.Tr).start = a.start from rfl, show (abs b : OsuModel.Sim.Tr).start = b.start from rfl, ec]
  have e1 : (abs c : Int) = c.val := rfl
  have e2 : (abs a : OsuModel.Sim.Tr).id = a.id.val := rfl
  have e3 : (abs b : OsuModel.Sim.Tr).id = b.id.val := rfl
  rw [e1, e2, e3]
  by_cases h1 : c.val < 0
  · have : c < 0#i32 := by scalar_tac
    simp [this, h1]
  · have : ¬ c < 0#i32 := by scalar_tac
    by_cases h2 : c.val = 0
    · have : c = 0#i32 := IScalar.eq_of_val_eq (by simp [h2])
      simp [*]
    · have : ¬ c = 0#i32 := fun e => h2 (by simp [e])
      simp [*]

theorem sim.transforms.abs_seq_refines (o : sim.transforms.TObj) (now t : F64) :
    ∃ r, sim.transforms.abs_seq o now t = ok r ∧ OsuModel.Sim.absSeq (abs o) now t = abs r := by
  exact ⟨_, by simp [sim.transforms.abs_seq, float.F64.sub]; rfl, rfl⟩

theorem sim.transforms.seq_then_refines (s : sim.transforms.Seq) :
    ∃ r, sim.transforms.seq_then s = ok r ∧ OsuModel.Sim.Seq.then_ (abs s) = abs r := by
  exact ⟨_, by simp [sim.transforms.seq_then, net.max_refines]; rfl, rfl⟩

theorem sim.transforms.delay_seq_refines (o : sim.transforms.TObj) (now d : F64) :
    ∃ r, sim.transforms.delay_seq o now d = ok r ∧ OsuModel.Sim.delaySeq (abs o) now d = abs r := by
  exact ⟨_, by simp [sim.transforms.delay_seq, sim.transforms.start_time_refines, float.F64.add]; rfl, rfl⟩

@[simp] theorem s2_member_eq (a b : sim.transforms.Member) :
    sim.transforms.Member.Insts.CoreCmpPartialEqMember.eq a b = ok ((abs a : OsuModel.Sim.Member) == abs b) := by
  cases a <;> cases b <;> simp [sim.transforms.Member.Insts.CoreCmpPartialEqMember.eq, read_discriminant,
    sim.transforms.Member.read_discriminant, abs, memberS] <;> decide

theorem sim.transforms.tracker_index_refines (o : sim.transforms.TObj) (m : sim.transforms.Member) :
    ∃ r, sim.transforms.tracker_index o m = ok r ∧
      r.map (·.val) = o.trackers.val.findIdx? (fun t => (abs t.member : OsuModel.Sim.Member) == abs m) := by
  have hmax := o.trackers.property
  obtain ⟨r, hr, er⟩ := s2_find_loop (alloc.vec.Vec.deref o.trackers) (fun t => (abs t.member : OsuModel.Sim.Member) == abs m)
    (fun x => sim.transforms.tracker_index_loop.body o m x.1 x.2)
    (by intro i h
        replace h : i.val < o.trackers.val.length := by simpa [ms_deref_val] using h
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        refine ⟨i1, hi1v, ?_⟩
        simp [sim.transforms.tracker_index_loop.body, vec_lt_len_iff, h, vec_index_usize_ok _ _ h, hi1, ms_deref_val])
    (by intro i j; simp [sim.transforms.tracker_index_loop.body])
    (by intro i r h; replace h : o.trackers.val.length ≤ i.val := by simpa [ms_deref_val] using h
        simp [sim.transforms.tracker_index_loop.body, vec_lt_len_iff, Nat.not_lt.mpr h])
    o.trackers.val.length 0#usize (by simp [alloc.vec.Vec.deref]) (by simp)
  refine ⟨r, by unfold sim.transforms.tracker_index sim.transforms.tracker_index_loop; exact hr, ?_⟩
  rw [er]; simp [ms_deref_val]

theorem sim.transforms.insertion_point_refines (ts : Slice sim.transforms.Tr) (t : sim.transforms.Tr) :
    ∃ r, sim.transforms.insertion_point ts t = ok r ∧
      ((abs ts : _root_.Array OsuModel.Sim.Tr).findIdx? (OsuModel.Sim.trLess (abs t) ·)).getD (abs ts : _root_.Array OsuModel.Sim.Tr).size = r.val := by
  have hmax := ts.property
  obtain ⟨r, hr, er⟩ := s2_find_loop ts (fun u => OsuModel.Sim.trLess (abs t) (abs u))
    (fun x => sim.transforms.insertion_point_loop.body ts t x.1 x.2)
    (by intro i h
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        refine ⟨i1, hi1v, ?_⟩
        simp [sim.transforms.insertion_point_loop.body, slice_lt_len_iff, h, slice_index_ok _ _ h, hi1,
          sim.transforms.tr_less_refines])
    (by intro i j; simp [sim.transforms.insertion_point_loop.body])
    (by intro i r h; simp [sim.transforms.insertion_point_loop.body, slice_lt_len_iff, Nat.not_lt.mpr h])
    ts.val.length 0#usize (by simp) (by simp)
  have ea : (abs ts : _root_.Array OsuModel.Sim.Tr) = (ts.val.map (fun u => (abs u : OsuModel.Sim.Tr))).toArray := rfl
  have hf : (abs ts : _root_.Array OsuModel.Sim.Tr).findIdx? (OsuModel.Sim.trLess (abs t) ·) =
      ts.val.findIdx? (fun u => OsuModel.Sim.trLess (abs t) (abs u)) := by
    rw [ea, List.findIdx?_toArray, List.findIdx?_map]; rfl
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Nat.add_zero, Option.map_id'] at er
  rw [hf, ← er]
  have hl : sim.transforms.insertion_point_loop ts t 0#usize none = ok r := by
    unfold sim.transforms.insertion_point_loop; exact hr
  cases r with
  | none => exact ⟨Slice.len ts, by simp [sim.transforms.insertion_point, hl], by simp [ea]⟩
  | some x => exact ⟨x, by simp [sim.transforms.insertion_point, hl], by simp⟩

theorem s2_forIn_yield_foldl {X S : Type} (G : X → S → Id (ForInStep S)) (g : S → X → S)
    (hG : ∀ x s, G x s = .yield (g s x)) : ∀ (l : List X) (s : S), forIn (m := Id) l s G = l.foldl g s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x t ih => intro s; rw [List.forIn_cons, hG]; exact ih _

def s2_leStep (m e : F64) : F64 := if m < e then e + 1 else m

theorem s2_latest_inner (v : alloc.vec.Vec sim.transforms.Tracker) (k : Usize) (hk : k.val < v.val.length) (m : F64) :
    sim.transforms.latest_end_loop0_loop0 v m k 0#usize =
      ok (((v.val[k.val]'hk).ts.val.map (·.end_t)).foldl s2_leStep m) := by
  have hmax := (v.val[k.val]'hk).ts.property
  have hv : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.transforms.Tracker) v k = ok (v.val[k.val]'hk) := by
    simp [vec_index_usize_ok _ _ hk]
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.transforms.latest_end_loop0_loop0.body v k x.1 x.2) (·.2)
    (v.val[k.val]'hk).ts.val.length (by omega)
    (fun _ => True) (fun t => t.1) (fun j a => s2_leStep a (((v.val[k.val]'hk).ts.val.map (·.end_t))[j]!)) (fun y a => y = a)
    (by
      intro t _ hlt j1 hj1 hj1v
      obtain ⟨a, j⟩ := t
      simp only at hlt hj1 hj1v ⊢
      have hlt' : j < alloc.vec.Vec.len (v.val[k.val]'hk).ts := (vec_lt_len_iff _ _).mpr hlt
      have hix : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.transforms.Tr) (v.val[k.val]'hk).ts j =
          ok ((v.val[k.val]'hk).ts.val[j.val]'hlt) := by simp [vec_index_usize_ok _ _ hlt]
      have h1 : float.F64.from_bits 4607182418800017408#u64 = ok (1 : F64) := by simp
      have hb : sim.transforms.latest_end_loop0_loop0.body v k a j =
          ok (.cont (s2_leStep a ((v.val[k.val]'hk).ts.val[j.val]'hlt).end_t, j1)) := by
        simp only [sim.transforms.latest_end_loop0_loop0.body, hv, hlt', ite_true, hix, float.F64.lt, bind_ok, h1,
          float.F64.add, hj1, s2_leStep]
        by_cases hc : a < ((v.val[k.val]'hk).ts.val[j.val]'hlt).end_t <;> simp [hc]
      exact ⟨_, hb, rfl, by simp only [s2_getElem!_map _ _ _ hlt], trivial⟩)
    (by
      intro t _ hge
      obtain ⟨a, j⟩ := t
      exact ⟨a, by simp [sim.transforms.latest_end_loop0_loop0.body, hv, vec_lt_len_iff, Nat.not_lt.mpr hge], rfl⟩)
    (m, 0#usize) trivial (by simp)
  unfold sim.transforms.latest_end_loop0_loop0; rw [hl, hy]
  rw [foldl_iterR]; simp

theorem sim.transforms.latest_end_refines (o : sim.transforms.TObj) (now : F64) :
    sim.transforms.latest_end o now = ok (OsuModel.Sim.latestEnd (abs o) now) := by
  have hmax := o.trackers.property
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.transforms.latest_end_loop0.body o x.1 x.2) (·.2)
    o.trackers.val.length (by omega)
    (fun _ => True) (fun t => t.1)
    (fun j a => ((o.trackers.val.map (fun (tk : sim.transforms.Tracker) => tk.ts.val.map (·.end_t)))[j]!).foldl s2_leStep a) (fun y a => y = a)
    (by
      intro t _ hlt j1 hj1 hj1v
      obtain ⟨a, j⟩ := t
      simp only at hlt hj1 hj1v ⊢
      refine ⟨(((o.trackers.val.map (fun (tk : sim.transforms.Tracker) => tk.ts.val.map (·.end_t)))[j.val]!).foldl s2_leStep a, j1), ?_, rfl, rfl, trivial⟩
      rw [s2_getElem!_map _ _ _ hlt]
      simp [sim.transforms.latest_end_loop0.body, vec_lt_len_iff, hlt, s2_latest_inner _ _ hlt, hj1])
    (by
      intro t _ hge
      obtain ⟨a, j⟩ := t
      exact ⟨a, by simp [sim.transforms.latest_end_loop0.body, vec_lt_len_iff, Nat.not_lt.mpr hge], rfl⟩)
    (OsuModel.Sim.startTime (abs o) now, 0#usize) trivial (by simp)
  let L := o.trackers.val.map (fun (tk : sim.transforms.Tracker) => tk.ts.val.map (·.end_t))
  have hF := foldl_iterR L (fun s l => l.foldl s2_leStep s) (OsuModel.Sim.startTime (abs o) now)
  simp only [L, List.length_map] at hF
  unfold sim.transforms.latest_end
  simp only [sim.transforms.start_time_refines, bind_ok]
  unfold sim.transforms.latest_end_loop0; rw [hl, hy]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  rw [← hF]
  congr 1
  unfold OsuModel.Sim.latestEnd
  have hin : ∀ (l : List OsuModel.Sim.Tr) (x : F64),
      forIn (m := Id) l x (fun a y => if y < a.endT then pure (ForInStep.yield (a.endT + 1)) else pure (ForInStep.yield y))
        = l.foldl (fun s t => s2_leStep s t.endT) x :=
    s2_forIn_yield_foldl _ _ (by intro a y; simp only [s2_leStep]; split <;> rfl)
  simp [Id.run, Array.forIn_pure_yield_eq_foldl, abs, List.foldl_map, hin]

theorem s2_cta_inner (v : alloc.vec.Vec sim.transforms.Tracker) (time : F64) (k : Usize) (hk : k.val < v.val.length) :
    ∀ (n : Nat) (ts : alloc.vec.Vec sim.transforms.Tr) (j : Usize), (v.val[k.val]'hk).ts.val.length - j.val = n →
      j.val ≤ (v.val[k.val]'hk).ts.val.length → ts.val.length ≤ j.val →
      ∃ r, sim.transforms.clear_transforms_after_loop0_loop0 v time k ts j = ok r ∧
        r.val = ts.val ++ ((v.val[k.val]'hk).ts.val.drop j.val).filter (fun t => t.start < time) := by
  have hmax := (v.val[k.val]'hk).ts.property
  have hv : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.transforms.Tracker) v k = ok (v.val[k.val]'hk) := by
    simp [vec_index_usize_ok _ _ hk]
  intro n
  induction n with
  | zero =>
    intro ts j hn hj hts
    refine ⟨ts, ?_, by rw [List.drop_eq_nil_of_le (by omega)]; simp⟩
    have hge : ¬ j.val < (v.val[k.val]'hk).ts.val.length := by omega
    unfold sim.transforms.clear_transforms_after_loop0_loop0; rw [loop_unfold]
    simp [sim.transforms.clear_transforms_after_loop0_loop0.body, hv, vec_lt_len_iff, hge]
  | succ n ih =>
    intro ts j hn hj hts
    have hlt : j.val < (v.val[k.val]'hk).ts.val.length := by omega
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    have hp : ts.val.length < Usize.max := by omega
    have hdrop := List.drop_eq_getElem_cons hlt
    have hf : ((v.val[k.val]'hk).ts.val.drop j.val).filter (fun t => decide (t.start < time)) =
        (if ((v.val[k.val]'hk).ts.val[j.val]'hlt).start < time then [(v.val[k.val]'hk).ts.val[j.val]'hlt] else []) ++
          ((v.val[k.val]'hk).ts.val.drop (j.val + 1)).filter (fun t => decide (t.start < time)) := by
      rw [hdrop, List.filter_cons]; split <;> simp_all
    let t := (v.val[k.val]'hk).ts.val[j.val]'hlt
    have hix : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.transforms.Tr) (v.val[k.val]'hk).ts j = ok t := by
      simp [vec_index_usize_ok _ _ hlt, t]
    have hlt' : j < alloc.vec.Vec.len (v.val[k.val]'hk).ts := (vec_lt_len_iff _ _).mpr hlt
    by_cases hc : t.start < time
    · obtain ⟨r, hr, er⟩ := ih (vpush ts t hp) j1 (by omega) (by omega) (by simp; omega)
      refine ⟨r, ?_, ?_⟩
      · have hb : sim.transforms.clear_transforms_after_loop0_loop0.body v time k ts j = ok (.cont (vpush ts t hp, j1)) := by
          simp only [sim.transforms.clear_transforms_after_loop0_loop0.body, hv, hlt', ite_true, hix, float.F64.lt, bind_ok,
            decide_eq_true hc, vec_push_ok _ _ hp, hj1]
        unfold sim.transforms.clear_transforms_after_loop0_loop0; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.transforms.clear_transforms_after_loop0_loop0 at hr; exact hr
      · rw [er, hj1v, hf]; simp [hc, t]
    · obtain ⟨r, hr, er⟩ := ih ts j1 (by omega) (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · have hb : sim.transforms.clear_transforms_after_loop0_loop0.body v time k ts j = ok (.cont (ts, j1)) := by
          simp only [sim.transforms.clear_transforms_after_loop0_loop0.body, hv, hlt', ite_true, hix, float.F64.lt, bind_ok,
            decide_eq_false hc, hj1]; simp
        unfold sim.transforms.clear_transforms_after_loop0_loop0; rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
        unfold sim.transforms.clear_transforms_after_loop0_loop0 at hr; exact hr
      · rw [er, hj1v, hf]; simp [hc, t]

def s2_filterVec (time : F64) (v : alloc.vec.Vec sim.transforms.Tr) : alloc.vec.Vec sim.transforms.Tr :=
  alloc.vec.Vec.from (v.val.filter (fun t => decide (t.start < time))) (by
    have := v.property; have := List.length_filter_le (fun t => decide (t.start < time)) v.val; omega)
def s2_ctaG (time : F64) (tk : sim.transforms.Tracker) : sim.transforms.Tracker :=
  { member := tk.member, ts := s2_filterVec time tk.ts, counter := tk.counter, last_applied := 0#usize }

theorem sim.transforms.clear_transforms_after_refines (o : sim.transforms.TObj) (time : F64) :
    ∃ r, sim.transforms.clear_transforms_after o time = ok r ∧
      OsuModel.Sim.clearTransformsAfter (abs o) time = abs r := by
  have hmax := o.trackers.property
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.transforms.clear_transforms_after_loop0.body time x.1 x.2) (·.2)
    o.trackers.val.length (by omega)
    (fun t => t.1.trackers.val.length = o.trackers.val.length ∧ t.1.pos = o.pos ∧ t.1.scale = o.scale ∧ t.1.rot = o.rot ∧
      t.1.alpha = o.alpha ∧ t.1.last_update = o.last_update ∧ t.1.delay = o.delay)
    (fun t => t.1.trackers.val) (fun k L => L.modify k (s2_ctaG time))
    (fun y L => y.2.2.2.2.1.val = L ∧ y.1 = o.pos ∧ y.2.1 = o.scale ∧ y.2.2.1 = o.rot ∧ y.2.2.2.1 = o.alpha ∧
      y.2.2.2.2.2.1 = o.last_update ∧ y.2.2.2.2.2.2 = o.delay)
    (by
      intro t hI hlt j1 hj1 hj1v
      obtain ⟨o', k⟩ := t
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
      simp only at hlt hj1 hj1v h1 h2 h3 h4 h5 h6 h7 ⊢
      have hk : k.val < o'.trackers.val.length := by omega
      obtain ⟨ts, hts, ets⟩ := s2_cta_inner o'.trackers time k hk _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
      let t := o'.trackers.val[k.val]'hk
      let v1 := alloc.vec.Vec.set o'.trackers k { t with ts := ts }
      have hk1 : k.val < v1.val.length := by simp [v1, vec_set_val']; omega
      have hv1 : v1.val[k.val]'hk1 = { t with ts := ts } := by simp [v1, vec_set_val']
      let v2 := alloc.vec.Vec.set v1 k { t with ts := ts, last_applied := 0#usize }
      refine ⟨({ o' with trackers := v2 }, j1), ?_, rfl, ?_, ?_⟩
      · have e1 := vec_index_mut_usize_ok o'.trackers k hk
        have e2 := vec_index_mut_usize_ok v1 k hk1
        simp only [v1] at e2 hv1
        simp [sim.transforms.clear_transforms_after_loop0.body, vec_lt_len_iff, hk, hts, e1, e2, hv1, hj1, v2, v1, t]
      · have ets' : ts = s2_filterVec time t.ts := by
          rw [alloc.vec.Vec.eq_iff]; simp [s2_filterVec, alloc.vec.Vec.from_val, ets, t]
        simp only [v2, v1, vec_set_val', List.set_set]
        rw [list_modify_set _ _ hk]
        simp [s2_ctaG, ets', t]
      · simp [v2, v1, vec_set_val', h1, h2, h3, h4, h5, h6, h7])
    (by
      intro t hI hge
      obtain ⟨o', k⟩ := t
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
      refine ⟨(o'.pos, o'.scale, o'.rot, o'.alpha, o'.trackers, o'.last_update, o'.delay), ?_, rfl, h2, h3, h4, h5, h6, h7⟩
      simp only at hge h1 h2 h3 h4 h5 h6 h7
      simp [sim.transforms.clear_transforms_after_loop0.body, vec_lt_len_iff, show ¬ k.val < o'.trackers.val.length by omega])
    (o, 0#usize) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by simp)
  obtain ⟨p, sc, ro, al, trs, lu, de⟩ := y
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hy
  simp only [show (0#usize : Usize).val = 0 from rfl] at y1
  rw [iterR_modify_map] at y1
  refine ⟨⟨p, sc, ro, al, trs, lu, de⟩, ?_, ?_⟩
  · unfold sim.transforms.clear_transforms_after
    rw [show sim.transforms.clear_transforms_after_loop0 o time 0#usize = ok (p, sc, ro, al, trs, lu, de) by
      unfold sim.transforms.clear_transforms_after_loop0; exact hl]
    simp
  · simp only at y2 y3 y4 y5 y6 y7
    subst y2 y3 y4 y5 y6 y7
    unfold OsuModel.Sim.clearTransformsAfter
    simp only [abs]
    rw [y1]
    simp [List.map_map, s2_ctaG, s2_filterVec, alloc.vec.Vec.from_val, List.filter_map, Function.comp_def]

end OsuProofs
