/-
Generator mods, part 8 (gen agent): Target Practice `beatmap::mod_target_practice::generate_beats`
(spec normal form `gen_gb_spec`; inner beat loop, timing-point loop, the two filters, kept loop, reversal).
-/
import OsuProofs.Post.GenTP1
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
open Mods.TargetPractice

def gen_gbInF (cpi : ControlPointInfo) (endT : F64) (ti : Nat) (tp : TimingPoint) (_ : Nat)
    (s : Array F64 × Int32 × F64) : ForInStep (Array F64 × Int32 × F64) :=
  if (definitelyBigger s.2.2 endT || timingPointIndexAt cpi s.2.2 != some ti) = true then .done s
  else .yield (s.1.push s.2.2.floor, s.2.1 + 1, tp.time + F64.ofInt32 (s.2.1 + 1) * tp.beatLength)

def gen_gbOutF (cpi : ControlPointInfo) (endT : F64) (s : Array F64 × Nat) (tp : TimingPoint) : Array F64 × Nat :=
  if (!definitelyBigger tp.time endT) = true then
    ((iterR (gen_gbInF cpi endT s.2 tp) 0 1000000000 (s.1, 0, tp.time)).1, s.2 + 1)
  else (s.1, s.2 + 1)

def gen_gbKeptF (B : Array F64) (cpi : ControlPointInfo) (k : Nat) (kept : List F64) : List F64 :=
  if definitelyBigger (kept.head! - B[B.size - 2 - k]!) ((cpi.timingPointAt B[B.size - 2 - k]!).beatLength / 2) = true
  then B[B.size - 2 - k]! :: kept else kept

def gen_gbB (pb : PlayableBeatmap) (orig : Array OsuHitObject) : Array F64 :=
  ((pb.controlPoints.timingPoints.toList.foldl (gen_gbOutF pb.controlPoints (Mods.lastObjectTime pb)) (#[], 0)).1.filter
    (fun b => almostBigger b pb.hitObjects[0]!.startTime)).filter (fun b => !insideBreak orig pb.breaks b)

theorem gen_gb_spec (pb : PlayableBeatmap) (orig : Array OsuHitObject) :
    generateBeats pb orig = if (gen_gbB pb orig).size < 2 then gen_gbB pb orig else
      (iterR (fun k s => .yield (gen_gbKeptF (gen_gbB pb orig) pb.controlPoints k s)) 0 ((gen_gbB pb orig).size - 1)
        [(gen_gbB pb orig).back!]).toArray := by
  unfold generateBeats
  simp only [Id.run]
  rw [← Array.forIn_toList, forIn_yield_foldl _ (gen_gbOutF pb.controlPoints (Mods.lastObjectTime pb)) ?hO]
  case hO =>
    intro tp s
    unfold gen_gbOutF
    split
    · rw [forIn_range_iterR, Nat.sub_zero]
      have hF : (fun (x : Nat) (r : Array F64 × Int32 × F64) =>
          (if (definitelyBigger r.2.2 (Mods.lastObjectTime pb) ||
              timingPointIndexAt pb.controlPoints r.2.2 != some s.2) = true then
            (pure (ForInStep.done (r.1, r.2.1, r.2.2)) : Id _)
          else pure (ForInStep.yield (r.1.push r.2.2.floor, r.2.1 + 1, tp.time + F64.ofInt32 (r.2.1 + 1) * tp.beatLength)))) =
          gen_gbInF pb.controlPoints (Mods.lastObjectTime pb) s.2 tp := by
        funext x r; unfold gen_gbInF; split <;> rfl
      rw [hF]
      rfl
    · rfl
  dsimp only [Bind.bind]
  unfold gen_gbB
  generalize Array.filter (fun b => !insideBreak orig pb.breaks b) _ = B
  split
  · rfl
  · rw [forIn_range_iterR, Nat.sub_zero]
    have hF : (fun (k : Nat) (r : List F64) =>
        (if definitelyBigger (r.head! - B[B.size - 2 - k]!) ((pb.controlPoints.timingPointAt B[B.size - 2 - k]!).beatLength / 2) = true
         then (pure (ForInStep.yield (B[B.size - 2 - k]! :: r)) : Id _) else pure (ForInStep.yield r))) =
        fun k r => .yield (gen_gbKeptF B pb.controlPoints k r) := by
      funext k r; unfold gen_gbKeptF; split <;> rfl
    rw [hF]
    rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice

instance : Inhabited (Option Usize) := ⟨none⟩
noncomputable def gen_tpiR (c : beatmap.control_points.ControlPointInfo) (t : F64) : Option Usize :=
  gen_val (beatmap.mod_target_practice.timing_point_index_at c t)
theorem gen_tpi_ok (c : beatmap.control_points.ControlPointInfo) (t : F64) (h : c.timing_points.val.length < 2^31) :
    beatmap.mod_target_practice.timing_point_index_at c t = ok (gen_tpiR c t) ∧
      (gen_tpiR c t).map (·.val) = timingPointIndexAt (cpS c) t := by
  obtain ⟨o, ho, hov⟩ := beatmap.mod_target_practice.timing_point_index_at_refines c t h
  have := gen_val_eq _ ⟨_, ho⟩
  rw [ho] at this
  have h2 := Result.ok_injective this
  unfold gen_tpiR; rw [ho, ← h2]; exact ⟨rfl, hov⟩

theorem gen_f64_i32 (x : I32) : float.F64.from_i64 (IScalar.cast .I64 x) = ok (F64.ofInt32 (i32S x)) := by
  simp [float.F64.from_i64, F64.ofInt32, i32S_toInt, IScalar.cast_val_eq]

theorem gen_gb_inner (v : alloc.vec.Vec beatmap.control_points.TimingPoint)
    (v1 : alloc.vec.Vec beatmap.control_points.DifficultyPoint) (v2 : alloc.vec.Vec beatmap.control_points.EffectPoint)
    (hc : v.val.length < 2^31) (endT : F64) (ti : Usize) (tp : TimingPoint)
    (beats : alloc.vec.Vec F64) (hb : beats.val.length + 1000000000 < Usize.max) :
    ∃ y, beatmap.mod_target_practice.generate_beats_loop0_loop0 v v1 v2 endT beats ti tp.time tp.beatLength
        0#i32 tp.time 0#u64 true = ok y ∧
      y.val = (iterR (gen_gbInF (cpS ⟨v, v1, v2⟩) endT ti.val tp) 0 1000000000 (beats.val.toArray, 0, tp.time)).1.toList ∧
      y.val.length ≤ beats.val.length + 1000000000 := by
  have hti := fun t => gen_tpi_ok ⟨v, v1, v2⟩ t hc
  have := loop_iterR (fun t : alloc.vec.Vec F64 × I32 × F64 × U64 × Bool =>
      beatmap.mod_target_practice.generate_beats_loop0_loop0.body v v1 v2 endT ti tp.time tp.beatLength
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)
    (gen_gbInF (cpS ⟨v, v1, v2⟩) endT ti.val tp) 1000000000 (fun t => t.2.2.2.1.val)
    (fun t s => t.2.2.2.2 = true ∧ t.1.val.toArray = s.1 ∧ i32S t.2.1 = s.2.1 ∧ t.2.2.1 = s.2.2 ∧
      t.1.val.length ≤ beats.val.length + t.2.2.2.1.val ∧ t.2.2.2.1.val ≤ 1000000000)
    (fun y s => y.val = s.1.toList ∧ y.val.length ≤ beats.val.length + 1000000000)
    (by
      rintro ⟨bs, i, cur, fuel, go⟩ ⟨s1, s2, s3⟩ ⟨hgo, h1, h2, h3, h4, h5⟩ hlt
      simp only at hgo h1 h2 h3 h4 h5 hlt ⊢
      subst hgo h1 h2 h3
      have hfuel : fuel < 1000000000#u64 := by scalar_tac
      have hcond := (hti cur).2
      unfold gen_gbInF
      simp only []
      by_cases hd : definitelyBigger cur endT = true
      · simp only [hd, Bool.true_or, if_true]
        refine ⟨(fun s' h => by cases h), fun s' h => ?_⟩
        cases h
        refine ⟨bs, Or.inr ⟨(bs, i, cur, fuel, false), ?_, ?_⟩, by simp, by omega⟩
        · simp only [beatmap.mod_target_practice.generate_beats_loop0_loop0.body, if_true, hfuel, (hti cur).1,
            bind_ok, tp_db, hd]
          cases gen_tpiR ⟨v, v1, v2⟩ cur <;> simp
        · simp [beatmap.mod_target_practice.generate_beats_loop0_loop0.body]
      · simp only [hd, Bool.false_or]
        by_cases hs : (timingPointIndexAt (cpS ⟨v, v1, v2⟩) cur != some ti.val) = true
        · simp only [hs, if_true]
          refine ⟨(fun s' h => by cases h), fun s' h => ?_⟩
          cases h
          refine ⟨bs, Or.inr ⟨(bs, i, cur, fuel, false), ?_, ?_⟩, by simp, by omega⟩
          · simp only [beatmap.mod_target_practice.generate_beats_loop0_loop0.body, if_true, hfuel, (hti cur).1,
              bind_ok, tp_db, hd, Bool.false_eq_true, if_false]
            rw [← hcond] at hs
            cases ho : gen_tpiR ⟨v, v1, v2⟩ cur with
            | none => simp
            | some x =>
              rw [ho] at hs
              have : ¬ x = ti := by intro e; subst e; simp at hs
              simp [this]
          · simp [beatmap.mod_target_practice.generate_beats_loop0_loop0.body]
        · simp only [hs, Bool.false_eq_true, if_false]
          refine ⟨fun s' h => ?_, (fun s' h => by cases h)⟩
          cases h
          have hpush : bs.val.length < Usize.max := by scalar_tac
          obtain ⟨fu1, hfu1, hfu1v⟩ := gen_u64_add_one fuel (by scalar_tac)
          refine ⟨(vpush bs cur.floor hpush, core.num.I32.wrapping_add i 1#i32,
            tp.time + F64.ofInt32 (i32S (core.num.I32.wrapping_add i 1#i32)) * tp.beatLength, fu1, true), ?_, by simp [hfu1v],
            rfl, by simp, by simp [i32S_wadd1], rfl, by simp; omega, by simp; omega⟩
          simp only [beatmap.mod_target_practice.generate_beats_loop0_loop0.body, if_true, hfuel, (hti cur).1,
            bind_ok, tp_db, hd, Bool.false_eq_true, if_false]
          rw [← hcond] at hs
          cases ho : gen_tpiR ⟨v, v1, v2⟩ cur with
          | none => rw [ho] at hs; simp at hs
          | some x =>
            rw [ho] at hs; simp at hs
            have hx : x = ti := UScalar.eq_of_val_eq hs
            subst hx
            simp only [bind_ok, decide_true, if_true, ite_true, float.F64.floor, vec_push_ok _ _ hpush, lift,
              gen_f64_i32, float.F64.mul, float.F64.add, hfu1])
    (by
      rintro ⟨bs, i, cur, fuel, go⟩ ⟨s1, s2, s3⟩ ⟨hgo, h1, h2, h3, h4, h5⟩ hge
      simp only at hgo h1 h2 h3 h4 h5 hge ⊢
      subst hgo h1
      have hfuel : ¬ fuel < 1000000000#u64 := by scalar_tac
      exact ⟨bs, by simp [beatmap.mod_target_practice.generate_beats_loop0_loop0.body, hfuel], by simp, by omega⟩)
    (beats, 0#i32, tp.time, 0#u64, true) (beats.val.toArray, 0, tp.time) ⟨rfl, rfl, rfl, rfl, by simp, by simp⟩ (by simp)
  obtain ⟨y, hl, hq1, hq2⟩ := this
  exact ⟨y, by unfold beatmap.mod_target_practice.generate_beats_loop0_loop0; exact hl, hq1, hq2⟩

theorem gen_gb_outer (cpi : beatmap.control_points.ControlPointInfo) (hc : cpi.timing_points.val.length < 2^31)
    (endT : F64) (h64 : System.Platform.numBits = 64) :
    ∃ y, beatmap.mod_target_practice.generate_beats_loop0 cpi endT (alloc.vec.Vec.new F64) 0#usize = ok y ∧
      y.1 = cpi.timing_points ∧ y.2.1 = cpi.difficulty_points ∧ y.2.2.1 = cpi.effect_points ∧
      y.2.2.2.val.toArray = ((cpS cpi).timingPoints.toList.foldl (gen_gbOutF (cpS cpi) endT) (#[], 0)).1 := by
  have hL : (cpS cpi).timingPoints.toList = cpi.timing_points.val.map tpS := by simp [cpS]
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec F64 × Usize => beatmap.mod_target_practice.generate_beats_loop0.body cpi endT x.1 x.2) (·.2)
    cpi.timing_points.val.length (by have := cpi.timing_points.property; omega)
    (fun x => x.1.val.length ≤ x.2.val * 1000000000)
    (fun x => (x.1.val.toArray, x.2.val))
    (fun k s => gen_gbOutF (cpS cpi) endT s ((cpS cpi).timingPoints.toList[k]!))
    (fun y s => y.1 = cpi.timing_points ∧ y.2.1 = cpi.difficulty_points ∧ y.2.2.1 = cpi.effect_points ∧
      y.2.2.2.val.toArray = s.1)
    (by
      rintro ⟨bs, ti⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hti : ti.val < cpi.timing_points.val.length := hlt
      have hLk : (cpS cpi).timingPoints.toList[ti.val]! = tpS (cpi.timing_points.val[ti.val]'hti) := by
        rw [hL, getElem!_pos _ _ (by simpa using hti)]; simp
      rw [hLk]
      unfold gen_gbOutF
      by_cases hd : Mods.TargetPractice.definitelyBigger (cpi.timing_points.val[ti.val]'hti).time endT = true
      · refine ⟨(bs, j1), ?_, rfl, ?_, ?_⟩
        · simp only [beatmap.mod_target_practice.generate_beats_loop0.body, vec_lt_len_iff, hti, if_true,
            vec_index_eq _ _ hti, bind_ok, tp_db, hd, hj1]
        · show _ = (if (!Mods.TargetPractice.definitelyBigger (cpi.timing_points.val[ti.val]'hti).time endT) = true then _ else _)
          simp [hd, hj1v]
        · simp only [hj1v]; nlinarith
      · have hb : bs.val.length + 1000000000 < Usize.max := by
          have : ti.val * 1000000000 < 2^31 * 1000000000 := by omega
          rw [usize_max_64 h64]; omega
        obtain ⟨z, hz, hzv, hzl⟩ := gen_gb_inner cpi.timing_points cpi.difficulty_points cpi.effect_points hc endT ti
          (tpS (cpi.timing_points.val[ti.val]'hti)) bs hb
        refine ⟨(z, j1), ?_, rfl, ?_, ?_⟩
        · simp only [beatmap.mod_target_practice.generate_beats_loop0.body, vec_lt_len_iff, hti, if_true,
            vec_index_eq _ _ hti, bind_ok, tp_db, hd, Bool.false_eq_true, if_false, hj1]
          rw [show beatmap.mod_target_practice.generate_beats_loop0_loop0 cpi.timing_points cpi.difficulty_points
            cpi.effect_points endT bs ti (cpi.timing_points.val[ti.val]'hti).time
            (cpi.timing_points.val[ti.val]'hti).beat_length 0#i32 (cpi.timing_points.val[ti.val]'hti).time 0#u64 true = ok z
            from hz]
          simp only [bind_ok]
        · show _ = (if (!Mods.TargetPractice.definitelyBigger (cpi.timing_points.val[ti.val]'hti).time endT) = true then _ else _)
          simp only [hd, Bool.not_false, if_true, hj1v]
          rw [hzv]
        · simp only [hj1v]; nlinarith)
    (by
      rintro ⟨bs, ti⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ ti < alloc.vec.Vec.len cpi.timing_points := by rw [vec_lt_len_iff]; omega
      exact ⟨(cpi.timing_points, cpi.difficulty_points, cpi.effect_points, bs),
        by simp [beatmap.mod_target_practice.generate_beats_loop0.body, this], rfl, rfl, rfl, rfl⟩)
    (alloc.vec.Vec.new F64, 0#usize) (by simp [alloc.vec.Vec.new]) (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.generate_beats_loop0; exact hl, hv.1, hv.2.1, hv.2.2.1, ?_⟩
  rw [hv.2.2.2, foldl_iterR]
  simp [hL, alloc.vec.Vec.new]
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice

theorem gen_filter_iterR {α} [Inhabited α] (l : List α) (p : α → Bool) :
    iterR (fun k (s : Array α) => .yield (if p l[k]! then s.push l[k]! else s)) 0 l.length #[] = l.toArray.filter p := by
  rw [← foldl_iterR (S := Array α) l (fun s x => if p x then s.push x else s) #[]]
  rw [List.filter_toArray]
  suffices h : ∀ (acc : Array α), l.foldl (fun s x => if p x then s.push x else s) acc = acc ++ (l.filter p).toArray by
    simpa using h #[]
  induction l with
  | nil => intro acc; simp
  | cons x t ih =>
    intro acc
    simp only [List.foldl_cons, List.filter_cons]
    split <;> simp [ih]

theorem gen_gb_l1 (st : F64) (beats : alloc.vec.Vec F64) :
    ∃ y, beatmap.mod_target_practice.generate_beats_loop1 st beats (alloc.vec.Vec.new F64) 0#usize = ok y ∧
      y.val.toArray = beats.val.toArray.filter (fun b => almostBigger b st) := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec F64 × Usize => beatmap.mod_target_practice.generate_beats_loop1.body st beats x.1 x.2) (·.2)
    beats.val.length (by have := beats.property; omega)
    (fun x => x.1.val.length ≤ x.2.val) (fun x => x.1.val.toArray)
    (fun k s => if almostBigger beats.val[k]! st then s.push beats.val[k]! else s)
    (fun y s => y.val.toArray = s)
    (by
      rintro ⟨b1, k⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hk : k.val < beats.val.length := hlt
      have hpush : b1.val.length < Usize.max := by have := beats.property; omega
      rw [getElem!_pos beats.val k.val hk]
      by_cases hp : almostBigger (beats.val[k.val]'hk) st = true
      · refine ⟨(vpush b1 (beats.val[k.val]'hk) hpush, j1), ?_, rfl, by simp [hp], by simp; omega⟩
        simp only [beatmap.mod_target_practice.generate_beats_loop1.body, vec_lt_len_iff, hk, if_true,
          vec_index_eq _ _ hk, bind_ok, tp_ab, hp, vec_push_ok _ _ hpush, hj1]
      · refine ⟨(b1, j1), ?_, rfl, by simp [hp], by simp; omega⟩
        simp only [beatmap.mod_target_practice.generate_beats_loop1.body, vec_lt_len_iff, hk, if_true,
          vec_index_eq _ _ hk, bind_ok, tp_ab, hp, Bool.false_eq_true, if_false, hj1])
    (by
      rintro ⟨b1, k⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ k < alloc.vec.Vec.len beats := by rw [vec_lt_len_iff]; omega
      exact ⟨b1, by simp [beatmap.mod_target_practice.generate_beats_loop1.body, this], rfl⟩)
    (alloc.vec.Vec.new F64, 0#usize) (by simp [alloc.vec.Vec.new]) (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.generate_beats_loop1; exact hl, ?_⟩
  rw [hv]
  simpa [alloc.vec.Vec.new] using gen_filter_iterR beats.val (fun b => almostBigger b st)

theorem gen_gb_l2 (br : alloc.vec.Vec beatmap.types.BreakPeriod) (orig : Slice beatmap.objects.OsuHitObject)
    (b1 : alloc.vec.Vec F64) :
    ∃ y, beatmap.mod_target_practice.generate_beats_loop2 br orig b1 0#usize (alloc.vec.Vec.new F64) = ok y ∧
      y.val.toArray = b1.val.toArray.filter (fun b => !insideBreak (abs orig) (abs br) b) := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : Usize × alloc.vec.Vec F64 => beatmap.mod_target_practice.generate_beats_loop2.body br orig b1 x.1 x.2) (·.1)
    b1.val.length (by have := b1.property; omega)
    (fun x => x.2.val.length ≤ x.1.val) (fun x => x.2.val.toArray)
    (fun k s => if !insideBreak (abs orig) (abs br) b1.val[k]! then s.push b1.val[k]! else s)
    (fun y s => y.val.toArray = s)
    (by
      rintro ⟨k, b2⟩ hI hlt j1 hj1 hj1v
      simp only at hI hlt hj1 hj1v ⊢
      have hk : k.val < b1.val.length := hlt
      have hpush : b2.val.length < Usize.max := by have := b1.property; omega
      rw [getElem!_pos b1.val k.val hk]
      obtain ⟨r, hr, hrv⟩ := beatmap.mod_target_practice.inside_break_refines orig (alloc.vec.Vec.deref br) (b1.val[k.val]'hk)
      rw [gen_abs_deref] at hrv
      have hrv' : insideBreak (abs orig) (abs br) (b1.val[k.val]'hk) = r := hrv
      by_cases hp : r = true
      · refine ⟨(j1, b2), ?_, rfl, by simp [hrv', hp], by simp; omega⟩
        simp only [beatmap.mod_target_practice.generate_beats_loop2.body, vec_lt_len_iff, hk, if_true,
          vec_index_eq _ _ hk, bind_ok, hr, hp, hj1]
      · refine ⟨(j1, vpush b2 (b1.val[k.val]'hk) hpush), ?_, rfl, by simp [hrv', hp], by simp; omega⟩
        simp only [beatmap.mod_target_practice.generate_beats_loop2.body, vec_lt_len_iff, hk, if_true,
          vec_index_eq _ _ hk, bind_ok, hr, hp, Bool.false_eq_true, if_false, vec_push_ok _ _ hpush, hj1])
    (by
      rintro ⟨k, b2⟩ hI hge
      simp only at hI hge ⊢
      have : ¬ k < alloc.vec.Vec.len b1 := by rw [vec_lt_len_iff]; omega
      exact ⟨b2, by simp [beatmap.mod_target_practice.generate_beats_loop2.body, this], rfl⟩)
    (0#usize, alloc.vec.Vec.new F64) (by simp [alloc.vec.Vec.new]) (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.generate_beats_loop2; exact hl, ?_⟩
  rw [hv]
  simpa [alloc.vec.Vec.new] using gen_filter_iterR b1.val (fun b => !insideBreak (abs orig) (abs br) b)
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice

theorem gen_gb_l4 (kr : alloc.vec.Vec F64) :
    ∀ (out : alloc.vec.Vec F64) (r : Usize), r.val ≤ kr.val.length → out.val.length + r.val ≤ kr.val.length →
      ∃ y, beatmap.mod_target_practice.generate_beats_loop4 kr out r = ok y ∧
        y.val = out.val ++ (kr.val.take r.val).reverse := by
  intro out r
  induction hr : r.val generalizing out r with
  | zero =>
    intro _ _
    refine ⟨out, ?_, by simp⟩
    unfold beatmap.mod_target_practice.generate_beats_loop4
    rw [loop_unfold]
    have : ¬ r > 0#usize := by scalar_tac
    simp [beatmap.mod_target_practice.generate_beats_loop4.body, this]
  | succ n ih =>
    intro hle hlen
    have hpos : r > 0#usize := by scalar_tac
    obtain ⟨r1, hr1, hr1v⟩ : ∃ r1 : Usize, r - 1#usize = ok r1 ∧ r1.val = n := by
      obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := r) (y := 1#usize) (by scalar_tac))
      exact ⟨z, hz, by have := hzv; scalar_tac⟩
    have hn : n < kr.val.length := by omega
    have hpush : out.val.length < Usize.max := by have := kr.property; omega
    obtain ⟨y, hy, hyv⟩ := ih (vpush out (kr.val[n]'hn) hpush) r1 hr1v (by omega) (by simp; omega)
    refine ⟨y, ?_, ?_⟩
    · unfold beatmap.mod_target_practice.generate_beats_loop4
      rw [loop_unfold]
      have hb : beatmap.mod_target_practice.generate_beats_loop4.body kr out r =
          ok (.cont (vpush out (kr.val[n]'hn) hpush, r1)) := by
        simp only [beatmap.mod_target_practice.generate_beats_loop4.body, hpos, if_true, hr1, bind_ok,
          vec_index_eq _ _ (show r1.val < kr.val.length by omega), hr1v, vec_push_ok _ _ hpush]
      dsimp only
      rw [hb]; simp only [bind_ok]
      unfold beatmap.mod_target_practice.generate_beats_loop4 at hy
      exact hy
    · rw [hyv, vpush_val]
      simp only [List.append_assoc, List.singleton_append]
      rw [List.take_succ, List.getElem?_eq_getElem hn]
      simp only [List.reverse_append, Option.toList_some, List.reverse_singleton, List.singleton_append]

theorem gen_usub (a b : Usize) (h : b.val ≤ a.val) : ∃ c : Usize, a - b = ok c ∧ c.val = a.val - b.val := by
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := a) (y := b) h)
  exact ⟨z, hz, by have := hzv; scalar_tac⟩

theorem gen_gb_l3 (v : alloc.vec.Vec beatmap.control_points.TimingPoint)
    (v1 : alloc.vec.Vec beatmap.control_points.DifficultyPoint) (v2 : alloc.vec.Vec beatmap.control_points.EffectPoint)
    (hc : v.val.length < 2^31) (b2 kr0 : alloc.vec.Vec F64) (h2 : 2 ≤ b2.val.length)
    (hk0 : kr0.val = [b2.val[b2.val.length - 1]'(by omega)]) :
    ∃ y, beatmap.mod_target_practice.generate_beats_loop3 v v1 v2 b2 kr0 0#usize = ok y ∧
      y.val.reverse = iterR (fun k s => .yield (gen_gbKeptF b2.val.toArray (cpS ⟨v, v1, v2⟩) k s)) 0
        (b2.val.toArray.size - 1) [b2.val.toArray.back!] := by
  have hn1 : ∃ l1 : Usize, alloc.vec.Vec.len b2 - 1#usize = ok l1 ∧ l1.val = b2.val.length - 1 := by
    obtain ⟨c, hc', hcv⟩ := gen_usub (alloc.vec.Vec.len b2) 1#usize (by simp; omega)
    exact ⟨c, hc', by simpa using hcv⟩
  obtain ⟨l1, hl1, hl1v⟩ := hn1
  obtain ⟨l2, hl2, hl2v⟩ : ∃ l2 : Usize, alloc.vec.Vec.len b2 - 2#usize = ok l2 ∧ l2.val = b2.val.length - 2 := by
    obtain ⟨c, hc', hcv⟩ := gen_usub (alloc.vec.Vec.len b2) 2#usize (by simp; omega)
    exact ⟨c, hc', by simpa using hcv⟩
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec F64 × Usize => beatmap.mod_target_practice.generate_beats_loop3.body v v1 v2 b2 x.1 x.2) (·.2)
    (b2.val.length - 1) (by have := b2.property; omega)
    (fun x => x.1.val ≠ [] ∧ x.1.val.length ≤ x.2.val + 1)
    (fun x => x.1.val.reverse)
    (gen_gbKeptF b2.val.toArray (cpS ⟨v, v1, v2⟩))
    (fun y s => y.val.reverse = s)
    (by
      rintro ⟨kr, m⟩ ⟨hne, hlen⟩ hlt j1 hj1 hj1v
      simp only at hne hlen hlt hj1 hj1v ⊢
      have hm : m < l1 := by scalar_tac
      obtain ⟨i4, hi4, hi4v⟩ := gen_usub l2 m (by omega)
      have hi4l : i4.val < b2.val.length := by omega
      obtain ⟨i6, hi6, hi6v⟩ := gen_usub (alloc.vec.Vec.len kr) 1#usize (by
        have : kr.val.length ≠ 0 := by simpa using hne
        simp; omega)
      have hi6l : i6.val < kr.val.length := by
        have : kr.val.length ≠ 0 := by simpa using hne
        simp at hi6v; omega
      have hpush : kr.val.length < Usize.max := by have := b2.property; omega
      have hhead : kr.val.reverse.head! = kr.val[i6.val]'hi6l := by
        have hi6' : i6.val = kr.val.length - 1 := by simp at hi6v; omega
        have hne' : kr.val ≠ [] := hne
        conv_lhs => rw [← List.dropLast_append_getLast hne']
        simp [List.getLast_eq_getElem, hi6']
      have hB : b2.val.toArray[b2.val.toArray.size - 2 - m.val]! = b2.val[i4.val]'hi4l := by
        rw [getElem!_pos _ _ (by simp; omega)]; simp [hi4v, hl2v]
      unfold gen_gbKeptF
      rw [hB, hhead]
      by_cases hd : definitelyBigger (kr.val[i6.val]'hi6l - b2.val[i4.val]'hi4l)
          (((cpS ⟨v, v1, v2⟩).timingPointAt (b2.val[i4.val]'hi4l)).beatLength / 2) = true
      · refine ⟨(vpush kr (b2.val[i4.val]'hi4l) hpush, j1), ?_, rfl, by simp [hd], by simp, by simp; omega⟩
        simp only [beatmap.mod_target_practice.generate_beats_loop3.body, hl1, bind_ok, hm, if_true, hl2, hi4,
          vec_index_eq _ _ hi4l, hi6, vec_index_eq _ _ hi6l, float.F64.sub,
          beatmap.control_points.timing_point_at_refines ⟨v, v1, v2⟩ _ hc, cst_beatmap_mod_target_practice_D2, float.F64.div,
          tp_db, tpI]
        simp only [hd, if_true, vec_push_ok _ _ hpush, bind_ok, hj1]
      · refine ⟨(kr, j1), ?_, rfl, by simp [hd], hne, by simp; omega⟩
        simp only [beatmap.mod_target_practice.generate_beats_loop3.body, hl1, bind_ok, hm, if_true, hl2, hi4,
          vec_index_eq _ _ hi4l, hi6, vec_index_eq _ _ hi6l, float.F64.sub,
          beatmap.control_points.timing_point_at_refines ⟨v, v1, v2⟩ _ hc, cst_beatmap_mod_target_practice_D2, float.F64.div,
          tp_db, tpI]
        simp only [hd, Bool.false_eq_true, if_false, bind_ok, hj1])
    (by
      rintro ⟨kr, m⟩ ⟨hne, hlen⟩ hge
      simp only at hne hlen hge ⊢
      have : ¬ m < l1 := by scalar_tac
      have h' : ¬ m.val < l1.val := by omega
      exact ⟨kr, by simp only [beatmap.mod_target_practice.generate_beats_loop3.body, hl1, bind_ok, this, if_false], rfl⟩)
    (kr0, 0#usize) ⟨by simp [hk0], by simp [hk0]⟩ (by simp)
  refine ⟨y, by unfold beatmap.mod_target_practice.generate_beats_loop3; exact hl, ?_⟩
  rw [hv, hk0]
  simp only [List.reverse_singleton, List.size_toArray]
  congr 1
  simp [Array.back!, getElem!_pos, show b2.val.length - 1 < b2.val.length by omega]
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice

theorem beatmap.mod_target_practice.generate_beats_refines (pb : beatmap.playable.PlayableBeatmap)
    (orig : Slice beatmap.objects.OsuHitObject) (hne : 0 < pb.hit_objects.val.length)
    (hc : pb.control_points.timing_points.val.length < 2^31) (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.mod_target_practice.generate_beats pb orig = ok r ∧
      r.val.toArray = generateBeats (abs pb) (abs orig) := by
  obtain ⟨et, het, hetv⟩ := beatmap.mods.last_object_time_refines pb hne
  obtain ⟨y0, hy0, hy1, hy2, hy3, hy4⟩ := gen_gb_outer pb.control_points hc et h64
  have hne0 : (0#usize : Usize).val < pb.hit_objects.val.length := by simpa using hne
  obtain ⟨b1, hb1, hb1v⟩ := gen_gb_l1 (pb.hit_objects.val[(0#usize : Usize).val]'hne0).start_time y0.2.2.2
  obtain ⟨b2, hb2, hb2v⟩ := gen_gb_l2 pb.breaks orig b1
  have hB : gen_gbB (abs pb) (abs orig) = b2.val.toArray := by
    rw [hb2v, hb1v, hy4]
    unfold gen_gbB
    have e1 : (abs pb : PlayableBeatmap).controlPoints = cpS pb.control_points := rfl
    have e2 : Mods.lastObjectTime (abs pb) = et := hetv
    have e3 : (abs pb : PlayableBeatmap).hitObjects[0]!.startTime = (pb.hit_objects.val[(0#usize : Usize).val]'hne0).start_time := by
      show (abs pb.hit_objects : Array OsuHitObject)[0]!.startTime = _
      rw [gen_abs_get (β := OsuHitObject) pb.hit_objects 0 hne]; rfl
    rw [e1, e2, e3]; rfl
  rw [gen_gb_spec, hB]
  unfold beatmap.mod_target_practice.generate_beats
  simp only [vec_index_eq pb.hit_objects 0#usize (by simpa using hne), bind_ok, het]
  rw [show beatmap.mod_target_practice.generate_beats_loop0 pb.control_points et (alloc.vec.Vec.new F64) 0#usize =
    ok (y0.1, y0.2.1, y0.2.2.1, y0.2.2.2) from hy0]
  simp only [bind_ok, gen_uncurry_eq, hy1, hy2, hy3]
  rw [hb1]
  simp only [bind_ok, hb2]
  have hsz : (b2.val.toArray).size = b2.val.length := by simp
  by_cases h2 : b2.val.length < 2
  · have : alloc.vec.Vec.len b2 < 2#usize := by scalar_tac
    simp only [this, if_true, hsz, h2]
    exact ⟨b2, rfl, rfl⟩
  · have : ¬ alloc.vec.Vec.len b2 < 2#usize := by scalar_tac
    simp only [this, if_false, hsz, h2]
    obtain ⟨i2, hi2, hi2v⟩ := gen_usub (alloc.vec.Vec.len b2) 1#usize (by simp; omega)
    have hi2l : i2.val < b2.val.length := by simp at hi2v; omega
    have hpush : (alloc.vec.Vec.new F64).val.length < Usize.max := by simp [alloc.vec.Vec.new]; rw [usize_max_64 h64]; omega
    have hk0 : (vpush (alloc.vec.Vec.new F64) (b2.val[i2.val]'hi2l) hpush).val =
        [b2.val[b2.val.length - 1]'(by omega)] := by
      simp [alloc.vec.Vec.new]; congr 1
    obtain ⟨y, hy, hyv⟩ := gen_gb_l3 pb.control_points.timing_points pb.control_points.difficulty_points
      pb.control_points.effect_points hc b2 _ (by omega) hk0
    obtain ⟨z, hz, hzv⟩ := gen_gb_l4 y (alloc.vec.Vec.with_capacity F64 (alloc.vec.Vec.len y)) (alloc.vec.Vec.len y)
      (by simp) (by simp [alloc.vec.Vec.with_capacity])
    refine ⟨z, ?_, ?_⟩
    · simp only [hi2, bind_ok, vec_index_eq _ _ hi2l, vec_push_ok _ _ hpush, hy, hz]
    · rw [hzv]
      simp only [alloc.vec.Vec.with_capacity, List.nil_append, alloc.vec.Vec.len_val, List.take_length]
      rw [show (y.val).reverse = iterR (fun k s => .yield (gen_gbKeptF b2.val.toArray
          (abs pb : PlayableBeatmap).controlPoints k s)) 0 (b2.val.toArray.size - 1) [b2.val.toArray.back!] from hyv]
      simp [alloc.vec.Vec.new]
end OsuProofs

