/-
`beatmap::mod_target_practice` (Rust) refines `OsuModel.Beatmap.Mods.TargetPractice` (mods proof agent;
continues Post/TargetPractice.lean).
-/
import OsuProofs.Post.ModRandom
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

/-- `rng.NextSingle()` as lazer computes it (`(float)(NextDouble() * 1f)`); spec: the local `nextSingle` of
`TargetPractice.randomizeCirclePos`. -/
theorem beatmap.mod_target_practice.next_single_refines (r : net.random.State) (hs : stOk r) :
    ∃ f r', beatmap.mod_target_practice.next_single r = ok (f, r') ∧ stOk r' ∧
      (f, stS r') = (let (d, r2) := NetRandom.nextDouble (stS r); (F64.toF32 (d * F32.toF64 1), r2)) := by
  obtain ⟨d, r2, h1, hs1, he1⟩ := net.random.next_double_refines r hs
  refine ⟨F64.toF32 (d * F32.toF64 1), r2, ?_, hs1, ?_⟩
  · simp only [beatmap.mod_target_practice.next_single, h1, bind_ok, float.F32.from_bits, float.F32.to_f64,
      float.F64.mul, float.F64.to_f32]
    congr 3
  · rw [← he1]

/-- first `k ≥ from` with `mapped[k] = key` (`max from len` if none); no spec def (helper of `fixComboInfo`). -/
theorem beatmap.mod_target_practice.next_match_refines (mapped : Slice I32) (key : I32) :
    ∀ fr : Usize, ∃ r, beatmap.mod_target_practice.next_match mapped key fr = ok r ∧
      r.val = match (mapped.val.drop fr.val).findIdx? (fun x => decide (x = key)) with
        | some k => fr.val + k | none => max fr.val mapped.val.length := by
  intro fr
  unfold beatmap.mod_target_practice.next_match
  suffices h : ∀ k : Usize, ∃ r, beatmap.mod_target_practice.next_match_loop mapped key k false = ok r ∧
      r.val = match (mapped.val.drop k.val).findIdx? (fun x => decide (x = key)) with
        | some j => k.val + j | none => max k.val mapped.val.length by exact h fr
  intro k
  induction hk : mapped.val.length - k.val using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    unfold beatmap.mod_target_practice.next_match_loop
    rw [loop_unfold]
    by_cases hlt : k.val < mapped.val.length
    · have hl : k < Slice.len mapped := by show k.val < (Slice.len mapped).val; simpa using hlt
      have hd : mapped.val.drop k.val = mapped.val[k.val] :: mapped.val.drop (k.val + 1) := List.drop_eq_getElem_cons hlt
      have hidx := index_eq mapped k hlt
      generalize hx : mapped.val[k.val]'hlt = x at hidx hd
      by_cases he : x = key
      · subst he
        have hb1 : beatmap.mod_target_practice.next_match_loop.body mapped x k false = ok (.cont (k, true)) := by
          simp [beatmap.mod_target_practice.next_match_loop.body, hl, hidx]
        have hb2 : beatmap.mod_target_practice.next_match_loop.body mapped x k true = ok (.done k) := by
          simp [beatmap.mod_target_practice.next_match_loop.body]
        refine ⟨k, ?_, ?_⟩
        · simp only [hb1, bind_ok]; rw [loop_unfold]; simp only [hb2, bind_ok]
        · rw [hd]; simp [List.findIdx?_cons]
      · obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := mapped.property; omega)
        obtain ⟨r, hr, hrv⟩ := ih (mapped.val.length - k1.val) (by omega) k1 rfl
        refine ⟨r, ?_, ?_⟩
        · have hb3 : beatmap.mod_target_practice.next_match_loop.body mapped key k false = ok (.cont (k1, false)) := by
            simp [beatmap.mod_target_practice.next_match_loop.body, hl, hidx, he, hk1]
          simp only [hb3, bind_ok]
          unfold beatmap.mod_target_practice.next_match_loop at hr; exact hr
        · simp only [hk1v] at hrv; rw [hrv, hd]; simp only [List.findIdx?_cons]
          have : decide (x = key) = false := by simpa using he
          rw [this]
          simp only [Bool.false_eq_true, ite_false]
          cases h : List.findIdx? (fun x => decide (x = key)) (List.drop (k.val + 1) mapped.val) <;> simp
          · rw [Nat.max_eq_right (by omega), Nat.max_eq_right (by omega)]
          · rw [Nat.add_assoc, Nat.add_comm 1]
    · have hl : ¬ k < Slice.len mapped := by show ¬ k.val < (Slice.len mapped).val; simpa using hlt
      refine ⟨k, by simp [beatmap.mod_target_practice.next_match_loop.body, hl], ?_⟩
      rw [List.drop_eq_nil_of_le (by omega)]; simp; omega

theorem beatmap.mod_target_practice.node_index_from_time_refines (h : beatmap.objects.OsuHitObject) (t : F64) :
    ∃ r, beatmap.mod_target_practice.node_index_from_time h t = ok r ∧
      Mods.TargetPractice.nodeIndexFromTime (abs h) (abs t) = abs r := by
  have hd1 : beatmap.mod_target_practice.D1 = ok (1 : F64) := by
    unfold beatmap.mod_target_practice.D1; simp [float.F64.from_bits] <;> decide
  have hv : ∀ x : Int32, ((i32I x).val : Int) = x.toInt := fun x => by rw [← i32S_toInt, i32S_i32I]
  unfold beatmap.mod_target_practice.node_index_from_time Mods.TargetPractice.nodeIndexFromTime
  rw [ob_kind_abs]
  have hc : ∀ x : I32, F64.ofInt32 (i32S x) = F64.ofInt (IScalar.cast .I64 x).val := by
    intro x; simp [F64.ofInt32, i32S_toInt, IScalar.cast_val_eq]
  cases hk : h.kind with
  | Slider s =>
    obtain ⟨r, hr, hr2⟩ := beatmap.objects.span_count_refines s
    simp only [ob_abs_slider, hr, bind_ok, beatmap.objects.duration_refines, hd1, net.mathops.f64_round_refines]
    rw [show (abs s : SliderData).spanCount = i32S r from hr2, hc]
    simp [lift, float.F64.from_i64, float.F64.div, float.F64.sub, float.F64.abs, float.F64.le, float.F64.to_i32_sat]
    split <;> simp [abs]; decide
  | Circle =>
    simp only [ob_abs_circle, ob_abs_spinner, bind_ok, beatmap.objects.duration_refines, hd1, net.mathops.f64_round_refines]
    rw [show (1 : Int32) = i32S 1#i32 by decide, hc]
    simp [lift, float.F64.from_i64, float.F64.div, float.F64.sub, float.F64.abs, float.F64.le, float.F64.to_i32_sat]
    split <;> simp [abs]; decide
  | Spinner _ =>
    simp only [ob_abs_circle, ob_abs_spinner, bind_ok, beatmap.objects.duration_refines, hd1, net.mathops.f64_round_refines]
    rw [show (1 : Int32) = i32S 1#i32 by decide, hc]
    simp [lift, float.F64.from_i64, float.F64.div, float.F64.sub, float.F64.abs, float.F64.le, float.F64.to_i32_sat]
    split <;> simp [abs]; decide

/-- the sample-lookup predicate `pred` of `TargetPractice.checkHitSamples` -/
def tpSamplePredS (t : F64) (o : OsuHitObject) : Bool :=
  if F64.abs (t - o.startTime) ≤ Mods.TargetPractice.TIMING_PRECISION then true
  else if !o.isSlider then false
  else if !Mods.TargetPractice.almostBigger t o.startTime || !Mods.TargetPractice.almostBigger o.endTime t then false
  else Mods.TargetPractice.nodeIndexFromTime o (t - o.startTime) != -1

theorem beatmap.mod_target_practice.sample_pred_refines (o : beatmap.objects.OsuHitObject) (t : F64) :
    beatmap.mod_target_practice.sample_pred o t = ok (tpSamplePredS t (abs o)) := by
  have htp : beatmap.mod_target_practice.TIMING_PRECISION = ok Mods.TargetPractice.TIMING_PRECISION := by
    unfold beatmap.mod_target_practice.TIMING_PRECISION; simp only [float.F64.from_bits]; congr 1
  obtain ⟨ni, hni, hniv⟩ := beatmap.mod_target_practice.node_index_from_time_refines o (t - o.start_time)
  unfold beatmap.mod_target_practice.sample_pred tpSamplePredS
  simp only [float.F64.sub, float.F64.abs, htp, float.F64.le, bind_ok, beatmap.objects.is_slider_refines, tp_ab,
    beatmap.objects.end_time_refines]
  have hst : (abs o : OsuHitObject).startTime = o.start_time := rfl
  rw [hst]
  by_cases h1 : F64.abs (t - o.start_time) ≤ Mods.TargetPractice.TIMING_PRECISION
  · simp [h1]
  · simp only [h1, decide_false, Bool.false_eq_true, if_false]
    cases hs : (abs o : OsuHitObject).isSlider
    · simp
    · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
      cases ha : Mods.TargetPractice.almostBigger t o.start_time
      · simp
      · cases hb : Mods.TargetPractice.almostBigger (abs o : OsuHitObject).endTime t
        · simp
        · simp only [if_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false, hni, bind_ok]
          have hniv' : Mods.TargetPractice.nodeIndexFromTime (abs o) (t - o.start_time) = i32S ni := hniv
          rw [hniv']
          have hm1 : i32S (-1)#i32 = -1 := by decide
          congr 1
          by_cases hn : ni = (-1)#i32
          · subst hn; rw [hm1]; simp
          · have : i32S ni ≠ -1 := by rw [← hm1]; intro h; exact hn ((abs_i32S_inj _ _).mp h)
            rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq]; exact ⟨fun _ => this, fun _ => hn⟩


theorem tp_chs_find (orig : Slice beatmap.objects.OsuHitObject) (t : F64) :
    ∀ j : Usize, j.val ≤ orig.val.length →
      ∃ r, beatmap.mod_target_practice.check_hit_samples_loop0_loop0 orig t none j = ok r ∧
        r.map (·.val) = (((orig.val.map (abs : _ → OsuHitObject)).drop j.val).findIdx? (tpSamplePredS t)).map (· + j.val) := by
  intro j
  induction hk : orig.val.length - j.val using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    intro hle
    unfold beatmap.mod_target_practice.check_hit_samples_loop0_loop0
    rw [loop_unfold]
    by_cases hlt : j.val < orig.val.length
    · have hl : j < Slice.len orig := by show j.val < (Slice.len orig).val; simpa using hlt
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := orig.property; omega)
      have hd : (orig.val.map (abs : _ → OsuHitObject)).drop j.val =
          (abs (orig.val[j.val]'hlt) : OsuHitObject) :: (orig.val.map abs).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
      rw [hd, List.findIdx?_cons]
      cases hp : tpSamplePredS t (abs (orig.val[j.val]'hlt))
      · obtain ⟨r, hr, hrv⟩ := ih (orig.val.length - j1.val) (by omega) j1 rfl (by omega)
        have hb : beatmap.mod_target_practice.check_hit_samples_loop0_loop0.body orig t none j = ok (.cont (none, j1)) := by
          simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop0.body, core.option.Option.is_none, hl,
            index_eq orig j hlt, beatmap.mod_target_practice.sample_pred_refines, hp, hj1]
        refine ⟨r, ?_, ?_⟩
        · simp only [hb, bind_ok]; unfold beatmap.mod_target_practice.check_hit_samples_loop0_loop0 at hr; exact hr
        · rw [hrv, hj1v]; simp [Option.map_map, Function.comp_def]; congr 1; funext x; omega
      · have hb : beatmap.mod_target_practice.check_hit_samples_loop0_loop0.body orig t none j = ok (.cont (some j, j1)) := by
          simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop0.body, core.option.Option.is_none, hl,
            index_eq orig j hlt, beatmap.mod_target_practice.sample_pred_refines, hp, hj1]
        refine ⟨some j, ?_, by simp⟩
        simp only [hb, bind_ok]; rw [loop_unfold]
        simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop0.body, core.option.Option.is_none]
    · have hl : ¬ j < Slice.len orig := by show ¬ j.val < (Slice.len orig).val; simpa using hlt
      refine ⟨none, by simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop0.body,
        core.option.Option.is_none, hl], ?_⟩
      rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl

theorem tp_chs_last (orig : Slice beatmap.objects.OsuHitObject) (t : F64) (hN : orig.val.length < 2^31) :
    ∀ k : Usize, k.val ≤ orig.val.length →
      ∃ p, beatmap.mod_target_practice.check_hit_samples_loop0_loop1 orig t (-1)#i64 k false = ok p ∧
        (p.val = -1 ↔ ∀ x ∈ orig.val.take k.val, ¬ x.start_time < t) := by
  intro k
  induction hkk : k.val generalizing k with
  | zero =>
    intro hle
    have hk0 : ¬ k > 0#usize := by show ¬ (0#usize).val < k.val; simp; omega
    refine ⟨(-1)#i64, ?_, ?_⟩
    · unfold beatmap.mod_target_practice.check_hit_samples_loop0_loop1; rw [loop_unfold]
      simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop1.body, hk0]
    · simp
  | succ m ih =>
    intro hle
    have hk0 : k > 0#usize := by show (0#usize).val < k.val; simp; omega
    obtain ⟨k1, hk1, hk1v, -⟩ := eq_ok_of_spec (UScalar.sub_spec (x := k) (y := 1#usize) (by simp; omega))
    have hk1v' : k1.val = m := by simp at hk1v; omega
    have hkl : k1.val < orig.val.length := by omega
    have htake : orig.val.take (m + 1) = orig.val.take m ++ [orig.val[k1.val]'hkl] := by
      rw [List.take_succ, ← hk1v', List.getElem?_eq_getElem hkl]; simp
    by_cases hlt : (orig.val[k1.val]'hkl).start_time < t
    · obtain ⟨p, hp, hpv⟩ := eq_ok_of_spec (UScalar.hcast_inBounds_spec .I64 k1 (by simp [IScalar.max, I64.max_eq]; omega))
      refine ⟨p, ?_, ?_⟩
      · unfold beatmap.mod_target_practice.check_hit_samples_loop0_loop1; rw [loop_unfold]
        have hb : beatmap.mod_target_practice.check_hit_samples_loop0_loop1.body orig t (-1)#i64 k false =
            ok (.cont (p, k1, true)) := by
          simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop1.body, hk0, hk1, index_eq orig k1 hkl,
            float.F64.lt, hlt, hp]
        simp only [hb, bind_ok]; rw [loop_unfold]
        simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop1.body]
      · rw [htake]
        constructor
        · intro h; rw [hpv] at h; omega
        · intro h; exact absurd hlt (h _ (by simp))
    · obtain ⟨p, hp, hpv⟩ := ih k1 hk1v' (by omega)
      refine ⟨p, ?_, ?_⟩
      · unfold beatmap.mod_target_practice.check_hit_samples_loop0_loop1; rw [loop_unfold]
        have hb : beatmap.mod_target_practice.check_hit_samples_loop0_loop1.body orig t (-1)#i64 k false =
            ok (.cont ((-1)#i64, k1, false)) := by
          simp [beatmap.mod_target_practice.check_hit_samples_loop0_loop1.body, hk0, hk1, index_eq orig k1 hkl,
            float.F64.lt, hlt]
        simp only [hb, bind_ok]; unfold beatmap.mod_target_practice.check_hit_samples_loop0_loop1 at hp; exact hp
      · rw [hpv, htake]
        constructor
        · intro h x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact h x hx
          · rw [List.mem_singleton] at hx; subst hx; exact hlt
        · intro h x hx; exact h x (List.mem_append_left _ hx)


/-- does beat `t` pass the `addHitSamples` lookups of `TargetPractice.checkHitSamples` (no throw) -/
def tpChk (orig : Array OsuHitObject) (t : F64) : Bool :=
  match orig.find? (tpSamplePredS t) with
  | some o =>
    match o.kind with
    | .slider s => !(decide (Mods.TargetPractice.nodeIndexFromTime o (t - o.startTime) < 0) ||
        decide (Mods.TargetPractice.nodeIndexFromTime o (t - o.startTime) > s.repeatCount + 1))
    | _ => true
  | none => !(orig.size ≠ 0 && (orig.toList.reverse.findIdx? fun h => decide (h.startTime < t)).isNone)

theorem tp_chk_spec_aux (orig : Array OsuHitObject) (G : F64 → PUnit → Except String (ForInStep PUnit))
    (hG : ∀ t, (tpChk orig t = true ∧ G t () = .ok (.yield ())) ∨ (tpChk orig t = false ∧ ∃ e, G t () = .error e)) :
    ∀ (l : List F64), (∃ u, forIn l PUnit.unit G = .ok u) ↔ l.all (tpChk orig) = true := by
  intro l
  induction l with
  | nil => rw [List.forIn_nil]; simp [pure, Except.pure]
  | cons t ts ih =>
    rw [List.forIn_cons, List.all_cons]
    rcases hG t with ⟨h1, h2⟩ | ⟨h1, e, h2⟩
    · rw [h2, h1]; simp only [Bind.bind, Except.bind, Bool.true_and]; exact ih
    · rw [h2, h1]; simp [Bind.bind, Except.bind]

theorem tp_chk_spec (orig : Array OsuHitObject) (beats : Array F64) :
    (∃ u, Mods.TargetPractice.checkHitSamples orig beats = .ok u) ↔ beats.toList.all (tpChk orig) = true := by
  unfold Mods.TargetPractice.checkHitSamples
  rw [← Array.forIn_toList]
  have key : ∀ (m : Except String PUnit), (∃ u, (m >>= fun _ => (pure () : Except String Unit)) = .ok u) ↔ ∃ u, m = .ok u := by
    intro m; cases m <;> simp [Bind.bind, Except.bind, pure, Except.pure]
  rw [key]
  apply tp_chk_spec_aux
  intro t
  simp only []
  split
  · rename_i o ho
    have ho' : orig.find? (tpSamplePredS t) = some o := ho
    split
    · rename_i s hs
      split
      · rename_i hc
        right; refine ⟨?_, _, rfl⟩
        simp only [tpChk, ho', hs]; simp only [hc, Bool.not_true]
      · rename_i hc
        left; refine ⟨?_, rfl⟩
        simp only [tpChk, ho', hs]; simp_all
    · rename_i hs
      left; refine ⟨?_, rfl⟩
      simp only [tpChk, ho']; try (split <;> first | rfl | simp_all)
  · rename_i ho
    have ho' : orig.find? (tpSamplePredS t) = none := ho
    split
    all_goals
      rename_i hf
      split
      · rename_i hc
        right; refine ⟨?_, _, rfl⟩
        simp only [tpChk, ho', hf]
        revert hc; simp
        first | done | (intro h he; subst he; simp at h) | (intro h; exact Array.eq_empty_of_size_eq_zero (by omega))
      · rename_i hc
        left; refine ⟨?_, rfl⟩
        simp only [tpChk, ho', hf]
        revert hc; simp
        first | done | (intro h he; subst he; simp at h) | (intro h; exact Array.eq_empty_of_size_eq_zero (by omega))

theorem tp_chs_body (orig : Slice beatmap.objects.OsuHitObject) (beats : Slice F64) (hN : orig.val.length < 2^31)
    (bi bi1 : Usize) (hb : bi.val < beats.val.length) (hbi1 : bi + 1#usize = ok bi1) :
    (tpChk (abs orig) (beats.val[bi.val]'hb) = true →
      beatmap.mod_target_practice.check_hit_samples_loop0.body orig beats bi = ok (.cont bi1)) ∧
    (tpChk (abs orig) (beats.val[bi.val]'hb) = false →
      ∃ e, beatmap.mod_target_practice.check_hit_samples_loop0.body orig beats bi = ok (.done (.Err e))) := by
  have hbl : bi < Slice.len beats := by show bi.val < (Slice.len beats).val; simpa using hb
  generalize ht : beats.val[bi.val]'hb = t
  have hidx : Slice.index_usize beats bi = ok t := by rw [index_eq beats bi hb, ht]
  obtain ⟨fo, hfo, hfov⟩ := tp_chs_find orig t 0#usize (by simp)
  have hfind : (abs orig : Array OsuHitObject).find? (tpSamplePredS t) =
      (fo.map (fun i => (orig.val.map (abs : _ → OsuHitObject))[i.val]!)) := by
    rw [show (abs orig : Array OsuHitObject) = (orig.val.map abs).toArray from rfl, List.find?_toArray,
      find?_eq_findIdx?]
    simp only [List.drop_zero, show (0#usize : Usize).val = 0 from rfl, Nat.add_zero, Option.map_id'] at hfov
    rw [← hfov]; cases fo <;> rfl
  cases fo with
  | some oi =>
    have hoi : oi.val < orig.val.length := by
      have := findIdx?_lt _ _ oi.val (by simpa using hfov.symm); simpa using this
    have hget : (orig.val.map (abs : _ → OsuHitObject))[oi.val]! = abs (orig.val[oi.val]'hoi) := by
      rw [getElem!_pos _ _ (by simpa using hoi)]; simp
    simp only [Option.map_some, hget] at hfind
    generalize ho : orig.val[oi.val]'hoi = o at hfind
    have hoidx : Slice.index_usize orig oi = ok o := by rw [index_eq orig oi hoi, ho]
    obtain ⟨ni, hni, hniv⟩ := beatmap.mod_target_practice.node_index_from_time_refines o (t - o.start_time)
    cases hk : o.kind with
    | Slider s =>
      have hka : (abs o : OsuHitObject).kind = .slider (abs s) := by rw [ob_kind_abs, hk]; rfl
      have hspec : tpChk (abs orig) t = !(decide (i32S ni < 0) || decide (i32S ni > i32S s.repeat_count + 1)) := by
        simp only [tpChk, hfind, hka]
        rw [show Mods.TargetPractice.nodeIndexFromTime (abs o) (t - (abs o : OsuHitObject).startTime) = i32S ni from hniv]
        rfl
      have e0 : (0 : Int32) = i32S 0#i32 := by decide
      have e1 : i32S s.repeat_count + 1 = i32S (core.num.I32.wrapping_add s.repeat_count 1#i32) := by
        rw [i32S_wadd]; rfl
      rw [hspec, e0, e1]
      by_cases h0 : ni < 0#i32
      · have h0' : i32S ni < i32S 0#i32 := (abs_i32S_lt_iff _ _).mpr h0
        refine ⟨fun h => by simp [h0'] at h, fun _ => ⟨.Msg beatmap.errors.M_ARGUMENTOUTOFRANGEEXCEPTION_NODESAMPLES, ?_⟩⟩
        have h0v : ni.val < 0 := by simpa using h0
        simp [beatmap.mod_target_practice.check_hit_samples_loop0.body, hbl, hidx, hfo, hoidx, hk, float.F64.sub, hni, h0v]
      · have h0' : ¬ i32S ni < i32S 0#i32 := fun h => h0 ((abs_i32S_lt_iff _ _).mp h)
        by_cases h1 : ni > core.num.I32.wrapping_add s.repeat_count 1#i32
        · have h1' : i32S ni > i32S (core.num.I32.wrapping_add s.repeat_count 1#i32) := (abs_i32S_lt_iff _ _).mpr h1
          refine ⟨fun h => by simp [h1'] at h, fun _ => ⟨.Msg beatmap.errors.M_ARGUMENTOUTOFRANGEEXCEPTION_NODESAMPLES, ?_⟩⟩
          have h0v : ¬ ni.val < 0 := by simpa using h0
          have h1v := h1
          simp [lift] at h1v
          simp [beatmap.mod_target_practice.check_hit_samples_loop0.body, hbl, hidx, hfo, hoidx, hk, float.F64.sub, hni,
            h0v, h1v, lift]
        · have h1' : ¬ i32S ni > i32S (core.num.I32.wrapping_add s.repeat_count 1#i32) :=
            fun h => h1 ((abs_i32S_lt_iff _ _).mp h)
          refine ⟨fun _ => ?_, fun h => by simp [h0', h1'] at h⟩
          have h0v : ¬ ni.val < 0 := by simpa using h0
          have h1v := h1
          simp [lift] at h1v
          simp [beatmap.mod_target_practice.check_hit_samples_loop0.body, hbl, hidx, hfo, hoidx, hk, float.F64.sub, hni,
            h0v, h1v, lift, hbi1]
    | Circle =>
      have hka : (abs o : OsuHitObject).kind = .circle := by rw [ob_kind_abs, hk]; rfl
      have hspec : tpChk (abs orig) t = true := by simp only [tpChk, hfind, hka]
      refine ⟨fun _ => ?_, fun h => by rw [hspec] at h; cases h⟩
      simp [beatmap.mod_target_practice.check_hit_samples_loop0.body, hbl, hidx, hfo, hoidx, hk, hbi1]
    | Spinner sp =>
      have hka : (abs o : OsuHitObject).kind = .spinner (abs sp) := by rw [ob_kind_abs, hk]; rfl
      have hspec : tpChk (abs orig) t = true := by simp only [tpChk, hfind, hka]
      refine ⟨fun _ => ?_, fun h => by rw [hspec] at h; cases h⟩
      simp [beatmap.mod_target_practice.check_hit_samples_loop0.body, hbl, hidx, hfo, hoidx, hk, hbi1]
  | none =>
    simp only [Option.map_none] at hfind
    obtain ⟨p, hp, hpv⟩ := tp_chs_last orig t hN (Slice.len orig) (by simp)
    obtain ⟨n64, hn64, hn64v⟩ := eq_ok_of_spec (UScalar.hcast_inBounds_spec .I64 (Slice.len orig)
      (by simp [IScalar.max, I64.max_eq]; omega))
    have hone : (1#i64 : I64).val = 1 := by decide
    obtain ⟨n1, hn1, hn1v⟩ := dns_i64_sub n64 1#i64 (by rw [hone, hn64v]; simp; omega) (by rw [hone, hn64v]; simp; omega)
    have hlen : (Slice.len orig).val = orig.val.length := by simp
    rw [hlen, List.take_of_length_le (le_refl _)] at hpv
    have hiff : ((abs orig : Array OsuHitObject).toList.reverse.findIdx? fun h => decide (h.startTime < t)).isNone =
        decide (∀ x ∈ orig.val, ¬ x.start_time < t) := by
      rw [Bool.eq_iff_iff, Option.isNone_iff_eq_none, List.findIdx?_eq_none_iff]
      simp [abs]
    have hspec : tpChk (abs orig) t = !(decide (orig.val.length ≠ 0) && decide (∀ x ∈ orig.val, ¬ x.start_time < t)) := by
      simp only [tpChk, hfind, hiff]; simp [abs]
    rw [hspec]
    have hbody : beatmap.mod_target_practice.check_hit_samples_loop0.body orig beats bi =
        (if p != n1 then (if p = (-1)#i64 then ok (.done (.Err (.Msg beatmap.errors.M_ARGUMENTOUTOFRANGEEXCEPTION_GETCLOSESTHI)))
          else ok (.cont bi1)) else ok (.cont bi1)) := by
      simp only [beatmap.mod_target_practice.check_hit_samples_loop0.body, hbl, if_true, hidx, hfo, bind_ok, hp, hn64, hn1,
        hbi1]
    rw [hbody]
    by_cases hm : p = (-1)#i64
    · have hall : ∀ x ∈ orig.val, ¬ x.start_time < t := hpv.mp (by rw [hm]; decide)
      by_cases hz : orig.val.length = 0
      · have hpn : (p != n1) = false := by
          rw [bne_eq_false_iff_eq]; apply IScalar.eq_of_val_eq; rw [hm, hn1v, hone, hn64v, hlen, hz]; decide
        refine ⟨fun _ => by rw [if_neg (by rw [hpn]; decide)], fun h => by simp [hz] at h⟩
      · have hpn : (p != n1) = true := by
          rw [bne_iff_ne, ne_eq]; intro h; have := congrArg IScalar.val h
          rw [hm, hn1v, hone, hn64v, hlen] at this; simp at this; omega
        have hd : decide (∀ x ∈ orig.val, ¬ x.start_time < t) = true := decide_eq_true hall
        refine ⟨fun h => by simp [hz, hd] at h,
          fun _ => ⟨.Msg beatmap.errors.M_ARGUMENTOUTOFRANGEEXCEPTION_GETCLOSESTHI, by rw [if_pos hpn, if_pos hm]⟩⟩
    · have hnall : ¬ ∀ x ∈ orig.val, ¬ x.start_time < t := fun h => hm (IScalar.eq_of_val_eq (by rw [hpv.mpr h]; decide))
      refine ⟨fun _ => ?_, fun h => by simp [hnall] at h⟩
      by_cases hpn : (p != n1) = true
      · rw [if_pos hpn, if_neg hm]
      · rw [if_neg hpn]


theorem tp_chs_loop (orig : Slice beatmap.objects.OsuHitObject) (beats : Slice F64) (hN : orig.val.length < 2^31) :
    ∀ bi : Usize, bi.val ≤ beats.val.length →
      ∃ r, beatmap.mod_target_practice.check_hit_samples_loop0 orig beats bi = ok r ∧
        (r = .Ok () ↔ (beats.val.drop bi.val).all (tpChk (abs orig)) = true) ∧ (∀ u, r = .Ok u ∨ ∃ e, r = .Err e) := by
  intro bi
  induction hk : beats.val.length - bi.val using Nat.strong_induction_on generalizing bi with
  | _ k ih =>
    intro hle
    unfold beatmap.mod_target_practice.check_hit_samples_loop0
    rw [loop_unfold]
    by_cases hlt : bi.val < beats.val.length
    · obtain ⟨bi1, hbi1, hbi1v⟩ := usize_add_one bi (by have := beats.property; omega)
      obtain ⟨hok, herr⟩ := tp_chs_body orig beats hN bi bi1 hlt hbi1
      have hd : beats.val.drop bi.val = (beats.val[bi.val]'hlt) :: beats.val.drop (bi.val + 1) :=
        List.drop_eq_getElem_cons hlt
      rw [hd, List.all_cons]
      cases hc : tpChk (abs orig) (beats.val[bi.val]'hlt)
      · obtain ⟨e, he⟩ := herr hc
        refine ⟨.Err e, by simp only [he, bind_ok], by simp, fun _ => Or.inr ⟨e, rfl⟩⟩
      · obtain ⟨r, hr, hrv, hrc⟩ := ih (beats.val.length - bi1.val) (by omega) bi1 rfl (by omega)
        refine ⟨r, ?_, by rw [hrv, hbi1v]; simp, hrc⟩
        simp only [hok hc, bind_ok]; unfold beatmap.mod_target_practice.check_hit_samples_loop0 at hr; exact hr
    · have hl : ¬ bi < Slice.len beats := by show ¬ bi.val < (Slice.len beats).val; simpa using hlt
      refine ⟨.Ok (), by simp [beatmap.mod_target_practice.check_hit_samples_loop0.body, hl], ?_, fun _ => Or.inl rfl⟩
      rw [List.drop_eq_nil_of_le (by omega)]; simp

/-- `addHitSamples` lookups; spec `TargetPractice.checkHitSamples` (both reject on the same beats) -/
theorem beatmap.mod_target_practice.check_hit_samples_refines (orig : Slice beatmap.objects.OsuHitObject)
    (beats : Slice F64) (hN : orig.val.length < 2^31) :
    ∃ r, beatmap.mod_target_practice.check_hit_samples orig beats = ok r ∧
      hRel (fun _ => ()) r (Mods.TargetPractice.checkHitSamples (abs orig) (abs beats)) := by
  obtain ⟨r, hr, hrv, hrc⟩ := tp_chs_loop orig beats hN 0#usize (by simp)
  refine ⟨r, by unfold beatmap.mod_target_practice.check_hit_samples; exact hr, ?_⟩
  have hspec := tp_chk_spec (abs orig) (abs beats)
  have hb : (abs beats : Array F64).toList = beats.val := by simp [abs]
  rw [hb] at hspec
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hrv
  cases hs : Mods.TargetPractice.checkHitSamples (abs orig) (abs beats) with
  | ok u =>
    have hall := hspec.mp ⟨u, hs⟩
    rw [hrv.mpr hall]; rfl
  | error e =>
    have hn : ¬ beats.val.all (tpChk (abs orig)) = true := fun h => by
      obtain ⟨u, hu⟩ := hspec.mpr h; rw [hs] at hu; cases hu
    rcases hrc () with h | ⟨e', h⟩
    · subst h; exact absurd (hrv.mp rfl) hn
    · subst h; trivial

end OsuProofs
