/-
Generator mods, part 9 (gen agent): Target Practice `randomize_circle_pos` (spec normal form `gen_rc_spec`;
overlap/preceding loops, the 100000-try placement loop, the per-object loop) and the top-level
`beatmap::mod_target_practice::apply` (`apply_refines`, size hypotheses only).
-/
import OsuProofs.Post.GenTP2
import OsuProofs.Post.ObjectsApply
import OsuProofs.Post.Playable
import OsuProofs.Post.ModsB
import OsuProofs.Beatmap.DotNetSort
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice Mods.Reposition

theorem gen_forIn_eq {S : Type} (n : Nat) (init : S) (F : Nat → S → Id (ForInStep S)) (G : Nat → S → ForInStep S)
    (h : ∀ k s, F k s = G k s) : forIn (m := Id) [:n] init F = iterR G 0 n init := by
  rw [forIn_range_iterR, Nat.sub_zero]
  have : F = G := funext fun k => funext fun s => h k s
  rw [this]

abbrev GenRcT := NetRandom.State × F32 × F32 × Nat × Vec2

/-- one try of `randomizeCirclePos`'s placement loop (spec normal form) -/
def gen_rcTryF (lastPos : Vec2) (radius : F64) (prec : Array Vec2) (_ : Nat) (s : GenRcT) : ForInStep GenRcT :=
  let rd : NetRandom.State × F32 := if s.2.2.2.1 > 0 then
      ((NetRandom.sample s.1).2, TWO_PI * ((NetRandom.sample s.1).1 * F32.toF64 1).toF32) else (s.1, s.2.1)
  let rel := rotateAwayFromEdge lastPos ⟨s.2.2.1 * rd.2.cos, s.2.2.1 * rd.2.sin⟩ EDGE_ROTATION_MULTIPLIER
  let pos := clampToPlayfield (lastPos + rel) radius.toF32
  let dist := if (s.2.2.2.1 + 1) % 10 == 0 then s.2.2.1 * 0.9 else s.2.2.1
  let st : GenRcT := (rd.1, atan2f rel.y rel.x, dist, s.2.2.2.1 + 1, pos)
  if (!(decide (radius * 2 ≤ dist.toF64) && prec.any fun p => decide ((p.distance pos).toF64 < radius * 2))) = true
  then .done st else .yield st

abbrev GenRcS := Array OsuHitObject × NetRandom.State × F32

/-- one object of `randomizeCirclePos` (spec normal form) -/
def gen_rcOutF (maxCI : Int32) (i : Nat) (s : GenRcS) : GenRcS :=
  let obj := s.1[i]!
  let lastPos := if (i == 0) = true then centre else s.1[i - 1]!.position
  let d0 : F32 := if (maxCI == 0) = true then obj.radius.toF32
    else mapRange (F32.ofInt32 obj.comboIndex) 0 (F32.ofInt32 maxCI) obj.radius.toF32 MAX_BASE_DISTANCE
  let d1 := if obj.newCombo = true then d0 * 1.5 else d0
  let d2 := if obj.kiai = true then d1 * 1.2 else d1
  let prec := (s.1.extract (if i ≥ OVERLAP_CHECK_COUNT then i - OVERLAP_CHECK_COUNT else 0) i).map (·.position)
  let t := iterR (gen_rcTryF lastPos obj.radius prec) 0 100000 (s.2.1, s.2.2, DISTANCE_CAP.min d2, 0, obj.position)
  let hos := s.1.set! i { obj with position := t.2.2.2.2 }
  let nd := NetRandom.sample t.1
  if obj.lastInCombo = true then (hos, nd.2, TWO_PI * (nd.1 * F32.toF64 1).toF32)
  else (hos, nd.2, t.2.1 + t.2.2.1 / DISTANCE_CAP * ((nd.1 * F32.toF64 1).toF32 * TWO_PI - PI))

theorem gen_rc_spec (hos : Array OsuHitObject) (r : NetRandom.State) (h : hos.size ≠ 0) :
    randomizeCirclePos hos r = (iterR (fun i s => .yield (gen_rcOutF hos.back!.comboIndex i s)) 0 hos.size
      (hos, (NetRandom.sample r).2, TWO_PI * ((NetRandom.sample r).1 * F32.toF64 1).toF32)).1 := by
  unfold randomizeCirclePos
  simp only [Id.run]
  have h' : (hos.size == 0) = false := by simpa using h
  simp only [h', Bool.false_eq_true, if_false]
  rw [gen_forIn_eq _ _ _ (fun i s => .yield (gen_rcOutF hos.back!.comboIndex i s))]
  · rfl
  intro i s
  unfold gen_rcOutF
  simp only []
  by_cases c1 : (i == 0) = true <;> by_cases c2 : (hos.back!.comboIndex == 0) = true <;>
    by_cases c3 : s.1[i]!.newCombo = true <;> by_cases c4 : s.1[i]!.kiai = true <;>
    simp only [c1, c2, c3, c4, if_true, if_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals
    rw [gen_forIn_eq _ _ _ (gen_rcTryF _ _ _)]
    · by_cases c5 : s.1[i]!.lastInCombo = true <;> simp only [c5, if_true, if_false, Bool.false_eq_true] <;> rfl
    · intro k t
      unfold gen_rcTryF
      simp only []
      repeat' gen_case_ite
      all_goals rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice Mods.Reposition

theorem gen_ov_loop (d2 rad : F64) (prec : alloc.vec.Vec net.osutk.Vector2) (pos : net.osutk.Vector2) :
    ∀ (ov : Bool) (z : Usize), ∃ r,
      beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0 d2 rad prec pos ov z = ok r ∧
      r = (ov || (prec.val.drop z.val).any (fun p => decide (((bv2S p).distance (bv2S pos)).toF64 < rad * d2))) := by
  intro ov z
  induction hn : prec.val.length - z.val using Nat.strong_induction_on generalizing ov z with
  | _ n ih =>
    unfold beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0
    rw [loop_unfold]
    by_cases hk : z.val < prec.val.length
    · obtain ⟨z1, hz1, hz1v⟩ := usize_add_one z (by have := prec.property; omega)
      have hs : ∃ s1, (if decide (((bv2S (prec.val[z.val]'hk)).distance (bv2S pos)).toF64 < rad * d2) = true
          then ok true else ok ov) = ok s1 ∧
          s1 = (ov || decide (((bv2S (prec.val[z.val]'hk)).distance (bv2S pos)).toF64 < rad * d2)) := by
        by_cases h : ((bv2S (prec.val[z.val]'hk)).distance (bv2S pos)).toF64 < rad * d2 <;> simp [h]
      obtain ⟨s1, hs1, hs1v⟩ := hs
      obtain ⟨r, hr, hrv⟩ := ih (prec.val.length - z1.val) (by omega) s1 z1 rfl
      refine ⟨r, ?_, ?_⟩
      · have hb : beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0.body d2 rad prec pos ov z =
            ok (.cont (s1, z1)) := by
          simp only [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0.body, vec_lt_len_iff, hk,
            if_true, vec_index_eq _ _ hk, bind_ok, beatmap.vector2.distance_refines, float.F32.to_f64, float.F64.mul,
            float.F64.lt, hs1, hz1]
        dsimp only
        rw [hb]; simp only [bind_ok]
        unfold beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0 at hr
        exact hr
      · rw [hrv, hs1v, hz1v, List.drop_eq_getElem_cons hk]
        simp only [List.any_cons, Bool.or_assoc]
    · refine ⟨ov, ?_, by rw [List.drop_eq_nil_of_le (by omega)]; simp⟩
      have : ¬ z < alloc.vec.Vec.len prec := by rw [vec_lt_len_iff]; exact hk
      simp [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0.body, this]

theorem gen_prec_loop (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (i : Usize) (hi : i.val ≤ hos.val.length) :
    ∀ (pr : alloc.vec.Vec net.osutk.Vector2) (q : Usize), q.val ≤ i.val → pr.val.length + (i.val - q.val) ≤ i.val →
      ∃ r, beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0 hos i pr q = ok r ∧
        r.val = pr.val ++ ((hos.val.drop q.val).take (i.val - q.val)).map (·.position) := by
  intro pr q
  induction hn : i.val - q.val using Nat.strong_induction_on generalizing pr q with
  | _ n ih =>
    intro hq hlen
    unfold beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0
    rw [loop_unfold]
    by_cases hk : q.val < i.val
    · have hkl : q.val < hos.val.length := by omega
      obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by have := hos.property; omega)
      have hpush : pr.val.length < Usize.max := by have := hos.property; omega
      obtain ⟨r, hr, hrv⟩ := ih (i.val - q1.val) (by omega) (vpush pr (hos.val[q.val]'hkl).position hpush) q1 rfl
        (by omega) (by simp; omega)
      refine ⟨r, ?_, ?_⟩
      · have hb : beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0.body hos i pr q =
            ok (.cont (vpush pr (hos.val[q.val]'hkl).position hpush, q1)) := by
          simp only [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0.body, show q < i by scalar_tac,
            if_true, vec_index_eq _ _ hkl, bind_ok, vec_push_ok _ _ hpush, hq1]
        dsimp only
        rw [hb]; simp only [bind_ok]
        unfold beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0 at hr
        exact hr
      · rw [hrv, vpush_val, hq1v, List.append_assoc]
        congr 1
        rw [List.drop_eq_getElem_cons hkl, show n = (i.val - (q.val + 1)) + 1 by omega, List.take_succ_cons]
        simp
    · refine ⟨pr, ?_, by rw [show n = 0 by omega]; simp⟩
      have : ¬ q < i := by scalar_tac
      simp [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0.body, this]

theorem gen_ov_eq (d2 rad : F64) (prec : alloc.vec.Vec net.osutk.Vector2) (pos : net.osutk.Vector2) :
    beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1_loop0 d2 rad prec pos false 0#usize =
      ok (prec.val.any (fun p => decide (((bv2S p).distance (bv2S pos)).toF64 < rad * d2))) := by
  obtain ⟨r, hr, hrv⟩ := gen_ov_loop d2 rad prec pos false 0#usize
  rw [hr, hrv]; simp

theorem gen_ns_eq (r : net.random.State) (h : stOk r) :
    beatmap.mod_target_practice.next_single r = ok (((gen_ndR r).1 * F32.toF64 1).toF32, (gen_ndR r).2) := by
  simp only [beatmap.mod_target_practice.next_single, gen_nd_ok r h, bind_ok, gen_uncurry_eq, float.F32.from_bits,
    float.F32.to_f64, float.F64.mul, float.F64.to_f32]
  congr 3

theorem gen_any_prec (prec : alloc.vec.Vec net.osutk.Vector2) (f : Vec2 → Bool) :
    (prec.val.map bv2S).toArray.any f = prec.val.any (fun p => f (bv2S p)) := by
  simp [List.any_map]; rfl

theorem gen_v2add (a b : Vec2) : Vec2.add a b = a + b := rfl

theorem gen_bv2S_mk (a b : F32) : bv2S ({ x := a, y := b } : net.osutk.Vector2) = ({ x := a, y := b } : Vec2) := rfl

theorem gen_bool_contra3 {a b : Bool} (h1 : a = false) (h2 : b = true) (h : a = b) : False := by
  subst h; simp_all

theorem gen_bool_contra4 {a b : Bool} (h1 : ¬ a = true) (h2 : b = true) (h : a = b) : False := by
  subst h; simp_all

open Lean Elab Tactic Meta in
/-- close `False` from hypotheses `a = false`, `b = true` with `a`, `b` definitionally equal -/
elab "gen_bool_clash" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  for d1 in lctx do
    if d1.isImplementationDetail then continue
    let t1 ← instantiateMVars d1.type
    let (a, neg) ← match t1.eq? with
      | some (_, a, f) => if f.isConstOf ``Bool.false then pure (a, false) else continue
      | none => match t1.not? with
        | some t1' => match t1'.eq? with
          | some (_, a, tr) => if tr.isConstOf ``Bool.true then pure (a, true) else continue
          | none => continue
        | none => continue
    for d2 in lctx do
      if d2.isImplementationDetail then continue
      let t2 ← instantiateMVars d2.type
      let some (_, b, tr) := t2.eq? | continue
      unless tr.isConstOf ``Bool.true do continue
      if ← isDefEq a b then
        let pf ← mkAppM (if neg then ``gen_bool_contra4 else ``gen_bool_contra3) #[d1.toExpr, d2.toExpr, ← mkEqRefl a]
        let tgt ← g.getType
        g.assign (← mkAppOptM ``False.elim #[tgt, pf])
        replaceMainGoal []
        return
  throwError "gen_bool_clash failed"

theorem gen_ite_nand {α} (a b : Bool) (x y : α) :
    (if (!(a && b)) = true then x else y) = (if a = true then (if b = true then y else x) else x) := by
  cases a <;> cases b <;> rfl

theorem gen_c09 : float.F32.from_bits 1063675494#u32 = ok (0.9 : F32) := by
  simp only [float.F32.from_bits]; congr 1

theorem gen_mod10 (x : U64) : ∃ m : U64, x % 10#u64 = ok m ∧ m.val = x.val % 10 := by
  obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (UScalar.rem_spec x (y := 10#u64) (by simp))
  exact ⟨m, hm, by simpa using hmv⟩

theorem gen_try_done (lastPos : net.osutk.Vector2) (objR : F64) (prec : alloc.vec.Vec net.osutk.Vector2)
    (r : net.random.State) (dr ds : F32) (tc : U64) (ps : net.osutk.Vector2) (fu : I32) :
    beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1.body TWO_PI 2 lastPos objR objR.toF32 prec
      r dr ds tc ps fu false = ok (.done (r, dr, ds, ps)) := by
  simp [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1.body]

theorem gen_try_loop (lastPos : net.osutk.Vector2) (objR : F64) (prec : alloc.vec.Vec net.osutk.Vector2)
    (rng : net.random.State) (hok : stOk rng) (dir dist : F32) (pos : net.osutk.Vector2) :
    ∃ y, beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1 TWO_PI rng dir 2 lastPos objR objR.toF32 dist
        prec 0#u64 pos 0#i32 true = ok y ∧ stOk y.1 ∧
      (stS y.1, y.2.1, y.2.2.1, bv2S y.2.2.2) = (fun t : GenRcT => (t.1, t.2.1, t.2.2.1, t.2.2.2.2))
        (iterR (gen_rcTryF (bv2S lastPos) objR (prec.val.map bv2S).toArray) 0 100000 (stS rng, dir, dist, 0, bv2S pos)) := by
  have := loop_iterR (fun t : net.random.State × F32 × F32 × U64 × net.osutk.Vector2 × I32 × Bool =>
      beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1.body TWO_PI 2 lastPos objR objR.toF32 prec
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2)
    (gen_rcTryF (bv2S lastPos) objR (prec.val.map bv2S).toArray) 100000 (fun t => t.2.2.2.2.2.1.val.toNat)
    (fun t s => t.2.2.2.2.2.2 = true ∧ stOk t.1 ∧ stS t.1 = s.1 ∧ t.2.1 = s.2.1 ∧ t.2.2.1 = s.2.2.1 ∧
      t.2.2.2.1.val = s.2.2.2.1 ∧ bv2S t.2.2.2.2.1 = s.2.2.2.2 ∧ (t.2.2.2.1.val : Int) = t.2.2.2.2.2.1.val ∧
      0 ≤ t.2.2.2.2.2.1.val ∧ t.2.2.2.2.2.1.val ≤ 100000)
    (fun y s => stOk y.1 ∧ (stS y.1, y.2.1, y.2.2.1, bv2S y.2.2.2) = (s.1, s.2.1, s.2.2.1, s.2.2.2.2))
    (by
      rintro ⟨r, dr, ds, tc, ps, fu, go⟩ ⟨s1, s2, s3, s4, s5⟩ ⟨hgo, hok, h1, h2, h3, h4, h5, h6, h7, h8⟩ hlt
      simp only at hgo hok h1 h2 h3 h4 h5 h6 h7 h8 hlt ⊢
      subst hgo h1 h2 h3 h5
      have hfu : fu < 100000#i32 := by scalar_tac
      obtain ⟨tc1, htc1, htc1v⟩ := gen_u64_add_one tc (by scalar_tac)
      obtain ⟨m, hm, hmv⟩ := gen_mod10 tc1
      obtain ⟨fu1, hfu1, hfu1v⟩ : ∃ fu1 : I32, fu + 1#i32 = ok fu1 ∧ fu1.val = fu.val + 1 := by
        obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (I32.add_spec (x := fu) (y := 1#i32) (by scalar_tac) (by scalar_tac))
        exact ⟨z, hz, by simpa using hzv⟩
      have hm0 : (m = 0#u64) ↔ ((tc.val + 1) % 10 == 0) = true := by
        constructor
        · intro h; have := congrArg (·.val) h; simp at this; simp; omega
        · intro h; simp at h; apply UScalar.eq_of_val_eq; simp; omega
      have hidx : (fu1.val.toNat) = fu.val.toNat + 1 := by omega
      unfold gen_rcTryF
      simp only [← h4]
      by_cases ht : tc > 0#u64
      on_goal 1 =>
        have ht' : tc.val > 0 := by scalar_tac
        simp only [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1.body, if_true, hfu, ht, bind_ok,
          gen_uncurry_eq, gen_ns_eq _ hok, float.F32.mul, float.F32.cos, float.F32.sin,
          cst_beatmap_mod_target_practice_EDGE_ROTATION_MULTIPLIER, beatmap.mod_random.rotate_away_from_edge_refines,
          beatmap.mod_random.atan2f_refines, beatmap.vector2.add_refines,
          beatmap.mod_target_practice.clamp_to_playfield_refines, htc1, hm, gen_c09, gen_ov_eq, float.F64.mul,
          float.F32.to_f64, float.F64.le, hfu1]
        simp only [ht', if_true, gen_nd_eq r hok, EDGE_ROTATION_MULTIPLIER, gen_any_prec, hm0, bv2S_I, gen_v2add,
          gen_bv2S_mk, OsuModel.Net.F32.cos, OsuModel.Net.F32.sin, gen_ite_nand]
      on_goal 2 =>
        have ht' : ¬ tc.val > 0 := by scalar_tac
        simp only [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1.body, if_true, hfu, ht, bind_ok,
          if_false, gen_uncurry_eq, float.F32.mul, float.F32.cos, float.F32.sin,
          cst_beatmap_mod_target_practice_EDGE_ROTATION_MULTIPLIER, beatmap.mod_random.rotate_away_from_edge_refines,
          beatmap.mod_random.atan2f_refines, beatmap.vector2.add_refines,
          beatmap.mod_target_practice.clamp_to_playfield_refines, htc1, hm, gen_c09, gen_ov_eq, float.F64.mul,
          float.F32.to_f64, float.F64.le, hfu1]
        simp only [ht', if_false, EDGE_ROTATION_MULTIPLIER, gen_any_prec, hm0, bv2S_I, gen_v2add,
          gen_bv2S_mk, OsuModel.Net.F32.cos, OsuModel.Net.F32.sin, gen_ite_nand]
      all_goals
        by_cases hmc : ((tc.val + 1) % 10 == 0) = true <;>
          simp only [hmc, hm0, if_true, if_false, ite_true, ite_false, Bool.false_eq_true, bind_ok]
      all_goals (repeat' gen_case_ite2 [hm0, bind_ok])
      all_goals
        refine ⟨fun s' h => ?_, fun s' h => ?_⟩
        all_goals first
          | simp only [show ((tc.val + 1) % 10 == 0) = true by assumption, if_true, ite_true] at h
          | simp only [show ¬ ((tc.val + 1) % 10 == 0) = true by assumption, if_false, ite_false, Bool.false_eq_true] at h
          | skip
        all_goals first
          | (cases h; done)
          | (cases h
             refine ⟨_, rfl, hidx, rfl, ?_, rfl, rfl, rfl, by first | rw [htc1v] | (simp only []; rw [htc1v]) | simp [htc1v], rfl,
               by first | omega | (simp only []; omega), by first | omega | (simp only []; omega),
               by first | omega | (simp only []; omega)⟩
             first | exact hok | exact gen_nd_st _ hok)
          | (cases h
             refine ⟨?_, Or.inr ⟨_, rfl, ?_⟩, ?_⟩
             rotate_left
             · simp
               try rfl
             · exact ⟨by first | exact hok | exact gen_nd_st _ hok, rfl⟩)
          | (exfalso; gen_bool_clash))
    (by
      rintro ⟨r, dr, ds, tc, ps, fu, go⟩ s ⟨hgo, hok, h1, h2, h3, h4, h5, h6, h7, h8⟩ hge
      simp only at hgo hok h1 h2 h3 h4 h5 h6 h7 h8 hge ⊢
      subst hgo
      have : ¬ fu < 100000#i32 := by scalar_tac
      refine ⟨(r, dr, ds, ps), by simp [beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1.body, this], hok, ?_⟩
      simp only [h1, h2, h3, h5])
    (rng, dir, dist, 0#u64, pos, 0#i32, true) (stS rng, dir, dist, 0, bv2S pos)
    ⟨rfl, hok, rfl, rfl, rfl, rfl, rfl, rfl, by simp, by simp⟩ (by simp)
  obtain ⟨y, hl, hq1, hq2⟩ := this
  exact ⟨y, by unfold beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1; exact hl, hq1, hq2⟩
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice Mods.Reposition

theorem gen_f32_i32 (x : I32) : float.F32.from_i64 (IScalar.cast .I64 x) = ok (F32.ofInt32 (i32S x)) := by
  simp [float.F32.from_i64, F32.ofInt32, i32S_toInt, IScalar.cast_val_eq]

theorem gen_mr (a b c d e : F32) :
    beatmap.mod_target_practice.map_range a b c d e = ok (mapRange a b c d e) := by
  obtain ⟨r, hr, hv⟩ := beatmap.mod_target_practice.map_range_refines a b c d e
  rw [hr]; congr 1; exact hv.symm

theorem gen_c15 : float.F32.from_bits 1069547520#u32 = ok (1.5 : F32) := by
  simp only [float.F32.from_bits]; congr 1
theorem gen_c12 : float.F32.from_bits 1067030938#u32 = ok (1.2 : F32) := by
  simp only [float.F32.from_bits]; congr 1

theorem gen_extract_eq (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (lo i : Nat) (h : lo ≤ i) :
    (((hos.val.drop lo).take (i - lo)).map (·.position) |>.map bv2S).toArray =
      ((abs hos : Array OsuHitObject).extract lo i).map (·.position) := by
  apply Array.ext
  · simp [abs]
  · intro n h1 h2
    simp [abs, List.getElem_take, List.getElem_drop, Array.getElem_extract] at h1 h2 ⊢

instance : Inhabited (alloc.vec.Vec net.osutk.Vector2) := ⟨alloc.vec.Vec.new _⟩
noncomputable instance : Inhabited (net.random.State × F32 × F32 × net.osutk.Vector2) := ⟨(Classical.choice inferInstance, 0, 0, ⟨0, 0⟩)⟩

noncomputable def gen_precR (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (i lo : Usize) :
    alloc.vec.Vec net.osutk.Vector2 :=
  gen_val (beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0 hos i (alloc.vec.Vec.new _) lo)
theorem gen_prec_ok (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (i lo : Usize) (h1 : lo.val ≤ i.val)
    (h2 : i.val ≤ hos.val.length) :
    beatmap.mod_target_practice.randomize_circle_pos_loop0_loop0 hos i (alloc.vec.Vec.new _) lo = ok (gen_precR hos i lo) ∧
      (gen_precR hos i lo).val = ((hos.val.drop lo.val).take (i.val - lo.val)).map (·.position) := by
  obtain ⟨r, hr, hrv⟩ := gen_prec_loop hos i h2 (alloc.vec.Vec.new _) lo h1 (by simp [alloc.vec.Vec.new])
  have := gen_val_eq _ ⟨_, hr⟩
  rw [hr] at this
  have e := Result.ok_injective this
  unfold gen_precR; rw [hr, ← e]; exact ⟨rfl, by simpa [alloc.vec.Vec.new] using hrv⟩

noncomputable def gen_tryR (lastPos : net.osutk.Vector2) (objR : F64) (prec : alloc.vec.Vec net.osutk.Vector2)
    (rng : net.random.State) (dir dist : F32) (pos : net.osutk.Vector2) : net.random.State × F32 × F32 × net.osutk.Vector2 :=
  gen_val (beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1 TWO_PI rng dir 2 lastPos objR objR.toF32 dist
    prec 0#u64 pos 0#i32 true)
theorem gen_tryR_ok (lastPos : net.osutk.Vector2) (objR : F64) (prec : alloc.vec.Vec net.osutk.Vector2)
    (rng : net.random.State) (hok : stOk rng) (dir dist : F32) (pos : net.osutk.Vector2) :
    beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1 TWO_PI rng dir 2 lastPos objR objR.toF32 dist
        prec 0#u64 pos 0#i32 true = ok (gen_tryR lastPos objR prec rng dir dist pos) ∧
      stOk (gen_tryR lastPos objR prec rng dir dist pos).1 ∧
      (stS (gen_tryR lastPos objR prec rng dir dist pos).1, (gen_tryR lastPos objR prec rng dir dist pos).2.1,
        (gen_tryR lastPos objR prec rng dir dist pos).2.2.1, bv2S (gen_tryR lastPos objR prec rng dir dist pos).2.2.2) =
      (fun t : GenRcT => (t.1, t.2.1, t.2.2.1, t.2.2.2.2))
        (iterR (gen_rcTryF (bv2S lastPos) objR (prec.val.map bv2S).toArray) 0 100000 (stS rng, dir, dist, 0, bv2S pos)) := by
  obtain ⟨y, hy, h1, h2⟩ := gen_try_loop lastPos objR prec rng hok dir dist pos
  have := gen_val_eq _ ⟨_, hy⟩
  rw [hy] at this
  have e := Result.ok_injective this
  unfold gen_tryR; rw [hy, ← e]; exact ⟨rfl, h1, h2⟩

theorem gen_c0f : float.F32.from_bits 0#u32 = ok (0 : F32) := by
  simp only [float.F32.from_bits]; congr 1

theorem gen_ite_ok {α} (c : Prop) [Decidable c] (a b : α) : (if c then ok a else ok b) = ok (if c then a else b) := by
  split <;> rfl
theorem gen_dcap : beatmap.mod_target_practice.DISTANCE_CAP = ok DISTANCE_CAP := by
  unfold beatmap.mod_target_practice.DISTANCE_CAP Mods.TargetPractice.DISTANCE_CAP
  simp only [float.F32.from_bits]; congr 1
theorem gen_mbd : beatmap.mod_target_practice.MAX_BASE_DISTANCE = ok MAX_BASE_DISTANCE := by
  unfold beatmap.mod_target_practice.MAX_BASE_DISTANCE Mods.TargetPractice.MAX_BASE_DISTANCE
  simp only [float.F32.from_bits]; congr 1
theorem gen_mci0 (m : I32) : (m = 0#i32) ↔ (i32S m == 0) = true := by
  have e : (0 : Int32) = i32S 0#i32 := by decide
  rw [e]; simp [abs_i32S_inj]
theorem gen_tryR_eq (lastPos : net.osutk.Vector2) (objR : F64) (prec : alloc.vec.Vec net.osutk.Vector2)
    (rng : net.random.State) (hok : stOk rng) (dir dist : F32) (pos : net.osutk.Vector2) :
    beatmap.mod_target_practice.randomize_circle_pos_loop0_loop1 TWO_PI rng dir 2 lastPos objR objR.toF32 dist
        prec 0#u64 pos 0#i32 true = ok (gen_tryR lastPos objR prec rng dir dist pos) :=
  (gen_tryR_ok lastPos objR prec rng hok dir dist pos).1

theorem gen_rc_loop (hos0 : alloc.vec.Vec beatmap.objects.OsuHitObject) (mci : I32)
    (rng0 : net.random.State) (hok0 : stOk rng0) (dir0 : F32) :
    ∃ y, beatmap.mod_target_practice.randomize_circle_pos_loop0 hos0 TWO_PI rng0 dir0 mci 2 0#usize = ok y ∧
      (abs y : Array OsuHitObject) = (iterR (fun k s => .yield (gen_rcOutF (i32S mci) k s)) 0 hos0.val.length
        ((abs hos0 : Array OsuHitObject), stS rng0, dir0)).1 := by
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec beatmap.objects.OsuHitObject × net.random.State × F32 × Usize =>
      beatmap.mod_target_practice.randomize_circle_pos_loop0.body TWO_PI mci 2 x.1 x.2.1 x.2.2.1 x.2.2.2) (·.2.2.2)
    hos0.val.length (by have := hos0.property; omega)
    (fun x => stOk x.2.1 ∧ x.1.val.length = hos0.val.length)
    (fun x => ((abs x.1 : Array OsuHitObject), stS x.2.1, x.2.2.1))
    (gen_rcOutF (i32S mci))
    (fun y s => (abs y : Array OsuHitObject) = s.1)
    (by
      rintro ⟨hos, rng, dir, i⟩ ⟨hok, hlen⟩ hlt j1 hj1 hj1v
      simp only at hok hlen hlt hj1 hj1v ⊢
      have hi : i.val < hos.val.length := by omega
      have hga := gen_abs_get (β := OsuHitObject) hos i.val hi
      have hgr := gen_rad_abs (hos.val[i.val]'hi)
      simp only [beatmap.mod_target_practice.randomize_circle_pos_loop0.body, vec_lt_len_iff, hi, if_true,
        vec_index_eq _ _ hi, bind_ok, gen_rad_ok, float.F64.to_f32, gen_f32_i32, gen_c0f, lift,
        gen_mbd, gen_mr, gen_c15, gen_c12, float.F32.mul,
        gen_dcap, net.mathops.f32_min_refines]
      unfold gen_rcOutF
      simp only [hga, ← hgr]
      have hoc : beatmap.mod_target_practice.OVERLAP_CHECK_COUNT = 5#usize := by
        unfold beatmap.mod_target_practice.OVERLAP_CHECK_COUNT; rfl
      have hoc' : OVERLAP_CHECK_COUNT = 5 := rfl
      simp only [hoc, hoc']
      obtain ⟨lp, hlp, hlpv⟩ : ∃ lp, (if i = 0#usize then beatmap.mod_random.CENTRE else do
          let i2 ← i - 1#usize
          let oho ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice beatmap.objects.OsuHitObject) hos i2
          ok oho.position) = ok lp ∧
          bv2S lp = (if (i.val == 0) = true then centre else (abs hos : Array OsuHitObject)[i.val - 1]!.position) := by
        by_cases c1 : i.val = 0
        · have c1r : i = 0#usize := UScalar.eq_of_val_eq (by simpa using c1)
          exact ⟨bv2I centre, by simp only [c1r, if_true, mr2_CENTRE], by simp [c1]⟩
        · have c1r : ¬ i = 0#usize := fun h => c1 (by rw [h]; rfl)
          obtain ⟨i2, hi2, hi2v⟩ := gen_usub i 1#usize (by simp; omega)
          have hi2l : i2.val < hos.val.length := by simp at hi2v; omega
          refine ⟨(hos.val[i2.val]'hi2l).position, by simp only [c1r, if_false, hi2, bind_ok, vec_index_eq _ _ hi2l], ?_⟩
          have : (i.val == 0) = false := by simp [c1]
          simp only [this, Bool.false_eq_true, if_false]
          rw [gen_abs_get (β := OsuHitObject) hos (i.val - 1) (by omega)]
          simp at hi2v; simp only [hi2v]; rfl
      obtain ⟨lo, hlo, hlov⟩ : ∃ lo : Usize, (if i ≥ 5#usize then i - 5#usize else ok 0#usize) = ok lo ∧
          lo.val = (if i.val ≥ 5 then i.val - 5 else 0) := by
        by_cases c : i.val ≥ 5
        · obtain ⟨z, hz, hzv⟩ := gen_usub i 5#usize (by simp; omega)
          exact ⟨z, by simp only [show i ≥ 5#usize by scalar_tac, if_true, hz], by simp at hzv; simp [c, hzv]⟩
        · exact ⟨0#usize, by simp only [show ¬ i ≥ 5#usize by scalar_tac, if_false], by simp [c]⟩
      have hlo1 : lo.val ≤ i.val := by rw [hlov]; split <;> omega
      obtain ⟨hpr, hprv⟩ := gen_prec_ok hos i lo hlo1 (by omega)
      rw [hlp]
      simp only [bind_ok, gen_ite_ok, gen_mci0, hlo, hpr, gen_tryR_eq _ _ _ _ hok]
      have ha1 : ∀ o : beatmap.objects.OsuHitObject, (abs o : OsuHitObject).kiai = o.kiai := fun _ => rfl
      have ha2 : ∀ o : beatmap.objects.OsuHitObject, (abs o : OsuHitObject).newCombo = o.new_combo := fun _ => rfl
      have ha3 : ∀ o : beatmap.objects.OsuHitObject, (abs o : OsuHitObject).comboIndex = i32S o.combo_index := fun _ => rfl
      have ha4 : ∀ o : beatmap.objects.OsuHitObject, (abs o : OsuHitObject).position = bv2S o.position := fun _ => rfl
      have ha5 : ∀ o : beatmap.objects.OsuHitObject, (abs o : OsuHitObject).lastInCombo = o.last_in_combo := fun _ => rfl
      simp only [ha1, ha2, ha3, ha4, ha5, ← hlpv, ← hlov]
      rw [← gen_extract_eq hos lo.val i.val hlo1, ← hprv]
      have htr := gen_tryR_ok lp (gen_radR (↑hos)[↑i]) (gen_precR hos i lo) rng hok dir
      generalize gen_tryR lp (gen_radR (↑hos)[↑i]) (gen_precR hos i lo) rng dir = T at htr ⊢
      simp only [Prod.mk.injEq] at htr
      generalize gen_rcTryF (bv2S lp) (gen_radR hos[i]) (List.map bv2S (gen_precR hos i lo).val).toArray = F at htr ⊢
      have e1 : ∀ d p, (iterR F 0 100000 (stS rng, dir, d, 0, bv2S p)).1 = stS (T d p).1 := fun d p => ((htr d p).2.2.1).symm
      have e2 : ∀ d p, (iterR F 0 100000 (stS rng, dir, d, 0, bv2S p)).2.1 = (T d p).2.1 := fun d p => ((htr d p).2.2.2.1).symm
      have e3 : ∀ d p, (iterR F 0 100000 (stS rng, dir, d, 0, bv2S p)).2.2.1 = (T d p).2.2.1 := fun d p => ((htr d p).2.2.2.2.1).symm
      have e4 : ∀ d p, (iterR F 0 100000 (stS rng, dir, d, 0, bv2S p)).2.2.2.2 = bv2S (T d p).2.2.2 := fun d p => ((htr d p).2.2.2.2.2).symm
      simp only [e1, e2, e3, e4]
      generalize hTT : T _ _ = TT
      have hokT : stOk TT.1 := hTT ▸ (htr _ _).2.1
      clear e1 e2 e3 e4 hTT htr
      obtain ⟨r1, d1, s1, p1⟩ := TT
      simp only at hokT ⊢
      have hi' : i.val < (alloc.vec.Vec.set hos i { (hos.val[i.val]'hi) with position := p1 }).val.length := by
        simp [vec_set_val', hi]
      simp only [vec_index_mut_eq _ _ hi, bind_ok, gen_uncurry_eq, vec_index_eq _ _ hi', vec_set_val',
        List.getElem_set_self, gen_ns_eq _ hokT, gen_nd_eq _ hokT, mr2_PI, float.F32.div, float.F32.sub, float.F32.add]
      by_cases hl : (hos.val[i.val]'hi).last_in_combo = true
      · simp only [hl, if_true, bind_ok, gen_uncurry_eq, hj1]
        refine ⟨_, rfl, rfl, ?_, gen_nd_st _ hokT, by simp [hlen]⟩
        rw [gen_abs_set]; try rfl
      · simp only [hl, Bool.false_eq_true, if_false, bind_ok, gen_uncurry_eq, hj1]
        refine ⟨_, rfl, rfl, ?_, gen_nd_st _ hokT, by simp [hlen]⟩
        rw [gen_abs_set]; try rfl)
    (by
      rintro ⟨hos, rng, dir, i⟩ ⟨hok, hlen⟩ hge
      simp only at hok hlen hge ⊢
      have : ¬ i < alloc.vec.Vec.len hos := by rw [vec_lt_len_iff]; omega
      exact ⟨hos, by simp [beatmap.mod_target_practice.randomize_circle_pos_loop0.body, this], rfl⟩)
    (hos0, rng0, dir0, 0#usize) ⟨hok0, rfl⟩ (by simp)
  exact ⟨y, by unfold beatmap.mod_target_practice.randomize_circle_pos_loop0; exact hl, hv⟩
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl
open Mods.TargetPractice Mods.Reposition

theorem beatmap.mod_target_practice.randomize_circle_pos_refines
    (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (rng : net.random.State) (hok : stOk rng) :
    ∃ r, beatmap.mod_target_practice.randomize_circle_pos hos rng = ok r ∧
      (abs r : Array OsuHitObject) = randomizeCirclePos (abs hos) (stS rng) := by
  by_cases h0 : hos.val.length = 0
  · have h0' : alloc.vec.Vec.len hos = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [h0]
    refine ⟨hos, by simp only [beatmap.mod_target_practice.randomize_circle_pos, h0', if_true], ?_⟩
    unfold randomizeCirclePos
    have : ((abs hos : Array OsuHitObject).size == 0) = true := by simp [abs, h0]
    simp only [Id.run, this, if_true]; rfl
  · have h0' : ¬ alloc.vec.Vec.len hos = 0#usize := by
      intro h; apply h0; have := congrArg UScalar.val h; simpa using this
    obtain ⟨i2, hi2, hi2v⟩ := gen_usub (alloc.vec.Vec.len hos) 1#usize (by simp; omega)
    have hi2l : i2.val < hos.val.length := by simp at hi2v; omega
    obtain ⟨y, hy, hyv⟩ := gen_rc_loop hos (hos.val[i2.val]'hi2l).combo_index (gen_ndR rng).2 (gen_nd_st rng hok)
      (TWO_PI * ((gen_ndR rng).1 * F32.toF64 1).toF32)
    refine ⟨y, ?_, ?_⟩
    · simp only [beatmap.mod_target_practice.randomize_circle_pos, h0', if_false, mr_two_pi, bind_ok,
        gen_ns_eq rng hok, gen_uncurry_eq, float.F32.mul, hi2, vec_index_eq _ _ hi2l,
        cst_beatmap_mod_target_practice_D2]
      exact hy
    · have hs : (abs hos : Array OsuHitObject).size ≠ 0 := by simp [abs, h0]
      rw [gen_rc_spec _ _ hs, hyv, gen_nd_eq rng hok]
      have hb : (abs hos : Array OsuHitObject).back!.comboIndex = i32S (hos.val[i2.val]'hi2l).combo_index := by
        rw [Array.back!, gen_abs_get (β := OsuHitObject) hos _ (by simp [abs] at *; omega)]
        simp at hi2v; simp only [abs, List.size_toArray, List.length_map, hi2v]
      have hsz : (abs hos : Array OsuHitObject).size = hos.val.length := by simp [abs]
      rw [hb, hsz]
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_f64z : float.F64.from_bits 0#u64 = ok (0 : F64) := by
  simp only [float.F64.from_bits]; congr 1

theorem gen_tpa_done (d : beatmap.types.Difficulty) (cpi : beatmap.control_points.ControlPointInfo)
    (beats : alloc.vec.Vec F64) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (k : Usize)
    (hk : beats.val.length ≤ k.val) :
    beatmap.mod_target_practice.apply_loop d cpi beats hos k none = ok (hos, none) := by
  unfold beatmap.mod_target_practice.apply_loop
  rw [loop_unfold]
  have : ¬ k < alloc.vec.Vec.len beats := by rw [vec_lt_len_iff]; omega
  simp [beatmap.mod_target_practice.apply_loop.body, this]

theorem gen_tpa_err (d : beatmap.types.Difficulty) (cpi : beatmap.control_points.ControlPointInfo)
    (beats : alloc.vec.Vec F64) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (k : Usize)
    (c0 c1 : beatmap.objects.OsuHitObject) (e : beatmap.hit_object_parser.DecodeError)
    (hc : beatmap.objects.object_default beatmap.objects.ObjectKind.Circle 0 (bv2I Vec2.zero) = ok c0)
    (hA : beatmap.objects.apply_defaults cpi d c0 = ok (.Err e, c1))
    (hk : k.val < beats.val.length) :
    beatmap.mod_target_practice.apply_loop d cpi beats hos k none = ok (hos, some e) := by
  unfold beatmap.mod_target_practice.apply_loop
  rw [loop_unfold]
  have h1 : k < alloc.vec.Vec.len beats := by rw [vec_lt_len_iff]; omega
  obtain ⟨k1, hk1, -⟩ := usize_add_one k (by have := beats.property; omega)
  have hb : beatmap.mod_target_practice.apply_loop.body d cpi beats hos k none = ok (.cont (hos, k1, some e)) := by
    simp only [beatmap.mod_target_practice.apply_loop.body, core.option.Option.is_none, Option.isNone_none, if_true, h1, gen_f64z,
      bm_vector2_ZERO, hc, hA, bind_ok, gen_uncurry_eq, hk1]
  have hb2 : beatmap.mod_target_practice.apply_loop.body d cpi beats hos k1 (some e) = ok (.done (hos, some e)) := by
    simp [beatmap.mod_target_practice.apply_loop.body, core.option.Option.is_none]
  dsimp only
  rw [hb]; simp only [bind_ok]
  rw [loop_unfold]; dsimp only
  rw [hb2]; simp only [bind_ok]

theorem gen_tpa_ok (d : beatmap.types.Difficulty) (cpi : beatmap.control_points.ControlPointInfo)
    (beats : alloc.vec.Vec F64) (c0 c1 : beatmap.objects.OsuHitObject) (u : Unit)
    (hc : beatmap.objects.object_default beatmap.objects.ObjectKind.Circle 0 (bv2I Vec2.zero) = ok c0)
    (hA : beatmap.objects.apply_defaults cpi d c0 = ok (.Ok u, c1)) :
    ∀ (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (k : Usize), k.val ≤ beats.val.length →
      hos.val.length + (beats.val.length - k.val) ≤ beats.val.length →
      ∃ y, beatmap.mod_target_practice.apply_loop d cpi beats hos k none = ok (y, none) ∧
        y.val = hos.val ++ (beats.val.drop k.val).map (fun b => { c1 with start_time := b }) := by
  intro hos k
  induction hn : beats.val.length - k.val using Nat.strong_induction_on generalizing hos k with
  | _ n ih =>
    intro hk hlen
    by_cases hlt : k.val < beats.val.length
    · obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := beats.property; omega)
      have hpush : hos.val.length < Usize.max := by have := beats.property; omega
      obtain ⟨w, hw, hwv⟩ := push_eq hos { c1 with start_time := beats.val[k.val]'hlt } hpush
      obtain ⟨y, hy, hyv⟩ := ih (beats.val.length - k1.val) (by omega) w k1 rfl (by omega) (by rw [hwv]; simp; omega)
      refine ⟨y, ?_, ?_⟩
      · unfold beatmap.mod_target_practice.apply_loop
        rw [loop_unfold]
        have h1 : k < alloc.vec.Vec.len beats := by rw [vec_lt_len_iff]; omega
        have hb : beatmap.mod_target_practice.apply_loop.body d cpi beats hos k none = ok (.cont (w, k1, none)) := by
          simp only [beatmap.mod_target_practice.apply_loop.body, core.option.Option.is_none, Option.isNone_none, if_true, h1, gen_f64z,
            bm_vector2_ZERO, hc, hA, bind_ok, gen_uncurry_eq, hk1, vec_index_eq _ _ hlt, hw]
        dsimp only
        rw [hb]; simp only [bind_ok]
        unfold beatmap.mod_target_practice.apply_loop at hy
        exact hy
      · rw [hyv, hwv, hk1v, List.append_assoc]
        congr 1
        rw [List.drop_eq_getElem_cons hlt, List.map_cons]; rfl
    · refine ⟨hos, gen_tpa_done d cpi beats hos k (by omega), ?_⟩
      simp [show beats.val.length - k.val = 0 by omega, List.drop_eq_nil_of_le (show beats.val.length ≤ k.val by omega)]

theorem gen_tpl_ok (c : OsuHitObject) : ∀ (l : List F64) (acc : Array OsuHitObject),
    forIn (m := Except String) l acc (fun b s => Except.ok (ForInStep.yield (s.push { c with startTime := b }))) =
      .ok (acc ++ (l.map fun b => { c with startTime := b }).toArray) := by
  intro l
  induction l with
  | nil => intro acc; simp [pure, Except.pure]
  | cons b l ih =>
    intro acc
    rw [List.forIn_cons]
    simp only [Bind.bind, Except.bind]
    rw [ih]; congr 1; simp

theorem gen_tpl_err (e : String) (b : F64) (l : List F64) (acc : Array OsuHitObject) :
    forIn (m := Except String) (b :: l) acc (fun b s => do
      let c ← (Except.error e : Except String OsuHitObject)
      pure (ForInStep.yield (s.push { c with startTime := b }))) = .error e := by
  rw [List.forIn_cons]; rfl

theorem gen_ad_circle (cpi : ControlPointInfo) (d : Difficulty) (h0 : OsuHitObject) (hk : h0.kind = .circle)
    (r : OsuHitObject) (hr : applyDefaults cpi d h0 = .ok r) : r.nested.size < 2^31 := by
  unfold applyDefaults at hr
  simp only [hk] at hr
  simp [Bind.bind, Except.bind, pure, Except.pure] at hr
  subst hr
  simp [sortNested, listSort]

theorem gen_tp_loop (d : beatmap.types.Difficulty) (cpi : beatmap.control_points.ControlPointInfo)
    (beats : alloc.vec.Vec F64)
    (hce : cpi.effect_points.val.length < 2^31) (hct : cpi.timing_points.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) :
    ∃ y err, beatmap.mod_target_practice.apply_loop d cpi beats
        (alloc.vec.Vec.with_capacity beatmap.objects.OsuHitObject (alloc.vec.Vec.len beats)) 0#usize none = ok (y, err) ∧
      (match err with
       | none => forIn (m := Except String) beats.val (#[] : Array OsuHitObject) (fun b s => do
            let c ← applyDefaults (abs cpi) (abs d) { kind := .circle, startTime := 0, position := Vec2.zero }
            pure (ForInStep.yield (s.push { c with startTime := b }))) = .ok (abs y)
       | some _ => ∃ m, forIn (m := Except String) beats.val (#[] : Array OsuHitObject) (fun b s => do
            let c ← applyDefaults (abs cpi) (abs d) { kind := .circle, startTime := 0, position := Vec2.zero }
            pure (ForInStep.yield (s.push { c with startTime := b }))) = .error m) := by
  obtain ⟨c0, hc0, hc0v⟩ := beatmap.objects.object_default_refines .Circle 0 (bv2I Vec2.zero)
  have hc0v' : ({ kind := .circle, startTime := 0, position := Vec2.zero } : OsuHitObject) = abs c0 := by
    rw [← hc0v]; simp [bv2S_I]; try rfl
  obtain ⟨e1, c1, hA, hrel⟩ := beatmap.objects.apply_defaults_refines cpi d c0 hce hct
    (by
      intro s hs
      have := congrArg OsuHitObject.kind hc0v
      rw [show (abs c0 : OsuHitObject).kind = abs c0.kind from rfl, hs] at this
      first | (simp [abs] at this) | exact nomatch this | cases this) h64
    (fun r hr => gen_ad_circle _ _ _ (by rw [← hc0v']) r hr)
  rw [← hc0v'] at hrel
  have hw : (alloc.vec.Vec.with_capacity beatmap.objects.OsuHitObject (alloc.vec.Vec.len beats)).val = [] := by
    simp [alloc.vec.Vec.with_capacity]
  cases e1 with
  | Ok u =>
    have hrel' := gen_hrel_ok hrel
    obtain ⟨y, hy, hyv⟩ := gen_tpa_ok d cpi beats c0 c1 u hc0 hA _ 0#usize (by simp) (by rw [hw]; simp)
    refine ⟨y, none, hy, ?_⟩
    simp only
    rw [hrel']
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [gen_tpl_ok]
    congr 1
    apply Array.ext'
    simp [abs, hyv, hw]
  | Err e =>
    obtain ⟨m, hm⟩ := gen_hrel_err hrel
    cases hb : beats.val with
    | nil =>
      refine ⟨_, none, gen_tpa_done d cpi beats _ 0#usize (by simp [hb]), ?_⟩
      simp [hw, abs, pure, Except.pure]
    | cons b l =>
      refine ⟨_, some e, gen_tpa_err d cpi beats _ 0#usize c0 c1 e hc0 hA (by simp [hb]), ?_⟩
      refine ⟨m, ?_⟩
      rw [hm]
      exact gen_tpl_err m b l _
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_ssb_merge_len {α : Type} (key : α → F64) :
    ∀ (fuel : Nat) (xs ys : List α), (stableSortBy.merge key xs ys fuel).length = xs.length + ys.length := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; simp [stableSortBy.merge]
  | succ k ih =>
    intro xs ys
    cases xs with
    | nil => simp [stableSortBy.merge]
    | cons x xs' =>
      cases ys with
      | nil => simp [stableSortBy.merge]
      | cons y ys' =>
        simp only [stableSortBy.merge]
        split
        · simp only [List.length_cons, ih]; omega
        · simp only [List.length_cons, ih]; omega

theorem gen_ssb_sort_len {α : Type} (key : α → F64) :
    ∀ (fuel : Nat) (xs : List α), (stableSortBy.sort key xs fuel).length = xs.length := by
  intro fuel
  induction fuel with
  | zero => intro xs; simp [stableSortBy.sort]
  | succ k ih =>
    intro xs
    simp only [stableSortBy.sort]
    split
    · rfl
    · rw [gen_ssb_merge_len, ih, ih, ← List.length_append, List.take_append_drop]

theorem gen_ssb_size {α : Type} (key : α → F64) (a : Array α) : (stableSortBy key a).size = a.size := by
  unfold stableSortBy; simp [gen_ssb_sort_len]

theorem beatmap.mod_target_practice.apply_refines (seed : I32) (idx : Usize) (pb : beatmap.playable.PlayableBeatmap)
    (hN : pb.hit_objects.val.length < 2^31)
    (hce : pb.control_points.effect_points.val.length < 2^31) (hct : pb.control_points.timing_points.val.length < 2^31)
    (hm : pb.mod_states.val.length < Usize.max) (hep : pb.epoch.val < Usize.max)
    (h64 : System.Platform.numBits = 64) :
    ∃ e r, beatmap.mod_target_practice.apply seed idx pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e (Mods.TargetPractice.apply (i32S seed) (abs idx) (abs pb)) := by
  obtain ⟨rng, hr, hrok, hrv⟩ := net.random.create_refines seed
  have e1 : (abs pb : PlayableBeatmap).hitObjects = (abs pb.hit_objects : Array OsuHitObject) := rfl
  by_cases h0 : pb.hit_objects.val.length = 0
  · have h0' : alloc.vec.Vec.len pb.hit_objects = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [h0]
    obtain ⟨w, hw, hwv⟩ := push_eq pb.mod_states (idx, beatmap.playable.ModState.FirstObject none) hm
    refine ⟨.Ok (), { pb with mod_states := w }, ?_, ?_⟩
    · simp only [beatmap.mod_target_practice.apply, hr, bind_ok, h0', if_true, hw]
    · unfold Mods.TargetPractice.apply
      have : ((abs pb : PlayableBeatmap).hitObjects.size == 0) = true := by rw [e1]; simp [abs, h0]
      simp only [this, if_true]
      show _ = _
      simp [abs, hwv]
  · have h0' : ¬ alloc.vec.Vec.len pb.hit_objects = 0#usize := by
      intro h; apply h0; have := congrArg UScalar.val h; simpa using this
    have hcl := vec_clone_id beatmap.objects.OsuHitObject.Insts.CoreCloneClone pl_ho_clone pb.hit_objects
    obtain ⟨o1, ho1, ho1v⟩ := beatmap.dotnet.stable_sort_by_refines beatmap.objects.OsuHitObject.Insts.CoreCloneClone
      pl_ho_clone beatmap.objects.OsuHitObject.Insts.Osu_eval_coreBeatmapDotnetSortKey (·.start_time) (fun _ => rfl)
      pb.hit_objects hN
    have hso : stableSortBy (·.startTime) (abs pb.hit_objects : Array OsuHitObject) = (abs o1 : Array OsuHitObject) := by
      have : (abs pb.hit_objects : Array OsuHitObject) = pb.hit_objects.val.toArray.map (abs : _ → OsuHitObject) := by
        apply Array.ext'; simp [abs]
      rw [this, stableSortBy_map,
        show ((·.startTime) ∘ (abs : beatmap.objects.OsuHitObject → OsuHitObject)) = (·.start_time) from rfl, ← ho1v]
      apply Array.ext'; simp [abs]
    have ho1l : o1.val.length = pb.hit_objects.val.length := by
      have := congrArg Array.size hso; simp [abs, gen_ssb_size] at this; omega
    obtain ⟨bt, hbt, hbtv⟩ := beatmap.mod_target_practice.generate_beats_refines pb (alloc.vec.Vec.deref o1)
      (by omega) hct h64
    obtain ⟨y, err, hy, hyv⟩ := gen_tp_loop pb.difficulty pb.control_points bt hce hct h64
    rw [gen_abs_deref] at hbtv
    have hsz : ((abs pb : PlayableBeatmap).hitObjects.size == 0) = false := by rw [e1]; simp [abs, h0]
    obtain ⟨SP, hSP⟩ : ∃ SP, Mods.TargetPractice.apply (i32S seed) (abs idx) (abs pb) = SP := ⟨_, rfl⟩
    rw [hSP]
    unfold Mods.TargetPractice.apply at hSP
    simp only [hsz, Bool.false_eq_true, if_false] at hSP
    have e2 : (abs pb : PlayableBeatmap).controlPoints = (abs pb.control_points : ControlPointInfo) := rfl
    have e3 : (abs pb : PlayableBeatmap).difficulty = (abs pb.difficulty : Difficulty) := rfl
    rw [e1, hso, ← hbtv, List.forIn_toArray, e2, e3] at hSP
    subst hSP
    cases err with
    | some e =>
      refine ⟨.Err e, pb, ?_, ?_⟩
      · simp only [beatmap.mod_target_practice.apply, hr, bind_ok, h0', if_false, hcl, ho1, hbt, hy, gen_uncurry_eq]
      · obtain ⟨m, hm'⟩ := hyv
        rw [hm']; try trivial
    | none =>
      simp only at hyv
      rw [hyv]; simp only [Bind.bind, Except.bind]
      have hdb : (abs (alloc.vec.Vec.deref bt) : Array F64) = bt.val.toArray := by
        apply Array.ext'; simp [abs, gen_deref_val]
      obtain ⟨r, hr2, hrr⟩ := beatmap.mod_target_practice.check_hit_samples_refines (alloc.vec.Vec.deref o1)
        (alloc.vec.Vec.deref bt) (by rw [gen_deref_val]; omega)
      rw [gen_abs_deref, hdb] at hrr
      cases r with
      | Err e' =>
        obtain ⟨m, hm'⟩ := gen_hrel_err hrr
        refine ⟨.Err e', pb, ?_, ?_⟩
        · simp only [beatmap.mod_target_practice.apply, hr, bind_ok, h0', if_false, hcl, ho1, hbt, hy, gen_uncurry_eq, hr2]
        · rw [hm']; try trivial
      | Ok u =>
        have hu := gen_hrel_ok hrr
        obtain ⟨h2, hh2, hh2l, hh2v⟩ := beatmap.mod_target_practice.fix_combo_info_refines y (alloc.vec.Vec.deref o1)
        obtain ⟨h3, hh3, hh3v⟩ := beatmap.mod_target_practice.randomize_circle_pos_refines h2 rng hrok
        obtain ⟨i2, hi2, hi2v⟩ := usize_add_one pb.epoch hep
        obtain ⟨pb1, hpb1, hpb1v⟩ := beatmap.mods.record_first_object_refines false idx
          { pb with hit_objects := h3, epoch := i2 } hm
        refine ⟨.Ok (), pb1, ?_, ?_⟩
        · simp only [beatmap.mod_target_practice.apply, hr, bind_ok, h0', if_false, hcl, ho1, hbt, hy, gen_uncurry_eq,
            hr2, hh2, hh3, hi2, hpb1]
        · rw [hu]
          simp only [hRel, pure, Except.pure]
          rw [← hpb1v, gen_abs_deref] at *
          rw [← hrv, ← hh2v, ← hh3v]
          congr 1
          rw [show (abs pb : PlayableBeatmap).epoch + 1 = (abs i2 : Nat) from by
            show pb.epoch.val + 1 = i2.val; omega]
          rfl
end OsuProofs
