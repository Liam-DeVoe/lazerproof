/-
Generator mods, part 6 (gen agent): `beatmap::mod_random::apply` (Random mod) refines `RandomMod.apply`.
Spec loop normal form `gen_ap_spec` (via the `gen_case_ite` splitter: the elaborated `do` block duplicates its
continuations, so `split`'s internal `simp` runs out of steps), random-state choice functions `gen_ndR`/`gen_roR`.
-/
import OsuProofs.Post.GenRD4
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

open Mods.RandomMod Mods.Reposition in
/-- `shouldStartNewSection` (spec `RandomMod.apply`, `i > 0` part inlined) -/
def gen_apNS (cpi : ControlPointInfo) (i : Nat) (rng : NetRandom.State) (hos : Array OsuHitObject) :
    NetRandom.State × Bool :=
  if i == 0 then (rng, true) else
  let started := gen_csS hos i
  let downbeat := isOnBeat cpi hos[i - 1]! true
  let onBeat := isOnBeat cpi hos[i - 1]! false
  let p := if started then ((NetRandom.nextDouble rng).2, decide ((NetRandom.nextDouble rng).1 < SIX_TENTHS_F)) else (rng, false)
  let r := if !p.2 then downbeat else p.2
  if !r && onBeat then ((NetRandom.nextDouble p.1).2, decide ((NetRandom.nextDouble p.1).1 < FOUR_TENTHS_F)) else (p.1, r)

abbrev GenApSt := NetRandom.State × Array OsuHitObject × Array Mods.Reposition.PositionInfo × F32 × Bool

open Mods.RandomMod Mods.Reposition in
/-- one iteration of the `RandomMod.apply` loop (spec normal form) -/
def gen_apG (sh : F32) (cpi : ControlPointInfo) (i : Nat) (st : GenApSt) : GenApSt :=
  let ns := gen_apNS cpi i st.1 st.2.1
  let a : NetRandom.State × F32 × Bool :=
    if ns.2 then (((randomOffset sh 0.0008).run ns.1).2, ((randomOffset sh 0.0008).run ns.1).1, !st.2.2.2.2)
    else (ns.1, st.2.2.2.1, st.2.2.2.2)
  let hs : NetRandom.State × Array OsuHitObject :=
    if st.2.1[i]!.isSlider then
      ((NetRandom.nextDouble a.1).2,
        if (NetRandom.nextDouble a.1).1 < 0.5 then st.2.1.set! i (flipSliderInPlaceHorizontally st.2.1[i]!) else st.2.1)
    else (a.1, st.2.1)
  let infos := st.2.2.1
  if i == 0 then
    let d1 := NetRandom.nextDouble hs.1
    let d2 := NetRandom.nextDouble d1.2
    (d2.2, hs.2, infos.set! 0 { infos[0]! with
        distanceFromPrevious := F64.toF32 (d1.1 * F32.toF64 384 / 2),
        relativeAngle := F64.toF32 (d2.1 * 2 * Float.ofBits 0x400921FB54442D18 - Float.ofBits 0x400921FB54442D18) },
      a.2.1, a.2.2)
  else
    let ot := (randomOffset sh 0.002).run hs.1
    let ap : NetRandom.State × Bool :=
      if gen_csS hs.2 i then ((NetRandom.nextDouble ot.2).2, decide ((NetRandom.nextDouble ot.2).1 < SIX_TENTHS_F))
      else (ot.2, false)
    let fc : NetRandom.State × F32 × Bool :=
      if ap.2 then (((randomOffset sh 0.002).run ap.1).2, ((randomOffset sh 0.002).run ap.1).1, !a.2.2) else (ap.1, 0, a.2.2)
    let dist := infos[i]!.distanceFromPrevious
    (fc.1, hs.2, infos.set! i { infos[i]! with
        relativeAngle := relativeTargetAngle sh dist ((a.2.1 + ot.1) * dist + fc.2.1 * (playfieldDiagonal - dist)) fc.2.2 },
      a.2.1, fc.2.2)

open Lean Elab Tactic Meta in
/-- case-split on the first `if` (with a closed condition) of the goal; simp both branches with a large step budget
(the elaborated `do` blocks duplicate continuations, so `split`'s internal `simp` runs out of steps) -/
elab "gen_case_ite" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars)
    | throwError "gen_case_ite: no ite"
  let cStx ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| by_cases hgc : $cStx <;>
    simp (config := { maxSteps := 20000000 }) only [hgc, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
      Bool.not_true, Bool.not_false, decide_true, decide_false, pure_bind, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.not_eq_true', Bool.not_eq_false', not_false_eq_true, Bool.not_not, Bool.true_eq_false] at ⊢))

set_option maxRecDepth 8000 in
theorem gen_ap_spec (seed : Int32) (sh : F32) (pb : PlayableBeatmap) :
    Mods.RandomMod.apply seed sh pb =
      (do
        let st ← gen_iterE (fun i st => (.ok (.yield (gen_apG sh pb.controlPoints i st)) : Except String _)) 0
          (Mods.Reposition.generatePositionInfos pb.hitObjects).size
          (NetRandom.create seed, pb.hitObjects, Mods.Reposition.generatePositionInfos pb.hitObjects, 0, false)
        let out ← Mods.Reposition.repositionHitObjects st.2.1 st.2.2.1
        pure { pb with hitObjects := out }) := by
  unfold Mods.RandomMod.apply
  simp only []
  rw [gen_forIn_range_iterE, Nat.sub_zero]
  congr 2
  funext i st
  obtain ⟨rng, hos, infos, so, flow⟩ := st
  beta_reduce
  repeat' (first | gen_case_ite | split)
  all_goals (simp (config := { maxSteps := 2000000 }) only [gen_apG, gen_apNS, gen_csS, NetRandom.nextDouble, *,
    if_true, if_false, ite_true, ite_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, decide_true, decide_false,
    Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, Bool.not_eq_true', Bool.not_eq_false', Bool.not_not,
    beq_self_eq_true, Prod.mk.injEq] at *)
  all_goals (try simp (config := { maxSteps := 2000000 }) only [*, if_true, if_false, ite_true, ite_false,
    Bool.false_eq_true, Bool.not_true, Bool.not_false, decide_true, decide_false, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, Bool.not_eq_true', Bool.not_eq_false', Bool.not_not, eq_self_iff_true] at ⊢)
  all_goals rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_six : beatmap.mod_random.six_tenths_f = ok Mods.RandomMod.SIX_TENTHS_F := by
  unfold beatmap.mod_random.six_tenths_f Mods.RandomMod.SIX_TENTHS_F
  simp only [float.F32.from_bits, float.F32.to_f64, bind_ok]
  congr 1
theorem gen_four : beatmap.mod_random.four_tenths_f = ok Mods.RandomMod.FOUR_TENTHS_F := by
  unfold beatmap.mod_random.four_tenths_f Mods.RandomMod.FOUR_TENTHS_F
  simp only [float.F32.from_bits, float.F32.to_f64, bind_ok]
  congr 1
theorem gen_pfd : beatmap.mod_random.playfield_diagonal = ok Mods.RandomMod.playfieldDiagonal := by
  unfold beatmap.mod_random.playfield_diagonal Mods.RandomMod.playfieldDiagonal
  simp only [float.F32.from_bits, float.F32.mul, float.F32.add, float.F32.div, bind_ok, net.osutk.inverse_sqrt_fast_refines,
    cst_beatmap_mod_random_F1]
  congr 1
theorem gen_c8e4 : float.F32.from_bits 978433815#u32 = ok (8e-4 : F32) := by
  simp only [float.F32.from_bits]; congr 1
theorem gen_c2e3 : float.F32.from_bits 990057071#u32 = ok (2e-3 : F32) := by
  simp only [float.F32.from_bits]; congr 1
theorem gen_c384 : float.F32.from_bits 1136656384#u32 = ok (384 : F32) := by
  simp only [float.F32.from_bits]; congr 1
theorem gen_chalf : float.F64.from_bits 4602678819172646912#u64 = ok (0.5 : F64) := by
  simp only [float.F64.from_bits]; congr 1

open Classical in
/-- the value of a `Result` known to be `ok` (`Nonempty` version) -/
noncomputable def gen_valN {α} [Nonempty α] (m : Result α) : α :=
  if h : ∃ a, m = ok a then h.choose else Classical.choice inferInstance
theorem gen_valN_eq {α} [Nonempty α] (m : Result α) (h : ∃ a, m = ok a) : m = ok (gen_valN m) := by
  unfold gen_valN; rw [dif_pos h]; exact h.choose_spec

instance : Nonempty net.random.State := by
  obtain ⟨s, _⟩ := net.random.create_refines 0#i32; exact ⟨s⟩

noncomputable def gen_ndR (r : net.random.State) : F64 × net.random.State := gen_valN (net.random.next_double r)
theorem gen_nd_all (r : net.random.State) (h : stOk r) :
    net.random.next_double r = ok (gen_ndR r) ∧ stOk (gen_ndR r).2 ∧
      NetRandom.sample (stS r) = ((gen_ndR r).1, stS (gen_ndR r).2) := by
  obtain ⟨f, st', e, ok', eq'⟩ := net.random.next_double_refines r h
  have := gen_valN_eq _ ⟨_, e⟩
  rw [e] at this
  have h2 := Result.ok_injective this
  unfold gen_ndR; rw [e, ← h2]
  exact ⟨rfl, ok', eq'.symm⟩
theorem gen_nd_ok (r : net.random.State) (h : stOk r) : net.random.next_double r = ok (gen_ndR r) := (gen_nd_all r h).1
theorem gen_nd_st (r : net.random.State) (h : stOk r) : stOk (gen_ndR r).2 := (gen_nd_all r h).2.1
theorem gen_nd_eq (r : net.random.State) (h : stOk r) : NetRandom.sample (stS r) = ((gen_ndR r).1, stS (gen_ndR r).2) :=
  (gen_nd_all r h).2.2

noncomputable def gen_roR (sh sd : F32) (r : net.random.State) : F32 × net.random.State :=
  gen_valN (beatmap.mod_random.random_offset sh sd r)
theorem gen_ro_all (sh sd : F32) (r : net.random.State) (h : stOk r) :
    beatmap.mod_random.random_offset sh sd r = ok (gen_roR sh sd r) ∧ stOk (gen_roR sh sd r).2 ∧
      StateT.run (Mods.RandomMod.randomOffset sh sd) (stS r) = ((gen_roR sh sd r).1, stS (gen_roR sh sd r).2) := by
  obtain ⟨f, st', e, ok', eq'⟩ := beatmap.mod_random.random_offset_refines sh sd r h
  have := gen_valN_eq _ ⟨_, e⟩
  rw [e] at this
  have h2 := Result.ok_injective this
  unfold gen_roR; rw [e, ← h2]
  exact ⟨rfl, ok', eq'.symm⟩
theorem gen_ro_ok (sh sd : F32) (r : net.random.State) (h : stOk r) :
    beatmap.mod_random.random_offset sh sd r = ok (gen_roR sh sd r) := (gen_ro_all sh sd r h).1
theorem gen_ro_st (sh sd : F32) (r : net.random.State) (h : stOk r) : stOk (gen_roR sh sd r).2 := (gen_ro_all sh sd r h).2.1
theorem gen_ro_eq (sh sd : F32) (r : net.random.State) (h : stOk r) :
    StateT.run (Mods.RandomMod.randomOffset sh sd) (stS r) = ((gen_roR sh sd r).1, stS (gen_roR sh sd r).2) :=
  (gen_ro_all sh sd r h).2.2

noncomputable def gen_flR (h : beatmap.objects.OsuHitObject) : beatmap.objects.OsuHitObject :=
  @gen_valN _ ⟨h⟩ (beatmap.mod_random.flip_slider_in_place_horizontally h)
theorem gen_fl_all (h : beatmap.objects.OsuHitObject) (hg : GenOk (abs h)) (h64 : System.Platform.numBits = 64) :
    beatmap.mod_random.flip_slider_in_place_horizontally h = ok (gen_flR h) ∧
      (abs (gen_flR h) : OsuHitObject) = Mods.Reposition.flipSliderInPlaceHorizontally (abs h) := by
  obtain ⟨o, e, hov⟩ := beatmap.mod_random.flip_slider_in_place_horizontally_refines h hg h64
  have := @gen_valN_eq _ ⟨h⟩ _ ⟨_, e⟩
  rw [e] at this
  have h2 := Result.ok_injective this
  unfold gen_flR; rw [e, ← h2]
  exact ⟨rfl, hov.symm⟩

theorem gen_cs_deref (v : alloc.vec.Vec beatmap.objects.OsuHitObject) (i : Usize) (h1 : 1 ≤ i.val)
    (h2 : i.val < v.val.length) :
    beatmap.mod_random.combo_started (alloc.vec.Vec.deref v) i = ok (gen_csS (abs v) i.val) := by
  rw [beatmap.mod_random.combo_started_refines _ i h1 (by rw [gen_deref_val]; exact h2)]
  simp only [gen_deref_val]; rfl

theorem gen_cp_abs (c : beatmap.control_points.ControlPointInfo) : cpS c = (abs c : ControlPointInfo) := rfl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

open Lean Elab Tactic Meta in
/-- `gen_case_ite` with extra simp lemmas -/
elab "gen_case_ite2" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars)
    | throwError "gen_case_ite2: no ite"
  let cStx ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| by_cases hgc : $cStx <;>
    simp (config := { maxSteps := 20000000, maxDischargeDepth := 8 }) only [hgc, $ls,*, if_true, if_false, ite_true, ite_false, Bool.false_eq_true,
      Bool.not_true, Bool.not_false, decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.not_eq_true', Bool.not_eq_false', not_false_eq_true, Bool.not_not,
      Bool.true_eq_false, decide_not, Bool.decide_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, not_true_eq_false] at ⊢))

theorem gen_rta (a b c : F32) (d : Bool) :
    beatmap.mod_random.relative_target_angle a b c d = ok (Mods.RandomMod.relativeTargetAngle a b c d) := by
  obtain ⟨r, e, hv⟩ := beatmap.mod_random.relative_target_angle_refines a b c d
  rw [e]; congr 1; exact hv.symm

theorem gen_uncurry_eq {α β γ} (f : α → β → γ) (p : α × β) : Aeneas.Std.uncurry f p = f p.1 p.2 := by
  cases p; exact uncurry_apply_pair _ _ _

open Mods.RandomMod Mods.Reposition in
/-- `gen_apNS` in the Rust evaluation order -/
def gen_apNS2 (cpi : ControlPointInfo) (i : Nat) (rng : NetRandom.State) (hos : Array OsuHitObject) :
    NetRandom.State × Bool :=
  if i == 0 then (rng, true) else
  let p := if gen_csS hos i then ((NetRandom.nextDouble rng).2, decide ((NetRandom.nextDouble rng).1 < SIX_TENTHS_F))
    else (rng, false)
  let r := if p.2 then p.2 else isOnBeat cpi hos[i - 1]! true
  if r then (p.1, r)
  else if isOnBeat cpi hos[i - 1]! false then
    ((NetRandom.nextDouble p.1).2, decide ((NetRandom.nextDouble p.1).1 < FOUR_TENTHS_F))
  else (p.1, r)

theorem gen_apNS2_eq (cpi : ControlPointInfo) (i : Nat) (rng : NetRandom.State) (hos : Array OsuHitObject) :
    gen_apNS cpi i rng hos = gen_apNS2 cpi i rng hos := by
  unfold gen_apNS gen_apNS2
  by_cases h0 : (i == 0) = true
  · simp only [h0, if_true]
  · simp only [h0, Bool.false_eq_true, if_false]
    cases hc : gen_csS hos i <;> cases hd : Mods.RandomMod.isOnBeat cpi hos[i - 1]! true <;>
      cases ho : Mods.RandomMod.isOnBeat cpi hos[i - 1]! false <;>
      cases hx : decide ((NetRandom.nextDouble rng).1 < Mods.RandomMod.SIX_TENTHS_F) <;>
      simp only [hc, hd, ho, hx, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false,
        Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, ite_true, ite_false]

def GenApInv (n : Nat) (t : alloc.vec.Vec beatmap.objects.OsuHitObject × net.random.State ×
    alloc.vec.Vec beatmap.mod_random.PositionInfo × F32 × Bool × Usize) : Prop :=
  stOk t.2.1 ∧ GenOkL t.1.val ∧ t.1.val.length = n ∧ t.2.2.1.val.length = n

theorem gen_ap_loop (sh : F32) (cpi : beatmap.control_points.ControlPointInfo) (hcp : cpi.timing_points.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) (n : Nat) :
    ∀ t, GenApInv n t → t.2.2.2.2.2.val ≤ n →
    ∃ y, beatmap.mod_random.apply_loop 0 sh cpi t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 Mods.RandomMod.SIX_TENTHS_F
        Mods.RandomMod.FOUR_TENTHS_F t.2.2.2.2.2 = ok y ∧
      GenOkL y.1.val ∧ y.1.val.length = n ∧ y.2.val.length = n ∧
      ((abs y.1 : Array OsuHitObject), (abs y.2 : Array Mods.Reposition.PositionInfo)) =
        (fun st : GenApSt => (st.2.1, st.2.2.1)) (iterR (fun k s => .yield (gen_apG sh (abs cpi) k s)) t.2.2.2.2.2.val
          (n - t.2.2.2.2.2.val) (stS t.2.1, abs t.1, abs t.2.2.1, t.2.2.2.1, t.2.2.2.2.1)) := by
  intro t ht hle
  have hn : n ≤ Usize.max := by rw [← ht.2.2.1]; have := t.1.property; omega
  obtain ⟨y, hl, hv⟩ := loop_fold_gen'
    (fun x : alloc.vec.Vec beatmap.objects.OsuHitObject × net.random.State ×
        alloc.vec.Vec beatmap.mod_random.PositionInfo × F32 × Bool × Usize =>
      beatmap.mod_random.apply_loop.body 0 sh cpi Mods.RandomMod.SIX_TENTHS_F Mods.RandomMod.FOUR_TENTHS_F
        x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) (·.2.2.2.2.2) n hn
    (GenApInv n) (fun x => ((stS x.2.1, abs x.1, abs x.2.2.1, x.2.2.2.1, x.2.2.2.2.1) : GenApSt))
    (gen_apG sh (abs cpi))
    (fun y s => GenOkL y.1.val ∧ y.1.val.length = n ∧ y.2.val.length = n ∧
      ((abs y.1 : Array OsuHitObject), (abs y.2 : Array Mods.Reposition.PositionInfo)) = (s.2.1, s.2.2.1))
    (by
      rintro ⟨v, rng, inf, so, fl, i⟩ ⟨hok, hgl, hvl, hil⟩ hlt j1 hj1 hj1v
      simp only at hok hgl hvl hil hlt hj1 hj1v ⊢
      have hi : i.val < inf.val.length := by omega
      have hiv : i.val < v.val.length := by omega
      have hgi := gen_okl_get _ hgl _ hiv
      simp only [beatmap.mod_random.apply_loop.body, vec_lt_len_iff, hi, if_true]
      unfold gen_apG
      rw [gen_apNS2_eq]
      unfold gen_apNS2
      have hga := gen_abs_get (β := OsuHitObject) v i.val hiv
      have hfl := gen_fl_all _ hgi h64
      by_cases h0 : i = 0#usize
      · subst h0
        have h0v : (0#usize : Usize).val = 0 := rfl
        have hga0 : (abs v : Array OsuHitObject)[0]! = abs (v.val[0]'hiv) := hga
        have hgf : beatmap.mod_random.flip_slider_in_place_horizontally (v.val[0]'hiv) = ok (gen_flR (v.val[0]'hiv)) ∧
            (abs (gen_flR (v.val[0]'hiv)) : OsuHitObject) = Mods.Reposition.flipSliderInPlaceHorizontally (abs (v.val[0]'hiv)) :=
          gen_fl_all _ hgi h64
        simp only [if_true, h0v, beq_self_eq_true, bind_ok, gen_uncurry_eq, gen_c8e4, gen_ro_ok _ _ _ hok,
          vec_index_eq _ _ hiv, is_slider_ok, hga, gen_ro_eq _ _ _ hok, gen_ro_st _ _ _ hok, gen_nd_ok, gen_nd_st,
          gen_nd_eq, gen_chalf, float.F64.lt, gen_c384, float.F32.to_f64, float.F64.mul, float.F64.div, float.F64.to_f32,
          float.F64.sub, cst_beatmap_mod_random_D2, cst_beatmap_mod_random_DPI, NetRandom.nextDouble, ite_true, hga0]
        repeat' gen_case_ite2 [bind_ok, gen_uncurry_eq, gen_nd_ok, gen_nd_st, gen_ro_st _ _ _ hok, gen_nd_eq,
          vec_index_mut_eq _ _ hiv, vec_index_mut_eq _ _ hi, gen_vset_mut _ _ _ hi, hfl.1, hj1, gen_vset_set,
          float.F64.lt, gen_ro_eq _ _ _ hok, hga0, h0v, hgf.1]
        all_goals (try simp (config := { maxDischargeDepth := 8 }) only [bind_ok, gen_uncurry_eq, gen_nd_ok, gen_nd_st, gen_ro_st _ _ _ hok, gen_nd_eq,
          vec_index_mut_eq _ _ hiv, vec_index_mut_eq _ _ hi, gen_vset_mut _ _ _ hi, hfl.1, hj1, gen_vset_set])
        all_goals
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
            refine ⟨rfl, ?_, ?_, rfl, rfl⟩
            · (try dsimp only) <;> first | rfl | (rw [gen_abs_set, hgf.2]; try rfl)
            · (try dsimp only) <;> (rw [gen_abs_set, gen_abs_get (β := Mods.Reposition.PositionInfo) inf 0 hi]; try rfl)
          · refine ⟨?_, ?_, ?_, ?_⟩
            · simp only
              repeat (first | exact hok | apply gen_nd_st | apply gen_ro_st)
            · simp only
              first | exact hgl | (rw [vec_set_val']; exact gen_okl_set _ hgl _ _ (by rw [hgf.2]; exact gen_ok_flip _ hgi))
            · simp [vec_set_val', hvl]
            · simp [vec_set_val', hil]
      · have h1 : 1 ≤ i.val := by
          rcases Nat.eq_zero_or_pos i.val with h | h
          · exact absurd (UScalar.eq_of_val_eq (by simp [h])) h0
          · omega
        have hb0 : (i.val == 0) = false := by simp; omega
        obtain ⟨i2, hi2, hi2v⟩ : ∃ i2 : Usize, i - 1#usize = ok i2 ∧ i2.val = i.val - 1 := by
          obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (Usize.sub_spec (x := i) (y := 1#usize) (by scalar_tac))
          exact ⟨z, hz, by have := hzv; scalar_tac⟩
        have hi2l : i2.val < v.val.length := by omega
        have hga1 : (abs v : Array OsuHitObject)[i.val - 1]! = abs (v.val[i2.val]'hi2l) := by
          rw [← hi2v]; exact gen_abs_get (β := OsuHitObject) v i2.val hi2l
        have hgai := gen_abs_get (β := Mods.Reposition.PositionInfo) inf i.val hi
        have hcs1 := gen_cs_deref v i h1 hiv
        have hcs2 := gen_cs_deref (v.set i (gen_flR (v.val[i.val]'hiv))) i h1 (by simp [vec_set_val']; omega)
        have hob := fun b => beatmap.mod_random.is_on_beat_refines cpi (v.val[i2.val]'hi2l) b hcp
        simp only [h0, if_false, hb0, Bool.false_eq_true, bind_ok, gen_uncurry_eq, hcs1, hi2, vec_index_eq _ _ hi2l,
          hob, gen_cp_abs, hga1, vec_index_eq _ _ hiv, is_slider_ok, hga, gen_nd_ok _ hok, gen_nd_eq _ hok, gen_six,
          gen_four, float.F64.lt, NetRandom.nextDouble]
        repeat' gen_case_ite2 [bind_ok, gen_uncurry_eq, gen_nd_ok, gen_nd_st, gen_ro_st, gen_nd_eq, gen_ro_ok, gen_ro_eq,
          gen_nd_st _ hok, gen_ro_st _ _ _ hok, hok, gen_c8e4, gen_c2e3, gen_chalf, hga, hfl.1, hfl.2, gen_abs_set,
          vec_index_mut_eq _ _ hiv, vec_index_mut_eq _ _ hi, gen_vset_mut _ _ _ hi, gen_vset_set, hj1, hcs1, hcs2, hgai,
          vec_index_eq _ _ hi, float.F32.add, float.F32.mul, float.F32.sub, gen_pfd, gen_rta, float.F64.lt]
        all_goals (try simp (config := { maxDischargeDepth := 8 }) only [bind_ok, gen_uncurry_eq, gen_nd_ok, gen_nd_st,
          gen_ro_st, gen_nd_eq, gen_ro_ok, gen_ro_eq, hok, vec_index_mut_eq _ _ hiv, vec_index_mut_eq _ _ hi,
          gen_vset_mut _ _ _ hi, hfl.1, hj1, gen_vset_set, hgai, hcs1, hcs2, vec_index_eq _ _ hi, float.F32.add, float.F32.mul,
          float.F32.sub, gen_pfd, gen_rta])
        all_goals
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
            refine ⟨rfl, ?_, ?_, rfl, rfl⟩
            · (try dsimp only) <;> first | rfl | (rw [gen_abs_set, hfl.2]; try rfl)
            · (try dsimp only) <;> (rw [gen_abs_set]; try rfl; done)
          · refine ⟨?_, ?_, ?_, ?_⟩
            · simp only
              repeat (first | exact hok | apply gen_nd_st | apply gen_ro_st)
            · simp only
              first | exact hgl | (rw [vec_set_val']; exact gen_okl_set _ hgl _ _ (by rw [hfl.2]; exact gen_ok_flip _ hgi))
            · simp [vec_set_val', hvl]
            · simp [vec_set_val', hil])
    (by
      rintro ⟨v, rng, inf, so, fl, i⟩ ⟨hok, hgl, hvl, hil⟩ hge
      simp only at hok hgl hvl hil hge ⊢
      have : ¬ i < alloc.vec.Vec.len inf := by rw [vec_lt_len_iff]; omega
      exact ⟨(v, inf), by simp [beatmap.mod_random.apply_loop.body, this], hgl, hvl, hil, rfl⟩)
    t ht hle
  refine ⟨y, ?_, hv⟩
  unfold beatmap.mod_random.apply_loop
  exact hl
end OsuProofs

open OsuModel.Net OsuModel.Beatmap
namespace OsuProofs
open OsuImpl

theorem gen_gpi_size (hos : Array OsuHitObject) : (Mods.Reposition.generatePositionInfos hos).size = hos.size := by
  rw [gen_gpi_spec]
  suffices h : ∀ n j (s : Array Mods.Reposition.PositionInfo × Vec2 × F32),
      (iterR (fun j s => .yield (gen_gpiG hos j s)) j n s).1.size = s.1.size + n by
    simpa using h hos.size 0 (#[], Mods.Reposition.centre, 0)
  intro n
  induction n with
  | zero => intro j s; simp [iterR]
  | succ n ih =>
    intro j s
    simp only [iterR]
    rw [ih]
    unfold gen_gpiG
    simp only []
    split <;> simp <;> omega

theorem gen_iterE_ok {ε S : Type} (f : Nat → S → ForInStep S) (n j : Nat) (s : S) :
    gen_iterE (ε := ε) (fun k s => Except.ok (f k s)) j n s = .ok (iterR f j n s) :=
  gen_iterE_pure f n j s

theorem beatmap.mod_random.apply_refines (seed : I32) (sh : F32) (pb : beatmap.playable.PlayableBeatmap)
    (hg : GenOkL pb.hit_objects.val) (hcp : pb.control_points.timing_points.val.length < 2^31)
    (h64 : System.Platform.numBits = 64) :
    ∃ e r, beatmap.mod_random.apply seed sh pb = ok (e, r) ∧
      hRel (fun _ => (abs r : PlayableBeatmap)) e (Mods.RandomMod.apply (i32S seed) sh (abs pb)) := by
  obtain ⟨rng, hr, hrok, hrv⟩ := net.random.create_refines seed
  obtain ⟨inf, hinf, hinfv⟩ := beatmap.mod_random.generate_position_infos_refines (alloc.vec.Vec.deref pb.hit_objects)
    (by rw [gen_deref_val]; intro h hm; exact gen_paths_ok h (hg h hm)) h64
  rw [gen_abs_deref] at hinfv
  have hn : inf.val.length = pb.hit_objects.val.length := by
    have := congrArg Array.size hinfv
    simp only [abs, List.size_toArray, List.length_map] at this
    rw [this, gen_gpi_size]; simp
  obtain ⟨y, hy, hyg, hyl, hyl2, hyv⟩ := gen_ap_loop sh pb.control_points hcp h64 pb.hit_objects.val.length
    (pb.hit_objects, rng, inf, 0, false, 0#usize) ⟨hrok, hg, rfl, hn⟩ (by simp)
  obtain ⟨e, hos', hr2, hg2, hl2, hrel⟩ := beatmap.mod_random.reposition_hit_objects_refines y.1
    (alloc.vec.Vec.deref y.2) (by rw [gen_deref_val]; omega) hyg h64
  refine ⟨e, { pb with hit_objects := hos' }, ?_, ?_⟩
  · unfold beatmap.mod_random.apply
    simp only [hr, bind_ok, hinf, cst_beatmap_mod_random_F0, gen_six, gen_four]
    simp only at hy
    rw [hy]
    simp only [bind_ok, gen_uncurry_eq, hr2]
  · rw [gen_ap_spec, gen_iterE_ok, gen_except_bind_ok]
    have hS : (Mods.Reposition.generatePositionInfos (abs pb : PlayableBeatmap).hitObjects).size =
        pb.hit_objects.val.length := by
      have : (abs pb : PlayableBeatmap).hitObjects = (abs pb.hit_objects : Array OsuHitObject) := rfl
      rw [this, ← hinfv]; simp [abs, hn]
    rw [hS]
    simp only [show ((0#usize : Usize).val) = 0 from rfl, Nat.sub_zero] at hyv
    have e1 : (abs pb : PlayableBeatmap).hitObjects = (abs pb.hit_objects : Array OsuHitObject) := rfl
    have e2 : (abs pb : PlayableBeatmap).controlPoints = (abs pb.control_points : ControlPointInfo) := rfl
    rw [e1, e2, ← hinfv, ← hrv]
    rw [gen_abs_deref] at hrel
    have hyv1 := congrArg Prod.fst hyv
    have hyv2 := congrArg Prod.snd hyv
    simp only at hyv1 hyv2
    rw [← hyv1, ← hyv2]
    revert hrel
    generalize Mods.Reposition.repositionHitObjects _ _ = R
    intro hrel
    cases e with
    | Ok u =>
      have := gen_hrel_ok hrel
      subst this
      rfl
    | Err er =>
      obtain ⟨e', h'⟩ := gen_hrel_err hrel
      subst h'
      trivial
end OsuProofs

