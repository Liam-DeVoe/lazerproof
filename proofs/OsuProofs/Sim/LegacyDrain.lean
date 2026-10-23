/-
`sim::scoring` legacy drain rate (Rust) refines `OsuModel.Sim.computeLegacyDrainRate`
(`LegacyDrainingHealthProcessor.ComputeDrainRate`): models `simLNest` (nested-object health), `simLStep` (one
object of a pass), `simLPassF` (a pass), `simLOStep`/`simLRun` (the outer `while` with fuel; `none` = fuel
exhausted); `legacy_nested_loop`, `legacy_pass`, `compute_legacy_drain_rate`.
-/
import OsuProofs.Sim.DrainRate
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

@[simp] theorem sim_kind_ne_ok (a b : sim.playable.Kind) :
    core.cmp.PartialEq.ne.trait_default sim.playable.Kind.Insts.CoreCmpPartialEqKind a b = ok (kindS a != kindS b) := by
  simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, bne]

def simLSkip (hk nk : sim.playable.Kind) : Bool :=
  (kindS hk == .spinner && kindS nk == .spinnerBonusTick) || (kindS hk != .slider && kindS hk != .spinner)

def simLInc (hp mult : F64) (n : sim.playable.HObj) : F64 :=
  OsuModel.Sim.legacyHealthIncrease hp mult (kindS n.kind) (hrS n.max_result)

def simLNest (hp mult : F64) (hk : sim.playable.Kind) (l : List sim.playable.HObj) (cu : F64 × F64) : F64 × F64 :=
  l.foldl (fun cu n => if simLSkip hk n.kind then cu
    else (F64.max 0 (F64.min 1 (cu.1 + simLInc hp mult n)), cu.2 + simLInc hp mult n)) cu

theorem sim_lnest_loop (v : alloc.vec.Vec sim.playable.HObj) (hp mult : F64) (hk : sim.playable.Kind) :
    ∀ n (cur unc : F64) (k : Usize), v.val.length - k.val = n → k.val ≤ v.val.length →
      sim.scoring.legacy_nested_loop_loop v hp mult hk cur unc k = ok (simLNest hp mult hk (v.val.drop k.val) (cur, unc)) := by
  intro n
  induction n with
  | zero =>
    intro cur unc k hn hk
    have hdn : v.val.drop k.val = [] := List.drop_of_length_le (by omega)
    unfold sim.scoring.legacy_nested_loop_loop; rw [loop_unfold]
    have : ¬ (k < alloc.vec.Vec.len v) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.legacy_nested_loop_loop.body, this, hdn, simLNest]
  | succ n ih =>
    intro cur unc k hn hkl
    have hlt : k.val < v.val.length := by omega
    have hlt' : k < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k (by have := v.property; omega)
    set x := v.val[k.val]'hlt with hx
    have hskip : ∀ (X : Bool → Result (ControlFlow (F64 × F64 × Usize) (F64 × F64))),
        (do
          let b ← sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq hk sim.playable.Kind.Spinner
          let skip ← if b then (do
              let b1 ← sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq x.kind sim.playable.Kind.SpinnerBonusTick
              if b1 then ok true else (do
                let b2 ← core.cmp.PartialEq.ne.trait_default sim.playable.Kind.Insts.CoreCmpPartialEqKind hk sim.playable.Kind.Slider
                if b2 then core.cmp.PartialEq.ne.trait_default sim.playable.Kind.Insts.CoreCmpPartialEqKind hk sim.playable.Kind.Spinner
                else ok false))
            else (do
              let b1 ← core.cmp.PartialEq.ne.trait_default sim.playable.Kind.Insts.CoreCmpPartialEqKind hk sim.playable.Kind.Slider
              if b1 then core.cmp.PartialEq.ne.trait_default sim.playable.Kind.Insts.CoreCmpPartialEqKind hk sim.playable.Kind.Spinner
              else ok false)
          X skip) = X (simLSkip hk x.kind) := by
      intro X
      cases hk <;> cases hxk : x.kind <;> simp [simLSkip, kindS] <;> rfl
    obtain ⟨a, ha, ea⟩ := sim.scoring.legacy_health_increase_refines hp mult x.kind x.max_result
    simp only [abs, id] at ea
    have hcu : ∀ c u, (if simLSkip hk x.kind then (c, u) else (F64.max 0 (F64.min 1 (c + simLInc hp mult x)), u + simLInc hp mult x)) =
        (if simLSkip hk x.kind then (c, u) else (F64.max 0 (F64.min 1 (c + a)), u + a)) := by
      intro c u; simp only [simLInc, ea]
    have IH := ih (if simLSkip hk x.kind then cur else F64.max 0 (F64.min 1 (cur + a)))
      (if simLSkip hk x.kind then unc else unc + a) k1 (by omega) (by omega)
    unfold sim.scoring.legacy_nested_loop_loop; rw [loop_unfold]; dsimp only
    rw [show sim.scoring.legacy_nested_loop_loop.body v hp mult hk cur unc k = ok (.cont
        ((if simLSkip hk x.kind then cur else F64.max 0 (F64.min 1 (cur + a))),
         (if simLSkip hk x.kind then unc else unc + a), k1)) by
      unfold sim.scoring.legacy_nested_loop_loop.body
      simp only [hlt', if_true, vec_index_usize_ok _ _ hlt, bind_ok, ← hx]
      cases hk <;> cases hxk : x.kind <;> simp only [hxk] at ha <;>
        simp (config := {decide := true}) [simLSkip, kindS, ha, float.F64.add, sim.scoring.cap01, net.max_refines, net.min_refines, hk1,
          vec_index_usize_ok _ _ hlt, vec_index_eq _ _ hlt, ← hx, hxk,
          sim_scoring_F64_0, sim_scoring_F64_1] <;> rfl]
    simp only [bind_ok]
    unfold sim.scoring.legacy_nested_loop_loop at IH
    rw [IH, ek1, List.drop_eq_getElem_cons hlt]
    simp only [simLNest, List.foldl_cons, ← hx]
    have e := hcu cur unc
    rw [e]
    cases simLSkip hk x.kind <;> rfl

def simVPS (v : alloc.vec.Vec sim.playable.Period) : List (F64 × F64) := v.val.map (fun p => (p.start, p.«end»))

theorem sim_lp_brk_loop (v : alloc.vec.Vec sim.playable.Period) (h : sim.playable.HObj) :
    ∀ n (lt : F64) (cb : Usize), v.val.length - cb.val = n → cb.val ≤ v.val.length →
      ∃ cb', sim.scoring.legacy_pass_loop0_loop0 v lt cb h = ok ((simBrk (simVPS v) h.start n (cb.val, lt)).2, cb', h) ∧
        cb'.val = (simBrk (simVPS v) h.start n (cb.val, lt)).1 := by
  intro n
  induction n with
  | zero =>
    intro lt cb hn hc
    refine ⟨cb, ?_, rfl⟩
    unfold sim.scoring.legacy_pass_loop0_loop0; rw [loop_unfold]
    have : ¬ (cb < alloc.vec.Vec.len v) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.legacy_pass_loop0_loop0.body, this, simBrk]
  | succ n ih =>
    intro lt cb hn hc
    have hlt : cb.val < v.val.length := by omega
    have hlt' : cb < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨cb1, hcb1, ecb1⟩ := usize_add_one cb (by have := v.property; omega)
    have hg : (simVPS v)[cb.val]? = some ((v.val[cb.val]'hlt).start, (v.val[cb.val]'hlt).«end») := by
      simp [simVPS, List.getElem?_eq_getElem hlt]
    unfold sim.scoring.legacy_pass_loop0_loop0; rw [loop_unfold]; dsimp only
    by_cases hb : (v.val[cb.val]'hlt).«end» ≤ h.start
    · obtain ⟨c2, hc2, ec2⟩ := ih h.start cb1 (by omega) (by omega)
      rw [show sim.scoring.legacy_pass_loop0_loop0.body v h lt cb = ok (.cont (h.start, cb1)) by
        simp [sim.scoring.legacy_pass_loop0_loop0.body, hlt', vec_index_usize_ok _ _ hlt, float.F64.le, hb, hcb1]]
      simp only [bind_ok]
      unfold sim.scoring.legacy_pass_loop0_loop0 at hc2
      simp only [simBrk, hg, hb, if_true, ← ecb1]
      exact ⟨c2, hc2, ec2⟩
    · refine ⟨cb, ?_, by simp [simBrk, hg, hb]⟩
      rw [show sim.scoring.legacy_pass_loop0_loop0.body v h lt cb = ok (.done (lt, cb, h)) by
        simp [sim.scoring.legacy_pass_loop0_loop0.body, hlt', vec_index_usize_ok _ _ hlt, float.F64.le, hb]]
      simp [simBrk, hg, hb]

abbrev SimLS := F64 × F64 × F64 × F64 × F64 × Nat × Bool × Nat

/-- one object of a legacy `computeLegacyDrainRate` pass -/
def simLStep (B : List (F64 × F64)) (hp mult lhe : F64) (o : sim.playable.TopObj) (st : SimLS) : ForInStep SimLS :=
  let bs := simBrk B o.h.start B.length (st.2.2.2.2.2.1, st.2.2.2.2.1)
  let amt := st.1 * (o.h.start - bs.2)
  let unc1 := F64.max 0 (st.2.2.1 - amt)
  let cur1 := F64.max 0 (st.2.1 - amt)
  let low1 := if cur1 < st.2.2.2.1 then cur1 else st.2.2.2.1
  let cnt' := st.2.2.2.2.2.2.2 + 1
  if cur1 ≤ lhe then .done (st.1 * 0.96, cur1, unc1, low1, o.h.end_time, bs.1, true, cnt')
  else
    let red := st.1 * (o.h.end_time - o.h.start)
    let over := F64.max 0 (red - cur1)
    let cu := simLNest hp mult o.h.kind o.nested.val (F64.max 0 (cur1 - red), F64.max 0 (unc1 - red))
    if 0 < over ∧ cu.1 - over ≤ lhe then .done (st.1 * 0.96, cu.1, cu.2, low1, o.h.end_time, bs.1, true, cnt')
    else .yield (st.1, F64.max 0 (F64.min 1 (cu.1 + simLInc hp mult o.h)), cu.2 + simLInc hp mult o.h, low1,
      o.h.end_time, bs.1, st.2.2.2.2.2.2.1, cnt')

def simLProj (s : SimLS) : Bool × F64 × F64 × F64 × Nat := (s.2.2.2.2.2.2.1, s.1, s.2.1, s.2.2.1, s.2.2.2.2.2.2.2)

theorem sim_lp_stopped (pb : sim.playable.Playable) (hp mult lhe td cur unc : F64) (cnt : U64) (low last : F64)
    (cb i : Usize) :
    sim.scoring.legacy_pass_loop0 pb hp mult lhe true td cur unc cnt low last cb i = ok (true, td, cur, unc, cnt) := by
  unfold sim.scoring.legacy_pass_loop0; rw [loop_unfold]
  by_cases h : i < alloc.vec.Vec.len pb.objects <;> simp [sim.scoring.legacy_pass_loop0.body, h]

theorem sim_lp_loop (pb : sim.playable.Playable) (hp mult lhe : F64) :
    ∀ n (td cur unc : F64) (cnt : U64) (low last : F64) (cb i : Usize),
      pb.objects.val.length - i.val = n → i.val ≤ pb.objects.val.length → cb.val ≤ pb.breaks.val.length →
      cnt.val = i.val →
      ∃ r, sim.scoring.legacy_pass_loop0 pb hp mult lhe false td cur unc cnt low last cb i = ok r ∧
        (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.val) = simLProj ((pb.objects.val.drop i.val).foldr
          (simForStep (simLStep (simVPS pb.breaks) hp mult lhe)) id (td, cur, unc, low, last, cb.val, false, cnt.val)) := by
  intro n
  induction n with
  | zero =>
    intro td cur unc cnt low last cb i hn hi hcb hcnt
    have hdn : pb.objects.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨(false, td, cur, unc, cnt), ?_, by simp [hdn, simLProj]⟩
    unfold sim.scoring.legacy_pass_loop0; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.objects) := by rw [vec_lt_len_iff]; omega
    simp [sim.scoring.legacy_pass_loop0.body, this]
  | succ n ih =>
    intro td cur unc cnt low last cb i hn hi hcb hcnt
    have hlt : i.val < pb.objects.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    have hmx := sim_u64_max_ge
    have hol := pb.objects.property
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by omega)
    obtain ⟨cnt1, hc1, ec1⟩ := eq_ok_of_spec (U64.add_spec (x := cnt) (y := 1#u64) (by simp; omega))
    set o := pb.objects.val[i.val]'hlt with ho
    obtain ⟨cb', hcb', ecb'⟩ := sim_lp_brk_loop pb.breaks o.h _ last cb rfl hcb
    rw [List.drop_eq_getElem_cons hlt, List.foldr_cons, ← ho]
    have hbf : simBrk (simVPS pb.breaks) o.h.start (pb.breaks.val.length - cb.val) (cb.val, last) =
        simBrk (simVPS pb.breaks) o.h.start (simVPS pb.breaks).length (cb.val, last) :=
      sim_brk_fuel _ _ _ _ _ _ (by simp [simVPS]) (by simp [simVPS])
    rw [hbf] at hcb' ecb'
    obtain ⟨bs, hbs⟩ : ∃ x, simBrk (simVPS pb.breaks) o.h.start (simVPS pb.breaks).length (cb.val, last) = x := ⟨_, rfl⟩
    rw [hbs] at hcb' ecb'
    have hcbl : cb'.val ≤ pb.breaks.val.length := by
      have := sim_brk_le (simVPS pb.breaks) o.h.start (simVPS pb.breaks).length cb.val last (by simp [simVPS]; omega)
      rw [hbs] at this; simp [simVPS] at this; omega
    obtain ⟨a, ha, ea⟩ := sim.scoring.legacy_health_increase_refines hp mult o.h.kind o.h.max_result
    simp only [abs, id] at ea
    have hnest : ∀ c u, sim.scoring.legacy_nested pb i hp mult c u = ok (simLNest hp mult o.h.kind o.nested.val (c, u)) := by
      intro c u
      have := sim_lnest_loop o.nested hp mult o.h.kind _ c u 0#usize rfl (by simp)
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at this
      simp [sim.scoring.legacy_nested, sim.scoring.legacy_nested_loop, vec_index_eq _ _ hlt, ← ho, this]
    have hcnt1 : cnt1.val = (i.val + 1) := by simp at ec1; omega
    set amt := td * (o.h.start - bs.2) with hamt
    set unc1 := F64.max 0 (unc - amt) with hunc1
    set cur1 := F64.max 0 (cur - amt) with hcur1
    set low1 := (if cur1 < low then cur1 else low) with hlow1
    unfold sim.scoring.legacy_pass_loop0; rw [loop_unfold]; dsimp only
    by_cases hA : cur1 ≤ lhe
    · rw [show sim.scoring.legacy_pass_loop0.body pb hp mult lhe false td cur unc cnt low last cb i =
          ok (.cont (true, td * 0.96, cur1, unc1, cnt1, low1, o.h.end_time, cb', i1)) by
        simp [sim.scoring.legacy_pass_loop0.body, hlt', hc1, vec_index_eq _ _ hlt, ← ho, hcb', float.F64.sub,
          float.F64.mul, net.max_refines, sim_scoring_F64_0, float.F64.lt, float.F64.le, hA, hi1, ← hamt, ← hunc1,
          ← hcur1]
        split_ifs <;> simp_all]
      simp only [bind_ok]
      have := sim_lp_stopped pb hp mult lhe (td * 0.96) cur1 unc1 cnt1 low1 o.h.end_time cb' i1
      unfold sim.scoring.legacy_pass_loop0 at this
      refine ⟨_, this, ?_⟩
      simp only [simForStep, simLStep, hbs, ← hamt, ← hunc1, ← hcur1, ← hlow1, hA, if_true, simLProj, hcnt1, hcnt]
    · set red := td * (o.h.end_time - o.h.start) with hred
      set over := F64.max 0 (red - cur1) with hover
      obtain ⟨cu, hcu⟩ : ∃ x, simLNest hp mult o.h.kind o.nested.val (F64.max 0 (cur1 - red), F64.max 0 (unc1 - red)) = x :=
        ⟨_, rfl⟩
      rcases cu with ⟨c1, c2⟩
      have hn2 := hnest (F64.max 0 (cur1 - red)) (F64.max 0 (unc1 - red))
      rw [hcu] at hn2
      have hla : simLInc hp mult o.h = a := by simp [simLInc, ea]
      by_cases hB : 0 < over ∧ c1 - over ≤ lhe
      · rw [show sim.scoring.legacy_pass_loop0.body pb hp mult lhe false td cur unc cnt low last cb i =
            ok (.cont (true, td * 0.96, c1, c2, cnt1, low1, o.h.end_time, cb', i1)) by
          simp [sim.scoring.legacy_pass_loop0.body, hlt', hc1, vec_index_eq _ _ hlt, ← ho, hcb', float.F64.sub,
            float.F64.mul, net.max_refines, sim_scoring_F64_0, float.F64.lt, float.F64.le, hA, hi1, ← hamt, ← hunc1,
            ← hcur1, ← hred, ← hover, hn2, hB.1, hB.2]
          split_ifs <;> simp_all]
        simp only [bind_ok]
        have := sim_lp_stopped pb hp mult lhe (td * 0.96) c1 c2 cnt1 low1 o.h.end_time cb' i1
        unfold sim.scoring.legacy_pass_loop0 at this
        refine ⟨_, this, ?_⟩
        simp only [simForStep, simLStep, hbs, ← hamt, ← hunc1, ← hcur1, ← hlow1, hA, if_false, ← hred, ← hover, hcu,
          hB, and_self, if_true, simLProj, hcnt1, hcnt]
      · rw [show sim.scoring.legacy_pass_loop0.body pb hp mult lhe false td cur unc cnt low last cb i =
            ok (.cont (false, td, F64.max 0 (F64.min 1 (c1 + a)), c2 + a, cnt1, low1, o.h.end_time, cb', i1)) by
          simp [sim.scoring.legacy_pass_loop0.body, hlt', hc1, vec_index_eq _ _ hlt, ← ho, hcb', float.F64.sub,
            float.F64.mul, net.max_refines, sim_scoring_F64_0, float.F64.lt, float.F64.le, hA, hi1, ← hamt, ← hunc1,
            ← hcur1, ← hred, ← hover, hn2, ha, float.F64.add, sim.scoring.cap01, net.min_refines, sim_scoring_F64_1]
          split_ifs <;> simp_all]
        simp only [bind_ok]
        obtain ⟨r, hr, er⟩ := ih td (F64.max 0 (F64.min 1 (c1 + a))) (c2 + a) cnt1 low1 o.h.end_time cb' i1
          (by omega) (by omega) hcbl (by omega)
        unfold sim.scoring.legacy_pass_loop0 at hr
        refine ⟨r, hr, ?_⟩
        rw [er]
        simp only [simForStep, simLStep, hbs, ← hamt, ← hunc1, ← hcur1, ← hlow1, hA, if_false, ← hred, ← hover, hcu,
          hB, hla, ei1, ← ecb', hcnt1, hcnt]

theorem sim_exc_forIn_map {α γ β : Type} (f : α → γ) (g : α → β → ForInStep β) (F : γ → β → Except String (ForInStep β)) :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ s, F (f x) s = .ok (g x s)) →
      forIn (l.map f) b F = .ok (l.foldr (simForStep g) id b) := by
  intro l; induction l with
  | nil => intro b _; rfl
  | cons x t ih =>
    intro b hF
    rw [List.map_cons, List.forIn_cons, hF x List.mem_cons_self]
    simp only [List.foldr_cons, simForStep]
    cases g x b with
    | done c => rfl
    | yield c => exact ih c (fun y hy s => hF y (List.mem_cons_of_mem _ hy) s)

theorem simS_lnest (hp mult : F64) (hk : sim.playable.Kind) (l : List sim.playable.HObj) (cu : F64 × F64) (tn : Nat → String) :
    forIn (m := Except String) (l.map (hobjS tn)).toArray cu (fun n s =>
      if ((kindS hk == OsuModel.Sim.Kind.spinner && n.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true) then
        pure (ForInStep.yield (s.1, s.2))
      else if (kindS hk != OsuModel.Sim.Kind.slider && kindS hk != OsuModel.Sim.Kind.spinner) = true then
        pure (ForInStep.yield (s.1, s.2))
      else pure (ForInStep.yield (F64.max 0 (F64.min 1 (s.1 + OsuModel.Sim.legacyHealthIncrease hp mult n.kind n.maxResult)),
        s.2 + OsuModel.Sim.legacyHealthIncrease hp mult n.kind n.maxResult))) =
      .ok (simLNest hp mult hk l cu) := by
  rw [← Array.forIn_toList, List.toList_toArray]
  rw [sim_exc_forIn_map (hobjS tn) (fun n s => ForInStep.yield (if simLSkip hk n.kind then s else
    (F64.max 0 (F64.min 1 (s.1 + simLInc hp mult n)), s.2 + simLInc hp mult n))) _ l cu ?hF]
  case hF =>
    intro x _ s
    simp only [simLSkip, simLInc, hobjS]
    by_cases c1 : (kindS hk == OsuModel.Sim.Kind.spinner && kindS x.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true <;>
      by_cases c2 : (kindS hk != OsuModel.Sim.Kind.slider && kindS hk != OsuModel.Sim.Kind.spinner) = true <;>
      simp only [c1, c2, if_true, if_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
        Bool.false_eq_true, ite_true, ite_false, Bool.not_eq_true] <;> rfl
  · unfold simLNest
    generalize cu = c
    induction l generalizing c with
    | nil => rfl
    | cons x t ih => simp only [List.foldr_cons, simForStep, List.foldl_cons]; exact ih _

abbrev SimLO := Option (F64 × F64) × F64 × F64 × Nat

def simLPassF (pb : sim.playable.Playable) (hp ds lhe mult td : F64) : Bool × F64 × F64 × F64 × Nat :=
  simLProj (pb.objects.val.foldr (simForStep (simLStep (simVPS pb.breaks) hp mult lhe)) id (td, 1, 1, 1, ds, 0, false, 0))

def simLOStep (pass : F64 → F64 → Bool × F64 × F64 × F64 × Nat) (lhe_end hra : F64) (st : SimLO) : ForInStep SimLO :=
  if st.2.2.2 > 0 then
    let P := pass st.2.1 st.2.2.1
    if (P.2.2.2.2 == 0) = true then .done (some (P.2.1, st.2.1), st.2.1, P.2.1, st.2.2.2 - 1)
    else
      let a := if (!P.1 && decide (P.2.2.1 < lhe_end)) = true then (true, P.2.1 * 0.94, st.2.1 * 1.01)
        else (P.1, P.2.1, st.2.1)
      let rc := (P.2.2.2.1 - 1) / F64.max 1 (F64.ofInt P.2.2.2.2)
      let b := if (!a.1 && decide (rc < hra)) = true then (true, a.2.1 * 0.96, a.2.2 * 1.01) else a
      if (!b.1 && (b.2.2 == F64.posInf || b.2.2 == F64.negInf)) = true then .done (some (0, 1), b.2.2, b.2.1, st.2.2.2 - 1)
      else if (!b.1) = true then .done (some (b.2.1, b.2.2), b.2.2, b.2.1, st.2.2.2 - 1)
      else .yield (none, b.2.2, b.2.1, st.2.2.2 - 1)
  else .done (none, st.2.1, st.2.2.1, st.2.2.2)

def simLRun (g : SimLO → ForInStep SimLO) : Nat → SimLO → SimLO
  | 0, st => st
  | n + 1, st => match g st with | .done c => c | .yield c => simLRun g n c

theorem sim_lo_fuel (pass : F64 → F64 → Bool × F64 × F64 × F64 × Nat) (le hra : F64) (st c : SimLO)
    (h : simLOStep pass le hra st = .yield c) : c.2.2.2 + 1 = st.2.2.2 := by
  unfold simLOStep at h
  by_cases h0 : st.2.2.2 > 0
  · rw [if_pos h0] at h
    generalize pass st.2.1 st.2.2.1 = P at h
    dsimp only at h
    repeat' split at h
    all_goals first
      | (rw [← ForInStep.yield.inj h]; dsimp only; omega)
      | exact absurd h (by simp)
  · rw [if_neg h0] at h; exact absurd h (by simp)

theorem sim_lo_loop (pass : F64 → F64 → Bool × F64 × F64 × F64 × Nat) (le hra : F64)
    (F : Unit → SimLO → Except String (ForInStep SimLO)) (hF : ∀ st, F () st = .ok (simLOStep pass le hra st)) :
    ∀ n st, st.2.2.2 < n → forIn Lean.Loop.mk st F = .ok (simLRun (simLOStep pass le hra) n st) := by
  intro n
  induction n with
  | zero => intro st h; omega
  | succ n ih =>
    intro st h
    rw [sim_exc_loop_unfold, hF]
    simp only [simLRun]
    cases hs : simLOStep pass le hra st with
    | done c => rfl
    | yield c =>
      have := sim_lo_fuel pass le hra st c hs
      exact ih c (by omega)

theorem sim_scanG_brk2 (B : List (F64 × F64)) (t : F64) :
    ∀ n cb lt, simScanG (fun (s : F64 × Nat) => match B[s.2]? with
        | some b => if b.2 ≤ t then ForInStep.yield (t, s.2 + 1) else ForInStep.done (s.1, s.2)
        | none => ForInStep.done (s.1, s.2)) n (lt, cb) = ((simBrk B t n (cb, lt)).2, (simBrk B t n (cb, lt)).1) := by
  intro n; induction n with
  | zero => intro cb lt; rfl
  | succ n ih =>
    intro cb lt
    simp only [simScanG, simBrk]
    cases B[cb]? with
    | none => rfl
    | some b => dsimp only; split_ifs <;> [exact ih _ _; rfl]


theorem simS_lpass (tn) (pb : sim.playable.Playable) (hp mult lhe : F64)
    (Fp : OsuModel.Sim.TopObj → SimLS → Except String (ForInStep SimLS))
    (hFp : ∀ o ∈ pb.objects.val, ∀ s, Fp (topS tn o) s = .ok (simLStep (simVPS pb.breaks) hp mult lhe o s))
    (s0 : SimLS) :
    forIn (playableS tn pb).objects s0 Fp = .ok (pb.objects.val.foldr (simForStep (simLStep (simVPS pb.breaks) hp mult lhe)) id s0) := by
  rw [← Array.forIn_toList]
  have : (playableS tn pb).objects.toList = pb.objects.val.map (topS tn) := by simp [playableS]
  rw [this]
  exact sim_exc_forIn_map (topS tn) _ Fp pb.objects.val s0 hFp


theorem simS_computeLegacyDrainRate (tn) (pb : sim.playable.Playable) (hp ds : F64) :
    OsuModel.Sim.computeLegacyDrainRate (playableS tn pb) hp ds =
      match (simLRun (simLOStep (simLPassF pb hp ds (OsuModel.Sim.difficultyRange hp 0.975 0.8 0.3))
          (OsuModel.Sim.difficultyRange hp 0.99 0.9 0.4) (OsuModel.Sim.difficultyRange hp 4e-2 2e-2 0))
          1000001 (none, 1, 25e-5, 1000000)).1 with
      | some r => .ok r
      | none => .error "internal: legacy ComputeDrainRate fuel exhausted" := by
  unfold OsuModel.Sim.computeLegacyDrainRate
  simp only []
  rw [sim_lo_loop (simLPassF pb hp ds (OsuModel.Sim.difficultyRange hp 0.975 0.8 0.3))
    (OsuModel.Sim.difficultyRange hp 0.99 0.9 0.4) (OsuModel.Sim.difficultyRange hp 4e-2 2e-2 0) _ ?hF 1000001 _ (by decide)]
  case hF =>
    intro st
    obtain ⟨r, mult, td, fuel⟩ := st
    by_cases h0 : fuel > 0
    · simp only [h0, if_true, simLOStep]
      rw [simS_lpass tn pb hp mult (OsuModel.Sim.difficultyRange hp 0.975 0.8 0.3) _ ?hFp]
      case hFp =>
        intro o _ s
        obtain ⟨td', cur, unc, low, last, cb, fail, cnt⟩ := s
        have hB : (playableS tn pb).breaks.toList = simVPS pb.breaks := by simp [playableS, abs, simVPS]
        have hBs : (playableS tn pb).breaks.size = (simVPS pb.breaks).length := by rw [← hB]; simp
        dsimp only
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        rw [sim_exc_forIn_constF (fun (s : F64 × Nat) => match (simVPS pb.breaks)[s.2]? with
          | some b => if b.2 ≤ o.h.start then ForInStep.yield (o.h.start, s.2 + 1) else ForInStep.done (s.1, s.2)
          | none => ForInStep.done (s.1, s.2)) _ ?hb]
        case hb =>
          intro j x
          have e : (playableS tn pb).breaks[x.2]? = (simVPS pb.breaks)[x.2]? := by rw [← Array.getElem?_toList, hB]
          cases hx : (simVPS pb.breaks)[x.2]? with
          | none => simp only [e, hx]; rfl
          | some b =>
            simp only [e, hx]
            split_ifs <;> first | rfl | (exfalso; rename_i h1 h2; exact h1 h2) | (exfalso; rename_i h1 h2; exact h2 h1)
        simp only [List.length_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, hBs,
          sim_scanG_brk2]
        have hN : ∀ c u, forIn (m := Except String) (topS tn o).nested (c, u) (fun n (__s : F64 × F64) =>
            if ((topS tn o).h.kind == OsuModel.Sim.Kind.spinner && n.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then
              pure (ForInStep.yield (__s.1, __s.2))
            else if ((topS tn o).h.kind != OsuModel.Sim.Kind.slider && (topS tn o).h.kind != OsuModel.Sim.Kind.spinner) = true then
              pure (ForInStep.yield (__s.1, __s.2))
            else pure (ForInStep.yield
              (F64.max 0 (F64.min 1 (__s.1 + OsuModel.Sim.legacyHealthIncrease hp mult n.kind n.maxResult)),
                __s.2 + OsuModel.Sim.legacyHealthIncrease hp mult n.kind n.maxResult))) =
            .ok (simLNest hp mult o.h.kind o.nested.val (c, u)) := by
          intro c u
          exact simS_lnest hp mult o.h.kind o.nested.val (c, u) tn
        simp only [hN]
        obtain ⟨bs, hbs⟩ : ∃ x, simBrk (simVPS pb.breaks) o.h.start (simVPS pb.breaks).length (cb, last) = x := ⟨_, rfl⟩
        rw [hbs]
        simp only [Bind.bind, Except.bind]
        unfold simLStep
        simp only [hbs]
        have e1 : (topS tn o).h.start = o.h.start := rfl
        have e2 : (topS tn o).h.endTime = o.h.end_time := rfl
        have e3 : OsuModel.Sim.legacyHealthIncrease hp mult (topS tn o).h.kind (topS tn o).h.maxResult = simLInc hp mult o.h := rfl
        simp only [e1, e2, e3]
        split_ifs <;> first | rfl | simp_all
      simp only [Bind.bind, Except.bind]
      generalize hX : List.foldr (simForStep (simLStep (simVPS pb.breaks) hp mult
        (OsuModel.Sim.difficultyRange hp 0.975 0.8 0.3))) id pb.objects.val (td, 1, 1, 1, ds, 0, false, 0) = X
      simp only [simLPassF, hX, simLProj]
      split_ifs <;> first | rfl | simp_all
    · simp [h0, simLOStep]
  simp only [Bind.bind, Except.bind]
  split <;> rename_i h <;> simp only [h] <;> rfl

@[simp] theorem sim_scoring_F64_POS_INF : sim.scoring.F64_POS_INF = ok F64.posInf := by
  simp [sim.scoring.F64_POS_INF]; decide
@[simp] theorem sim_scoring_F64_NEG_INF : sim.scoring.F64_NEG_INF = ok F64.negInf := by
  simp [sim.scoring.F64_NEG_INF]; decide

theorem sim.scoring.legacy_pass_refines (pb : sim.playable.Playable) (hp ds mult td0 lhe : F64) :
    ∃ p, sim.scoring.legacy_pass pb hp ds mult td0 lhe = ok p ∧
      (p.fail, p.test_drop, p.current_hp, p.current_hp_uncapped, p.top_level_object_count.val) =
        simLPassF pb hp ds lhe mult td0 := by
  obtain ⟨r, hr, er⟩ := sim_lp_loop pb hp mult lhe _ td0 1 1 0#u64 1 ds 0#usize 0#usize rfl (by simp) (by simp) (by simp)
  refine ⟨⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩, ?_, ?_⟩
  · simp only [sim.scoring.legacy_pass, sim_scoring_F64_1, bind_ok, hr]
    obtain ⟨a, b, c, d, e⟩ := r; rfl
  · simp only [simLPassF]; rw [er]; simp

def simLRate (x : sim.scoring.LegacyRate) : F64 × F64 := (x.test_drop, x.mult)

theorem sim_lo_stopped (pb : sim.playable.Playable) (hp ds lhe lhn hra mult td : F64) (fuel : U32)
    (x : sim.scoring.LegacyRate) :
    sim.scoring.compute_legacy_drain_rate_loop 0 1 pb hp ds lhe lhn hra mult td fuel (some x) = ok (some x) := by
  unfold sim.scoring.compute_legacy_drain_rate_loop; rw [loop_unfold]
  by_cases h : fuel > 0#u32 <;> simp [sim.scoring.compute_legacy_drain_rate_loop.body, h, core.option.Option.is_none]

theorem sim_lo_loop_rust (pb : sim.playable.Playable) (hp ds lhe lhn hra : F64) :
    ∀ n (mult td : F64) (fuel : U32), fuel.val < n →
      ∃ R, sim.scoring.compute_legacy_drain_rate_loop 0 1 pb hp ds lhe lhn hra mult td fuel none = ok R ∧
        R.map simLRate = (simLRun (simLOStep (simLPassF pb hp ds lhe) lhn hra) n (none, mult, td, fuel.val)).1 := by
  intro n
  induction n with
  | zero => intro mult td fuel h; omega
  | succ n ih =>
    intro mult td fuel hfu
    by_cases h0 : fuel.val > 0
    · have hfp : fuel > 0#u32 := h0
      obtain ⟨f1, hf1, ef1⟩ : ∃ z, fuel - 1#u32 = ok z ∧ z.val = fuel.val - 1 := u32_sub_one fuel (by omega)
      obtain ⟨p, hp', ep⟩ := sim.scoring.legacy_pass_refines pb hp ds mult td lhe
      simp only [simLRun, simLOStep, h0, if_true, ← ep]
      unfold sim.scoring.compute_legacy_drain_rate_loop; rw [loop_unfold]
      dsimp only
      have hst := fun (x : F64 × F64 × sim.scoring.LegacyRate) => sim_lo_stopped pb hp ds lhe lhn hra x.1 x.2.1 f1 x.2.2
      by_cases c0 : p.top_level_object_count = 0#u64
      · have c0' : p.top_level_object_count.val = 0 := by rw [c0]; rfl
        rw [show sim.scoring.compute_legacy_drain_rate_loop.body 0 1 pb hp ds lhe lhn hra mult td fuel none =
            ok (.cont (mult, p.test_drop, f1, some ⟨p.test_drop, mult⟩)) by
          simp [sim.scoring.compute_legacy_drain_rate_loop.body, hfp, core.option.Option.is_none, hf1, hp', c0]]
        simp only [bind_ok]
        have := hst (mult, p.test_drop, ⟨p.test_drop, mult⟩)
        unfold sim.scoring.compute_legacy_drain_rate_loop at this
        refine ⟨_, this, ?_⟩
        simp [c0', simLRate]
      · have c0' : p.top_level_object_count.val ≠ 0 := fun e => c0 (UScalar.eq_of_val_eq (by simpa using e))
        simp only [c0', beq_iff_eq, if_false]
        set a : Bool × F64 × F64 := if (!p.fail && decide (p.current_hp < lhn)) = true then (true, p.test_drop * 0.94, mult * 1.01)
          else (p.fail, p.test_drop, mult) with ha
        set rc := (p.current_hp_uncapped - 1) / F64.max 1 (F64.ofInt p.top_level_object_count.val) with hrc
        set b : Bool × F64 × F64 := if (!a.1 && decide (rc < hra)) = true then (true, a.2.1 * 0.96, a.2.2 * 1.01) else a with hb
        have hbody : sim.scoring.compute_legacy_drain_rate_loop.body 0 1 pb hp ds lhe lhn hra mult td fuel none =
            ok (.cont (b.2.2, b.2.1, f1, if b.1 then none else
              if (b.2.2 == F64.posInf || b.2.2 == F64.negInf) then some ⟨0, 1⟩ else some ⟨b.2.1, b.2.2⟩)) := by
          simp only [sim.scoring.compute_legacy_drain_rate_loop.body, hfp, if_true, core.option.Option.is_none,
            Option.isNone_none, hf1, bind_ok, hp', c0, if_false]
          by_cases cA : (!p.fail && decide (p.current_hp < lhn)) = true <;>
            by_cases cB : (!a.1 && decide (rc < hra)) = true <;>
            simp_all [float.F64.lt, float.F64.mul, float.F64.sub, float.F64.from_u64, net.max_refines, float.F64.div,
              sim_scoring_F64_POS_INF, sim_scoring_F64_NEG_INF, float.F64.eq] <;>
            split_ifs <;> simp_all <;> (intros; simp_all)
        rw [hbody]; simp only [bind_ok]
        cases hb1 : b.1
        · by_cases hinf : (b.2.2 == F64.posInf || b.2.2 == F64.negInf) = true
          · have := hst (b.2.2, b.2.1, ⟨0, 1⟩)
            unfold sim.scoring.compute_legacy_drain_rate_loop at this
            refine ⟨_, by simp only [hinf, if_true, Bool.false_eq_true, if_false]; exact this, ?_⟩
            simp [hinf, simLRate]
          · have := hst (b.2.2, b.2.1, ⟨b.2.1, b.2.2⟩)
            unfold sim.scoring.compute_legacy_drain_rate_loop at this
            refine ⟨_, by simp only [hinf, if_false, Bool.false_eq_true]; exact this, ?_⟩
            simp [hinf, simLRate]
        · obtain ⟨R, hR, eR⟩ := ih b.2.2 b.2.1 f1 (by omega)
          unfold sim.scoring.compute_legacy_drain_rate_loop at hR
          refine ⟨R, by simp only [if_true]; exact hR, ?_⟩
          simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
          rw [eR, ef1]
    · have hfp : ¬ fuel > 0#u32 := h0
      refine ⟨none, ?_, ?_⟩
      · unfold sim.scoring.compute_legacy_drain_rate_loop; rw [loop_unfold]
        simp [sim.scoring.compute_legacy_drain_rate_loop.body, hfp]
      · simp [simLRun, simLOStep, h0]

theorem sim_scoring_difficulty_range_eq (d mn mid mx : F64) :
    sim.scoring.difficulty_range d mn mid mx = ok (OsuModel.Sim.difficultyRange d mn mid mx) := by
  obtain ⟨r, h, e⟩ := sim.scoring.difficulty_range_refines d mn mid mx
  rw [h]; simp only [abs, id] at e; rw [e]

def simLRF (D : Option sim.scoring.LegacyRate) : core.result.Result sim.scoring.LegacyRate sim.err.SimErr :=
  match D with
  | none => core.result.Result.Err (sim.err.SimErr.Internal sim.err.Internal.LegacyDrainFuel)
  | some r => core.result.Result.Ok r

theorem sim.scoring.compute_legacy_drain_rate_refines (tn) (pb : sim.playable.Playable) (hp ds : F64) :
    ∃ R, sim.scoring.compute_legacy_drain_rate pb hp ds = ok R ∧
      simRel simLRate R (OsuModel.Sim.computeLegacyDrainRate (playableS tn pb) hp ds) := by
  rw [simS_computeLegacyDrainRate]
  obtain ⟨D, hD, eD⟩ := sim_lo_loop_rust pb hp ds (OsuModel.Sim.difficultyRange hp 0.975 0.8 0.3)
    (OsuModel.Sim.difficultyRange hp 0.99 0.9 0.4) (OsuModel.Sim.difficultyRange hp 4e-2 2e-2 0) 1000001 1 25e-5
    1000000#u32 (by simp)
  have hloop : sim.scoring.compute_legacy_drain_rate pb hp ds = ok (simLRF D) := by
    simp only [sim.scoring.compute_legacy_drain_rate, sim_scoring_difficulty_range_eq, sim_scoring_F64_0,
      sim_scoring_F64_1, bind_ok, fb64_4606957238818648883, fb64_4605380978949069210, fb64_4599075939470750515,
      fb64_4607092346807469998, fb64_4606281698874543309, fb64_4600877379321698714, fb64_4585925428558828667,
      fb64_4581421828931458171, fb64_4553247309662628348]
    erw [hD]; cases D <;> simp [simLRF]
  refine ⟨_, hloop, ?_⟩
  simp only [show (1000000#u32 : U32).val = 1000000 from rfl] at eD
  rw [← eD]
  cases D with
  | none => exact ⟨_, rfl⟩
  | some r => rfl
end OsuProofs
