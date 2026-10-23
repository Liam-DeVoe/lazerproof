/-
Sim3b part 5: `adaptive_speed_on_result` refines `Sim.adaptiveSpeedOnResult` (ModAdaptiveSpeed `OnNewResult`).
Spec side: the zipped `for d in dynRates, k in [0:n]` loop is evaluated by `s3b_forIn_zip` against the list
recursion `s3b_asLoopS` (one step per dyn rate; AS steps via `s3b_asBodyS`); the Rust index loop is matched against
the same recursion.
-/
import OsuProofs.Sim3.SB_Dyn
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-- spec result relation up to error messages -/
def s3b_res {α : Type} : Except String OsuModel.Sim.St → Except String (α × OsuModel.Sim.St) → Prop
  | .ok S, .ok (_, S') => S = S'
  | .error _, .error _ => True
  | _, _ => False

/-- `k`-th position stream of `[0:n]` -/
def s3b_rg (k n : Nat) : Std.Legacy.Range := { start := k, stop := n, step := 1, step_pos := by omega }

theorem s3b_rg_next (k n : Nat) (h : k < n) : Std.Stream.next? (s3b_rg k n) = some (k, s3b_rg (k + 1) n) := by
  simp [Std.Stream.next?, s3b_rg, h]

/-- the abstract AS loop: `G d ai k S` is one step (identity for non-AS rates); `ai` counts AS mods -/
def s3b_asLoop (G : OsuModel.Sim.DynRate → Nat → Nat → OsuModel.Sim.St → Except String OsuModel.Sim.St) :
    List OsuModel.Sim.DynRate → Nat → Nat → OsuModel.Sim.St → Except String OsuModel.Sim.St
  | [], _, _, S => .ok S
  | d :: l, ai, k, S => match G d ai k S with
    | .ok S' => s3b_asLoop G l (if s3b_isAdS d then ai + 1 else ai) (k + 1) S'
    | .error e => .error e

/-- the zipped spec loop, given a characterisation of its body `F` by the step function `G` -/
theorem s3b_forIn_zip (F : OsuModel.Sim.DynRate → Nat × Std.Legacy.Range →
      OsuModel.Sim.SimM (ForInStep (Nat × Std.Legacy.Range))) (C : OsuModel.Sim.Ctx)
    (G : OsuModel.Sim.DynRate → Nat → Nat → OsuModel.Sim.St → Except String OsuModel.Sim.St)
    (hF : ∀ d ai k n S, k < n →
      (∀ S', G d ai k S = .ok S' →
        F d (ai, s3b_rg k n) C S = .ok (.yield (if s3b_isAdS d then ai + 1 else ai, s3b_rg (k + 1) n), S')) ∧
      (∀ e, G d ai k S = .error e → ∃ m, F d (ai, s3b_rg k n) C S = .error m)) :
    ∀ (l : List OsuModel.Sim.DynRate) ai k n S, l.length + k ≤ n →
      s3b_res (s3b_asLoop G l ai k S) (forIn l (ai, s3b_rg k n) F C S) := by
  intro l
  induction l with
  | nil => intro ai k n S _; exact rfl
  | cons d l ih =>
    intro ai k n S hl
    simp only [List.length_cons] at hl
    rw [List.forIn_cons, s3b_asLoop]
    obtain ⟨h1, h2⟩ := hF d ai k n S (by omega)
    cases hG : G d ai k S with
    | ok S' =>
      simp only [simM_bind, h1 S' hG, Except.bind]
      exact ih _ (k + 1) n S' (by omega)
    | error e =>
      obtain ⟨m, hm⟩ := h2 e hG
      simp only [simM_bind, hm, Except.bind]
      exact trivial

/-- the spec consistency loop result for `x :: l` (first failing `sign` is reported, as `liftNet` does) -/
def s3b_consRes (x : F64) (l : List F64) (S : OsuModel.Sim.St) :
    Except String ((Int × Option F64) × OsuModel.Sim.St) :=
  match s3b_cons x l 0 with
  | .ok c => .ok ((c, some ((x :: l).getLast (by simp))), S)
  | .error e => .error s!"lazer would throw: {repr e}"

theorem s3b_cons_forIn_list (F : F64 → Int × Option F64 → OsuModel.Sim.SimM (ForInStep (Int × Option F64)))
    (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St)
    (hF1 : ∀ x c p sg, F64.sign (x - p) = .ok sg → F x (c, some p) C S = .ok (.yield (c + sg.toInt, some x), S))
    (hF2 : ∀ x c p e, F64.sign (x - p) = .error e → F x (c, some p) C S = .error s!"lazer would throw: {repr e}") :
    ∀ (l : List F64) (p : F64) (c : Int), forIn l (c, some p) F C S =
      match s3b_cons p l c with
      | .ok c' => .ok ((c', some ((p :: l).getLast (by simp))), S)
      | .error e => .error s!"lazer would throw: {repr e}" := by
  intro l
  induction l with
  | nil => intro p c; rfl
  | cons x t ih =>
    intro p c
    rw [List.forIn_cons]
    simp only [s3b_cons]
    cases hs : F64.sign (x - p) with
    | ok sg =>
      simp only [simM_bind, hF1 x c p sg hs, Except.bind]
      rw [ih x (c + sg.toInt)]
      simp [List.getLast_cons]
    | error e => simp only [simM_bind, hF2 x c p e hs, Except.bind]

theorem s3b_cons_forIn (F : F64 → Int × Option F64 → OsuModel.Sim.SimM (ForInStep (Int × Option F64)))
    (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (a : _root_.Array F64) (x : F64) (l : List F64) (ha : a.toList = x :: l)
    (hF0 : ∀ x c, F x (c, none) C S = .ok (.yield (c, some x), S))
    (hF1 : ∀ x c p sg, F64.sign (x - p) = .ok sg → F x (c, some p) C S = .ok (.yield (c + sg.toInt, some x), S))
    (hF2 : ∀ x c p e, F64.sign (x - p) = .error e → F x (c, some p) C S = .error s!"lazer would throw: {repr e}") :
    forIn a ((0 : Int), (none : Option F64)) F C S = s3b_consRes x l S := by
  rw [← Array.forIn_toList, ha, List.forIn_cons]
  simp only [simM_bind, hF0, Except.bind]
  rw [s3b_cons_forIn_list F C S hF1 hF2]
  rfl

/-- one AS step of `adaptiveSpeedOnResult` on the spec state (errors: any message) -/
def s3b_asBodyS (C : OsuModel.Sim.Ctx) (r : OsuModel.Sim.Ref) (ty : OsuModel.Sim.HitResult) (t : F64)
    (h : OsuModel.Sim.HObj) (ai k : Nat) (S : OsuModel.Sim.St) : Except String OsuModel.Sim.St :=
  match S.asSeen[ai]?, C.precEnd[r.1]? with
  | some seen, some (top, ns) =>
    match (if r.2 < 0 then some top else ns[r.2.toNat]?) with
    | none => .error ""
    | some prev? =>
      if (!seen.contains r && ty.affectsAccuracy) = true then
        match prev? with
        | some prev =>
          match S.speed[k]?, S.asRecent[ai]?, S.asTarget[ai]? with
          | some sp, some rc, some tg =>
            match s3b_asStep ty.isHit h.endTime (OsuModel.Sim.Sim.timeAbsolute h t) prev rc.toList sp tg with
            | .ok (tgt, rec) =>
              .ok { S with asSeen := S.asSeen.set! ai (r :: seen), asRecent := S.asRecent.set! ai rec.toArray, asTarget := S.asTarget.set! ai tgt }
            | .error _ => .error ""
          | _, _, _ => .error ""
        | none => .ok S
      else .ok S
  | _, _ => .error ""

def s3b_asG (C : OsuModel.Sim.Ctx) (r : OsuModel.Sim.Ref) (ty : OsuModel.Sim.HitResult) (t : F64)
    (h : OsuModel.Sim.HObj) (d : OsuModel.Sim.DynRate) (ai k : Nat) (S : OsuModel.Sim.St) :
    Except String OsuModel.Sim.St :=
  match d with
  | .adaptive _ => s3b_asBodyS C r ty t h ai k S
  | .timeRamp .. => .ok S

@[simp] theorem s3b_ebind_ok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a).bind f = f a := rfl

theorem s3b_res_post {α : Type} (C : OsuModel.Sim.Ctx) (x : Except String OsuModel.Sim.St) (y : Except String (α × OsuModel.Sim.St))
    (h : s3b_res x y) :
    s3b_res x (y.bind (fun p => (pure PUnit.unit : OsuModel.Sim.SimM PUnit) C p.2)) := by
  rcases x with _ | x <;> rcases y with _ | ⟨a, S⟩ <;> simp_all [s3b_res, Except.bind] <;> rfl

theorem s3b_extract_eq (rc : _root_.Array F64) (x : F64) :
    (((rc.toList.drop 1).take 7 ++ [x]).toArray) = (rc.extract 1 8).push x := by
  apply Array.ext'; simp [List.take_drop]; rcases rc.toList with _ | ⟨a, l⟩ <;> simp

theorem s3b_list_head (L : List F64) (h : L ≠ []) : L = L[0]! :: L.drop 1 := by
  rcases L with _ | ⟨a, l⟩
  · exact absurd rfl h
  · rfl

theorem s3b_set_bang {α} (a : _root_.Array α) (i : Nat) (h : i < a.size) (x : α) : a.set! i x = a.set i x h := by
  simp [Array.set!, Array.setIfInBounds, h]

set_option hygiene false in
/-- the AS step after `rel` (shared by the hit / non-hit branches of the spec) -/
macro "s3b_as_core" : tactic => `(tactic| (
  try simp only [simM_bind, simM_pure, s3b_ebind_ok]
  by_cases hs1 : k < S'.speed.size
  swap
  · simp only [getElem?_neg S'.speed k hs1]
    exact ⟨fun S1 hG => (nomatch hG), fun e _ => ⟨_, by simp only [dif_neg hs1, simM_throw, Except.bind]; rfl⟩⟩
  by_cases hs2 : ai < S'.asRecent.size
  swap
  · simp only [getElem?_neg S'.asRecent ai hs2]
    exact ⟨fun S1 hG => (by revert hG; cases S'.speed[k]? <;> simp),
      fun e _ => ⟨_, by simp only [dif_pos hs1, dif_neg hs2, simM_pure, simM_throw, Except.bind, s3b_ebind_ok]; rfl⟩⟩
  simp only [getElem?_pos S'.speed k hs1, getElem?_pos S'.asRecent ai hs2, dif_pos hs1, dif_pos hs2, simM_pure,
    s3b_ebind_ok]
  unfold s3b_asCore
  cases hcl2 : F64.clamp (rel * S'.speed[k]) 0.4 2.5 with
  | error e =>
    refine ⟨fun S1 hG => ?_, fun e' _ => ⟨_, by simp only [OsuModel.Sim.Sim.liftNet, hcl2, simM_throw, Except.bind]; rfl⟩⟩
    revert hG; cases S'.asTarget[ai]? <;> intro hG <;> simp only [hcl2, reduceCtorEq] at hG
  | ok last =>
    simp only [OsuModel.Sim.Sim.liftNet, simM_pure, s3b_ebind_ok]
    try dsimp only
    generalize hL : (S'.asRecent[ai].toList.drop 1).take 7 ++ [last] = L
    have hLne : L ≠ [] := by rw [← hL]; simp
    have ha : ((S'.asRecent[ai].extract 1 8).push last).toList = L[0]! :: L.drop 1 := by
      rw [← s3b_extract_eq, ← hL]; simp only [List.toList_toArray]; rw [hL]; exact s3b_list_head L hLne
    rw [s3b_cons_forIn _ C S' _ _ _ ha (by intro x c; rfl)
      (by intro x c p sg hs; simp only [OsuModel.Sim.Sim.liftNet, hs, simM_bind, simM_pure, s3b_ebind_ok])
      (by intro x c p e hs; simp only [OsuModel.Sim.Sim.liftNet, hs, simM_bind, simM_throw, Except.bind])]
    unfold s3b_consRes
    cases hcons : s3b_cons L[0]! (L.drop 1) 0 with
    | error e =>
      refine ⟨fun S1 hG => ?_, fun e' _ => ⟨_, by simp only [Except.bind]; rfl⟩⟩
      revert hG; cases S'.asTarget[ai]? <;> intro hG <;> simp only [hcl2, hL, hcons, reduceCtorEq] at hG
    | ok c =>
      simp only [s3b_ebind_ok]
      have hLa : ((S'.asRecent[ai].extract 1 8).push last).toList = L := by rw [← s3b_extract_eq, ← hL]; try simp
      rw [hLa]
      cases hav : SysMisc.averageF64 L with
      | error e =>
        refine ⟨fun S1 hG => ?_, fun e' _ => ⟨_, by simp only [OsuModel.Sim.Sim.liftNet, hav, simM_throw, Except.bind]; rfl⟩⟩
        revert hG; cases S'.asTarget[ai]? <;> intro hG <;> simp only [hcl2, hL, hcons, hav, reduceCtorEq] at hG
      | ok avg =>
        simp only [OsuModel.Sim.Sim.liftNet, hav, simM_pure, s3b_ebind_ok]
        by_cases hs3 : ai < S'.asTarget.size
        swap
        · simp only [getElem?_neg S'.asTarget ai hs3]
          exact ⟨fun S1 hG => (by simp only [hcl2, hL, hcons, hav, reduceCtorEq] at hG), fun e _ => ⟨_, by simp only [dif_neg hs3, simM_throw]; rfl⟩⟩
        simp only [getElem?_pos S'.asTarget ai hs3, dif_pos hs3, simM_pure, s3b_ebind_ok, OsuModel.Sim.Sim.setA,
          dif_pos h1, dif_pos hs2, simM_set]
        refine ⟨fun S1 hG => ?_, fun e hG => (by simp only [hcl2, hL, hcons, hav, reduceCtorEq] at hG)⟩
        simp only [hcl2, hL, hcons, hav] at hG
        cases hG
        rw [s3b_set_bang _ _ h1, s3b_set_bang _ _ hs2, s3b_set_bang _ _ hs3, ← hLa, Array.toArray_toList]))

theorem s3b_asOnResult_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (r : OsuModel.Sim.Ref)
    (ty : OsuModel.Sim.HitResult) (t : F64) (h : OsuModel.Sim.HObj) (hne : C.cfg.dynRates.isEmpty = false)
    (hh : OsuModel.Sim.Sim.hobjOf r C S = .ok (h, S)) :
    s3b_res (s3b_asLoop (s3b_asG C r ty t h) C.cfg.dynRates.toList 0 0 S)
      (OsuModel.Sim.Sim.adaptiveSpeedOnResult r ty t C S) := by
  unfold OsuModel.Sim.Sim.adaptiveSpeedOnResult
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebind_ok, hne, Bool.false_eq_true, if_false, hh]
  rw [← Array.forIn_toList]
  apply s3b_res_post
  refine s3b_forIn_zip _ C (s3b_asG C r ty t h) ?_ C.cfg.dynRates.toList 0 0 C.cfg.dynRates.size S (by simp)
  intro d ai k n S' hk
  simp only [s3b_rg_next _ _ hk]
  cases d with
  | timeRamp i f b ft =>
    refine ⟨fun S'' hG => ?_, fun e hG => ?_⟩
    · simp only [s3b_asG] at hG; cases hG; rfl
    · simp [s3b_asG] at hG
  | adaptive a =>
    simp only [s3b_asG, s3b_isAdS, if_true]
    simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebind_ok, OsuModel.Sim.Sim.getA]
    by_cases h1 : ai < S'.asSeen.size
    swap
    · refine ⟨fun S'' hG => ?_, fun e _ => ⟨_, by simp only [dif_neg h1, simM_throw, Except.bind]; rfl⟩⟩
      simp [s3b_asBodyS, h1] at hG
    by_cases h2 : r.1 < C.precEnd.size
    swap
    · refine ⟨fun S'' hG => ?_, fun e _ => ⟨_, by simp only [dif_pos h1, dif_neg h2, simM_pure, simM_throw, s3b_ebind_ok, Except.bind]; rfl⟩⟩
      simp [s3b_asBodyS, h1, h2] at hG
    simp only [dif_pos h1, dif_pos h2, simM_pure, s3b_ebind_ok]
    generalize hpe : C.precEnd[r.1] = pe
    obtain ⟨top, ns⟩ := pe
    generalize hseen : S'.asSeen[ai] = seen
    have hB : s3b_asBodyS C r ty t h ai k S' = (match (if r.2 < 0 then some top else ns[r.2.toNat]?) with
        | none => .error ""
        | some prev? =>
          if (!seen.contains r && ty.affectsAccuracy) = true then
            match prev? with
            | some prev =>
              match S'.speed[k]?, S'.asRecent[ai]?, S'.asTarget[ai]? with
              | some sp, some rc, some tg =>
                match s3b_asStep ty.isHit h.endTime (OsuModel.Sim.Sim.timeAbsolute h t) prev rc.toList sp tg with
                | .ok (tgt, rec) =>
                  .ok { S' with asSeen := S'.asSeen.set! ai (r :: seen), asRecent := S'.asRecent.set! ai rec.toArray, asTarget := S'.asTarget.set! ai tgt }
                | .error _ => .error ""
              | _, _, _ => .error ""
            | none => .ok S'
          else .ok S') := by
      simp only [s3b_asBodyS, getElem?_pos S'.asSeen ai h1, getElem?_pos C.precEnd r.1 h2, hpe, hseen]
    rw [hB]
    -- prev?
    by_cases hr : r.2 < 0
    · simp only [hr, if_true, simM_pure, s3b_ebind_ok]
      generalize top = po
      by_cases hc : (!seen.contains r && ty.affectsAccuracy) = true
      swap
      · simp only [hc, Bool.false_eq_true, if_false]
        exact ⟨fun S'' hG => by cases hG; rfl, fun e hG => by cases hG⟩
      simp only [hc, if_true]
      rcases po with _ | prev
      · exact ⟨fun S'' hG => by cases hG; rfl, fun e hG => by cases hG⟩
      simp only [simM_bind, simM_pure, s3b_ebind_ok]
      unfold s3b_asStep s3b_asRel
      cases hhit : ty.isHit
      · simp only [Bool.not_false, if_true, simM_pure, s3b_ebind_ok]
        generalize (0.95 : F64) = rel
        s3b_as_core
      · simp only [Bool.not_true, Bool.false_eq_true, if_false]
        cases hcl : F64.clamp ((h.endTime - prev) / (OsuModel.Sim.Sim.timeAbsolute h t - prev)) 0.9 1.11 with
        | error e =>
          refine ⟨fun S1 hG => ?_, fun e' _ => ⟨_, by
            simp only [simM_bind, OsuModel.Sim.Sim.liftNet, hcl, simM_throw, Except.bind]; rfl⟩⟩
          revert hG; cases S'.speed[k]? <;> cases S'.asRecent[ai]? <;> cases S'.asTarget[ai]? <;> simp [hcl]
        | ok rel =>
          simp only [simM_bind, OsuModel.Sim.Sim.liftNet, hcl, simM_pure, s3b_ebind_ok]
          s3b_as_core
    · simp only [hr, if_false]
      by_cases hn : r.2.toNat < ns.size
      swap
      · refine ⟨fun S'' hG => ?_, fun e _ => ⟨_, by simp only [dif_neg hn, simM_throw, Except.bind]; rfl⟩⟩
        simp only [hr, if_false, getElem?_neg ns r.2.toNat hn, reduceCtorEq] at hG
      · simp only [dif_pos hn, getElem?_pos ns r.2.toNat hn, simM_pure, s3b_ebind_ok, simM_bind]
        generalize ns[r.2.toNat] = po
        by_cases hc : (!seen.contains r && ty.affectsAccuracy) = true
        swap
        · simp only [hc, Bool.false_eq_true, if_false]
          exact ⟨fun S'' hG => by cases hG; rfl, fun e hG => by cases hG⟩
        simp only [hc, if_true]
        rcases po with _ | prev
        · exact ⟨fun S'' hG => by cases hG; rfl, fun e hG => by cases hG⟩
        simp only [simM_bind, simM_pure, s3b_ebind_ok]
        unfold s3b_asStep s3b_asRel
        cases hhit : ty.isHit
        · simp only [Bool.not_false, if_true, simM_pure, s3b_ebind_ok]
          generalize (0.95 : F64) = rel
          s3b_as_core
        · simp only [Bool.not_true, Bool.false_eq_true, if_false]
          cases hcl : F64.clamp ((h.endTime - prev) / (OsuModel.Sim.Sim.timeAbsolute h t - prev)) 0.9 1.11 with
          | error e =>
            refine ⟨fun S1 hG => ?_, fun e' _ => ⟨_, by
              simp only [simM_bind, OsuModel.Sim.Sim.liftNet, hcl, simM_throw, Except.bind]; rfl⟩⟩
            revert hG; cases S'.speed[k]? <;> cases S'.asRecent[ai]? <;> cases S'.asTarget[ai]? <;> simp [hcl]
          | ok rel =>
            simp only [simM_bind, OsuModel.Sim.Sim.liftNet, hcl, simM_pure, s3b_ebind_ok]
            s3b_as_core


/-! ## Rust side -/
/-- Rust result vs the abstract AS loop -/
def s3b_lrel (tn : Nat → String) : core.result.Result Unit sim.err.SimErr × sim.state.St → Except String OsuModel.Sim.St → Prop
  | (.Ok (), s'), .ok S => simStS tn s' = S
  | (.Err _, _), .error _ => True
  | _, _ => False

theorem s3b_contains_reverse (l : List (Nat × Int)) (x : Nat × Int) : l.reverse.contains x = l.contains x := by
  simp [List.contains_iff_mem]

theorem s3b_timeAbsolute_tn (tn tn' : Nat → String) (h : sim.playable.HObj) (t : F64) :
    OsuModel.Sim.Sim.timeAbsolute (hobjS tn h) t = OsuModel.Sim.Sim.timeAbsolute (hobjS tn' h) t := by
  simp [OsuModel.Sim.Sim.timeAbsolute, hobjS]

/-- invariant of the Rust AS loop at dyn-rate index `k` with `ai` AS mods done -/
structure s3b_asInv (c : sim.state.Ctx) (s : sim.state.St) (ai k : Nat) : Prop where
  sp : c.cfg.dyn_rates.val.length ≤ s.speed.val.length
  cnt : ai + ((c.cfg.dyn_rates.val.drop k).filter s3b_isAd).length ≤ s.as_target.val.length ∧
    ai + ((c.cfg.dyn_rates.val.drop k).filter s3b_isAd).length ≤ s.as_recent.val.length ∧
    ai + ((c.cfg.dyn_rates.val.drop k).filter s3b_isAd).length ≤ s.as_seen.val.length
  cap : ∀ j (h : j < s.as_seen.val.length), ai ≤ j → (s.as_seen.val[j]'h).val.length < Usize.max

theorem s3b_as_step (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref) (ty : sim.basic.HitResult)
    (t : F64) (h : sim.playable.HObj) (ai k : Usize) (hpre : s3b_precOk c r)
    (hk : k.val < s.speed.val.length) (h0 : ai.val < s.as_target.val.length) (h1 : ai.val < s.as_recent.val.length)
    (h2 : ai.val < s.as_seen.val.length) (hcap : (s.as_seen.val[ai.val]'h2).val.length < Usize.max) :
    ∃ res s', sim.step.adaptive_speed_one s k ai r h ty t (s3b_precEnd c r) = ok (res, s') ∧
      s3b_lrel tn (res, s') (s3b_asBodyS (simCtxS tn fo c) (abs r) (abs ty) t (hobjS tn h) ai.val k.val (simStS tn s)) ∧
      (∃ a b d, s' = { s with as_target := a, as_recent := b, as_seen := d }) ∧
      s'.as_target.val.length = s.as_target.val.length ∧ s'.as_recent.val.length = s.as_recent.val.length ∧
      s'.as_seen.val.length = s.as_seen.val.length ∧
      (∀ j (hj : j < s.as_seen.val.length) (hj' : j < s'.as_seen.val.length), j ≠ ai.val →
        s'.as_seen.val[j]'hj' = s.as_seen.val[j]'hj) ∧
      (∀ (hj' : ai.val < s'.as_seen.val.length),
        (s'.as_seen.val[ai.val]'hj').val.length ≤ (s.as_seen.val[ai.val]'h2).val.length + 1) := by
  obtain ⟨res, s', hR, hC⟩ := sim.step.adaptive_speed_one_eq s k ai r h ty t (s3b_precEnd c r) hk h0 h1 h2 hcap
  refine ⟨res, s', hR, ?_⟩
  have hS1 : (simStS tn s).asSeen[ai.val]? = some (((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).reverse) := by
    simp [simStS, h2]
  obtain ⟨ht, hn⟩ := hpre
  have hS2 : (simCtxS tn fo c).precEnd[(abs r : Nat × Int).1]? =
      some ((c.prec_end.val[r.top.val]'ht).top, (c.prec_end.val[r.top.val]'ht).nested.val.toArray) := by
    simp [simCtxS, abs, ht]
  have hS3 : (if (abs r : Nat × Int).2 < 0 then some (c.prec_end.val[r.top.val]'ht).top
      else (c.prec_end.val[r.top.val]'ht).nested.val.toArray[(abs r : Nat × Int).2.toNat]?) = some (s3b_precEnd c r) := by
    unfold s3b_precEnd
    by_cases hneg : r.nested.val < 0
    · simp [abs, hneg, getElem!_def, ht]
    · have := hn (by omega)
      simp [abs, hneg, getElem!_def, ht, this]
  have hsp : (simStS tn s).speed[k.val]? = some (s.speed.val[k.val]'hk) := by simp [simStS, abs, hk]
  have hrc : (simStS tn s).asRecent[ai.val]? = some ((s.as_recent.val[ai.val]'h1).val.toArray) := by
    simp [simStS, abs, h1]
  have htg : (simStS tn s).asTarget[ai.val]? = some (s.as_target.val[ai.val]'h0) := by simp [simStS, abs, h0]
  unfold s3b_asBodyS
  rw [hS1, hS2]
  simp only []
  rw [hS3]
  simp only [s3b_contains_reverse]
  generalize hcond : (((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).contains (abs r) ||
      !(abs ty : OsuModel.Sim.HitResult).affectsAccuracy || (s3b_precEnd c r).isNone) = cond at hC
  cases cond with
  | true =>
    simp only [if_true] at hC
    obtain ⟨hres, hs'⟩ := hC; subst hres; subst s'
    refine ⟨?_, ⟨_, _, _, rfl⟩, rfl, rfl, rfl, fun j hj hj' _ => rfl, fun _ => by omega⟩
    have habs : (abs ty : OsuModel.Sim.HitResult) = abs ty := rfl
    cases hc1 : ((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).contains (abs r) <;>
      cases hc2 : (abs ty : OsuModel.Sim.HitResult).affectsAccuracy <;>
      cases hc3 : s3b_precEnd c r <;> simp_all [s3b_lrel]
  | false =>
    simp only [Bool.false_eq_true, if_false] at hC
    have hc1 : ((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).contains (abs r) = false := by
      revert hcond; cases ((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).contains (abs r) <;> simp
    have hc2 : (abs ty : OsuModel.Sim.HitResult).affectsAccuracy = true := by
      revert hcond; cases (abs ty : OsuModel.Sim.HitResult).affectsAccuracy <;> simp
    obtain ⟨prev, hprev⟩ : ∃ prev, s3b_precEnd c r = some prev := by
      revert hcond; cases s3b_precEnd c r <;> simp
    rw [hprev] at hC ⊢; simp only [Option.getD_some] at hC
    simp only [hc1, hc2, Bool.not_false, Bool.true_and, if_true, hsp, hrc, htg, Option.getD_some]
    have hend : (hobjS tn h).endTime = h.end_time := by simp [hobjS]
    rw [hend, s3b_timeAbsolute_tn tn simTnDefault h t]
    have habsh : (abs h : OsuModel.Sim.HObj) = hobjS simTnDefault h := rfl
    rw [habsh] at hC
    revert hC
    cases s3b_asStep (abs ty : OsuModel.Sim.HitResult).isHit h.end_time
        (OsuModel.Sim.Sim.timeAbsolute (hobjS simTnDefault h) t) prev (s.as_recent.val[ai.val]'h1).val
        (s.speed.val[k.val]'hk) (s.as_target.val[ai.val]'h0) with
    | error e =>
      intro hC; obtain ⟨hres, hs'⟩ := hC; subst hres; subst s'
      exact ⟨trivial, ⟨_, _, _, rfl⟩, rfl, rfl, rfl, fun j hj hj' _ => rfl, fun _ => by omega⟩
    | ok p =>
      obtain ⟨tgt, rec⟩ := p
      intro hC; obtain ⟨hres, rv, hrv, hs'⟩ := hC; subst hres; subst s'
      refine ⟨?_, ⟨_, _, _, rfl⟩, by simp [alloc.vec.Vec.set], by simp [alloc.vec.Vec.set], by simp [alloc.vec.Vec.set], ?_,
        fun _ => by simp [alloc.vec.Vec.set, vpush_val]⟩
      · show simStS tn _ = _
        have e0 : ∀ (a b : alloc.vec.Vec _) (d : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref)),
            simStS tn { s with as_target := a, as_recent := b, as_seen := d } =
              { simStS tn s with asTarget := abs a, asRecent := abs b, asSeen := (d.val.map (fun l => (l.val.map (fun r => (abs r : Nat × Int))).reverse)).toArray } :=
              fun _ _ _ => rfl
        rw [e0]
        have e1 : (abs (s.as_target.set ai tgt) : _root_.Array F64) = (simStS tn s).asTarget.set! ai.val tgt := by
          simp [simStS, abs, alloc.vec.Vec.set, Array.set!, Array.setIfInBounds, List.map_set, h0]
        have e2 : (abs (s.as_recent.set ai rv) : _root_.Array (_root_.Array F64)) = (simStS tn s).asRecent.set! ai.val rec.toArray := by
          simp [simStS, abs, alloc.vec.Vec.set, Array.set!, Array.setIfInBounds, List.map_set, h1, hrv]
        have e3 : ((s.as_seen.set ai (vpush (s.as_seen.val[ai.val]'h2) r hcap)).val.map
            fun l => (l.val.map (fun r => (abs r : Nat × Int))).reverse).toArray =
            (simStS tn s).asSeen.set! ai.val ((abs r : Nat × Int) :: ((s.as_seen.val[ai.val]'h2).val.map (fun x => (abs x : Nat × Int))).reverse) := by
          simp [simStS, alloc.vec.Vec.set, Array.set!, Array.setIfInBounds, List.map_set, h2]
        rw [e1, e2, e3]
      · intro j hj hj' hne
        simp [alloc.vec.Vec.set, List.getElem_set, Ne.symm hne]

/-- AS state shape after the AS loop from slot `ai` on: lengths kept, slots `≥ ai` grow by at most one seen ref -/
def s3b_asGrow (s s' : sim.state.St) (ai : Nat) : Prop :=
  s'.as_target.val.length = s.as_target.val.length ∧ s'.as_recent.val.length = s.as_recent.val.length ∧
  s'.as_seen.val.length = s.as_seen.val.length ∧ ∀ j (hj : j < s.as_seen.val.length) (hj' : j < s'.as_seen.val.length),
    (s'.as_seen.val[j]'hj').val.length ≤ (s.as_seen.val[j]'hj).val.length + (if j < ai then 0 else 1)

theorem s3b_asGrow_refl (s : sim.state.St) (ai : Nat) : s3b_asGrow s s ai :=
  ⟨rfl, rfl, rfl, fun j _ _ => by split <;> omega⟩

/-- the Rust AS loop body as a function of the loop state -/
def s3b_ASB (c : sim.state.Ctx) (r : sim.step.Ref) (ty : sim.basic.HitResult) (t : F64) (h : sim.playable.HObj)
    (x : sim.state.St × Usize × Usize) :=
  sim.step.adaptive_speed_on_result_loop.body c.env c.cfg.policy c.cfg.classic_head_block c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj r ty t h x.1 x.2.1 x.2.2

theorem s3b_as_loop_eq (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref) (ty : sim.basic.HitResult) (t : F64)
    (h : sim.playable.HObj) (ai k : Usize) :
    sim.step.adaptive_speed_on_result_loop c.env c.cfg.policy c.cfg.classic_head_block c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj s r ty t h ai k = loop (s3b_ASB c r ty t h) (s, ai, k) := rfl

theorem s3b_drop_filter_succ (l : List sim.mods.DynRate) (k : Nat) (hk : k < l.length) :
    ((l.drop k).filter s3b_isAd).length = (if s3b_isAd (l[k]'hk) then 1 else 0) + ((l.drop (k + 1)).filter s3b_isAd).length := by
  rw [List.drop_eq_getElem_cons hk, List.filter_cons]; split <;> simp_all; omega

theorem s3b_as_loop (tn fo) (c : sim.state.Ctx) (r : sim.step.Ref) (ty : sim.basic.HitResult) (t : F64)
    (h : sim.playable.HObj) (hpre : (∃ d ∈ c.cfg.dyn_rates.val, s3b_isAd d = true) → s3b_precOk c r) :
    ∀ n (k ai : Usize) (s : sim.state.St), c.cfg.dyn_rates.val.length - k.val = n → k.val ≤ c.cfg.dyn_rates.val.length →
      s3b_asInv c s ai.val k.val →
      ∃ res s', loop (s3b_ASB c r ty t h) (s, ai, k) = ok (res, s') ∧
        s3b_lrel tn (res, s') (s3b_asLoop (s3b_asG (simCtxS tn fo c) (abs r) (abs ty) t (hobjS tn h))
          ((c.cfg.dyn_rates.val.drop k.val).map (fun d => (abs d : OsuModel.Sim.DynRate))) ai.val k.val (simStS tn s)) ∧
        (∃ a b d, s' = { s with as_target := a, as_recent := b, as_seen := d }) ∧ s3b_asGrow s s' ai.val := by
  have hmax := c.cfg.dyn_rates.property
  intro n
  induction n with
  | zero =>
    intro k ai s hn hk _
    have : ¬ k < alloc.vec.Vec.len c.cfg.dyn_rates := by rw [vec_lt_len_iff]; omega
    refine ⟨.Ok (), s, ?_, ?_, ⟨_, _, _, rfl⟩, s3b_asGrow_refl s _⟩
    · rw [loop_unfold]; simp [s3b_ASB, sim.step.adaptive_speed_on_result_loop.body, this]
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro k ai s hn hk hI
    have hlt : k.val < c.cfg.dyn_rates.val.length := by omega
    have hkl : k < alloc.vec.Vec.len c.cfg.dyn_rates := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by omega)
    have hcnt := s3b_drop_filter_succ c.cfg.dyn_rates.val k.val hlt
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, s3b_asLoop]
    cases hd : c.cfg.dyn_rates.val[k.val]'hlt with
    | TimeRamp a b d f =>
      have hb : s3b_ASB c r ty t h (s, ai, k) = ok (.cont (s, ai, k1)) := by
        simp [s3b_ASB, sim.step.adaptive_speed_on_result_loop.body, hkl, vec_index_eq _ _ hlt, hd, hk1]
      rw [hd] at hcnt
      obtain ⟨res, s', hl, hR, hS, hG⟩ := ih k1 ai s (by omega) (by omega)
        ⟨hI.sp, by simp [s3b_isAd] at hcnt; rw [hk1v]; have := hI.cnt; omega, hI.cap⟩
      refine ⟨res, s', by rw [loop_unfold, hb]; simpa using hl, ?_, hS, hG⟩
      simp only [s3b_asG, s3b_abs_tr, s3b_isAdS, Bool.false_eq_true, if_false]
      rw [hk1v] at hR; exact hR
    | Adaptive a =>
      have hpo : s3b_precOk c r := hpre ⟨_, List.getElem_mem hlt, by rw [hd]; rfl⟩
      rw [hd] at hcnt; simp only [s3b_isAd, if_true] at hcnt
      obtain ⟨c0, c1, c2⟩ := hI.cnt
      have hs0 : ai.val < s.as_target.val.length := by omega
      have hs1 : ai.val < s.as_recent.val.length := by omega
      have hs2 : ai.val < s.as_seen.val.length := by omega
      have hkk : k.val < s.speed.val.length := by have := hI.sp; omega
      obtain ⟨res1, s1, h1R, hrel1, ⟨ta, tb, td, hshape⟩, hl0, hl1, hl2, hother, hgrow⟩ :=
        s3b_as_step tn fo c s r ty t h ai k hpo hkk hs0 hs1 hs2 (hI.cap _ hs2 (le_refl _))
      have hpe : sim.step.prec_end_of c r = ok (s3b_precEnd c r) := sim.step.prec_end_of_refines c r hpo
      simp only [s3b_asG, s3b_abs_ad, s3b_isAdS, if_true]
      rcases res1 with ⟨⟨⟩⟩ | e
      · obtain ⟨ai1, hai1, hai1v⟩ := usize_add_one ai (by have := s.as_target.property; omega)
        have hb : s3b_ASB c r ty t h (s, ai, k) = ok (.cont (s1, ai1, k1)) := by
          simp only [s3b_ASB, sim.step.adaptive_speed_on_result_loop.body, hkl, if_true, vec_index_eq _ _ hlt, hd,
            bind_ok]
          rw [show sim.step.prec_end_of _ r = ok (s3b_precEnd c r) from hpe]
          simp [h1R, hai1, hk1, core.result.Result.Insts.CoreOpsTry.branch]
        have hsp1 : s1.speed = s.speed := by rw [hshape]
        obtain ⟨res, s', hl, hR, ⟨a', b', d', hS⟩, hG⟩ := ih k1 ai1 s1 (by omega) (by omega)
          ⟨by rw [hsp1]; exact hI.sp, by rw [hai1v, hk1v, hl0, hl1, hl2]; exact ⟨by omega, by omega, by omega⟩,
           fun j hj hj' => by
             have hj0 : j < s.as_seen.val.length := by omega
             rw [hother j hj0 hj (by omega)]; exact hI.cap j hj0 (by omega)⟩
        refine ⟨res, s', by rw [loop_unfold, hb]; simpa using hl, ?_, ⟨a', b', d', by rw [hS, hshape]⟩, ?grow⟩
        case grow =>
          obtain ⟨g0, g1, g2, g3⟩ := hG
          refine ⟨g0.trans hl0, g1.trans hl1, g2.trans hl2, fun j hj hj' => ?_⟩
          have hj1 : j < s1.as_seen.val.length := by omega
          have := g3 j hj1 hj'
          rw [hai1v] at this
          by_cases hja : j = ai.val
          · subst hja; have := hgrow hj1; simp only [lt_irrefl, if_false, Nat.lt_succ_self, if_true] at *; omega
          · rw [hother j hj hj1 hja] at this; split at this <;> split <;> omega
        cases hB : s3b_asBodyS (simCtxS tn fo c) (abs r) (abs ty) t (hobjS tn h) ai.val k.val (simStS tn s) with
        | error _ => rw [hB] at hrel1; exact absurd hrel1 (by simp [s3b_lrel])
        | ok S1 =>
          rw [hB] at hrel1; simp only [s3b_lrel] at hrel1
          simp only [← hrel1]
          rw [hai1v, hk1v] at hR; exact hR
      · have hb : s3b_ASB c r ty t h (s, ai, k) = ok (.done (.Err e, s1)) := by
          simp only [s3b_ASB, sim.step.adaptive_speed_on_result_loop.body, hkl, if_true, vec_index_eq _ _ hlt, hd,
            bind_ok]
          rw [show sim.step.prec_end_of _ r = ok (s3b_precEnd c r) from hpe]
          simp [h1R, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        refine ⟨.Err e, s1, by rw [loop_unfold, hb]; simp, ?_, ⟨ta, tb, td, hshape⟩, ?grow⟩
        case grow =>
          refine ⟨hl0, hl1, hl2, fun j hj hj' => ?_⟩
          by_cases hja : j = ai.val
          · subst hja; have := hgrow hj'; split <;> omega
          · rw [hother j hj hj' hja]; split <;> omega
        revert hrel1
        cases s3b_asBodyS (simCtxS tn fo c) (abs r) (abs ty) t (hobjS tn h) ai.val k.val (simStS tn s) <;>
          simp [s3b_lrel]

/-- ModAdaptiveSpeed `OnNewResult` (`Sim.adaptiveSpeedOnResult`). Side conditions: the judged reference is in range
(`simRefOk`), the preceding-end-times entry exists when an AS mod is active, one speed per dyn rate, one AS state slot
per AS mod (`as_target`/`as_recent`/`as_seen`), and every `as_seen` list can take one more push. Only the three AS
fields change (`objs`/`insts`/`dict_slots`/`future_order` untouched). -/
theorem sim.step.adaptive_speed_on_result_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (ty : sim.basic.HitResult) (t : F64) (hinv : SimInv c s)
    (hr : c.cfg.dyn_rates.val ≠ [] → simRefOk c r)
    (hpre : (∃ d ∈ c.cfg.dyn_rates.val, s3b_isAd d = true) → s3b_precOk c r)
    (hsp : c.cfg.dyn_rates.val.length ≤ s.speed.val.length)
    (hcnt : (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_target.val.length ∧
      (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_recent.val.length ∧
      (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_seen.val.length)
    (hcap : ∀ l ∈ s.as_seen.val, l.val.length < Usize.max) :
    ∃ res s', sim.step.adaptive_speed_on_result c s r ty t = ok (res, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') res
        (OsuModel.Sim.Sim.adaptiveSpeedOnResult (abs r) (abs ty) t (simCtxS tn fo c) (simStS tn s)) ∧
      (∃ a b d, s' = { s with as_target := a, as_recent := b, as_seen := d }) ∧ SimInv c s' ∧
      s'.future_order = s.future_order := by
  have hdr : (simCtxS tn fo c).cfg.dynRates = (c.cfg.dyn_rates.val.map (fun d => (abs d : OsuModel.Sim.DynRate))).toArray := by
    simp [simCtxS, abs, configS]
  by_cases h0 : c.cfg.dyn_rates.val = []
  · refine ⟨.Ok (), s, ?_, ?_, ⟨_, _, _, rfl⟩, hinv, rfl⟩
    · have : alloc.vec.Vec.len c.cfg.dyn_rates = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [h0]
      simp [sim.step.adaptive_speed_on_result, this]
    · unfold OsuModel.Sim.Sim.adaptiveSpeedOnResult
      simp [OsuModel.Sim.Sim.ctx, hdr, h0, s3b_rrel]
  · have hne : (simCtxS tn fo c).cfg.dynRates.isEmpty = false := by simp [hdr, h0]
    have hlen0 : ¬ alloc.vec.Vec.len c.cfg.dyn_rates = 0#usize := by
      intro e; apply h0; have := congrArg (·.val) e; simpa using this
    obtain ⟨h, hh, eh⟩ := sim.step.hobj_of_refines tn fo c r (hr h0)
    have hspec := s3b_asOnResult_spec (simCtxS tn fo c) (simStS tn s) (abs r) (abs ty) t (hobjS tn h) hne (eh _)
    obtain ⟨res, s', hl, hR, hS, -⟩ := s3b_as_loop tn fo c r ty t h hpre c.cfg.dyn_rates.val.length 0#usize 0#usize s
      (by simp) (by simp)
      ⟨hsp, by simpa using hcnt, fun j hj _ => hcap _ (List.getElem_mem hj)⟩
    refine ⟨res, s', ?_, ?_, hS, ?_, ?_⟩
    · simp only [sim.step.adaptive_speed_on_result, hlen0, if_false, hh, bind_ok]
      rw [s3b_as_loop_eq]; exact hl
    · rw [hdr, List.toList_toArray] at hspec
      simp only [List.drop_zero, show (0#usize : Usize).val = 0 from rfl] at hR
      revert hR hspec
      cases s3b_asLoop (s3b_asG (simCtxS tn fo c) (abs r) (abs ty) t (hobjS tn h))
          (c.cfg.dyn_rates.val.map (fun d => (abs d : OsuModel.Sim.DynRate))) 0 0 (simStS tn s) <;>
        cases OsuModel.Sim.Sim.adaptiveSpeedOnResult (abs r) (abs ty) t (simCtxS tn fo c) (simStS tn s) <;>
        rcases res with ⟨⟨⟩⟩ | e <;> simp [s3b_lrel, s3b_res, s3b_rrel]
      all_goals (intro h1 h2; rw [h2, h1])
    · obtain ⟨a, b, d, rfl⟩ := hS; exact s3b_inv_of hinv rfl rfl
    · obtain ⟨a, b, d, rfl⟩ := hS; rfl

/-- shape of the AS state after `adaptive_speed_on_result` (Rust side; sim core request 16:50): slot counts kept, each
`as_seen` list grows by at most one reference. Same side conditions as `adaptive_speed_on_result_refines`. -/
theorem sim.step.adaptive_speed_on_result_grow (c : sim.state.Ctx) (s : sim.state.St) (r : sim.step.Ref)
    (ty : sim.basic.HitResult) (t : F64) (hinv : SimInv c s)
    (hr : c.cfg.dyn_rates.val ≠ [] → simRefOk c r)
    (hpre : (∃ d ∈ c.cfg.dyn_rates.val, s3b_isAd d = true) → s3b_precOk c r)
    (hsp : c.cfg.dyn_rates.val.length ≤ s.speed.val.length)
    (hcnt : (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_target.val.length ∧
      (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_recent.val.length ∧
      (c.cfg.dyn_rates.val.filter s3b_isAd).length ≤ s.as_seen.val.length)
    (hcap : ∀ l ∈ s.as_seen.val, l.val.length < Usize.max)
    (res : core.result.Result Unit sim.err.SimErr) (s' : sim.state.St)
    (hok : sim.step.adaptive_speed_on_result c s r ty t = ok (res, s')) :
    s'.as_target.val.length = s.as_target.val.length ∧ s'.as_recent.val.length = s.as_recent.val.length ∧
    s'.as_seen.val.length = s.as_seen.val.length ∧ ∀ i (h : i < s.as_seen.val.length) (h' : i < s'.as_seen.val.length),
      (s'.as_seen.val[i]'h').val.length ≤ (s.as_seen.val[i]'h).val.length + 1 := by
  by_cases h0 : c.cfg.dyn_rates.val = []
  · have : alloc.vec.Vec.len c.cfg.dyn_rates = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [h0]
    simp [sim.step.adaptive_speed_on_result, this] at hok
    obtain ⟨-, rfl⟩ := hok
    exact ⟨rfl, rfl, rfl, fun _ _ _ => by omega⟩
  · have hlen0 : ¬ alloc.vec.Vec.len c.cfg.dyn_rates = 0#usize := by
      intro e; apply h0; have := congrArg (·.val) e; simpa using this
    obtain ⟨h, hh, -⟩ := sim.step.hobj_of_refines simTnDefault (alloc.vec.Vec.new Usize) c r (hr h0)
    obtain ⟨res2, s2, hl, -, -, g0, g1, g2, g3⟩ := s3b_as_loop simTnDefault (alloc.vec.Vec.new Usize) c r ty t h hpre
      c.cfg.dyn_rates.val.length 0#usize 0#usize s (by simp) (by simp)
      ⟨hsp, by simpa using hcnt, fun j hj _ => hcap _ (List.getElem_mem hj)⟩
    have e : sim.step.adaptive_speed_on_result c s r ty t = ok (res2, s2) := by
      simp only [sim.step.adaptive_speed_on_result, hlen0, if_false, hh, bind_ok]
      rw [s3b_as_loop_eq]; exact hl
    rw [e] at hok; cases Result.ok_injective hok
    refine ⟨g0, g1, g2, fun i hi hi' => ?_⟩
    have := g3 i hi hi'; simp only [show (0#usize : Usize).val = 0 from rfl, Nat.not_lt_zero, if_false] at this
    exact this

end OsuProofs
