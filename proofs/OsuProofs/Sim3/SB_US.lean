/-
Sim3b part 7: `update_state` / `update_state_from_result` refine `Sim.updateState` / `Sim.updateStateFromResult`
(`DrawableHitObject.UpdateState`). Spec normal form `s3b_updateState_spec` (generic in the spec context/state),
Rust normal form, and the refinement. The `ApplyCustomUpdateState` handlers (`customState`) enter through the
hypothesis `s3b_CSOk` (proved separately), the transform engine through `s3b_TfEng` (D44 CONDITIONAL).
-/
import OsuProofs.Sim3.SB_Tf
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

@[simp] theorem s3b_ebok {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a).bind f = f a := rfl

/-- the transformables and lifetime end computed by `updateState` (before `ApplyCustomUpdateState`) -/
def s3b_usCore (now hst t0 fi : F64) (kind : OsuModel.Sim.Kind) (isSl : Bool) (ns : OsuModel.Sim.Armed)
    (headHit : Bool) (tf0 body0 : OsuModel.Sim.TObj) : OsuModel.Sim.TObj × OsuModel.Sim.TObj × F64 :=
  let tf1 := OsuModel.Sim.fadeInFromZero (OsuModel.Sim.absSeq (OsuModel.Sim.clearState tf0) now t0) now
  let body1 := if isSl then OsuModel.Sim.fadeInFromZero (OsuModel.Sim.absSeq (OsuModel.Sim.clearState body0) now t0) now fi
    else body0
  let tf2 := OsuModel.Sim.absSeq { tf1 with delay := 0 } now hst
  let body2 := OsuModel.Sim.absSeq { body1 with delay := 0 } now hst
  match kind with
  | .circle | .head =>
    let T1 := ((OsuModel.Sim.delaySeq tf2 now 800).append tf2 now .alpha (OsuModel.Sim.vs 0) 0).1
    let T2 := if ns == .miss then (OsuModel.Sim.transformTo T1 now .alpha (OsuModel.Sim.vs 0) 100).1 else T1
    ({ T2 with delay := 0 }, { body2 with delay := 0 }, OsuModel.Sim.latestEnd T2 now)
  | .slider =>
    let body3 := if (ns == .hit && headHit) = true then (OsuModel.Sim.transformTo body2 now .alpha (OsuModel.Sim.vs 0) 40).1
      else body2
    let R := OsuModel.Sim.transformTo tf2 now .alpha (OsuModel.Sim.vs 0) 240
    ({ R.1 with delay := 0 }, { body3 with delay := 0 }, OsuModel.Sim.latestEnd (OsuModel.Sim.absSeq R.1 now R.2.currentTime) now)
  | _ =>
    let T := (OsuModel.Sim.transformTo tf2 now .alpha (OsuModel.Sim.vs 0) 240).1
    ({ T with delay := 0 }, { body2 with delay := 0 }, OsuModel.Sim.latestEnd T now)

/-- `HitStateUpdateTime` of `updateState` -/
def s3b_hst (h : OsuModel.Sim.HObj) (ro : Option OsuModel.Sim.Res) : F64 :=
  match ro with | some (_, raw) => OsuModel.Sim.Sim.timeAbsolute h raw | none => h.endTime

/-- the state after `updateState`'s own writes (before the custom-state handlers) -/
def s3b_usSt (S : OsuModel.Sim.St) (i k : Nat) (p : OsuModel.Sim.Sim.Part) (ns : OsuModel.Sim.Armed)
    (X : OsuModel.Sim.TObj × OsuModel.Sim.TObj × F64) : OsuModel.Sim.St :=
  { S with insts := S.insts.modify k (fun ins => { ins with tf := X.1, bodyTf := X.2.1 }),
           objs := S.objs.modify i (fun os => if p == .top then { os with armed := ns, lifetimeEnd := X.2.2 }
             else { os with headArmed := ns, headLifetimeEnd := X.2.2 }) }

theorem s3b_modifyInst_ok (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (k : Nat) (f : OsuModel.Sim.Inst → OsuModel.Sim.Inst)
    (hk : k < S.insts.size) :
    OsuModel.Sim.Sim.modifyInst k f C S = .ok ((), { S with insts := S.insts.modify k f }) := by
  simp [OsuModel.Sim.Sim.modifyInst, OsuModel.Sim.Sim.checkIdx, OsuModel.Sim.Sim.st, hk]
theorem s3b_modifyObj_ok (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (i : Nat) (f : OsuModel.Sim.OState → OsuModel.Sim.OState)
    (hi : i < S.objs.size) :
    OsuModel.Sim.Sim.modifyObj i f C S = .ok ((), { S with objs := S.objs.modify i f }) := by
  simp [OsuModel.Sim.Sim.modifyObj, OsuModel.Sim.Sim.checkIdx, OsuModel.Sim.Sim.st, hi]

set_option maxHeartbeats 4000000 in
theorem s3b_updateState_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (i : Nat) (p : OsuModel.Sim.Sim.Part)
    (ns : OsuModel.Sim.Armed) (force : Bool) (passes : Nat) (a : OsuModel.Sim.Armed) (k : Nat) (o : OsuModel.Sim.TopObj)
    (r : OsuModel.Sim.Ref) (h : OsuModel.Sim.HObj) (ro : Option OsuModel.Sim.Res) (hh : Bool)
    (hpa : OsuModel.Sim.Sim.partArmed i p C S = .ok (a, S)) (hpi : OsuModel.Sim.Sim.partInst i p C S = .ok (k, S))
    (hto : OsuModel.Sim.Sim.topObj i C S = .ok (o, S)) (hpr : OsuModel.Sim.Sim.partRef i p C S = .ok (r, S))
    (hho : OsuModel.Sim.Sim.hobjOf r C S = .ok (h, S)) (hro : OsuModel.Sim.Sim.resOf r C S = .ok (ro, S))
    (hk : k < S.insts.size) (hio : i < S.objs.size)
    (hhit : h.kind = .slider → ∃ hj, OsuModel.Sim.Sim.headIdxOf i C S = .ok (hj, S) ∧
      OsuModel.Sim.Sim.isHitRef (i, (hj : Int)) C S = .ok (hh, S))
    (htr : C.cfg.traceObj = none) :
    OsuModel.Sim.Sim.updateState i p ns force passes C S =
      if (a == ns && !force) = true then .ok ((), S) else
      let X := s3b_usCore S.t (s3b_hst h ro) (h.start - h.preempt) h.fadeIn h.kind (p == .top && o.h.kind == .slider) ns hh
        S.insts[k].tf S.insts[k].bodyTf
      (do OsuModel.Sim.Sim.customState i p ns false
          if passes ≥ 2 then OsuModel.Sim.Sim.customState i p ns true else pure ()) C (s3b_usSt S i k p ns X) := by
  unfold OsuModel.Sim.Sim.updateState
  rw [simM_bind, hpa, s3b_ebok]
  dsimp (config := {zeta := false}) only
  split
  · rfl
  rw [simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, hpi, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, hto, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, hpr, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind, hho, s3b_ebok]; dsimp (config := {zeta := false}) only
  rw [simM_bind]; simp (config := {zeta := false}) only [hro, s3b_ebok]
  rw [simM_bind, OsuModel.Sim.Sim.instOf, simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok]
  dsimp (config := {zeta := false}) only
  rw [OsuModel.Sim.Sim.getA, dif_pos hk, simM_pure, s3b_ebok]; dsimp (config := {zeta := false}) only
  generalize S.insts[k] = ins
  unfold s3b_usCore
  generalize OsuModel.Sim.clearState ins.tf = T0
  generalize OsuModel.Sim.clearState ins.bodyTf = B0
  generalize S.t = now
  generalize OsuModel.Sim.fadeInFromZero (OsuModel.Sim.absSeq T0 now (h.start - h.preempt)) now = F1
  obtain ⟨hst, hhst⟩ : ∃ hst, s3b_hst h ro = hst := ⟨_, rfl⟩
  rcases ro with _ | ⟨rty, raw⟩ <;> simp only [s3b_hst] at hhst ⊢ <;> rw [hhst] <;>
    generalize OsuModel.Sim.absSeq { F1 with delay := 0 } now hst = T2 <;>
    cases p <;> cases hsl : (o.h.kind == .slider) <;> cases hkd : h.kind
  all_goals simp only [hkd, hsl, sim_part_beq_tt, sim_part_beq_th, sim_part_beq_ht, sim_part_beq_hh, Bool.and_false,
    Bool.and_true, Bool.true_and, Bool.false_and, Bool.false_eq_true, if_false, if_true, simM_bind, simM_ite]
  all_goals (try (obtain ⟨hj, hj1, hj2⟩ := hhit hkd; rw [hj1, s3b_ebok]; dsimp only; rw [hj2, s3b_ebok]; dsimp only; cases hh2 : (ns == OsuModel.Sim.Armed.hit && hh) <;> simp only [hh2, if_true, if_false, Bool.false_eq_true]))
  all_goals (try (cases hm : (ns == OsuModel.Sim.Armed.miss) <;> simp only [hm, if_true, if_false, Bool.false_eq_true] <;>
    simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok, htr, Option.isSome_none, Bool.and_false,
      Bool.false_eq_true, if_false, simM_ite]))
  all_goals (try (rw [s3b_modifyInst_ok _ _ _ _ hk, s3b_ebok]; (try dsimp only); (try simp only [if_true, if_false, simM_bind])
                  rw [s3b_modifyObj_ok _ _ _ _ (by simpa using hio), s3b_ebok]; rfl))


end OsuProofs
