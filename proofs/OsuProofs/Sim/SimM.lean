/-
Evaluation lemmas for the spec's simulation monad `SimM = ReaderT Ctx (StateT St (Except String))` applied to a
context and a state (`m C S : Except String (α × St)`), and spec-side evaluation of the small `Sim` accessors under
in-range hypotheses. Generic over the spec context/state (no Rust maps), so the Rust refinement proofs only need
projection lemmas of `simCtxS`/`simStS`.
-/
import OsuProofs.Sim.AbsState
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open OsuModel.Net OsuModel.Sim

namespace OsuProofs
/-! ## Evaluating `SimM` (= ReaderT Ctx (StateT St (Except String))) at a context and a state -/
@[simp] theorem simM_read_bind {α} (f : Ctx → SimM α) (C : Ctx) (S : St) :
    ((read : SimM Ctx) >>= f) C S = f C C S := rfl
@[simp] theorem simM_get_bind {α} (f : St → SimM α) (C : Ctx) (S : St) :
    ((get : SimM St) >>= f) C S = f S C S := rfl
@[simp] theorem simM_read (C : Ctx) (S : St) : (read : SimM Ctx) C S = .ok (C, S) := rfl
@[simp] theorem simM_get (C : Ctx) (S : St) : (get : SimM St) C S = .ok (S, S) := rfl
@[simp] theorem simM_pure {α} (a : α) (C : Ctx) (S : St) : (pure a : SimM α) C S = .ok (a, S) := rfl
@[simp] theorem simM_map {α β} (f : α → β) (m : SimM α) (C : Ctx) (S : St) :
    (f <$> m) C S = (m C S).map (fun p => (f p.1, p.2)) := by
  show (do let a ← m C S; pure (f a.1, a.2)) = _
  cases m C S <;> rfl
@[simp] theorem simM_bind {α β} (m : SimM α) (f : α → SimM β) (C : Ctx) (S : St) :
    (m >>= f) C S = (m C S).bind (fun p => f p.1 C p.2) := rfl
@[simp] theorem simM_set (S' : St) (C : Ctx) (S : St) : (set S' : SimM PUnit) C S = .ok (PUnit.unit, S') := rfl
@[simp] theorem simM_modify (g : St → St) (C : Ctx) (S : St) : (modify g : SimM PUnit) C S = .ok (PUnit.unit, g S) := rfl
@[simp] theorem simM_throw {α} (e : String) (C : Ctx) (S : St) : (throw e : SimM α) C S = .error e := rfl
@[simp] theorem simM_dite {α} (p : Prop) [Decidable p] (a : p → SimM α) (b : ¬p → SimM α) (C : Ctx) (S : St) :
    (if h : p then a h else b h) C S = (if h : p then a h C S else b h C S) := by split <;> rfl
@[simp] theorem simM_ite {α} (p : Prop) [Decidable p] (a b : SimM α) (C : Ctx) (S : St) :
    (if p then a else b) C S = (if p then a C S else b C S) := by split <;> rfl

theorem simS_hobjOf (C : Ctx) (S : St) (r : Nat × Int) (h : r.1 < C.pb.objects.size)
    (hn : 0 ≤ r.2 → r.2.toNat < (C.pb.objects[r.1]'h).nested.size) :
    Sim.hobjOf r C S = .ok (if r.2 < 0 then (C.pb.objects[r.1]'h).h else (C.pb.objects[r.1]'h).nested[r.2.toNat]!, S) := by
  unfold Sim.hobjOf Sim.topObj Sim.getA Sim.ctx Sim.nestedOf
  by_cases hr : r.2 < 0
  · simp [h, hr, Except.map, Except.bind]
  · have := hn (by omega)
    simp [h, hr, this, Except.bind, Sim.getA]
theorem simS_ostate (C : Ctx) (S : St) (i : Nat) (h : i < S.objs.size) :
    Sim.ostate i C S = .ok (S.objs[i]'h, S) := by
  simp [Sim.ostate, Sim.getA, Sim.st, h, Except.bind]

theorem simS_resOf (C : Ctx) (S : St) (r : Nat × Int) (h : r.1 < S.objs.size)
    (hn : 0 ≤ r.2 → r.2.toNat < (S.objs[r.1]'h).nested.size) :
    Sim.resOf r C S = .ok (if r.2 < 0 then (S.objs[r.1]'h).result else (S.objs[r.1]'h).nested[r.2.toNat]!, S) := by
  unfold Sim.resOf
  by_cases hr : r.2 < 0
  · simp [simS_ostate _ _ _ h, hr, Except.bind]
  · have := hn (by omega)
    simp [simS_ostate _ _ _ h, hr, this, Except.bind, Sim.getA]

theorem simS_judged (C : Ctx) (S : St) (r : Nat × Int) (h : r.1 < S.objs.size)
    (hn : 0 ≤ r.2 → r.2.toNat < (S.objs[r.1]'h).nested.size) :
    Sim.judged r C S = .ok ((if r.2 < 0 then (S.objs[r.1]'h).result else (S.objs[r.1]'h).nested[r.2.toNat]!).isSome, S) := by
  unfold Sim.judged; simp [simS_resOf _ _ _ h hn, Except.bind]

theorem simS_isHitRef (C : Ctx) (S : St) (r : Nat × Int) (h : r.1 < S.objs.size)
    (hn : 0 ≤ r.2 → r.2.toNat < (S.objs[r.1]'h).nested.size) :
    Sim.isHitRef r C S = .ok ((match (if r.2 < 0 then (S.objs[r.1]'h).result else (S.objs[r.1]'h).nested[r.2.toNat]!) with
      | some (ty, _) => ty.isHit | none => false), S) := by
  unfold Sim.isHitRef; simp only [simM_bind, simS_resOf _ _ _ h hn, Except.bind]
  generalize (if r.2 < 0 then (S.objs[r.1]'h).result else (S.objs[r.1]'h).nested[r.2.toNat]!) = o
  rcases o with _ | ⟨ty, _⟩ <;> rfl

theorem simS_allJudged (C : Ctx) (S : St) (i : Nat) (h : i < S.objs.size) :
    Sim.allJudged i C S = .ok ((S.objs[i]'h).result.isSome && (S.objs[i]'h).nested.all (·.isSome), S) := by
  unfold Sim.allJudged; simp [simS_ostate _ _ _ h, Except.bind]

end OsuProofs
