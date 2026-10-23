/-
e2e2: reader-congruence of the spec simulation (`OsuModel.Sim.SimM`).

`e2_cong` proves goals `x C S = x' C' S` for spec actions `x x' : SimM α` that are the same program up to
definitional equality of the values they read from the context, e.g. `C' = {C with cfg := {C.cfg with mods := []}}`:
the spec never reads `Config.mods`, so every value it takes from `C'` reduces to the one taken from `C`.
Plain `rfl` cannot do this: loops over symbolic arrays (`forIn`, `Array.mapM`, ...) are stuck terms applied to the
reader, and `C` and `C'` are not definitionally equal. The tactic descends the program structurally (bind, read,
if/dite, matchers via `casesOn`, loop lemmas `e2_forIn_*`), proves each spec function once as a lemma
`∀ args S, g args C S = g args C' S` (memo), and closes the leaves (pure/get/modify/throw on values) by `isDefEq`.
-/
import Lean
import OsuModel.Sim.Step
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace OsuProofs
open OsuModel.Sim

/-! ## Congruence lemmas (generic in the two readers) -/

theorem e2_bind {α β : Type} (C C' : Ctx) (y y' : SimM α) (k k' : α → SimM β) (S : St)
    (h1 : y C S = y' C' S) (h2 : ∀ a S, k a C S = k' a C' S) : (y >>= k) C S = (y' >>= k') C' S := by
  show (y C S >>= fun p => k p.1 C p.2) = (y' C' S >>= fun p => k' p.1 C' p.2)
  rw [h1]; cases y' C' S <;> simp [Bind.bind, Except.bind, h2]

theorem e2_bind_read {β : Type} (C C' : Ctx) (k k' : Ctx → SimM β) (S : St)
    (h : k C C S = k' C' C' S) : (read >>= k) C S = (read >>= k') C' S := h

theorem e2_ite {α : Type} (C C' : Ctx) (c : Prop) [Decidable c] (t e t' e' : SimM α) (S : St)
    (ht : c → t C S = t' C' S) (he : ¬ c → e C S = e' C' S) : (ite c t e) C S = (ite c t' e') C' S := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ht h
  · rw [if_neg h, if_neg h]; exact he h

theorem e2_dite {α : Type} (C C' : Ctx) (c : Prop) [Decidable c] (t t' : c → SimM α) (e e' : ¬ c → SimM α) (S : St)
    (ht : ∀ h, t h C S = t' h C' S) (he : ∀ h, e h C S = e' h C' S) : (dite c t e) C S = (dite c t' e') C' S := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]; exact ht h
  · rw [dif_neg h, dif_neg h]; exact he h

theorem e2_forIn_list {α β : Type} (C C' : Ctx) (xs : List α) (b : β) (f f' : α → β → SimM (ForInStep β))
    (h : ∀ a b S, f a b C S = f' a b C' S) (S : St) : forIn xs b f C S = forIn xs b f' C' S := by
  induction xs generalizing b S with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine e2_bind C C' _ _ _ _ S (h x b S) (fun r S => ?_)
    cases r with
    | done b => rfl
    | yield b => exact ih b S

theorem e2_forIn'_list {α β : Type} (C C' : Ctx) : ∀ (xs : List α) (b : β) (f f' : (a : α) → a ∈ xs → β → SimM (ForInStep β))
    (h : ∀ a m b S, f a m b C S = f' a m b C' S) (S : St), forIn' xs b f C S = forIn' xs b f' C' S := by
  intro xs
  induction xs with
  | nil => intro b f f' h S; rfl
  | cons x xs ih =>
    intro b f f' h S
    simp only [List.forIn'_cons]
    refine e2_bind C C' _ _ _ _ S (h x _ b S) (fun r S => ?_)
    cases r with
    | done b => rfl
    | yield b => exact ih b _ _ (fun a m b S => h a _ b S) S

theorem e2_forIn_array {α β : Type} (C C' : Ctx) (xs : Array α) (b : β) (f f' : α → β → SimM (ForInStep β))
    (h : ∀ a b S, f a b C S = f' a b C' S) (S : St) : forIn xs b f C S = forIn xs b f' C' S := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]; exact e2_forIn_list C C' xs.toList b f f' h S

theorem e2_forIn_range {β : Type} (C C' : Ctx) (r : Std.Legacy.Range) (b : β) (f f' : Nat → β → SimM (ForInStep β))
    (h : ∀ a b S, f a b C S = f' a b C' S) (S : St) : forIn r b f C S = forIn r b f' C' S := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact e2_forIn_list C C' _ b f f' h S

theorem e2_forIn'_range {β : Type} (C C' : Ctx) (r : Std.Legacy.Range) (b : β) (f f' : (a : Nat) → a ∈ r → β → SimM (ForInStep β))
    (h : ∀ a m b S, f a m b C S = f' a m b C' S) (S : St) : forIn' r b f C S = forIn' r b f' C' S := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact e2_forIn'_list C C' _ b _ _ (fun a m b S => h a _ b S) S

theorem e2_mapM_list {α β : Type} (C C' : Ctx) (xs : List α) (f f' : α → SimM β)
    (h : ∀ a S, f a C S = f' a C' S) (S : St) : xs.mapM f C S = xs.mapM f' C' S := by
  induction xs generalizing S with
  | nil => simp only [List.mapM_nil]; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact e2_bind C C' _ _ _ _ S (h x S) (fun a S => e2_bind C C' _ _ _ _ S (ih S) (by intros; rfl))

theorem e2_mapM_array {α β : Type} (C C' : Ctx) (xs : Array α) (f f' : α → SimM β)
    (h : ∀ a S, f a C S = f' a C' S) (S : St) : xs.mapM f C S = xs.mapM f' C' S := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, map_eq_pure_bind, map_eq_pure_bind]
  exact e2_bind C C' _ _ _ _ S (e2_mapM_list C C' xs.toList f f' h S) (by intros; rfl)


theorem e2_foldlM_list {α β : Type} (C C' : Ctx) (f f' : β → α → SimM β)
    (h : ∀ b a S, f b a C S = f' b a C' S) : ∀ (xs : List α) (b : β) (S : St), xs.foldlM f b C S = xs.foldlM f' b C' S := by
  intro xs; induction xs with
  | nil => intro b S; rfl
  | cons x xs ih =>
    intro b S
    simp only [List.foldlM_cons]
    exact e2_bind C C' _ _ _ _ S (h b x S) (fun b S => ih b S)

theorem e2_foldlM_array {α β : Type} (C C' : Ctx) (f f' : β → α → SimM β) (xs : Array α) (b : β)
    (h : ∀ b a S, f b a C S = f' b a C' S) (S : St) : (xs.foldlM f b : SimM β) C S = (xs.foldlM f' b : SimM β) C' S := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]; exact e2_foldlM_list C C' f f' h xs.toList b S

/-- every `yield` of the loop body `x` is below `b` -/
def E2YOlt (b : Nat) (x : SimM (ForInStep Nat)) : Prop :=
  ∀ C S b' S', x C S = .ok (.yield b', S') → b' < b

theorem e2_yo_bind {α : Type} (b : Nat) (y : SimM α) (k : α → SimM (ForInStep Nat)) (h : ∀ a, E2YOlt b (k a)) :
    E2YOlt b (y >>= k) := by
  intro C S b' S' e
  change (y C S >>= fun p => k p.1 C p.2) = _ at e
  cases hy : y C S with
  | error _ => rw [hy] at e; cases e
  | ok p => rw [hy] at e; exact h p.1 C p.2 b' S' e

theorem e2_yo_ite (b : Nat) (c : Prop) [Decidable c] (t e : SimM (ForInStep Nat))
    (ht : c → E2YOlt b t) (he : ¬ c → E2YOlt b e) : E2YOlt b (ite c t e) := by
  by_cases h : c
  · rw [if_pos h]; exact ht h
  · rw [if_neg h]; exact he h

theorem e2_yo_dite (b : Nat) (c : Prop) [Decidable c] (t : c → SimM (ForInStep Nat)) (e : ¬ c → SimM (ForInStep Nat))
    (ht : ∀ h, E2YOlt b (t h)) (he : ∀ h, E2YOlt b (e h)) : E2YOlt b (dite c t e) := by
  by_cases h : c
  · rw [dif_pos h]; exact ht h
  · rw [dif_neg h]; exact he h

theorem e2_yo_yield (b v : Nat) (h : v < b) : E2YOlt b (pure (.yield v)) := by
  intro C S b' S' e; cases e; exact h

theorem e2_yo_done (b v : Nat) : E2YOlt b (pure (.done v)) := by
  intro C S b' S' e; cases e

theorem e2_yo_throw (b : Nat) (m : String) : E2YOlt b (throw m) := by
  intro C S b' S' e; cases e

theorem e2_bind_res {α β : Type} (C C' : Ctx) (y y' : SimM α) (k k' : α → SimM β) (S : St)
    (h1 : y C S = y' C' S) (h2 : ∀ a S', y C S = .ok (a, S') → k a C S' = k' a C' S') :
    (y >>= k) C S = (y' >>= k') C' S := by
  show (y C S >>= fun p => k p.1 C p.2) = (y' C' S >>= fun p => k' p.1 C' p.2)
  cases hy : y C S with
  | error _ => rw [← h1, hy]; rfl
  | ok p => rw [← h1, hy]; exact h2 p.1 p.2 hy

theorem e2_simm_loop_unfold {β : Type} (F : Unit → β → SimM (ForInStep β)) (b : β) :
    forIn Lean.Loop.mk b F = (do let r ← F () b; match r with | .done c => pure c | .yield c => forIn Lean.Loop.mk c F) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

/-- `while fuel > 0` loops of the spec (state = fuel; every yield decreases it) -/
theorem e2_loop_nat (C C' : Ctx) (b : Nat) (f f' : Unit → Nat → SimM (ForInStep Nat))
    (h : ∀ u b S, f u b C S = f' u b C' S) (hd : ∀ b, E2YOlt b (f () b)) (S : St) :
    forIn Lean.Loop.mk b f C S = forIn Lean.Loop.mk b f' C' S := by
  induction b using Nat.strongRecOn generalizing S with
  | ind b ih =>
    rw [e2_simm_loop_unfold f, e2_simm_loop_unfold f']
    refine e2_bind_res C C' _ _ _ _ S (h () b S) (fun r S' hr => ?_)
    cases r with
    | done c => rfl
    | yield c => exact ih c (hd b C S c S' hr) S'

/-- the context with the unread `Config.mods` erased -/
def e2N (C : Ctx) : Ctx := { C with cfg := { C.cfg with mods := [] } }

end OsuProofs

/-! ## The tactic -/

namespace OsuProofs.E2C
open Lean Meta Elab Tactic


structure Env where
  C : Lean.Expr
  C' : Lean.Expr
  lemmas : Array Lean.Name
  /-- user-supplied congruence facts `h : ∀ zs, x C S = x' C' S` (tried before unfolding) -/
  facts : Array Lean.Expr := #[]
  /-- local congruence hypotheses `(r, r', h)`, `h : ∀ zs S, r zs C S = r' zs C' S` -/
  hyps : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]

structure St where
  memo : Std.HashMap (Lean.Name × List Lean.Level) Lean.Expr := {}
  depth : Nat := 0
  log : Array String := #[]

abbrev M := ReaderT Env (StateRefT St MetaM)

def userDef (n : Lean.Name) : Bool := (`OsuModel).isPrefixOf n

def isReadE (y : Lean.Expr) : Bool :=
  y.isConstOf ``OsuModel.Sim.Sim.ctx ||
    (match y.getAppFn with
     | .const n _ => n == ``MonadReader.read || n == ``MonadReaderOf.read || n == ``readThe || n == ``ReaderT.read
     | _ => false)

/-- `e` applied to the two last arguments: returns the action part and `(R, S)` -/
def splitAct (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  let args := e.getAppArgs
  if args.size < 2 then none else
  some (mkAppN e.getAppFn (args.extract 0 (args.size - 2)), args[args.size - 2]!, args[args.size - 1]!)

/-- `forallTelescope` that beta/zeta-reduces (`whnfCore`, no delta) between binder groups -/
partial def telescopeCore {α : Type} (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) : MetaM α :=
  forallTelescope e fun xs b => do
    let b' ← whnfCore b
    if b'.isForall then telescopeCore b' (fun ys c => k (xs ++ ys) c) else k xs b'

/-- prove `E2YOlt b x` (every `yield` of the loop body `x` is below `b`) structurally -/
partial def post (b x : Lean.Expr) (hyps : Array (Lean.Expr × Lean.Expr) := #[]) : MetaM Lean.Expr := do
  let x ← whnfCore x
  if x.getAppFn.isFVar then
    for (r, h) in hyps do
      if x.getAppFn == r then return mkAppN h x.getAppArgs
  if x.isAppOfArity ``Bind.bind 6 then
    let a := x.getAppArgs
    let p ← withLocalDeclD `a a[2]! fun av => do mkLambdaFVars #[av] (← post b (a[5]!.beta #[av]) hyps)
    return mkAppN (mkConst ``OsuProofs.e2_yo_bind) #[a[2]!, b, a[4]!, a[5]!, p]
  if x.isAppOfArity ``ite 5 then
    let a := x.getAppArgs
    let pt ← withLocalDeclD `h a[1]! fun h => do mkLambdaFVars #[h] (← post b a[3]! hyps)
    let pe ← withLocalDeclD `h (mkNot a[1]!) fun h => do mkLambdaFVars #[h] (← post b a[4]! hyps)
    return mkAppN (mkConst ``OsuProofs.e2_yo_ite) #[b, a[1]!, a[2]!, a[3]!, a[4]!, pt, pe]
  if x.isAppOfArity ``dite 5 then
    let a := x.getAppArgs
    let pt ← withLocalDeclD `h a[1]! fun h => do mkLambdaFVars #[h] (← post b (a[3]!.beta #[h]) hyps)
    let pe ← withLocalDeclD `h (mkNot a[1]!) fun h => do mkLambdaFVars #[h] (← post b (a[4]!.beta #[h]) hyps)
    return mkAppN (mkConst ``OsuProofs.e2_yo_dite) #[b, a[1]!, a[2]!, a[3]!, a[4]!, pt, pe]
  if x.isAppOfArity ``Pure.pure 4 then
    let v ← whnfCore x.getAppArgs[3]!
    if v.isAppOfArity ``ForInStep.yield 2 then
      let w := v.getAppArgs[1]!
      let g ← mkFreshExprMVar (← mkAppM ``LT.lt #[w, b])
      let some g' ← g.mvarId!.falseOrByContra | throwError "e2_cong(post): falseOrByContra"
      g'.withContext do
        let hyps := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hyps g'
      return mkAppN (mkConst ``OsuProofs.e2_yo_yield) #[b, w, ← instantiateMVars g]
    if v.isAppOfArity ``ForInStep.done 2 then
      return mkAppN (mkConst ``OsuProofs.e2_yo_done) #[b, v.getAppArgs[1]!]
  if (← isMatcherApp x) then
    if let some xu ← delta? x then return ← post b xu hyps
  -- recursor with symbolic major, no remaining args
  if let .const cn lvls := x.getAppFn then
    if let .recInfo ri ← getConstInfo cn then
      let args := x.getAppArgs
      let nP := ri.numParams; let nM := ri.numMinors; let nI := ri.numIndices
      let total := nP + 1 + nM + nI + 1
      if args.size ≥ total && ri.numMotives == 1 then
        let maj ← whnf args[total - 1]!
        if maj.isLit || (← isConstructorApp maj) then
          let x2 ← whnfCore (mkAppN x.getAppFn (args.set! (total - 1) maj))
          if x2 != x then return ← post b x2 hyps
        let params := args.extract 0 nP
        let motive := args[nP]!
        let minors := args.extract (nP + 1) (nP + 1 + nM)
        let idxMaj := args.extract (nP + 1 + nM) total
        let rem := args.extract total args.size
        let yo (e : Lean.Expr) := mkApp2 (mkConst ``OsuProofs.E2YOlt) b e
        -- remaining binders: Prop args shared; action args with a hypothesis `∀ zs, E2YOlt b (r zs)`
        let rec remB (k : Nat) (T : Lean.Expr) (la bs : Array Lean.Expr)
            (kont : Array Lean.Expr → Array Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
          if k == 0 then return ← kont la bs
          let T ← whnf T
          let .forallE n A B _ := T | throwError "e2_cong(post): rec remaining binder{indentExpr T}"
          if ← isProp A then
            withLocalDeclD n A fun z => remB (k - 1) (B.instantiate1 z) (la.push z) (bs.push z) kont
          else
            withLocalDeclD n A fun r => do
              let hty ← forallTelescope A fun zs _ => do mkForallFVars zs (yo (mkAppN r zs))
              withLocalDeclD `hr hty fun hr => remB (k - 1) (B.instantiate1 r) (la.push r) ((bs.push r).push hr) kont
        let newMotive ← forallTelescope (← inferType motive) fun ys _ => do
          remB rem.size (mkAppN motive ys) #[] #[] fun la bs => do
            mkLambdaFVars ys (← mkForallFVars bs (yo (mkAppN (mkConst cn lvls) (params ++ #[motive] ++ minors ++ ys ++ la))))
        let pc := mkAppN (mkConst cn (Level.zero :: lvls.tail)) (params ++ #[newMotive])
        let alts ← forallBoundedTelescope (← inferType pc) nM fun hs _ => do
          let mut ps := #[]
          for h in hs do
            let p ← telescopeCore (← inferType h) fun fs body => do
              unless body.isAppOfArity ``OsuProofs.E2YOlt 2 do throwError "e2_cong(post): rec alt{indentExpr body}"
              let mut hy := hyps
              for f in fs do
                let fty ← inferType f
                let r? ← forallTelescope fty fun _ bb => do
                  if bb.isAppOfArity ``OsuProofs.E2YOlt 2 && bb.appArg!.getAppFn.isFVar then return some bb.appArg!.getAppFn
                  else return none
                if let some r := r? then hy := hy.push (r, f)
              mkLambdaFVars fs (← post b (← whnfCore body.appArg!) hy)
            ps := ps.push p
          return ps
        let mut extra := #[]
        for a in rem do
          if ← isProp (← inferType a) then extra := extra.push a
          else
            let pa ← forallTelescope (← inferType a) fun zs _ => do mkLambdaFVars zs (← post b (mkAppN a zs).headBeta hyps)
            extra := (extra.push a).push pa
        return mkAppN (mkAppN (mkAppN pc alts) idxMaj) extra
  -- throw
  let m ← mkFreshExprMVar (mkConst ``String)
  let thr := mkAppN (mkConst ``OsuProofs.e2_yo_throw) #[b, m]
  if ← isDefEq (← inferType thr) (mkApp2 (mkConst ``OsuProofs.E2YOlt) b x) then
    return ← instantiateMVars thr
  if let some xu ← unfoldDefinition? x then return ← post b xu hyps
  throwError "e2_cong(post): stuck at{indentExpr x}"

partial def act (x x' S : Lean.Expr) : M Lean.Expr := do
  let env ← read
  let x ← whnfCore x
  let x' ← whnfCore x'
  modify fun s => { s with depth := s.depth + 1 }
  if (← get).depth > 200000 then throwError "e2_cong: step budget exhausted"
  -- bind
  if x.isAppOfArity ``Bind.bind 6 && x'.isAppOfArity ``Bind.bind 6 then
    let a := x.getAppArgs; let a' := x'.getAppArgs
    let y := a[4]!; let k := a[5]!; let y' := a'[4]!; let k' := a'[5]!
    let yw ← whnfCore y
    if isReadE yw then
      let p ← act (k.beta #[env.C]) (k'.beta #[env.C']) S
      return mkAppN (mkConst ``e2_bind_read) #[a[3]!, env.C, env.C', k, k', S, p]
    let p1 ← act y y' S
    let α := a[2]!
    let p2 ← withLocalDeclD `a α fun av => withLocalDeclD `S (mkConst ``OsuModel.Sim.St) fun Sv => do
      let p ← act (k.beta #[av]) (k'.beta #[av]) Sv
      mkLambdaFVars #[av, Sv] p
    return mkAppN (mkConst ``e2_bind) #[α, a[3]!, env.C, env.C', y, y', k, k', S, p1, p2]
  -- ite / dite
  if x.isAppOfArity ``ite 5 && x'.isAppOfArity ``ite 5 then
    let a := x.getAppArgs; let a' := x'.getAppArgs
    let c := a[1]!
    let pt ← withLocalDeclD `h c fun h => do mkLambdaFVars #[h] (← act a[3]! a'[3]! S)
    let pe ← withLocalDeclD `h (mkNot c) fun h => do mkLambdaFVars #[h] (← act a[4]! a'[4]! S)
    return mkAppN (mkConst ``e2_ite) #[a[0]!.appArg!, env.C, env.C', c, a[2]!, a[3]!, a[4]!, a'[3]!, a'[4]!, S, pt, pe]
  if x.isAppOfArity ``dite 5 && x'.isAppOfArity ``dite 5 then
    let a := x.getAppArgs; let a' := x'.getAppArgs
    let c := a[1]!
    let pt ← withLocalDeclD `h c fun h => do mkLambdaFVars #[h] (← act (a[3]!.beta #[h]) (a'[3]!.beta #[h]) S)
    let pe ← withLocalDeclD `h (mkNot c) fun h => do mkLambdaFVars #[h] (← act (a[4]!.beta #[h]) (a'[4]!.beta #[h]) S)
    return mkAppN (mkConst ``e2_dite) #[a[0]!.appArg!, env.C, env.C', c, a[2]!, a[3]!, a'[3]!, a[4]!, a'[4]!, S, pt, pe]
  -- local hypotheses (remaining action arguments of a recursor)
  if x.getAppFn.isFVar then
    for (r, r', h) in env.hyps do
      if x.getAppFn == r && x'.getAppFn == r' then
        return mkAppN h (x.getAppArgs.push S)
  -- user facts
  for f in env.facts do
    if let some p ← tryFact f x x' S then return p
  -- loop lemmas
  for lem in env.lemmas do
    if let some p ← tryLemma lem x x' S then return p
  -- matchers: unfold to casesOn / dite
  if (← isMatcherApp x) then
    if let some xu ← delta? x then
      if let some xu' ← delta? x' then
        return ← act xu xu' S
  -- casesOn with symbolic major
  if let some p ← casesOnRule x x' S then return p
  -- user definitions: memo lemma
  if let .const n lvls := x.getAppFn then
    if let .recInfo _ ← getConstInfo n then
      throwError "e2_cong: recursor not handled{indentExpr x}\nvs{indentExpr x'}"
    if userDef n && x'.getAppFn.isConstOf n then
      let ci ← getConstInfo n
      let ty ← instantiateTypeLevelParams ci.toConstantVal lvls
      let simTy ← forallTelescope ty fun ps body =>
        return ps.size == x.getAppNumArgs && (body.isAppOf ``OsuModel.Sim.SimM || body.isAppOf ``ReaderT)
      if simTy then
        let pm ← memoFor n lvls
        let args := x.getAppArgs
        return mkAppN pm (args.push S)
      if let some xu ← delta? x then
        if let some xu' ← delta? x' then
          return ← act xu xu' S
  -- leaf
  let l := mkApp2 x env.C S
  let r := mkApp2 x' env.C' S
  if ← isDefEq l r then return ← mkEqRefl l
  -- fallback: unfold the head (monad plumbing)
  if let some xu ← unfoldDefinition? x then
    if let some xu' ← unfoldDefinition? x' then
      return ← act xu xu' S
  throwError "e2_cong: stuck at{indentExpr x}\nvs{indentExpr x'}"
where
  tryFact (f x x' S : Lean.Expr) : M (Option Lean.Expr) := do
    let env ← read
    let (mvs, _, concl) ← forallMetaTelescope (← inferType f)
    let some (_, lhs, _) := concl.eq? | return none
    let some (lx, _, _) := splitAct lhs | return none
    unless lx.getAppFn.constName? == x.getAppFn.constName? && lx.getAppFn.constName?.isSome do return none
    let saved ← (saveState : MetaM Meta.SavedState)
    let goal ← mkEq (mkApp2 x env.C S) (mkApp2 x' env.C' S)
    if ← isDefEq concl goal then return some (← instantiateMVars (mkAppN f mvs))
    (saved.restore : MetaM Unit); return none
  /-- try a congruence lemma `∀ .. C C' .. (h : ∀ .., f .. C S = f' .. C' S) .. S, lhs C S = rhs C' S` -/
  tryLemma (lem : Lean.Name) (x x' S : Lean.Expr) : M (Option Lean.Expr) := do
    let env ← read
    let cinfo ← getConstInfo lem
    let c ← mkConstWithFreshMVarLevels lem
    let (mvs, bis, concl) ← forallMetaTelescope (← inferType c)
    let some (_, lhs, rhs) := concl.eq? | return none
    let some (lx, _, _) := splitAct lhs | return none
    -- quick head check
    unless lx.getAppFn.constName? == x.getAppFn.constName? do return none
    let saved ← (saveState : MetaM Meta.SavedState)
    let goal ← mkEq (mkApp2 x env.C S) (mkApp2 x' env.C' S)
    let ok ← isDefEq (← mkEq lhs rhs) goal
    unless ok do (saved.restore : MetaM Unit); return none
    let _ := cinfo
    -- fill the remaining hypotheses (∀ .., a C S = b C' S) by `act`
    for mv in mvs, bi in bis do
      let mv := mv.mvarId!
      if ← mv.isAssigned then continue
      let ty ← instantiateMVars (← mv.getType)
      if bi.isInstImplicit then
        let inst ← synthInstance ty
        mv.assign inst; continue
      let p ← forallTelescope ty fun xs body => do
        if body.isAppOfArity ``OsuProofs.E2YOlt 2 then
          return ← mkLambdaFVars xs (← post body.appFn!.appArg! (← whnfCore body.appArg!))
        let some (_, l, r) := body.eq? | throwError "e2_cong: lemma {lem}: unexpected hypothesis{indentExpr ty}"
        let some (la, _, ls) := splitAct l | throwError "e2_cong: lemma {lem}: bad lhs{indentExpr l}"
        let some (ra, _, _) := splitAct r | throwError "e2_cong: lemma {lem}: bad rhs{indentExpr r}"
        let p ← act la.headBeta ra.headBeta ls
        mkLambdaFVars xs p
      mv.assign p
    return some (← instantiateMVars (mkAppN c mvs))
  /-- `T.rec params motive minors idx major` (no extra args; major symbolic): prove by `T.rec` itself with the
  motive `fun idx d => (T.rec .. d) C S = (T.rec' .. d) C' S` (the minors' induction hypotheses are unused). -/
  casesOnRule (x x' S : Lean.Expr) : M (Option Lean.Expr) := do
    let env ← read
    let .const cn lvls := x.getAppFn | return none
    unless x'.getAppFn.isConstOf cn do return none
    let .recInfo ri ← getConstInfo cn | return none
    unless ri.numMotives == 1 do return none
    let args := x.getAppArgs; let args' := x'.getAppArgs
    let nP := ri.numParams; let nM := ri.numMinors; let nI := ri.numIndices
    let total := nP + 1 + nM + nI + 1
    unless args.size ≥ total && args'.size == args.size do return none
    let params := args.extract 0 nP
    let motive := args[nP]!; let motive' := args'[nP]!
    let minors := args.extract (nP + 1) (nP + 1 + nM)
    let minors' := args'.extract (nP + 1) (nP + 1 + nM)
    let idxMaj := args.extract (nP + 1 + nM) total
    -- a major premise that reduces to a constructor (e.g. `n + 1`, a literal): reduce instead of splitting
    let maj ← whnf args[total - 1]!
    if maj.isLit || (maj.getAppFn.isConst && (← isConstructorApp maj)) then
      let x2 ← whnfCore (mkAppN x.getAppFn (args.set! (total - 1) maj))
      let x2' ← whnfCore (mkAppN x'.getAppFn (args'.set! (total - 1) maj))
      unless x2 == x do return some (← act x2 x2' S)
    let rem := args.extract total args.size
    let rem' := args'.extract total args'.size
    let St := mkConst ``OsuModel.Sim.St
    let mty ← inferType motive
    -- binders for the remaining arguments: a Prop argument is shared, an action argument is doubled with a
    -- congruence hypothesis
    let rec remB (k : Nat) (T T' : Lean.Expr) (la ra bs : Array Lean.Expr)
        (kont : Array Lean.Expr → Array Lean.Expr → Array Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
      if k == 0 then return ← kont la ra bs
      let T ← whnf T; let T' ← whnf T'
      let .forallE n A B _ := T | throwError "e2_cong: rec remaining binder{indentExpr T}"
      let .forallE _ A' B' _ := T' | throwError "e2_cong: rec remaining binder'{indentExpr T'}"
      if ← isProp A then
        withLocalDeclD n A fun z => remB (k - 1) (B.instantiate1 z) (B'.instantiate1 z) (la.push z) (ra.push z) (bs.push z) kont
      else
        withLocalDeclD n A fun r => withLocalDeclD n A' fun r' => do
          let hty ← forallTelescope A fun zs _ => withLocalDeclD `S St fun S2 => do
            mkForallFVars (zs.push S2) (← mkEq (mkApp2 (mkAppN r zs) env.C S2) (mkApp2 (mkAppN r' zs) env.C' S2))
          withLocalDeclD `hr hty fun hr =>
            remB (k - 1) (B.instantiate1 r) (B'.instantiate1 r') (la.push r) (ra.push r') (((bs.push r).push r').push hr) kont
    let newMotive ← forallTelescope mty fun ys _ => do
      remB rem.size (mkAppN motive ys) (mkAppN motive' ys) #[] #[] #[] fun la ra bs => do
        let l := mkApp2 (mkAppN (mkConst cn lvls) (params ++ #[motive] ++ minors ++ ys ++ la)) env.C S
        let r := mkApp2 (mkAppN (mkConst cn lvls) (params ++ #[motive'] ++ minors' ++ ys ++ ra)) env.C' S
        mkLambdaFVars ys (← mkForallFVars bs (← mkEq l r))
    let plvls := Level.zero :: lvls.tail
    let pc := mkAppN (mkConst cn plvls) (params ++ #[newMotive])
    let pty ← inferType pc
    let altProofs ← forallBoundedTelescope pty nM fun hs _ => do
      let mut ps := #[]
      for h in hs do
        let hty ← inferType h
        let p ← forallTelescopeReducing hty fun fs body => do
          let some (_, l, r) := body.eq? | throwError "e2_cong: rec alt{indentExpr body}"
          let some (la, _, _) := splitAct l | throwError "e2_cong: rec alt lhs"
          let some (ra, _, _) := splitAct r | throwError "e2_cong: rec alt rhs"
          let la ← whnfCore la
          let ra ← whnfCore ra
          -- register the congruence hypotheses among the binders
          let mut hyps := env.hyps
          for f in fs do
            let fty ← inferType f
            let hy? ← forallTelescope fty fun _ b => do
              match b.eq? with
              | some (_, l, r) =>
                if l.getAppFn.isFVar && r.getAppFn.isFVar && fs.contains l.getAppFn then
                  return some (l.getAppFn, r.getAppFn)
                else return none
              | none => return none
            if let some (a, b) := hy? then hyps := hyps.push (a, b, f)
          let p ← withReader (fun e => { e with hyps }) (act la ra S)
          mkLambdaFVars fs p
        ps := ps.push p
      return ps
    -- arguments for the remaining binders
    let mut extra := #[]
    for j in [0:rem.size] do
      let a := rem[j]!; let a' := rem'[j]!
      if ← isProp (← inferType a) then extra := extra.push a
      else
        let pj ← forallTelescope (← inferType a) fun zs _ => withLocalDeclD `S St fun S2 => do
          mkLambdaFVars (zs.push S2) (← act (mkAppN a zs).headBeta (mkAppN a' zs).headBeta S2)
        extra := ((extra.push a).push a').push pj
    return some (mkAppN (mkAppN (mkAppN pc altProofs) idxMaj) extra)
  reduceCases (e : Lean.Expr) : M Lean.Expr := do
    match ← unfoldDefinition? e with
    | some e' => whnfCore e'
    | none => whnfCore e
  memoFor (n : Lean.Name) (lvls : List Lean.Level) : M Lean.Expr := do
    let env ← read
    if let some p := (← get).memo[(n, lvls)]? then return p
    let ci ← getConstInfo n
    let fc := mkConst n lvls
    let ty ← instantiateTypeLevelParams ci.toConstantVal lvls
    let p ← forallTelescope ty fun ps _ => withLocalDeclD `S (mkConst ``OsuModel.Sim.St) fun Sv => do
      let app := mkAppN fc ps
      let some body ← delta? app | throwError "e2_cong: cannot unfold {n}"
      let p ← act body body Sv
      let _ := env
      mkLambdaFVars (ps.push Sv) p
    modify fun s => { s with memo := s.memo.insert (n, lvls) p }
    return p

end OsuProofs.E2C

namespace OsuProofs
open Lean Meta Elab Tactic

syntax (name := e2Cong) "e2_cong" "[" ident,* "]" ("using" term,*)? : tactic

@[tactic e2Cong] def evalE2Cong : Tactic := fun stx => do
  let lems ← stx[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  let facts ← if stx[4].isNone then pure #[] else
    stx[4][1].getSepArgs.mapM fun t => withMainContext (Lean.Elab.Tactic.elabTerm t none)
  let facts ← facts.mapM instantiateMVars
  liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, l, r) := tgt.eq? | throwError "e2_cong: goal is not an equation"
    let some (x, C, S) := OsuProofs.E2C.splitAct l | throwError "e2_cong: lhs is not `x C S`"
    let some (x', C', _) := OsuProofs.E2C.splitAct r | throwError "e2_cong: rhs is not `x' C' S`"
    let p ← (OsuProofs.E2C.act x x' S { C, C', lemmas := lems, facts }).run' {}
    g.assign p
    return []

end OsuProofs


/-! ## The spec simulation does not read `Config.mods` -/

namespace OsuProofs
open OsuModel.Sim


theorem e2_applyResult (C : Ctx) : ∀ n, (∀ r ty S, Sim.applyResult n r ty C S = Sim.applyResult n r ty (e2N C) S) ∧
    (∀ r S, Sim.handleHit n r C S = Sim.handleHit n r (e2N C) S) := by
  intro n
  induction n with
  | zero =>
    have h1 : ∀ r ty S, Sim.applyResult 0 r ty C S = Sim.applyResult 0 r ty (e2N C) S := by
      intro r ty S; rw [Sim.applyResult.eq_def]
      e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list, OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array, OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat]
    refine ⟨h1, fun r S => ?_⟩
    rw [Sim.handleHit.eq_def]
    e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list, OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array, OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat] using h1
  | succ n ih =>
    have h1 : ∀ r ty S, Sim.applyResult (n+1) r ty C S = Sim.applyResult (n+1) r ty (e2N C) S := by
      intro r ty S; rw [Sim.applyResult.eq_def]
      e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list, OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array, OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat] using ih.2
    refine ⟨h1, fun r S => ?_⟩
    rw [Sim.handleHit.eq_def]
    e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list, OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array, OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat] using h1
end OsuProofs

namespace OsuProofs
open OsuModel.Sim

set_option maxHeartbeats 0 in
theorem e2_stepOnce (C : Ctx) (S : St) : Sim.stepOnce C S = Sim.stepOnce (e2N C) S := by
  e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list,
    OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array,
    OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat]
    using (fun n => (e2_applyResult C n).1), (fun n => (e2_applyResult C n).2)

set_option maxHeartbeats 0 in
theorem e2_run (C : Ctx) (S : St) : Sim.run C S = Sim.run (e2N C) S := by
  e2_cong [OsuProofs.e2_forIn_array, OsuProofs.e2_forIn_range, OsuProofs.e2_forIn'_range, OsuProofs.e2_forIn_list,
    OsuProofs.e2_forIn'_list, OsuProofs.e2_mapM_array, OsuProofs.e2_mapM_list, OsuProofs.e2_foldlM_array,
    OsuProofs.e2_foldlM_list, OsuProofs.e2_loop_nat]
    using e2_stepOnce C

theorem e2_initState (cfg : Config) (pb : Playable) (w : Int) : initState cfg pb w = initState { cfg with mods := [] } pb w := rfl

/-- `runWith` does not read `Config.mods` (neither in the context nor in the initial-state config) -/
theorem e2_runWith (C : Ctx) (pb : Playable) : runWith C C.cfg pb = runWith (e2N C) (e2N C).cfg pb := by
  unfold runWith
  rw [show (e2N C).cfg = { C.cfg with mods := [] } from rfl, show (e2N C).smax = C.smax from rfl, ← e2_initState]
  cases initState C.cfg pb C.smax.initWithoutMods with
  | error e => rfl
  | ok s0 =>
    show (Sim.run C s0 >>= _) = (Sim.run (e2N C) s0 >>= _)
    rw [e2_run]
end OsuProofs

namespace OsuProofs
open OsuModel.Sim

theorem e2_forIn_inv {α : Type} (P : Config → Prop) (f : α → Config → Id (ForInStep Config))
    (h : ∀ a c, P c → P (f a c).value) : ∀ (l : List α) (c : Config), P c → P (forIn l c f) := by
  intro l; induction l with
  | nil => intro c hc; exact hc
  | cons x l ih =>
    intro c hc
    rw [List.forIn_cons]
    have := h x c hc
    revert this
    cases f x c with
    | done d => intro hd; exact hd
    | yield d => intro hd; exact ih d hd

theorem e2_ofMods_dbg (ms : List OsuModel.Beatmap.ModConfig) (pb : Playable) :
    (Config.ofMods ms pb).traceObj = none ∧ (Config.ofMods ms pb).dbgNoPresence = false := by
  unfold Config.ofMods
  simp only [Id.run]
  split
  all_goals
    refine e2_forIn_inv (fun c => c.traceObj = none ∧ c.dbgNoPresence = false) _ ?_ _ _ ?_
    intro a c hc
    repeat' split
    all_goals first | exact hc | simp_all

/-- mod-index ranges of `Config.ofMods` (the updatables' dynamic-rate / input-blocker indices) -/
def e2CfgIdx3 (c : Config) : Prop :=
  (∀ k, Updatable.dynRate k ∈ c.updatables → k < c.dynRates.size) ∧
  (∀ k, Updatable.inputBlock k ∈ c.updatables → k < c.inputBlockers.size) ∧
  (∀ p k, (p, RateVal.dyn k) ∈ c.rateSources → k < c.dynRates.size)

theorem e2_ofMods_idx3 (ms : List OsuModel.Beatmap.ModConfig) (pb : Playable) : e2CfgIdx3 (Config.ofMods ms pb) := by
  unfold Config.ofMods
  simp only [Id.run]
  split
  all_goals
    refine e2_forIn_inv e2CfgIdx3 _ ?_ _ _ ?_
    intro a c hc
    obtain ⟨h1, h2, h3⟩ := hc
    repeat' split
    all_goals first
      | exact ⟨h1, h2, h3⟩
      | (refine ⟨fun k hk => ?_, fun k hk => ?_, fun p k hk => ?_⟩ <;>
          simp only [ForInStep.value, pure, Array.mem_push, Array.size_push, Prod.mk.injEq, reduceCtorEq, and_false,
            or_false, false_or] at hk ⊢ <;>
          (try rcases hk with hk | hk) <;>
          first
            | exact h1 k hk | exact h2 k hk | exact h3 p k hk
            | exact Nat.lt_succ_of_lt (h1 k hk) | exact Nat.lt_succ_of_lt (h2 k hk)
            | exact Nat.lt_succ_of_lt (h3 p k hk)
            | (simp_all; done) | (simp_all; omega)
            | (rcases hk with hk | hk <;> simp_all <;> omega))
  all_goals (refine ⟨?_, ?_, ?_⟩ <;> simp)
/-- sim9: every `easy k` fail override indexes `easyRetries` (`Config.ofMods` pushes `.easy size` with the retry) -/
def s9EasyOk (c : Config) : Prop := ∀ k, FailOverride.easy k ∈ c.failOverrides → k < c.easyRetries.size

theorem s9_ofMods_easy (ms : List OsuModel.Beatmap.ModConfig) (pb : Playable) : s9EasyOk (Config.ofMods ms pb) := by
  unfold Config.ofMods
  simp only [Id.run]
  split
  all_goals
    refine e2_forIn_inv s9EasyOk _ ?_ _ _ ?_
    intro a c hc
    repeat' split
    all_goals first
      | exact hc
      | (intro k hk
         simp only [ForInStep.value, pure, Array.mem_push, Array.size_push, reduceCtorEq, or_false,
           FailOverride.easy.injEq] at hk ⊢
         first
           | exact hc k hk
           | exact Nat.lt_succ_of_lt (hc k hk)
           | (rcases hk with hk | hk
              · exact Nat.lt_succ_of_lt (hc k hk)
              · omega)
           | (simp_all; done))
  all_goals (intro k hk; simp at hk)

/-- the config facts of `Config.ofMods` the sim proofs use: mod-index ranges (`sc3Cfg`) and easy-retry indices
(sim9's initial `simEmitBud`) -/
def e2CfgIdx (c : Config) : Prop := e2CfgIdx3 c ∧ s9EasyOk c

theorem e2_ofMods_idx (ms : List OsuModel.Beatmap.ModConfig) (pb : Playable) : e2CfgIdx (Config.ofMods ms pb) :=
  ⟨e2_ofMods_idx3 ms pb, s9_ofMods_easy ms pb⟩
end OsuProofs
