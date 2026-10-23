/-
Spec-level size fact for `EvalAssumptions.config` (json agent): `resolveMods` returns at most
`|decoded| + |override|` mods (the override loop replaces or appends one mod per entry).
-/
import OsuModel.Eval
open OsuModel.Eval
open OsuModel.Beatmap (ModConfig)

namespace OsuProofs

theorem js_forIn_len {ε α : Type} (f : α → List ModConfig → Except ε (ForInStep (List ModConfig)))
    (hf : ∀ m r x, f m r = .ok x → ∃ r', x = .yield r' ∧ r'.length ≤ r.length + 1) :
    ∀ (ov : List α) (mods M : List ModConfig), forIn ov mods f = .ok M → M.length ≤ mods.length + ov.length := by
  intro ov; induction ov with
  | nil => intro mods M h; simp only [List.forIn_nil] at h; cases h; simp
  | cons m ov ih =>
    intro mods M h
    simp only [List.forIn_cons] at h
    cases hm : f m mods with
    | error e => rw [hm] at h; cases h
    | ok x =>
      obtain ⟨r', rfl, hl⟩ := hf m mods x hm
      rw [hm] at h
      have := ih r' M h
      simp; omega

theorem js_resolveMods_len (d : List ModConfig) (o : OsuModel.Eval.Options) (M : List ModConfig) (h : resolveMods d o = .ok M) :
    M.length ≤ d.length + (o.modsOverride.map List.length).getD 0 := by
  obtain ⟨ov, rm, nc⟩ := o
  have hfin : ∀ (L : List ModConfig), (if (L.any fun m => m.known && (m.acronym == "AT" || m.acronym == "CN")) = true then
      (reject "mods" "autoplay-type mods are not supported (they replace the replay)" : EvalM PUnit) >>= fun _ => (pure L : EvalM _)
      else pure L) = .ok M → M = L := by
    intro L hL; split at hL
    · simp [reject, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hL
    · cases hL; rfl
  have hc : ∀ L : List ModConfig, (if nc = true then L.filter (fun m => !(m.known && m.acronym == "CL")) else L).length ≤ L.length := by
    intro L; split <;> simp [List.length_filter_le]
  cases ov with
  | none =>
    simp only [OsuModel.Eval.resolveMods] at h
    simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ite_false] at h
    split at h <;> (have := hfin _ h; subst this; simp [List.length_filter_le])
  | some ov =>
    simp only [OsuModel.Eval.resolveMods, Option.isSome_some, Bool.and_true] at h
    have hbind : ∀ x : Except Rejection (List ModConfig), (x >>= fun s =>
        if (s.any fun m => m.known && (m.acronym == "AT" || m.acronym == "CN")) = true then
          (reject "mods" "autoplay-type mods are not supported (they replace the replay)" : EvalM PUnit) >>= fun _ => (pure s : EvalM _)
        else pure s) = .ok M → x = .ok M := by
      intro x hx; cases x with
      | error e => simp [Bind.bind, Except.bind] at hx
      | ok L => simp only [Bind.bind, Except.bind] at hx; have := hfin L hx; subst this; rfl
    have hf : ∀ (m : ModConfig) (r : List ModConfig) x, (if (!m.known) = true then
            (reject "mods" (toString "unknown mod acronym: " ++ toString m.acronym) : EvalM PUnit) >>= fun _ =>
              (pure (ForInStep.yield (List.filter (fun x => x.acronym != m.acronym) r ++ [m])) : EvalM _)
            else pure (ForInStep.yield (List.filter (fun x => x.acronym != m.acronym) r ++ [m]))) = .ok x →
          ∃ r', x = .yield r' ∧ r'.length ≤ r.length + 1 := by
      intro m r x hx
      split at hx
      · simp [reject, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hx
      · cases hx; exact ⟨_, rfl, by simp [List.length_filter_le]⟩
    have hS : (if rm = true then [] else d).length ≤ d.length := by split <;> simp
    split at h
    · have := js_forIn_len _ hf ov _ M (hbind _ h)
      have := List.length_filter_le (fun m : ModConfig => !(m.known && m.acronym == "CL")) (if rm = true then [] else d)
      simp only [Option.map_some, Option.getD_some]; omega
    · have := js_forIn_len _ hf ov _ M (hbind _ h)
      simp only [Option.map_some, Option.getD_some]; omega

end OsuProofs
