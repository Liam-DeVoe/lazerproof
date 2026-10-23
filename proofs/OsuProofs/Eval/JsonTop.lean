/-
`osu_eval_refines` (json agent, final-audit M2/M3): the end-to-end theorem at the binary's environment
(`default_env`), and its `--mods` composition with `parse_mods` (discharging `hopts`).

What is compared (docs/proof-pipeline.md §5, final-audit m1/m2):
* rejections: only the STAGE is compared (`ev_topRel`, D52b); the reason text is NOT compared;
* float fields are compared as Lean `Float`s, i.e. up to NaN payload (FunsExternal maps every Rust NaN to the
  model's single NaN, §4); no output field is proved NaN-free;
* the environment: the spec side is `defaultEnv` itself. The Rust `Env` keeps only an is-PAC flag per chain node
  (`default_env_refines`: `abs default_env = ev_envNorm defaultEnv`), and since D72 (final-audit M2(a)) the spec's
  `defaultEnv` blanks every non-PAC type name, so `ev_envNorm defaultEnv = defaultEnv` (`ev_envNorm_defaultEnv`);
  the former §5 row `Env.typeNames` is gone.
* the step frame-index range (formerly the §5 row `SchedFramesIn`) is checked by `sched_ctx` (D72).
The CLI shell (impl/osu_eval/src/main.rs: argv, `explicit:` parsing, JSON printer) is outside (§5 row `CLI shell`).
-/
import OsuProofs.Eval.JsonFinal
import OsuProofs.Eval.JsonMods
import OsuProofs.Eval.Osr
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

-- CONDITIONAL: O = js_EvalOpen: lzmaBound [TRUSTED, §5] only. Trusted hypotheses: InputBounds, PlayableBounds, RunBudgetIn (§5).
/-- **`osu_eval` refines the spec** at the binary's environment `default_env` (main.rs:546): for every input pair
within `InputBounds` / `PlayableBounds`, options with well-formed override mods and schedules within the bound, the
Rust `evaluate` returns a result related by `ev_topRel` to `OsuModel.Eval.evaluate defaultEnv`
(results equal up to NaN payload; rejections equal in stage, reason text not compared). -/
theorem osu_eval_refines (O : js_EvalOpen) (e : sim.geometry.Env) (he : eval.env.default_env = ok e)
    (bm osr : Slice U8) (hb : InputBounds bm osr) (opts : eval.Options)
    (hopts : ∀ ov, opts.mods_override = some ov → (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^61)
    (hpb : PlayableBounds bm osr opts)
    (sched : eval.Schedule) (hsched : ∀ refs, sched = .Explicit refs → refs.val.length * 100000000 + 4 < 2^61)
    (hrb : RunBudgetIn OsuModel.Eval.defaultEnv bm osr opts sched) :
    ∃ r, eval.evaluate e bm osr opts sched = ok r ∧
      ev_topRel r (OsuModel.Eval.evaluate OsuModel.Eval.defaultEnv (bytesS bm) (bytesS osr)
        (ev_optsS opts) (ev_schedS sched)) := by
  obtain ⟨e', he', ee⟩ := eval.env.default_env_refines
  have := Result.ok_injective (he.symm.trans he'); subst this
  rw [ev_envNorm_defaultEnv] at ee
  rw [← ee] at hrb ⊢
  exact eval.evaluate_refines_open O e bm osr hb opts hopts hpb sched hsched hrb

/-- `--mods` (main.rs:506-510): options built from a successful `parse_mods` satisfy `hopts` (every config
`ev_mcOk`, from `eval.mods_json.parse_mods_refines`); the count bound `< 2^61` is the §5 row `CLI shell`. -/
theorem js_hopts_of_parse_mods (h64 : System.Platform.numBits = 64) (s : Slice U32) (hs : ValidStr s)
    (hlen : s.val.length + 8 ≤ Usize.max) (h62 : s.val.length < 2^62)
    (ms : alloc.vec.Vec beatmap.mod_settings.ModConfig) (hp : eval.mods_json.parse_mods s = ok (.Ok ms))
    (hn : ms.val.length < 2^61) (rm nc : Bool) :
    ∀ ov, ({ mods_override := some ms, replace_mods := rm, no_classic := nc } : eval.Options).mods_override = some ov →
      (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^61 := by
  intro ov hov
  simp only [Option.some.injEq] at hov; subst hov
  obtain ⟨r, hr, hrel⟩ := eval.mods_json.parse_mods_refines h64 s hs hlen h62
  have := Result.ok_injective (hp.symm.trans hr); subst this
  revert hrel
  cases SimJson.parseMods (String.ofList (strS s)) with
  | ok MS => intro h; exact ⟨h.2, hn⟩
  | error _ => intro h; exact h.elim

/-- `hopts` without `--mods` -/
theorem js_hopts_none (rm nc : Bool) :
    ∀ ov, ({ mods_override := none, replace_mods := rm, no_classic := nc } : eval.Options).mods_override = some ov →
      (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^61 := by
  intro ov h; cases h

end OsuProofs
