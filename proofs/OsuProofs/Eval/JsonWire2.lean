/-
Wiring of `EvalAssumptions.config` (Sim2/ModsCfg `config_of_mods_refines_wf`) and `.trueRate` (Sim2/Mods), json agent.
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Sim2.ModsCfg
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl

theorem js_ev_config (h64 : System.Platform.numBits = 64) :
    ∀ (ms : Slice beatmap.mod_settings.ModConfig) (pb : sim.playable.Playable) (lr : Bool),
    (∀ m ∈ ms.val, ev_mcOk m) → ms.val.length < 2^62 + 2^61 → ∃ c, sim.mods.config_of_mods ms pb lr = ok c ∧
    ev_cfgRel c { OsuModel.Sim.Config.ofMods (ms.val.map mcS) (playableS ev_tn pb) with lazerReplay := lr } ∧
    ev_cfgWF c := by
  intro ms pb lr hok hl
  have hU := usize_max_64 h64
  obtain ⟨c, hc, e, wf⟩ := sim.mods.config_of_mods_refines_wf ev_tn ms pb lr (fun m h => ⟨(hok m h).2.2, (hok m h).1⟩)
    (by omega)
  exact ⟨c, hc, e, wf⟩

theorem js_ev_trueRate : ∀ (c : sim.mods.Config) (sp : Slice float.F64) (C : OsuModel.Sim.Config), ev_cfgRel c C →
    ev_cfgWF c → sp.val.length = c.dyn_rates.val.length →
    ∃ x, sim.mods.true_rate c sp = ok x ∧ C.trueRate sp.val.toArray = .ok x := by
  intro c sp C hrel hwf hl
  obtain ⟨x, hx, hX⟩ := sim.mods.true_rate_refines c sp (fun s hs k hk => by rw [hl]; exact hwf s hs k hk)
  refine ⟨x, hx, ?_⟩
  unfold ev_cfgRel at hrel
  have eR : (configS c).rateSources = C.rateSources := by rw [hrel]
  have eT : ∀ s, C.trueRate s = (configS c).trueRate s := by
    intro s; unfold OsuModel.Sim.Config.trueRate; rw [eR]
  rw [eT]
  have ea : (abs sp : _root_.Array float.F64) = sp.val.toArray := by simp [abs]
  rw [← ea]; exact hX

end OsuProofs
