/-
`sim::step::init_state` (Rust) refines `OsuModel.Sim.initState`: `ostate_init`, `as_init` (+`as_init_one`),
`initial_speeds`, `initial_pools`, the object / AS-history / input-blocker loops, and the initial `St` record
(`simStS`). Lake-only (imports Sim2.Mods for the `DynRate` lemmas); not in the REPL client chain (Sim/ORDER).
-/
import OsuProofs.Sim.IdxKind
import OsuProofs.Sim.ProcPhase
import OsuProofs.Sim.AccChallenge
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_ostate_init_loop (n : Usize) :
    ∀ m (v : alloc.vec.Vec (Option sim.state.Res)) (i : Usize), n.val - i.val = m → i.val ≤ n.val →
      v.val = List.replicate i.val none →
      ∃ w, sim.state.ostate_init_loop n v i = ok w ∧ w.val = List.replicate n.val none := by
  intro m
  induction m with
  | zero =>
    intro v i hm hi hv
    refine ⟨v, ?_, by rw [hv]; congr 1; omega⟩
    unfold sim.state.ostate_init_loop; rw [loop_unfold]
    have : ¬ (i < n) := by scalar_tac
    simp [sim.state.ostate_init_loop.body, this]
  | succ m ih =>
    intro v i hm hi hv
    have hlt : i < n := by scalar_tac
    have hmax : n.val ≤ Usize.max := by scalar_tac
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by omega)
    have hpl : v.val.length < Usize.max := by rw [hv]; simp; omega
    obtain ⟨w, hw, ew⟩ := ih (vpush v none hpl) i1 (by omega) (by omega) (by simp [hv, ei1, List.replicate_succ'])
    refine ⟨w, ?_, ew⟩
    unfold sim.state.ostate_init_loop; rw [loop_unfold]; dsimp only
    rw [show sim.state.ostate_init_loop.body n v i = ok (.cont (vpush v none hpl, i1)) by
      simp [sim.state.ostate_init_loop.body, hlt, vec_push_ok _ _ hpl, hi1]]
    simp only [bind_ok]
    unfold sim.state.ostate_init_loop at hw; exact hw

theorem sim.state.ostate_init_refines (s e : F64) (n : Usize) :
    ∃ o, sim.state.ostate_init s e n = ok o ∧
      ({ lifetimeStart := s, lifetimeEnd := e, nested := (List.replicate n.val none).toArray } : OsuModel.Sim.OState) =
        abs o := by
  obtain ⟨w, hw, ew⟩ := sim_ostate_init_loop n _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  refine ⟨?o, ?h1, ?h2⟩
  case h1 => simp [sim.state.ostate_init, hw, fb32_0, netx_F64_POS_INF, netx_F64_NEG_INF]; rfl
  case h2 =>
    simp [abs, ostateS, ew, actListS, s2_empty_val.2, lifeS, armedS, alloc.vec.Vec.new]
    first | rfl | decide

def simAdL (L : List sim.mods.DynRate) : List F64 :=
  L.filterMap (fun d => match d with | .Adaptive ir => some ir | _ => none)

def simSetSp (i : F64) : Except NetExn F64 := OsuModel.Sim.DynRate.setSpeed (.adaptive i) 1 i

theorem sim_as_init_loop (cfg : sim.mods.Config) :
    ∀ n (out : alloc.vec.Vec F64) (d : Usize), cfg.dyn_rates.val.length - d.val = n → d.val ≤ cfg.dyn_rates.val.length →
      out.val.length ≤ d.val →
      ∃ R, sim.step.as_init_loop cfg out d = ok R ∧
        simRel (fun v : alloc.vec.Vec F64 => v.val) R
          (OsuModel.Sim.netStr (((simAdL (cfg.dyn_rates.val.drop d.val)).mapM simSetSp).map (out.val ++ ·))) := by
  intro n
  induction n with
  | zero =>
    intro out d hn hd ho
    have hdn : cfg.dyn_rates.val.drop d.val = [] := List.drop_of_length_le (by omega)
    refine ⟨.Ok out, ?_, by simp [hdn, simAdL, simRel, Except.map, OsuModel.Sim.netStr]⟩
    unfold sim.step.as_init_loop; rw [loop_unfold]
    have : ¬ (d < alloc.vec.Vec.len cfg.dyn_rates) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.as_init_loop.body, this]
  | succ n ih =>
    intro out d hn hd ho
    have hlt : d.val < cfg.dyn_rates.val.length := by omega
    have hlt' : d < alloc.vec.Vec.len cfg.dyn_rates := by rw [vec_lt_len_iff]; exact hlt
    have hmax := cfg.dyn_rates.property
    obtain ⟨d1, hd1, ed1⟩ := usize_add_one d (by omega)
    rw [List.drop_eq_getElem_cons hlt]
    cases hx : cfg.dyn_rates.val[d.val]'hlt with
    | TimeRamp a b c e =>
      obtain ⟨R, hR, eR⟩ := ih out d1 (by omega) (by omega) (by omega)
      refine ⟨R, ?_, ?_⟩
      · unfold sim.step.as_init_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.as_init_loop.body cfg out d = ok (.cont (out, d1)) by
          simp [sim.step.as_init_loop.body, hlt', vec_index_usize_ok _ _ hlt, hx, sim.step.as_init_one,
            core.result.Result.Insts.CoreOpsTry.branch, hd1]]
        simp only [bind_ok]
        unfold sim.step.as_init_loop at hR; exact hR
      · rw [ed1] at eR; simpa [simAdL] using eR
    | Adaptive ir =>
      have hss := sim.mods.dyn_rate_set_speed_refines (.Adaptive ir) 1 ir
      cases hsp : simSetSp ir with
      | error x =>
        refine ⟨.Err (.Net (exnI x)), ?_, ⟨s!"lazer would throw: {repr x}", ?_⟩⟩
        · unfold sim.step.as_init_loop; rw [loop_unfold]
          simp [sim.step.as_init_loop.body, hlt', vec_index_usize_ok _ _ hlt, hx, sim.step.as_init_one, sim_step_F64_1,
            hss, show (abs (sim.mods.DynRate.Adaptive ir) : OsuModel.Sim.DynRate).setSpeed 1 ir = simSetSp ir from rfl, hsp,
            exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
            core.convert.From.from]
        · simp [simAdL, List.mapM_cons, hsp, Bind.bind, Except.bind, Except.map, OsuModel.Sim.netStr]
      | ok y =>
        have hpl : out.val.length < Usize.max := by omega
        obtain ⟨R, hR, eR⟩ := ih (vpush out y hpl) d1 (by omega) (by omega) (by simp; omega)
        refine ⟨R, ?_, ?_⟩
        · unfold sim.step.as_init_loop; rw [loop_unfold]; dsimp only
          rw [show sim.step.as_init_loop.body cfg out d = ok (.cont (vpush out y hpl, d1)) by
            simp [sim.step.as_init_loop.body, hlt', vec_index_usize_ok _ _ hlt, hx, sim.step.as_init_one, sim_step_F64_1,
              hss, show (abs (sim.mods.DynRate.Adaptive ir) : OsuModel.Sim.DynRate).setSpeed 1 ir = simSetSp ir from rfl,
              hsp, exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, vec_push_ok _ _ hpl, hd1]]
          simp only [bind_ok]
          unfold sim.step.as_init_loop at hR; exact hR
        · rw [ed1] at eR
          simp only [simAdL, List.filterMap_cons, List.mapM_cons, hsp] at eR ⊢
          cases hm : List.mapM simSetSp (simAdL (List.drop (d.val + 1) cfg.dyn_rates.val)) <;>
            simp_all [simAdL, Bind.bind, Except.bind, Except.map, OsuModel.Sim.netStr, simRel, Pure.pure, Except.pure]

theorem sim_init_speeds_loop (cfg : sim.mods.Config) :
    ∀ n (out : alloc.vec.Vec F64) (d : Usize), cfg.dyn_rates.val.length - d.val = n → d.val ≤ cfg.dyn_rates.val.length →
      out.val.length ≤ d.val →
      ∃ R, sim.step.initial_speeds_loop cfg out d = ok R ∧
        simRel (fun v : alloc.vec.Vec F64 => v.val) R
          (OsuModel.Sim.netStr ((((cfg.dyn_rates.val.drop d.val).map abs).mapM
            (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed)).map (out.val ++ ·))) := by
  intro n
  induction n with
  | zero =>
    intro out d hn hd ho
    have hdn : cfg.dyn_rates.val.drop d.val = [] := List.drop_of_length_le (by omega)
    refine ⟨.Ok out, ?_, by simp [hdn, simRel, Except.map, OsuModel.Sim.netStr]⟩
    unfold sim.step.initial_speeds_loop; rw [loop_unfold]
    have : ¬ (d < alloc.vec.Vec.len cfg.dyn_rates) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.initial_speeds_loop.body, this]
  | succ n ih =>
    intro out d hn hd ho
    have hlt : d.val < cfg.dyn_rates.val.length := by omega
    have hlt' : d < alloc.vec.Vec.len cfg.dyn_rates := by rw [vec_lt_len_iff]; exact hlt
    have hmax := cfg.dyn_rates.property
    obtain ⟨d1, hd1, ed1⟩ := usize_add_one d (by omega)
    rw [List.drop_eq_getElem_cons hlt]
    set x := cfg.dyn_rates.val[d.val]'hlt with hx
    have hs := sim.mods.dyn_rate_initial_speed_refines x
    cases hsp : (abs x : OsuModel.Sim.DynRate).initialSpeed with
    | error e =>
      refine ⟨.Err (.Net (exnI e)), ?_, ⟨s!"lazer would throw: {repr e}", ?_⟩⟩
      · unfold sim.step.initial_speeds_loop; rw [loop_unfold]
        simp [sim.step.initial_speeds_loop.body, hlt', vec_index_usize_ok _ _ hlt, ← hx, hs, hsp, exceptI,
          sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.From.from]
      · simp [List.mapM_cons, hsp, Bind.bind, Except.bind, Except.map, OsuModel.Sim.netStr]
    | ok y =>
      have hpl : out.val.length < Usize.max := by omega
      obtain ⟨R, hR, eR⟩ := ih (vpush out y hpl) d1 (by omega) (by omega) (by simp; omega)
      refine ⟨R, ?_, ?_⟩
      · unfold sim.step.initial_speeds_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.initial_speeds_loop.body cfg out d = ok (.cont (vpush out y hpl, d1)) by
          simp [sim.step.initial_speeds_loop.body, hlt', vec_index_usize_ok _ _ hlt, ← hx, hs, hsp, exceptI,
            sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, vec_push_ok _ _ hpl, hd1]]
        simp only [bind_ok]
        unfold sim.step.initial_speeds_loop at hR; exact hR
      · rw [ed1] at eR
        simp only [List.map_cons, List.mapM_cons, hsp] at eR ⊢
        cases hm : List.mapM (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed)
            (List.map abs (List.drop (d.val + 1) cfg.dyn_rates.val)) <;>
          simp_all [Bind.bind, Except.bind, Except.map, OsuModel.Sim.netStr, simRel, Pure.pure, Except.pure]

theorem sim_pool_init (pk : Usize) (h : pk.val < 6) :
    ∃ m : Usize, Std.Array.index_usize sim.state.POOL_INITIAL pk = ok m ∧
      m.val = OsuModel.Sim.poolInitial[pk.val]'(by simp [OsuModel.Sim.poolInitial]; omega) := by
  have hl : sim.state.POOL_INITIAL.val = [20#usize, 20#usize, 20#usize, 2#usize, 10#usize, 10#usize] := by
    unfold sim.state.POOL_INITIAL; rfl
  have h' : pk.val < sim.state.POOL_INITIAL.val.length := by rw [hl]; simpa using h
  refine ⟨_, s2_arr_index _ _ h', ?_⟩
  simp only [hl]
  have : pk.val = 0 ∨ pk.val = 1 ∨ pk.val = 2 ∨ pk.val = 3 ∨ pk.val = 4 ∨ pk.val = 5 := by omega
  rcases this with e | e | e | e | e | e <;> simp [e, OsuModel.Sim.poolInitial]

theorem sim_pool_inner (pk : Usize) (N : Usize) (hN : Std.Array.index_usize sim.state.POOL_INITIAL pk = ok N) :
    ∀ m (p : alloc.vec.Vec (Option Usize)) (q : Usize), N.val - q.val = m → q.val ≤ N.val →
      p.val = List.replicate q.val none →
      ∃ w, sim.step.initial_pools_loop0_loop0 pk p q = ok w ∧ w.val = List.replicate N.val none := by
  intro m
  induction m with
  | zero =>
    intro p q hm hq hp
    refine ⟨p, ?_, by rw [hp]; congr 1; omega⟩
    unfold sim.step.initial_pools_loop0_loop0; rw [loop_unfold]
    have : ¬ (q.val < N.val) := by omega
    simp [sim.step.initial_pools_loop0_loop0.body, hN, this]
  | succ m ih =>
    intro p q hm hq hp
    have hlt : q.val < N.val := by omega
    have hmax : N.val ≤ Usize.max := by scalar_tac
    obtain ⟨q1, hq1, eq1⟩ := usize_add_one q (by omega)
    have hpl : p.val.length < Usize.max := by rw [hp]; simp; omega
    obtain ⟨w, hw, ew⟩ := ih (vpush p none hpl) q1 (by omega) (by omega) (by simp [hp, eq1, List.replicate_succ'])
    refine ⟨w, ?_, ew⟩
    unfold sim.step.initial_pools_loop0_loop0; rw [loop_unfold]; dsimp only
    rw [show sim.step.initial_pools_loop0_loop0.body pk p q = ok (.cont (vpush p none hpl, q1)) by
      simp [sim.step.initial_pools_loop0_loop0.body, hN, hlt, vec_push_ok _ _ hpl, hq1]]
    simp only [bind_ok]
    unfold sim.step.initial_pools_loop0_loop0 at hw; exact hw

theorem sim_pools_loop :
    ∀ m (pools : alloc.vec.Vec (alloc.vec.Vec (Option Usize))) (pk : Usize), 6 - pk.val = m → pk.val ≤ 6 →
      pools.val.map (fun l => l.val) = (OsuModel.Sim.poolInitial.toList.take pk.val).map (fun n => List.replicate n (none : Option Usize)) →
      ∃ w, sim.step.initial_pools_loop0 pools pk = ok w ∧
        w.val.map (fun l => l.val) = OsuModel.Sim.poolInitial.toList.map (fun n => List.replicate n none) := by
  intro m
  induction m with
  | zero =>
    intro pools pk hm hpk hp
    refine ⟨pools, ?_, ?_⟩
    · unfold sim.step.initial_pools_loop0; rw [loop_unfold]
      have : ¬ (pk < 6#usize) := by scalar_tac
      simp [sim.step.initial_pools_loop0.body, this]
    · rw [hp, List.take_of_length_le (by simp [OsuModel.Sim.poolInitial]; omega)]
  | succ m ih =>
    intro pools pk hm hpk hp
    have hlt : pk.val < 6 := by omega
    have hlt' : pk < 6#usize := by scalar_tac
    obtain ⟨N, hN, eN⟩ := sim_pool_init pk hlt
    obtain ⟨p, hpp, ep⟩ := sim_pool_inner pk N hN _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
    obtain ⟨pk1, hpk1, epk1⟩ := usize_add_one pk (by scalar_tac)
    have hpl : pools.val.length < Usize.max := by
      have := congrArg List.length hp; simp at this
      have : pools.val.length ≤ 6 := by rw [this]; have := Nat.min_le_left pk.val OsuModel.Sim.poolInitial.size; omega
      have := sim_usize_max_ge; omega
    obtain ⟨w, hw, ew⟩ := ih (vpush pools p hpl) pk1 (by omega) (by omega) (by
      simp only [vpush_val, List.map_append, List.map_cons, List.map_nil, hp, epk1, ep, eN]
      rw [List.take_add_one]
      simp [List.getElem?_eq_getElem (show pk.val < OsuModel.Sim.poolInitial.toList.length by
        simp [OsuModel.Sim.poolInitial]; omega)])
    refine ⟨w, ?_, ew⟩
    unfold sim.step.initial_pools_loop0; rw [loop_unfold]; dsimp only
    rw [show sim.step.initial_pools_loop0.body pools pk = ok (.cont (vpush pools p hpl, pk1)) by
      simp [sim.step.initial_pools_loop0.body, hlt', hpp, vec_push_ok _ _ hpl, hpk1]]
    simp only [bind_ok]
    unfold sim.step.initial_pools_loop0 at hw; exact hw

theorem sim.step.initial_pools_refines :
    ∃ w, sim.step.initial_pools = ok w ∧
      w.val.map (fun l => l.val) = OsuModel.Sim.poolInitial.toList.map (fun n => List.replicate n none) := by
  obtain ⟨w, hw, ew⟩ := sim_pools_loop _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  exact ⟨w, hw, ew⟩

theorem sim_rec8_loop (ir : F64) :
    ∀ m (rec : alloc.vec.Vec F64) (q : Usize), 8 - q.val = m → q.val ≤ 8 → rec.val = List.replicate q.val ir →
      ∃ w, sim.step.init_state_loop1_loop0 ir rec q = ok w ∧ w.val = List.replicate 8 ir := by
  intro m
  induction m with
  | zero =>
    intro rec q hm hq hr
    refine ⟨rec, ?_, by rw [hr]; congr 1; omega⟩
    unfold sim.step.init_state_loop1_loop0; rw [loop_unfold]
    have : ¬ (q < 8#usize) := by scalar_tac
    simp [sim.step.init_state_loop1_loop0.body, this]
  | succ m ih =>
    intro rec q hm hq hr
    have hlt : q < 8#usize := by scalar_tac
    have := sim_usize_max_ge
    obtain ⟨q1, hq1, eq1⟩ := usize_add_one q (by scalar_tac)
    have hpl : rec.val.length < Usize.max := by rw [hr]; simp; scalar_tac
    obtain ⟨w, hw, ew⟩ := ih (vpush rec ir hpl) q1 (by omega) (by omega) (by simp [hr, eq1, List.replicate_succ'])
    refine ⟨w, ?_, ew⟩
    unfold sim.step.init_state_loop1_loop0; rw [loop_unfold]; dsimp only
    rw [show sim.step.init_state_loop1_loop0.body ir rec q = ok (.cont (vpush rec ir hpl, q1)) by
      simp [sim.step.init_state_loop1_loop0.body, hlt, vec_push_ok _ _ hpl, hq1]]
    simp only [bind_ok]
    unfold sim.step.init_state_loop1_loop0 at hw; exact hw

theorem sim_as_recent_loop (v : alloc.vec.Vec sim.mods.DynRate) :
    ∀ m (ar : alloc.vec.Vec (alloc.vec.Vec F64)) (sn : alloc.vec.Vec (alloc.vec.Vec sim.step.Ref)) (d : Usize),
      v.val.length - d.val = m → d.val ≤ v.val.length → ar.val.length ≤ d.val → sn.val.length ≤ d.val →
      ∃ ar' sn', sim.step.init_state_loop1 v ar sn d = ok (ar', sn') ∧
        ar'.val.map (·.val) = ar.val.map (·.val) ++ (simAdL (v.val.drop d.val)).map (fun ir => List.replicate 8 ir) ∧
        sn'.val.map (·.val) = sn.val.map (·.val) ++ (simAdL (v.val.drop d.val)).map (fun _ => []) := by
  intro m
  induction m with
  | zero =>
    intro ar sn d hm hd har has
    have hdn : v.val.drop d.val = [] := List.drop_of_length_le (by omega)
    refine ⟨ar, sn, ?_, by simp [hdn, simAdL], by simp [hdn, simAdL]⟩
    unfold sim.step.init_state_loop1; rw [loop_unfold]
    have : ¬ (d < alloc.vec.Vec.len v) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.init_state_loop1.body, this]
  | succ m ih =>
    intro ar sn d hm hd har has
    have hlt : d.val < v.val.length := by omega
    have hlt' : d < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
    have hmax := v.property
    obtain ⟨d1, hd1, ed1⟩ := usize_add_one d (by omega)
    rw [List.drop_eq_getElem_cons hlt]
    cases hx : v.val[d.val]'hlt with
    | TimeRamp a b c e =>
      obtain ⟨ar', sn', hw, e1, e2⟩ := ih ar sn d1 (by omega) (by omega) (by omega) (by omega)
      refine ⟨ar', sn', ?_, by rw [e1, ed1]; simp [simAdL], by rw [e2, ed1]; simp [simAdL]⟩
      unfold sim.step.init_state_loop1; rw [loop_unfold]; dsimp only
      rw [show sim.step.init_state_loop1.body v ar sn d = ok (.cont (ar, sn, d1)) by
        simp [sim.step.init_state_loop1.body, hlt', vec_index_usize_ok _ _ hlt, hx, hd1]]
      simp only [bind_ok]
      unfold sim.step.init_state_loop1 at hw; exact hw
    | Adaptive ir =>
      obtain ⟨rec, hrec, erec⟩ := sim_rec8_loop ir _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
      have hpl1 : ar.val.length < Usize.max := by omega
      have hpl2 : sn.val.length < Usize.max := by omega
      obtain ⟨ar', sn', hw, e1, e2⟩ := ih (vpush ar rec hpl1) (vpush sn (alloc.vec.Vec.new _) hpl2) d1 (by omega)
        (by omega) (by simp; omega) (by simp; omega)
      refine ⟨ar', sn', ?_, by rw [e1, ed1]; simp [simAdL, erec], by rw [e2, ed1]; simp [simAdL, alloc.vec.Vec.new]⟩
      unfold sim.step.init_state_loop1; rw [loop_unfold]; dsimp only
      rw [show sim.step.init_state_loop1.body v ar sn d = ok (.cont (vpush ar rec hpl1, vpush sn (alloc.vec.Vec.new _) hpl2, d1)) by
        simp [sim.step.init_state_loop1.body, hlt', vec_index_usize_ok _ _ hlt, hx, hrec, vec_push_ok _ _ hpl1,
          vec_push_ok _ _ hpl2, hd1]]
      simp only [bind_ok]
      unfold sim.step.init_state_loop1 at hw; exact hw

theorem sim_block_loop (v : alloc.vec.Vec Bool) :
    ∀ m (bl : alloc.vec.Vec (Option replay.frames.Action)) (bi : alloc.vec.Vec Usize) (b : Usize),
      v.val.length - b.val = m → b.val ≤ v.val.length → bl.val = List.replicate b.val none →
      bi.val.map (·.val) = List.replicate b.val 0 →
      ∃ bl' bi', sim.step.init_state_loop2 v bl bi b = ok (bl', bi') ∧
        bl'.val = List.replicate v.val.length none ∧ bi'.val.map (·.val) = List.replicate v.val.length 0 := by
  intro m
  induction m with
  | zero =>
    intro bl bi b hm hb hbl hbi
    refine ⟨bl, bi, ?_, by rw [hbl]; congr 1; omega, by rw [hbi]; congr 1; omega⟩
    unfold sim.step.init_state_loop2; rw [loop_unfold]
    have : ¬ (b < alloc.vec.Vec.len v) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.init_state_loop2.body, this]
  | succ m ih =>
    intro bl bi b hm hb hbl hbi
    have hlt : b.val < v.val.length := by omega
    have hlt' : b < alloc.vec.Vec.len v := by rw [vec_lt_len_iff]; exact hlt
    have hmax := v.property
    obtain ⟨b1, hb1, eb1⟩ := usize_add_one b (by omega)
    have hl2 : bi.val.length = b.val := by have := congrArg List.length hbi; simpa using this
    have hpl1 : bl.val.length < Usize.max := by rw [hbl]; simp; omega
    have hpl2 : bi.val.length < Usize.max := by omega
    obtain ⟨bl', bi', hw, e1, e2⟩ := ih (vpush bl none hpl1) (vpush bi 0#usize hpl2) b1 (by omega) (by omega)
      (by simp [hbl, eb1, List.replicate_succ']) (by simp [hbi, eb1, List.replicate_succ'])
    refine ⟨bl', bi', ?_, e1, e2⟩
    unfold sim.step.init_state_loop2; rw [loop_unfold]; dsimp only
    rw [show sim.step.init_state_loop2.body v bl bi b = ok (.cont (vpush bl none hpl1, vpush bi 0#usize hpl2, b1)) by
      simp [sim.step.init_state_loop2.body, hlt', vec_push_ok _ _ hpl1, vec_push_ok _ _ hpl2, hb1]]
    simp only [bind_ok]
    unfold sim.step.init_state_loop2 at hw; exact hw

def simOS0 (o : sim.playable.TopObj) : OsuModel.Sim.OState :=
  { lifetimeStart := o.h.start - o.h.preempt
    lifetimeEnd := o.h.end_time + (match o.h.hit_windows with | some hw => hw.miss | none => 0)
    nested := (List.replicate o.nested.val.length none).toArray }

theorem sim_objs_loop (pb : sim.playable.Playable) :
    ∀ m (objs : alloc.vec.Vec sim.state.OState) (i : Usize), pb.objects.val.length - i.val = m →
      i.val ≤ pb.objects.val.length → objs.val.length ≤ i.val →
      ∃ w, sim.step.init_state_loop0 pb objs i = ok w ∧
        w.val.map (fun o => (abs o : OsuModel.Sim.OState)) = objs.val.map (fun o => (abs o : OsuModel.Sim.OState)) ++
          (pb.objects.val.drop i.val).map simOS0 := by
  intro m
  induction m with
  | zero =>
    intro objs i hm hi ho
    have hdn : pb.objects.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨objs, ?_, by simp [hdn]⟩
    unfold sim.step.init_state_loop0; rw [loop_unfold]
    have : ¬ (i < alloc.vec.Vec.len pb.objects) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.init_state_loop0.body, this]
  | succ m ih =>
    intro objs i hm hi ho
    have hlt : i.val < pb.objects.val.length := by omega
    have hlt' : i < alloc.vec.Vec.len pb.objects := by rw [vec_lt_len_iff]; exact hlt
    have hmax := pb.objects.property
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i (by omega)
    set o := pb.objects.val[i.val]'hlt with ho'
    let miss : F64 := match o.h.hit_windows with | some hw => hw.miss | none => 0
    obtain ⟨os, hos, eos⟩ := sim.state.ostate_init_refines (o.h.start - o.h.preempt) (o.h.end_time + miss)
      (alloc.vec.Vec.len o.nested)
    have hpl : objs.val.length < Usize.max := by omega
    obtain ⟨w, hw, ew⟩ := ih (vpush objs os hpl) i1 (by omega) (by omega) (by simp; omega)
    refine ⟨w, ?_, ?_⟩
    · unfold sim.step.init_state_loop0; rw [loop_unfold]; dsimp only
      rw [show sim.step.init_state_loop0.body pb objs i = ok (.cont (vpush objs os hpl, i1)) by
        have hos' := hos
        cases hhw : o.h.hit_windows <;> simp only [miss, hhw] at hos' <;>
          simp [sim.step.init_state_loop0.body, hlt', vec_index_eq _ _ hlt, ← ho', hhw, sim_step_F64_0,
            float.F64.sub, float.F64.add, hos', vec_push_ok _ _ hpl, hi1]]
      simp only [bind_ok]
      unfold sim.step.init_state_loop0 at hw; exact hw
    · rw [ew, ei1, List.drop_eq_getElem_cons hlt, ← ho']
      simp only [vpush_val, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      rw [← eos]
      rfl

theorem sim.step.init_state_refines (tn) (cfg : sim.mods.Config) (pb : sim.playable.Playable) (w : I64) :
    ∃ R, sim.step.init_state cfg pb w = ok R ∧
      simRel (simStS tn) R (OsuModel.Sim.initState (abs cfg) (playableS tn pb) w.val) := by
  have hAd : ∀ f : OsuModel.Sim.DynRate → Option F64,
      (∀ d : sim.mods.DynRate, f (abs d) = (match d with | .Adaptive ir => some ir | _ => none)) →
      Array.filterMap f (abs cfg : OsuModel.Sim.Config).dynRates = (simAdL cfg.dyn_rates.val).toArray := by
    intro f hf
    simp only [abs, configS, simAdL, List.filterMap_toArray, List.filterMap_map, Function.comp_def]
    congr 1; congr 1; funext d; exact hf d
  have hObjs : ∀ g : OsuModel.Sim.TopObj → OsuModel.Sim.OState, (∀ o, g (topS tn o) = simOS0 o) →
      Array.map g (playableS tn pb).objects = (pb.objects.val.map simOS0).toArray := by
    intro g hg
    simp only [playableS, List.map_toArray, List.map_map, Function.comp_def, hg]
  unfold OsuModel.Sim.initState
  dsimp only
  rw [hAd _ (by intro d; cases d <;> rfl)]
  rw [hObjs _ (by
    intro o; simp only [simOS0, topS, hobjS]
    cases o.h.hit_windows <;> (simp only [Option.map_none, Option.map_some]; congr 1 <;>
      first | rfl | (apply Array.toList_inj.mp; simp [Function.comp_def])))]
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  have hdr : (abs cfg : OsuModel.Sim.Config).dynRates.toList = cfg.dyn_rates.val.map abs := by simp [abs, configS]
  rw [hdr, List.toList_toArray]
  have hsimp : (fun i => (OsuModel.Sim.DynRate.adaptive i).setSpeed 1 i) = simSetSp := rfl
  rw [hsimp]
  obtain ⟨R1, hR1, eR1⟩ := sim_as_init_loop cfg _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.nil_append] at eR1
  obtain ⟨R2, hR2, eR2⟩ := sim_init_speeds_loop cfg _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.nil_append] at eR2
  obtain ⟨objs, hobjs, eobjs⟩ := sim_objs_loop pb _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.map_nil,
    List.nil_append] at eobjs
  obtain ⟨rk, hrk, erk⟩ := sim.scoring.adjust_rank_refines cfg.rank_adjust .X
  obtain ⟨hs0, hhs0, ehs0⟩ := sim.scoring.health_st_init_refines cfg.easy_retries
  have hAI : sim.step.as_init cfg = ok R1 := hR1
  have hIS : sim.step.initial_speeds cfg = ok R2 := hR2
  cases R1 with
  | Err e =>
    obtain ⟨m, hm⟩ := eR1
    refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
    · unfold sim.step.init_state
      simp [sim_score_init, sim_clone_vec_u64, hobjs, hAI, hrk, hhs0, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.From.from]
    · simp only [Functor.map] at hm ⊢
      cases hq : List.mapM simSetSp (simAdL cfg.dyn_rates.val) <;> rw [hq] at hm <;>
        simp_all [OsuModel.Sim.netStr, Except.map, Bind.bind, Except.bind]
  | Ok asv =>
    cases R2 with
    | Err e =>
      obtain ⟨m, hm⟩ := eR2
      refine ⟨.Err e, ?_, ⟨m, ?_⟩⟩
      · unfold sim.step.init_state
        simp [sim_score_init, sim_clone_vec_u64, hobjs, hAI, hrk, hhs0, hIS, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.From.from]
      · simp only [simRel] at eR1
        simp only [Functor.map] at hm eR1 ⊢
        cases hq : List.mapM simSetSp (simAdL cfg.dyn_rates.val) <;> rw [hq] at eR1 <;>
          cases hq2 : List.mapM (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed) (List.map abs cfg.dyn_rates.val) <;>
          rw [hq2] at hm <;> simp_all [OsuModel.Sim.netStr, Except.map, Bind.bind, Except.bind]
    | Ok spv =>
      obtain ⟨ar, sn, hl1, e1, e2⟩ := sim_as_recent_loop cfg.dyn_rates _ (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
        0#usize rfl (by simp) (by simp) (by simp)
      obtain ⟨bl, bi, hl2, e3, e4⟩ := sim_block_loop cfg.input_blockers _ (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
        0#usize rfl (by simp) (by simp) (by simp)
      obtain ⟨pools, hpo, epo⟩ := sim.step.initial_pools_refines
      refine ⟨?R, ?h1, ?h2⟩
      case h1 =>
        unfold sim.step.init_state
        simp [sim_score_init, sim_clone_vec_u64, hobjs, hAI, hIS, hrk, hhs0, hl1, hl2, hpo,
          core.result.Result.Insts.CoreOpsTry.branch, sim_step_F64_0, sim_step_F64_1, sim_basic_F32_0]
        rfl
      case h2 =>
        simp only [simRel] at eR1 eR2 ⊢
        have hq1 : List.mapM simSetSp (simAdL cfg.dyn_rates.val) = .ok asv.val := by
          cases hq : List.mapM simSetSp (simAdL cfg.dyn_rates.val) <;> rw [hq] at eR1 <;>
            simp_all [OsuModel.Sim.netStr, Except.map]
        have hq2 : List.mapM (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed) (List.map abs cfg.dyn_rates.val) = .ok spv.val := by
          cases hq : List.mapM (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed) (List.map abs cfg.dyn_rates.val) <;>
            rw [hq] at eR2 <;> simp_all [OsuModel.Sim.netStr, Except.map]
        rw [hq1, hq2]
        simp only [Functor.map, Except.map, OsuModel.Sim.netStr, Bind.bind, Except.bind, Pure.pure, Except.pure]
        simp only [simStS, Except.ok.injEq, Prod.mk.injEq, true_and, and_true]
        have hsc : (abs ({ simScoreInit with rank := rk, total_score_without_mods := w } : sim.scoring.ScoreSt) :
            OsuModel.Sim.ScoreSt) =
            { (abs simScoreInit : OsuModel.Sim.ScoreSt) with rank := rankS rk, totalScoreWithoutMods := w.val } := by
          simp only [abs, scoreS]
        rw [sim_score_init_abs] at hsc
        simp only [abs, id] at erk
        have hscore : ({ rank := OsuModel.Sim.adjustRank cfg.rank_adjust .x, totalScoreWithoutMods := w.val } :
            OsuModel.Sim.ScoreSt) =
            abs ({ simScoreInit with rank := rk, total_score_without_mods := w } : sim.scoring.ScoreSt) := by
          rw [hsc]; dsimp only; rw [← erk]; rfl
        have hV : OsuModel.Sim.Vec2.zero = abs ({ x := 0, y := 0 } : sim.basic.Vec2) := rfl
        have e1' := e1
        simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.map_nil,
          List.nil_append] at e1'
        have e2' := e2
        simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.map_nil,
          List.nil_append] at e2'
        have hAR : Array.map (fun i => Array.replicate 8 i) (simAdL cfg.dyn_rates.val).toArray = abs ar := by
          apply Array.toList_inj.mp
          have : ar.val.map (fun v => (abs v : _root_.Array F64)) = (ar.val.map (·.val)).map List.toArray := by
            simp [abs, Function.comp_def]
          simp only [abs] at this ⊢
          rw [List.toList_toArray, this, e1']; simp [Function.comp_def]; intro a _; rfl
        have hSNg : Array.map (fun _ => ([] : List (Nat × Int))) (simAdL cfg.dyn_rates.val).toArray =
            (sn.val.map (fun l => (l.val.map (fun r => (abs r : Nat × Int))).reverse)).toArray := by
          apply Array.toList_inj.mp
          have : sn.val.map (fun l => (l.val.map (fun r => (abs r : Nat × Int))).reverse) =
              (sn.val.map (·.val)).map (fun l => (l.map (fun r => (abs r : Nat × Int))).reverse) := by
            simp [Function.comp_def]
          rw [List.toList_toArray, this, e2']; simp [Function.comp_def]
        have hBL : Array.map (fun _ => (none : Option OsuModel.Replay.Action)) (abs cfg : OsuModel.Sim.Config).inputBlockers =
            (bl.val.map (fun x => Option.map actS x)).toArray := by
          apply Array.toList_inj.mp
          simp [abs, configS, e3, List.map_const']
        have hBI : Array.map (fun _ => (0 : Nat)) (abs cfg : OsuModel.Sim.Config).inputBlockers = abs bi := by
          apply Array.toList_inj.mp
          have : (abs bi : _root_.Array Nat).toList = bi.val.map (·.val) := by simp [abs]
          rw [this, e4]; simp [abs, configS, List.map_const']
        have hPO : Array.map (fun n => List.replicate n (none : Option Nat)) OsuModel.Sim.poolInitial =
            (pools.val.map (fun l => (l.val.map (fun x => Option.map (fun x => x.val) x)).reverse)).toArray := by
          apply Array.toList_inj.mp
          have : pools.val.map (fun l => (l.val.map (fun x => Option.map (fun x => x.val) x)).reverse) =
              (pools.val.map (·.val)).map (fun l => (l.map (fun x => Option.map (fun x => x.val) x)).reverse) := by
            simp [Function.comp_def]
          rw [List.toList_toArray, this, epo]; simp [Function.comp_def, List.map_replicate]
        have hOB : (pb.objects.val.map simOS0).toArray = abs objs := by
          have : (abs objs : _root_.Array OsuModel.Sim.OState) = (objs.val.map (fun o => (abs o : OsuModel.Sim.OState))).toArray := rfl
          rw [this, eobjs]; simp [alloc.vec.Vec.new]
        simp only [OsuModel.Sim.St.mk.injEq]
        repeat' apply And.intro
        all_goals (try with_reducible rfl)
        all_goals (try (simp only [abs, alloc.vec.Vec.new, List.map_nil, List.reverse_nil, Option.map_none]; done))
        all_goals first
          | (simp; done)
          | (simp [abs, alloc.vec.Vec.new]; done)
          | (simp [actListS, s2_empty_val.2]; done)
          | exact hscore
          | exact ehs0
          | exact hV
          | exact hAR
          | exact hSNg
          | exact hBL
          | exact hBI
          | exact hPO
          | exact hOB
end OsuProofs
