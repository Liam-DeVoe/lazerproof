/-
Sim3c part 4: small `sim::step` helpers without an owner (infra RECON 2026-10-22 20:55): `first_idx_of_kind`,
`last_idx_of_kind`, `first_head`, `part_present`, `receptor_ref`, ...
-/
import OsuProofs.Sim3.SC_Upd
import OsuProofs.Sim.IdxKind
import OsuProofs.Sim.InitState
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

/-! ## nested kind searches -/
theorem s3c_kinds_topS (tn) (o : sim.playable.TopObj) :
    (topS tn o).nested.toList.map (·.kind) = simKinds o := by simp [topS, hobjS, simKinds]

/-- `List.findIdx?` over the nested kinds (the spec's `idxOf … false` of `mkCtx`) -/
theorem sim.step.first_idx_of_kind_refines (tn) (o : sim.playable.TopObj) (k : sim.playable.Kind) :
    ∃ r, sim.step.first_idx_of_kind o k = ok r ∧
      r.map (·.val) = ((topS tn o).nested.toList.map (·.kind)).findIdx? (· == kindS k) := by
  obtain ⟨r, hr, er⟩ := sim_first_idx_loop o k _ 0#usize rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Nat.add_zero, Option.map_id'] at er
  exact ⟨r, hr, by rw [er, s3c_kinds_topS]⟩

/-- `simLastFrom` over the nested kinds (the spec's `idxOf … true` of `mkCtx`) -/
theorem sim.step.last_idx_of_kind_refines (tn) (o : sim.playable.TopObj) (k : sim.playable.Kind) :
    ∃ r, sim.step.last_idx_of_kind o k = ok r ∧
      r.map (·.val) = simLastFrom (kindS k) ((topS tn o).nested.toList.map (·.kind)) 0 none := by
  obtain ⟨r, hr, er⟩ := sim_last_idx_loop o k _ none 0#usize rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Option.map_none] at er
  exact ⟨r, hr, by rw [er, s3c_kinds_topS]⟩

theorem s3c_first_head_loop (o : sim.playable.TopObj) :
    ∀ n (j : Usize), o.nested.val.length - j.val = n → j.val ≤ o.nested.val.length →
      ∃ r', sim.step.first_head_loop o j none = ok r' ∧
        r'.map (·.val) = (((simKinds o).drop j.val).findIdx? (· == .head)).map (· + j.val) := by
  intro n
  induction n with
  | zero =>
    intro j hn hj
    have hdn : (simKinds o).drop j.val = [] := List.drop_of_length_le (by simp [simKinds]; omega)
    refine ⟨none, ?_, by simp [hdn]⟩
    unfold sim.step.first_head_loop; rw [loop_unfold]
    have : ¬ (j < alloc.vec.Vec.len o.nested) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.first_head_loop.body, this]
  | succ n ih =>
    intro j hn hj
    have hlt : j.val < o.nested.val.length := by omega
    have hlt' : j < alloc.vec.Vec.len o.nested := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨j1, hj1, ej1⟩ := usize_add_one j (by have := o.nested.property; omega)
    have hd : (simKinds o).drop j.val = kindS (o.nested.val[j.val]'hlt).kind :: (simKinds o).drop (j.val + 1) := by
      simp only [simKinds]; rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hd, List.findIdx?_cons]
    have hh : kindS sim.playable.Kind.Head = OsuModel.Sim.Kind.head := rfl
    by_cases hc : (kindS (o.nested.val[j.val]'hlt).kind == kindS .Head) = true
    · refine ⟨some j, ?_, by rw [hh] at hc; simp [hc]⟩
      unfold sim.step.first_head_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.first_head_loop.body o j none = ok (.cont (j1, some j)) by
        simp [sim.step.first_head_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt, hc, hj1]]
      simp only [bind_ok]; rw [loop_unfold]
      by_cases h2 : j1 < alloc.vec.Vec.len o.nested <;>
        simp [sim.step.first_head_loop.body, h2, core.option.Option.is_none]
    · obtain ⟨r', hr', er'⟩ := ih j1 (by omega) (by omega)
      refine ⟨r', ?_, ?_⟩
      · unfold sim.step.first_head_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.first_head_loop.body o j none = ok (.cont (j1, none)) by
          simp [sim.step.first_head_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt,
            hc, hj1]]
        simp only [bind_ok]
        unfold sim.step.first_head_loop at hr'; exact hr'
      · rw [hh] at hc
        rw [er', ej1]; simp only [hc, Bool.false_eq_true, if_false, Option.map_map]
        congr 1; funext x; simp; omega

/-- index of the first nested slider head (`findIdx?` over the nested kinds) -/
theorem sim.step.first_head_refines (tn) (o : sim.playable.TopObj) :
    ∃ r, sim.step.first_head o = ok r ∧
      r.map (·.val) = ((topS tn o).nested.toList.map (·.kind)).findIdx? (· == .head) := by
  obtain ⟨r, hr, er⟩ := s3c_first_head_loop o _ 0#usize rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Nat.add_zero, Option.map_id'] at er
  exact ⟨r, hr, by rw [er, s3c_kinds_topS]⟩

/-! ## `partPresent` -/
theorem sim.step.part_present_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part)
    (hi : i.val < s.objs.val.length) (hio : i.val < c.pb.objects.val.length)
    (hk : ∀ k, sim.step.part_inst s i p = ok k → k.val < s.insts.val.length)
    (hhd : p = .Head → ∃ hhi : i.val < c.head_idx.val.length,
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hio).nested.val.length) :
    ∃ b, sim.step.part_present c s i p = ok b ∧
      OsuModel.Sim.Sim.partPresent i.val (abs p) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
  obtain ⟨k, hk1, ek⟩ := sim.step.part_inst_refines tn fo c s i p hi
  obtain ⟨a, ha1, ea⟩ := sim.step.part_armed_refines tn fo c s i p hi
  have hkl := hk k hk1
  have hi' : i.val < (simStS tn s).objs.size := by simpa using hi
  have eos := simS_ostate (simCtxS tn fo c) (simStS tn s) i.val hi'
  have ein := s3a_instOf tn fo c s k.val hkl
  have hdbg : (simCtxS tn fo c).cfg.dbgNoPresence = false := rfl
  cases p
  · obtain ⟨b, hb, eb⟩ := sim.step.present_tf_refines (s.insts.val[k.val]'hkl).tf a s.t (s.objs.val[i.val]'hi).lifetime_start
    refine ⟨b, ?_, ?_⟩
    · simp [sim.step.part_present, hk1, sim.step.Part.read_discriminant, vec_index_eq _ _ hi, vec_index_eq _ _ hkl, vec_index_usize_ok _ _ hkl, ha1, hb]
    · unfold OsuModel.Sim.Sim.partPresent
      simp only [show (abs sim.step.Part.Top : OsuModel.Sim.Sim.Part) = .top from rfl] at ek ea
      simp only [simM_bind, eos, s3b_ebok, ek, ein, ea, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_read, simM_get,
        simM_pure, hdbg, Bool.false_or, show (abs sim.step.Part.Top : OsuModel.Sim.Sim.Part) = .top from rfl,
        sim_part_beq_tt, if_true]
      rw [sim_stS_obj]
      exact congrArg (fun x => Except.ok (x, simStS tn s)) eb
  · obtain ⟨hhi, hhb⟩ := hhd rfl
    have hhd := hhb
    let hd := (c.pb.objects.val[i.val]'hio).nested.val[(c.head_idx.val[i.val]'hhi).val]'hhb
    obtain ⟨b, hb, eb⟩ := sim.step.present_tf_refines (s.insts.val[k.val]'hkl).tf a s.t (hd.start - hd.preempt)
    refine ⟨b, ?_, ?_⟩
    · simp [sim.step.part_present, hk1, sim.step.Part.read_discriminant, vec_index_eq _ _ hio, vec_index_eq _ _ hhi,
        vec_index_eq _ _ hhb, vec_index_eq _ _ hkl, vec_index_usize_ok _ _ hkl,
        vec_index_usize_ok _ _ hhb, ha1, hb, float.F64.sub, hd]
    · have ehead : OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) (simStS tn s) =
          .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn s) := by
        have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
        simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]
      have enes : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hio)) (c.head_idx.val[i.val]'hhi).val
          (simCtxS tn fo c) (simStS tn s) = .ok (hobjS tn hd, simStS tn s) := by
        have hh' : (c.head_idx.val[i.val]'hhi).val < (topS tn (c.pb.objects.val[i.val]'hio)).nested.size := by
          simpa [topS] using hhb
        simp only [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, dif_pos hh', simM_pure]; simp [topS, hd]
      unfold OsuModel.Sim.Sim.partPresent
      simp only [show (abs sim.step.Part.Head : OsuModel.Sim.Sim.Part) = .head from rfl] at ek ea
      simp only [simM_bind, eos, s3b_ebok, ek, ein, ea, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_read, simM_get,
        simM_pure, hdbg, Bool.false_or, show (abs sim.step.Part.Head : OsuModel.Sim.Sim.Part) = .head from rfl,
        sim_part_beq_ht, Bool.false_eq_true, if_false, s3b_topObj tn fo c _ _ hio, ehead, enes]
      exact congrArg (fun x => Except.ok (x, simStS tn s)) eb

/-! ## `receptor_ref` -/
/-- the spec's receptor reference of `propagatePress` (Step.lean, verbatim) -/
def s3c_recRefS (o : OsuModel.Sim.TopObj) (os : OsuModel.Sim.OState) (i : Nat) : OsuModel.Sim.SimM (Option OsuModel.Sim.Ref) :=
  match o.h.kind with
  | .circle => pure (some (i, -1))
  | .slider => if os.headAlive then do pure (some (i, ((← OsuModel.Sim.Sim.headIdxOf i) : Int))) else pure none
  | _ => pure none

theorem sim.step.receptor_ref_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < s.objs.val.length) (hio : i.val < c.pb.objects.val.length)
    (hhd : (c.pb.objects.val[i.val]'hio).h.kind = .Slider → ∃ hhi : i.val < c.head_idx.val.length,
      (c.head_idx.val[i.val]'hhi).val < 2 ^ 63) :
    ∃ r, sim.step.receptor_ref c s i = ok r ∧
      s3c_recRefS (topS tn (c.pb.objects.val[i.val]'hio)) (ostateS (s.objs.val[i.val]'hi)) i.val (simCtxS tn fo c)
        (simStS tn s) = .ok (r.map abs, simStS tn s) := by
  unfold sim.step.receptor_ref s3c_recRefS
  simp only [vec_index_eq _ _ hio]
  have hk : (topS tn (c.pb.objects.val[i.val]'hio)).h.kind = kindS (c.pb.objects.val[i.val]'hio).h.kind := rfl
  rw [hk]
  cases hK : (c.pb.objects.val[i.val]'hio).h.kind
  case Slider =>
    obtain ⟨hhi, hhb⟩ := hhd hK
    have hc : (UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)).val = ((c.head_idx.val[i.val]'hhi).val : Int) := by
      rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
    have ehead : OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((c.head_idx.val[i.val]'hhi).val, simStS tn s) := by
      have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
      simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]
    by_cases ha : (s.objs.val[i.val]'hi).head_alive = true
    · refine ⟨some ⟨i, UScalar.hcast .I64 (c.head_idx.val[i.val]'hhi)⟩, ?_, ?_⟩
      · simp [hK, vec_index_eq _ _ hi, ha, vec_index_eq _ _ hhi, lift]
      · simp [kindS, ostateS, ha, simM_bind, ehead, abs, hc]
    · refine ⟨none, ?_, ?_⟩
      · simp [hK, vec_index_eq _ _ hi, ha]
      · simp [kindS, ostateS, ha]
  case Circle => exact ⟨some ⟨i, (-1)#i64⟩, by simp [hK], by simp [kindS, abs]⟩
  all_goals exact ⟨none, by simp [hK], rfl⟩

/-! ## `liftNet`, `initState` helpers -/
theorem sim.err.lift_net_refines {α β : Type} (f : α → β) (x : Except NetExn α) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) :
    ∃ r, sim.err.lift_net (exceptI f x) = ok r ∧
      simRel id r ((OsuModel.Sim.Sim.liftNet x C S).map (fun p => f p.1)) ∧ ∀ a, x = .ok a → OsuModel.Sim.Sim.liftNet x C S = .ok (a, S) := by
  cases x with
  | ok a => exact ⟨.Ok (f a), rfl, rfl, fun a' h => (by cases h; rfl)⟩
  | error e => exact ⟨.Err (.Net (exnI e)), rfl, ⟨_, rfl⟩, fun a' h => by cases h⟩

/-- `asInit` of `initState` (`adaptive.mapM (setSpeed (.adaptive i) 1 i)`, `simAdL` = the AS initial rates) -/
theorem sim.step.as_init_refines (cfg : sim.mods.Config) :
    ∃ R, sim.step.as_init cfg = ok R ∧
      simRel (fun v : alloc.vec.Vec F64 => v.val) R (OsuModel.Sim.netStr ((simAdL cfg.dyn_rates.val).mapM simSetSp)) := by
  obtain ⟨R1, hR1, eR1⟩ := sim_as_init_loop cfg _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.nil_append] at eR1
  refine ⟨R1, hR1, ?_⟩
  cases h : (simAdL cfg.dyn_rates.val).mapM simSetSp <;> rw [h] at eR1 <;> exact eR1

/-- one AS entry of `as_init` -/
theorem sim.step.as_init_one_refines (dr : sim.mods.DynRate) :
    ∃ r, sim.step.as_init_one dr = ok r ∧
      (∀ ir, dr = .Adaptive ir → simRel id r (OsuModel.Sim.netStr ((simSetSp ir).map some))) ∧
      (∀ a b c e, dr = .TimeRamp a b c e → r = .Ok none) := by
  cases dr with
  | TimeRamp a b c e => exact ⟨.Ok none, by simp [sim.step.as_init_one], fun _ h => (by cases h), fun _ _ _ _ _ => rfl⟩
  | Adaptive ir =>
    have hss := sim.mods.dyn_rate_set_speed_refines (.Adaptive ir) 1 ir
    cases hsp : simSetSp ir with
    | error x =>
      have hsp' : (OsuModel.Sim.DynRate.adaptive ir).setSpeed 1 ir = .error x := hsp
      refine ⟨.Err (.Net (exnI x)), ?_, fun _ h => ?_, fun _ _ _ _ h => by cases h⟩
      · simp [sim.step.as_init_one, sim_step_F64_1,
          hss, show (abs (sim.mods.DynRate.Adaptive ir) : OsuModel.Sim.DynRate).setSpeed 1 ir = simSetSp ir from rfl, hsp,
          exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.From.from, hsp']
      · cases h; exact ⟨_, by simp [hsp, OsuModel.Sim.netStr, Except.map]; rfl⟩
    | ok y =>
      have hsp' : (OsuModel.Sim.DynRate.adaptive ir).setSpeed 1 ir = .ok y := hsp
      refine ⟨.Ok (some y), ?_, fun _ h => ?_, fun _ _ _ _ h => by cases h⟩
      · simp [sim.step.as_init_one, sim_step_F64_1,
          hss, show (abs (sim.mods.DynRate.Adaptive ir) : OsuModel.Sim.DynRate).setSpeed 1 ir = simSetSp ir from rfl,
          hsp, exceptI, sim.err.lift_net, core.result.Result.Insts.CoreOpsTry.branch, hsp']
      · cases h; simp [simRel, hsp, OsuModel.Sim.netStr, Except.map]

/-- `speed` of `initState` (`cfg.dynRates.mapM (·.initialSpeed)`) -/
theorem sim.step.initial_speeds_refines (cfg : sim.mods.Config) :
    ∃ R, sim.step.initial_speeds cfg = ok R ∧
      simRel (fun v : alloc.vec.Vec F64 => v.val) R
        (OsuModel.Sim.netStr ((cfg.dyn_rates.val.map abs).mapM (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed))) := by
  obtain ⟨R2, hR2, eR2⟩ := sim_init_speeds_loop cfg _ (alloc.vec.Vec.new _) 0#usize rfl (by simp) (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, alloc.vec.Vec.new, List.nil_append] at eR2
  refine ⟨R2, hR2, ?_⟩
  cases h : (cfg.dyn_rates.val.map abs).mapM (fun (x : OsuModel.Sim.DynRate) => x.initialSpeed) <;> rw [h] at eR2 <;>
    exact eR2

/-! ## `classicHead` of `circleCheckForResult` -/
theorem sim.step.is_classic_head_refines (tn fo) (c : sim.state.Ctx) (i : Usize) (kind : sim.playable.Kind)
    (hi : i.val < c.pb.objects.val.length) :
    ∃ r, sim.step.is_classic_head c i kind = ok r ∧ ∀ S, s3aR id S r
      ((if kindS kind == .head then do pure (← OsuModel.Sim.Sim.sliderData i.val).classic else pure false :
        OsuModel.Sim.SimM Bool) (simCtxS tn fo c) S) := by
  by_cases hk : kind = .Head
  · subst hk
    obtain ⟨sr, hsr, esr⟩ := sim.step.slider_data_refines tn fo c i hi
    cases sr with
    | Err er =>
      refine ⟨.Err er, ?_, fun S => ?_⟩
      · simp (config := {decide := true}) [sim.step.is_classic_head, hsr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          core.convert.From.from, kindS]
      · obtain ⟨m, hm⟩ := esr S
        refine ⟨m, ?_⟩
        simp only [show (kindS sim.playable.Kind.Head == OsuModel.Sim.Kind.head) = true from rfl, if_true, simM_bind, hm]
        rfl
    | Ok sd =>
      refine ⟨.Ok sd.classic, ?_, fun S => ?_⟩
      · simp (config := {decide := true}) [sim.step.is_classic_head, hsr, core.result.Result.Insts.CoreOpsTry.branch, kindS]
      · have h1 := esr S
        simp only [s3aR] at h1
        simp only [show (kindS sim.playable.Kind.Head == OsuModel.Sim.Kind.head) = true from rfl, if_true, simM_bind, h1]
        rfl
  · have hks : (kindS kind == OsuModel.Sim.Kind.head) = false := by
      cases kind <;> simp_all (config := {decide := true}) [kindS]
    have hkr : (kindS kind == kindS .Head) = false := hks
    refine ⟨.Ok false, ?_, fun S => ?_⟩
    · simp [sim.step.is_classic_head, hkr]
    · simp only [hks, Bool.false_eq_true, if_false, simM_pure]; rfl

/-! ## `vEq` of `applyBindings` -/
/-- the spec's local `vEq` of `applyBindings` (Step.lean, verbatim) -/
def s3c_vEq (a b : OsuModel.Sim.Vec2) : Bool :=
  (a.x == b.x || (a.x.isNaN && b.x.isNaN)) && (a.y == b.y || (a.y.isNaN && b.y.isNaN))

theorem sim.step.v_eq_bindable_refines (a b : sim.basic.Vec2) :
    sim.step.v_eq_bindable a b = ok (s3c_vEq (abs a) (abs b)) := by
  unfold sim.step.v_eq_bindable s3c_vEq
  by_cases h1 : (a.x == b.x) = true <;> by_cases h2 : (a.y == b.y) = true <;>
    by_cases h3 : a.x.isNaN = true <;> by_cases h4 : b.x.isNaN = true <;>
    by_cases h5 : a.y.isNaN = true <;> by_cases h6 : b.y.isNaN = true <;>
    simp_all [float.F32.eq, float.F32.is_nan, abs]

/-! ## `dictSlots.idxOf? (some i)` -/
theorem s3c_dict_slot_loop (s : sim.state.St) (i : Usize) :
    ∀ n (k : Usize), s.dict_slots.val.length - k.val = n → k.val ≤ s.dict_slots.val.length →
      ∃ r', sim.step.dict_slot_of_loop s i k none = ok r' ∧
        r'.map (·.val) = (((s.dict_slots.val.map (Option.map (·.val))).drop k.val).findIdx? (· == some i.val)).map (· + k.val) := by
  intro n
  induction n with
  | zero =>
    intro k hn hk
    have hdn : (s.dict_slots.val.map (Option.map (·.val))).drop k.val = [] := List.drop_of_length_le (by simp; omega)
    refine ⟨none, ?_, by simp [hdn]⟩
    unfold sim.step.dict_slot_of_loop; rw [loop_unfold]
    have : ¬ (k < alloc.vec.Vec.len s.dict_slots) := by rw [vec_lt_len_iff]; omega
    simp [sim.step.dict_slot_of_loop.body, this]
  | succ n ih =>
    intro k hn hk
    have hlt : k.val < s.dict_slots.val.length := by omega
    have hlt' : k < alloc.vec.Vec.len s.dict_slots := by rw [vec_lt_len_iff]; exact hlt
    obtain ⟨k1, hk1, ek1⟩ := usize_add_one k (by have := s.dict_slots.property; omega)
    have hd : (s.dict_slots.val.map (Option.map (·.val))).drop k.val =
        (s.dict_slots.val[k.val]'hlt).map (·.val) :: (s.dict_slots.val.map (Option.map (·.val))).drop (k.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hd, List.findIdx?_cons]
    have hc : ((s.dict_slots.val[k.val]'hlt).map (·.val) == some i.val) = true ↔ s.dict_slots.val[k.val]'hlt = some i := by
      cases (s.dict_slots.val[k.val]'hlt) with
      | none => simp
      | some x => simp; exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => by rw [h]⟩
    by_cases hc' : s.dict_slots.val[k.val]'hlt = some i
    · refine ⟨some k, ?_, by simp [hc.mpr hc']⟩
      unfold sim.step.dict_slot_of_loop; rw [loop_unfold]; dsimp only
      rw [show sim.step.dict_slot_of_loop.body s i k none = ok (.cont (k1, some k)) by
        simp [sim.step.dict_slot_of_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt, hc', hk1]]
      simp only [bind_ok]; rw [loop_unfold]
      by_cases h2 : k1 < alloc.vec.Vec.len s.dict_slots <;>
        simp [sim.step.dict_slot_of_loop.body, h2, core.option.Option.is_none]
    · have hcf : ((s.dict_slots.val[k.val]'hlt).map (·.val) == some i.val) = false := by
        cases h : ((s.dict_slots.val[k.val]'hlt).map (·.val) == some i.val)
        · rfl
        · exact absurd (hc.mp h) hc'
      obtain ⟨r', hr', er'⟩ := ih k1 (by omega) (by omega)
      refine ⟨r', ?_, ?_⟩
      · unfold sim.step.dict_slot_of_loop; rw [loop_unfold]; dsimp only
        rw [show sim.step.dict_slot_of_loop.body s i k none = ok (.cont (k1, none)) by
          cases hx : s.dict_slots.val[k.val]'hlt with
          | none => simp [sim.step.dict_slot_of_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt, hx, hk1]
          | some x =>
            have : x ≠ i := fun h => hc' (by rw [hx, h])
            simp [sim.step.dict_slot_of_loop.body, hlt', core.option.Option.is_none, vec_index_usize_ok _ _ hlt, hx, hk1, this]]
        simp only [bind_ok]
        unfold sim.step.dict_slot_of_loop at hr'; exact hr'
      · rw [er', ek1]; simp only [hcf, Bool.false_eq_true, if_false, Option.map_map]
        congr 1; funext x; simp; omega

theorem sim.step.dict_slot_of_refines (tn) (s : sim.state.St) (i : Usize) :
    ∃ r, sim.step.dict_slot_of s i = ok r ∧ r.map (·.val) = (simStS tn s).dictSlots.idxOf? (some i.val) := by
  obtain ⟨r, hr, er⟩ := s3c_dict_slot_loop s i _ 0#usize rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, Nat.add_zero, Option.map_id'] at er
  refine ⟨r, hr, ?_⟩
  rw [er]
  show _ = (s.dict_slots.val.map (fun o => (abs o : Option Nat))).toArray.idxOf? (some i.val)
  rw [List.idxOf?_toArray]; rfl

end OsuProofs
