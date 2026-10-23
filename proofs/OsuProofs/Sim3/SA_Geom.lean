/-
sim3a (D37): `sim::step` current-geometry accessors (Rust, read-only on `(c, s)`) refine the `SimM` accessors of
`OsuModel.Sim.Sim` (Step.lean): `br_scale`, `cur_hoc`, `cur_env_hoc` (= `(← curEnv).hoc`), `cur_circle_receptor`,
`cur_slider_geom`, `cur_spinner_geom`. Read-only: the spec state is returned unchanged (`objs`/`insts` untouched).
Geometry callees: Sim2/Geometry.lean (read-only reuse).
-/
import OsuProofs.Sim.Hit
import OsuProofs.Sim2.Geometry
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

theorem sim.step.br_scale_refines (env : sim.geometry.Env) :
    ∃ v, sim.step.br_scale env = ok v ∧ OsuModel.Sim.Sim.brScale (abs env) = abs v := by
  refine ⟨⟨F32.min env.hoc_size.x env.hoc_size.y / F32.max env.hoc_size.x env.hoc_size.y,
    F32.min env.hoc_size.x env.hoc_size.y / F32.max env.hoc_size.x env.hoc_size.y⟩, ?_, rfl⟩
  simp [sim.step.br_scale, sim.netx.f32_min_refines, sim.netx.f32_max_refines, float.F32.div]

@[simp] theorem s3a_br_scale_eq (env : sim.geometry.Env) :
    sim.step.br_scale env = ok (s2_v2R (OsuModel.Sim.Sim.brScale (abs env))) :=
  s2_eq_of_ex s2_v2R (fun _ => rfl) (sim.step.br_scale_refines env)

/-! projections of the context/state maps (kept small: never unfold `simCtxS`/`simStS` wholesale) -/
@[simp] theorem s3a_ctx_env (tn fo) (c : sim.state.Ctx) : (simCtxS tn fo c).env = abs c.env := rfl
@[simp] theorem s3a_ctx_br (tn fo) (c : sim.state.Ctx) : (simCtxS tn fo c).cfg.barrelRoll = c.cfg.barrel_roll := rfl
@[simp] theorem s3a_ctx_spunOut (tn fo) (c : sim.state.Ctx) : (simCtxS tn fo c).cfg.spunOut = c.cfg.spun_out := rfl
@[simp] theorem s3a_st_k (tn) (s : sim.state.St) : (simStS tn s).k = s.k.val := rfl
@[simp] theorem s3a_st_brRot (tn) (s : sim.state.St) : (simStS tn s).brRot = s.br_rot := rfl
@[simp] theorem s3a_st_t (tn) (s : sim.state.St) : (simStS tn s).t = s.t := rfl
@[simp] theorem s3a_st_mouse (tn) (s : sim.state.St) : (simStS tn s).mouse = abs s.mouse := rfl
@[simp] theorem s3a_env_hoc (e : sim.geometry.Env) : (abs e : OsuModel.Sim.Env).hoc = abs e.hoc := rfl
@[simp] theorem s3a_env_hocFirst (e : sim.geometry.Env) : (abs e : OsuModel.Sim.Env).hocFirst = abs e.hoc_first := rfl

theorem s3a_abs_deref {α β : Type} [AbsTo α β] (v : alloc.vec.Vec α) :
    (abs (alloc.vec.Vec.deref v) : _root_.Array β) = abs v := by simp [abs, alloc.vec.Vec.deref]

theorem sim.step.cur_hoc_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) :
    ∃ d, sim.step.cur_hoc c s = ok d ∧
      OsuModel.Sim.Sim.curHoc (simCtxS tn fo c) (simStS tn s) = .ok (abs d, simStS tn s) := by
  unfold sim.step.cur_hoc OsuModel.Sim.Sim.curHoc
  simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind, s3a_ctx_br]
  cases hb : c.cfg.barrel_roll with
  | none =>
    by_cases hk : s.k = 0#usize
    · have : s.k.val = 0 := by simp [hk]
      exact ⟨c.env.hoc_first, by simp [hk], by simp [this]⟩
    · have : s.k.val ≠ 0 := fun h => hk (UScalar.eq_of_val_eq (by simpa using h))
      exact ⟨c.env.hoc, by simp [hk], by simp [this]⟩
  | some br =>
    by_cases hk : s.k = 0#usize
    · have hk' : s.k.val = 0 := by simp [hk]
      obtain ⟨d, hd, ed⟩ := sim.geometry.compose_chain_refines (alloc.vec.Vec.deref c.env.chain_first)
        (some (s.br_rot, s2_v2R (OsuModel.Sim.Sim.brScale (abs c.env))))
      refine ⟨d, by simp [hk, hd], ?_⟩
      simp only [hk', s3a_st_k, s3a_st_brRot, s3a_ctx_env, beq_self_eq_true, if_true]
      rw [← ed, s3a_abs_deref]; rfl
    · have hk' : s.k.val ≠ 0 := fun h => hk (UScalar.eq_of_val_eq (by simpa using h))
      obtain ⟨d, hd, ed⟩ := sim.geometry.compose_chain_refines (alloc.vec.Vec.deref c.env.chain)
        (some (s.br_rot, s2_v2R (OsuModel.Sim.Sim.brScale (abs c.env))))
      refine ⟨d, by simp [hk, hd], ?_⟩
      have : (s.k.val == 0) = false := by simpa using hk'
      simp only [this, s3a_st_brRot, s3a_ctx_env, s3a_st_k, Bool.false_eq_true, if_false]
      rw [← ed, s3a_abs_deref]; rfl

theorem sim.step.cur_env_hoc_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) :
    ∃ d, sim.step.cur_env_hoc c s = ok d ∧
      OsuModel.Sim.Sim.curEnv (simCtxS tn fo c) (simStS tn s) = .ok ({ (abs c.env : OsuModel.Sim.Env) with hoc := abs d }, simStS tn s) := by
  unfold sim.step.cur_env_hoc OsuModel.Sim.Sim.curEnv
  simp only [OsuModel.Sim.Sim.ctx, simM_bind, simM_read, Except.bind]
  rcases Option.eq_none_or_eq_some c.cfg.barrel_roll with hb | ⟨br, hb⟩
  · have e : (simCtxS tn fo c).cfg.barrelRoll = none := by rw [s3a_ctx_br, hb]
    refine ⟨c.env.hoc, by simp only [hb], ?_⟩
    simp only [e, Option.isNone_none, if_true, simM_pure, s3a_ctx_env]; rfl
  · have e : (simCtxS tn fo c).cfg.barrelRoll = some br := by rw [s3a_ctx_br, hb]
    obtain ⟨d, hd, ed⟩ := sim.step.cur_hoc_refines tn fo c s
    refine ⟨d, by simp only [hb]; exact hd, ?_⟩
    simp only [e, Option.isNone_some, Bool.false_eq_true, if_false, simM_bind, ed, Except.bind, simM_pure, s3a_ctx_env]

/-! ## state/context reads -/
theorem s3a_ostate (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Nat) (h : i < s.objs.val.length) :
    OsuModel.Sim.Sim.ostate i (simCtxS tn fo c) (simStS tn s) = .ok (ostateS (s.objs.val[i]'h), simStS tn s) := by
  rw [simS_ostate _ _ _ (by simpa using h), sim_stS_obj]
theorem s3a_instOf (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (k : Nat) (h : k < s.insts.val.length) :
    OsuModel.Sim.Sim.instOf k (simCtxS tn fo c) (simStS tn s) = .ok (abs (s.insts.val[k]'h), simStS tn s) := by
  have h' : k < (simStS tn s).insts.size := by simpa [simStS, abs] using h
  simp [OsuModel.Sim.Sim.instOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.st, h', Except.bind]
  simp [simStS, abs]
theorem s3a_topObj (tn fo) (c : sim.state.Ctx) (S : OsuModel.Sim.St) (i : Nat) (h : i < c.pb.objects.val.length) :
    OsuModel.Sim.Sim.topObj i (simCtxS tn fo c) S = .ok (topS tn (c.pb.objects.val[i]'h), S) := by
  have h' : i < (simCtxS tn fo c).pb.objects.size := by simpa using h
  simp only [OsuModel.Sim.Sim.topObj, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, simM_bind, simM_read, Except.bind,
    simM_dite, dif_pos h', simM_pure]
  rw [sim_ctxS_object]
@[simp] theorem s3a_ostateS_inst (o : sim.state.OState) : (ostateS o).inst = o.inst.val := rfl
@[simp] theorem s3a_ostateS_headInst (o : sim.state.OState) : (ostateS o).headInst = o.head_inst.val := rfl
@[simp] theorem s3a_topS_h (tn) (o : sim.playable.TopObj) : (topS tn o).h = hobjS tn o.h := rfl
@[simp] theorem s3a_hobjS_scale (tn) (h : sim.playable.HObj) : (hobjS tn h).scale = h.scale := rfl
@[simp] theorem s3a_inst_tf (k : sim.state.Inst) : (abs k : OsuModel.Sim.Inst).tf = abs k.tf := rfl
@[simp] theorem s3a_inst_size (k : sim.state.Inst) : (abs k : OsuModel.Sim.Inst).size = abs k.size := rfl
@[simp] theorem s3a_inst_origin (k : sim.state.Inst) : (abs k : OsuModel.Sim.Inst).origin = abs k.origin := rfl
@[simp] theorem s3a_inst_relAnchor (k : sim.state.Inst) : (abs k : OsuModel.Sim.Inst).relAnchor = abs k.rel_anchor := rfl
@[simp] theorem s3a_placement_of_eq (tf : sim.transforms.TObj) :
    sim.step.placement_of tf = ok ⟨tf.pos, tf.scale, tf.rot⟩ := by simp [sim.step.placement_of]
@[simp] theorem s3a_placementOf (tf : sim.transforms.TObj) :
    OsuModel.Sim.Sim.placementOf (abs tf) = abs (⟨tf.pos, tf.scale, tf.rot⟩ : sim.geometry.Placement) := rfl

/-- in-range accesses of the current-geometry accessors -/
def s3aInstOk (s : sim.state.St) (i : Nat) : Prop :=
  ∃ h : i < s.objs.val.length, (s.objs.val[i]'h).inst.val < s.insts.val.length ∧
    (s.objs.val[i]'h).head_inst.val < s.insts.val.length

theorem sim.step.cur_circle_receptor_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hinv : SimInv c s) (hi : s3aInstOk s i.val) :
    ∃ d, sim.step.cur_circle_receptor c s i = ok d ∧
      OsuModel.Sim.Sim.curCircleReceptor i.val (simCtxS tn fo c) (simStS tn s) = .ok (abs d, simStS tn s) := by
  obtain ⟨h1, h2, _⟩ := hi
  have h3 : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact h1
  obtain ⟨d, hd, ed⟩ := sim.step.cur_env_hoc_refines tn fo c s
  unfold sim.step.cur_circle_receptor OsuModel.Sim.Sim.curCircleReceptor
  simp only [vec_index_eq _ _ h1, vec_index_eq _ _ h2, vec_index_eq _ _ h3, bind_ok, hd, s3a_placement_of_eq,
    sim.basic.VEC2_ZERO, sim_basic_F32_0, s2_receptor_from_placement_eq]
  refine ⟨_, rfl, ?_⟩
  simp only [simM_bind, s3a_ostate _ _ _ _ _ h1, Except.bind, s3a_ostateS_inst, s3a_instOf _ _ _ _ _ h2,
    s3a_topObj _ _ _ _ _ h3, ed, simM_pure, s3a_topS_h, s3a_hobjS_scale, s3a_inst_tf, s3a_placementOf]
  rfl

theorem sim.step.cur_spinner_geom_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : s3aInstOk s i.val) :
    ∃ g, sim.step.cur_spinner_geom c s i = ok g ∧
      OsuModel.Sim.Sim.curSpinnerGeom i.val (simCtxS tn fo c) (simStS tn s) = .ok (abs g, simStS tn s) := by
  obtain ⟨h1, h2, _⟩ := hi
  obtain ⟨d, hd, ed⟩ := sim.step.cur_env_hoc_refines tn fo c s
  obtain ⟨g, hg, eg⟩ := sim.geometry.spinner_geom_p_refines d c.env.hoc_size
    ⟨(s.insts.val[(s.objs.val[i.val]'h1).inst.val]'h2).tf.pos, (s.insts.val[(s.objs.val[i.val]'h1).inst.val]'h2).tf.scale,
     (s.insts.val[(s.objs.val[i.val]'h1).inst.val]'h2).tf.rot⟩ { c.env with hoc := d } ⟨rfl, rfl⟩
  unfold sim.step.cur_spinner_geom OsuModel.Sim.Sim.curSpinnerGeom
  simp only [vec_index_eq _ _ h1, vec_index_eq _ _ h2, bind_ok, hd, s3a_placement_of_eq]
  refine ⟨g, hg, ?_⟩
  simp only [simM_bind, s3a_ostate _ _ _ _ _ h1, Except.bind, s3a_ostateS_inst, s3a_instOf _ _ _ _ _ h2,
    ed, simM_pure, s3a_inst_tf, s3a_placementOf]
  rw [← eg]; rfl

/-- `sliderGeomP` reads only `h.scale` of the hit object (so the type-name table does not matter) -/
theorem s3a_sliderGeomP_tn (tn : Nat → String) (env : OsuModel.Sim.Env) (h : sim.playable.HObj) (pl : OsuModel.Sim.Placement)
    (a b r : OsuModel.Sim.Vec2) (hp : OsuModel.Sim.Placement) :
    OsuModel.Sim.sliderGeomP env (hobjS tn h) pl a b r hp = OsuModel.Sim.sliderGeomP env (abs h) pl a b r hp := by
  unfold OsuModel.Sim.sliderGeomP; rfl

theorem sim.step.cur_slider_geom_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hinv : SimInv c s) (hi : s3aInstOk s i.val) :
    ∃ g, sim.step.cur_slider_geom c s i = ok g ∧
      OsuModel.Sim.Sim.curSliderGeom i.val (simCtxS tn fo c) (simStS tn s) = .ok (abs g, simStS tn s) := by
  obtain ⟨h1, h2, h4⟩ := hi
  have h3 : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact h1
  obtain ⟨d, hd, ed⟩ := sim.step.cur_env_hoc_refines tn fo c s
  let ins := s.insts.val[(s.objs.val[i.val]'h1).inst.val]'h2
  let hins := s.insts.val[(s.objs.val[i.val]'h1).head_inst.val]'h4
  obtain ⟨g, hg, eg⟩ := sim.geometry.slider_geom_p_refines d c.env.argon_path_radius (c.pb.objects.val[i.val]'h3).h
    ⟨ins.tf.pos, ins.tf.scale, ins.tf.rot⟩ ins.size ins.origin ins.rel_anchor ⟨hins.tf.pos, hins.tf.scale, hins.tf.rot⟩
    { c.env with hoc := d } ⟨rfl, rfl⟩
  unfold sim.step.cur_slider_geom OsuModel.Sim.Sim.curSliderGeom
  simp only [vec_index_eq _ _ h1, vec_index_eq _ _ h2, vec_index_eq _ _ h3, vec_index_eq _ _ h4, bind_ok, hd,
    s3a_placement_of_eq]
  refine ⟨g, hg, ?_⟩
  simp only [simM_bind, s3a_ostate _ _ _ _ _ h1, Except.bind, s3a_ostateS_inst, s3a_ostateS_headInst,
    s3a_instOf _ _ _ _ _ h2, s3a_instOf _ _ _ _ _ h4, s3a_topObj _ _ _ _ _ h3, ed, simM_pure, s3a_inst_tf,
    s3a_placementOf, s3a_topS_h, s3a_inst_size, s3a_inst_origin, s3a_inst_relAnchor, s3a_sliderGeomP_tn]
  rw [← eg]; rfl

end OsuProofs
