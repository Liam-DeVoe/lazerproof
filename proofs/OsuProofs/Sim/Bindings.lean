/-
`apply_bindings` (DrawableOsuHitObject.OnApply bindings) against `OsuModel.Sim.Sim.applyBindings`, with the
instance frame `simABFr` (only bound values / position / body geometry change) for its callers (became_alive).
-/
import OsuProofs.Sim.OnKilled
import OsuProofs.Sim2.Transforms
import OsuProofs.Sim2.Geometry
import OsuProofs.Sim3.SB_US
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem sim_ehead (tn fo) (c : sim.state.Ctx) (i : Usize) (hhi : i.val < c.head_idx.val.length) (S : OsuModel.Sim.St) :
    OsuModel.Sim.Sim.headIdxOf i.val (simCtxS tn fo c) S = .ok ((c.head_idx.val[i.val]'hhi).val, S) := by
  have hhi' : i.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
  simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]

/-- the spec's local `vEq` of `applyBindings` -/
def simVEq (a b : OsuModel.Sim.Vec2) : Bool :=
  (a.x == b.x || (a.x.isNaN && b.x.isNaN)) && (a.y == b.y || (a.y.isNaN && b.y.isNaN))

theorem sim_v_eq_bindable (a b : sim.basic.Vec2) :
    sim.step.v_eq_bindable a b = ok (simVEq (abs a) (abs b)) := by
  unfold sim.step.v_eq_bindable simVEq
  by_cases h1 : (a.x == b.x) = true <;> by_cases h2 : (a.y == b.y) = true <;>
    by_cases h3 : a.x.isNaN = true <;> by_cases h4 : b.x.isNaN = true <;>
    by_cases h5 : a.y.isNaN = true <;> by_cases h6 : b.y.isNaN = true <;>
    simp_all [float.F32.eq, float.F32.is_nan, abs]

theorem sim_modify_insts (tn) (s : sim.state.St) (t : alloc.vec.Vec sim.state.Inst) (kk : Usize)
    (hk : kk.val < t.val.length) (Y : sim.state.Inst) (X : OsuModel.Sim.Inst) (hf : X = abs Y) :
    { simStS tn { s with insts := t } with insts := (simStS tn { s with insts := t }).insts.modify kk.val (fun _ => X) } =
      simStS tn { s with insts := t.set kk Y } := by
  have e : (simStS tn { s with insts := t }).insts = (t.val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray := rfl
  rw [e, s3b_arr_modify_toArray _ _ _ hk, hf]
  show _ = { simStS tn { s with insts := t } with insts := ((t.set kk Y).val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray }
  rw [vec_set_val', List.map_set]

theorem sim_modify_insts' (tn) (s : sim.state.St) (kk : Usize) (hk : kk.val < s.insts.val.length) (Y : sim.state.Inst)
    (X : OsuModel.Sim.Inst) (hX : X = abs Y) :
    (Except.ok ((), { simStS tn s with insts := (simStS tn s).insts.modify kk.val (fun _ => X) }) :
      Except String (Unit × OsuModel.Sim.St)) = .ok ((), simStS tn { s with insts := s.insts.set kk Y }) := by
  have := sim_modify_insts tn s s.insts kk hk Y X hX
  exact congrArg (fun x => Except.ok ((), x)) this

theorem sim_kb_circle_circle : (OsuModel.Sim.Kind.circle == OsuModel.Sim.Kind.circle) = true := by decide
theorem sim_kb_circle_slider : (OsuModel.Sim.Kind.circle == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_circle_spinner : (OsuModel.Sim.Kind.circle == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_slider_circle : (OsuModel.Sim.Kind.slider == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_slider_slider : (OsuModel.Sim.Kind.slider == OsuModel.Sim.Kind.slider) = true := by decide
theorem sim_kb_slider_spinner : (OsuModel.Sim.Kind.slider == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_spinner_circle : (OsuModel.Sim.Kind.spinner == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_spinner_slider : (OsuModel.Sim.Kind.spinner == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_spinner_spinner : (OsuModel.Sim.Kind.spinner == OsuModel.Sim.Kind.spinner) = true := by decide
theorem sim_kb_head_circle : (OsuModel.Sim.Kind.head == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_head_slider : (OsuModel.Sim.Kind.head == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_head_spinner : (OsuModel.Sim.Kind.head == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_tick_circle : (OsuModel.Sim.Kind.tick == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_tick_slider : (OsuModel.Sim.Kind.tick == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_tick_spinner : (OsuModel.Sim.Kind.tick == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_repeat_circle : (OsuModel.Sim.Kind.«repeat» == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_repeat_slider : (OsuModel.Sim.Kind.«repeat» == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_repeat_spinner : (OsuModel.Sim.Kind.«repeat» == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_tail_circle : (OsuModel.Sim.Kind.tail == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_tail_slider : (OsuModel.Sim.Kind.tail == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_tail_spinner : (OsuModel.Sim.Kind.tail == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_spinnerTick_circle : (OsuModel.Sim.Kind.spinnerTick == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_spinnerTick_slider : (OsuModel.Sim.Kind.spinnerTick == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_spinnerTick_spinner : (OsuModel.Sim.Kind.spinnerTick == OsuModel.Sim.Kind.spinner) = false := by decide
theorem sim_kb_spinnerBonusTick_circle : (OsuModel.Sim.Kind.spinnerBonusTick == OsuModel.Sim.Kind.circle) = false := by decide
theorem sim_kb_spinnerBonusTick_slider : (OsuModel.Sim.Kind.spinnerBonusTick == OsuModel.Sim.Kind.slider) = false := by decide
theorem sim_kb_spinnerBonusTick_spinner : (OsuModel.Sim.Kind.spinnerBonusTick == OsuModel.Sim.Kind.spinner) = false := by decide

/-- only the position of a transformable differs -/
structure simPosFr (a b : sim.transforms.TObj) : Prop where
  scale : b.scale = a.scale
  rot : b.rot = a.rot
  alpha : b.alpha = a.alpha
  trackers : b.trackers = a.trackers
  last_update : b.last_update = a.last_update
  delay : b.delay = a.delay

theorem simPosFr_refl (a : sim.transforms.TObj) : simPosFr a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem simPosFr_trans {a b c : sim.transforms.TObj} (h1 : simPosFr a b) (h2 : simPosFr b c) : simPosFr a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5, h2.6.trans h1.6⟩
theorem sim_tobj_set_pos {o r : sim.transforms.TObj} {v : sim.basic.Vec2}
    (h : sim.transforms.tobj_set o .Position v = ok r) : simPosFr o r := by
  unfold sim.transforms.tobj_set at h
  by_cases hb : (o.pos.x == v.x && o.pos.y == v.y) = true <;>
    simp [sim.basic.Vec2.eq, hb] at h <;> subst h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- the instance fields `apply_bindings` keeps -/
structure simABFr (a b : sim.state.Inst) : Prop where
  loaded : b.loaded = a.loaded
  armed : b.armed = a.armed
  body_tf : b.body_tf = a.body_tf
  body_loaded : b.body_loaded = a.body_loaded
  tf : simPosFr a.tf b.tf

theorem sim_ab_top_ns (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (k : Usize) (hi : i.val < c.pb.objects.val.length) (hhi : i.val < c.head_idx.val.length)
    (hk : k.val < s.insts.val.length)
    (hns : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Slider) :
    ∃ res s', sim.step.apply_bindings c s i .Top k = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyBindings i.val (abs sim.step.Part.Top) k.val (simCtxS tn fo c) (simStS tn s)) ∧
      ∃ Y, s' = { s with insts := s.insts.set k Y } ∧ simABFr (s.insts.val[k.val]'hk) Y := by
  have hk' : k.val < (simStS tn s).insts.size := by simpa [simStS, abs] using hk
  generalize hh : (c.pb.objects.val[i.val]'hi).h = h at hns
  generalize hins : s.insts.val[k.val]'hk = ins
  have hinsS : (simStS tn s).insts[k.val]'hk' = abs ins := by rw [← hins]; simp [simStS, abs]
  obtain ⟨tS, etS, atS⟩ := sim.transforms.tobj_set_refines ins.tf .Position h.stacked
  obtain ⟨tP, etP, atP⟩ := sim.transforms.tobj_set_refines ins.tf .Position h.pos
  have atP' : (abs ins : OsuModel.Sim.Inst).tf.set .position (hobjS tn h).pos = abs tP := atP
  obtain ⟨tSS, etSS, atSS⟩ := sim.transforms.tobj_set_refines tS .Position h.stacked
  have hfS := sim_tobj_set_pos etS
  have hfSS := sim_tobj_set_pos etSS
  have hfP := sim_tobj_set_pos etP
  have atS' : (abs ins : OsuModel.Sim.Inst).tf.set .position (hobjS tn h).stacked = abs tS := atS
  have atSS' : (abs tS : OsuModel.Sim.TObj).set .position (hobjS tn h).stacked = abs tSS := atSS
  have hhS : (topS tn (c.pb.objects.val[i.val]'hi)).h = hobjS tn h := by rw [← hh]; rfl
  have hkS : (hobjS tn h).kind = kindS h.kind := rfl
  have hpcS : ∀ X : OsuModel.Sim.Inst, X = abs ins →
      ((X.boundPos.x == (hobjS tn h).pos.x || X.boundPos.x.isNaN && (hobjS tn h).pos.x.isNaN) &&
       (X.boundPos.y == (hobjS tn h).pos.y || X.boundPos.y.isNaN && (hobjS tn h).pos.y.isNaN)) =
      simVEq (abs ins.bound_pos) (abs h.pos) := by rintro X rfl; rfl
  have hscS : ∀ X : OsuModel.Sim.Inst, X = abs ins → (X.boundStack == (hobjS tn h).stackHeight) =
      decide (ins.bound_stack = h.stack_height) := by
    rintro X rfl
    show (ins.bound_stack.val == h.stack_height.val) = _
    by_cases e : ins.bound_stack = h.stack_height
    · simp [e]
    · have : ins.bound_stack.val ≠ h.stack_height.val := fun h' => e (IScalar.eq_of_val_eq h')
      simp [e, this]
  have hI64 : (ins.bound_stack == h.stack_height) = decide (ins.bound_stack = h.stack_height) := by
    by_cases e : ins.bound_stack = h.stack_height <;> simp [e]
  unfold sim.step.apply_bindings OsuModel.Sim.Sim.applyBindings
  simp only [simM_bind, s3a_topObj tn fo c _ i.val hi, Except.bind, vec_index_eq _ _ hi, bind_ok,
    s3a_instOf tn fo c s k.val hk, vec_index_mut_eq _ _ hk, sim_ehead tn fo c i hhi, part_eq_ok,
    sim_v_eq_bindable, kind_eq_ok, hh, hins, hhS, simM_pure, uncurry_apply_pair]
  simp (config := {decide := true}) only [decide_true, ite_true, if_true, bind_ok, float.F32.eq,
    float.F32.is_nan, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, kind_eq_ok, bne,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, if_false, hkS]
  try simp only [simM_bind, simM_pure, Except.bind, s3a_instOf tn fo c s k.val hk, hins]

  simp only [hpcS _ rfl, hscS _ rfl, hI64]
  cases hkd : h.kind <;> (try exact absurd hkd hns) <;>
  by_cases hpc : simVEq (abs ins.bound_pos) (abs h.pos) = true <;>
  by_cases hsc : ins.bound_stack = h.stack_height <;>
  by_cases hsc2 : (ins.bound_scale == h.scale) = true <;> by_cases hn : F32.isNaN ins.bound_scale = true <;>
  simp (config := {decide := true}) only [hkd, kindS, kind_eq_ok, hpc, hsc, hsc2, hn, etS, etSS, decide_true, decide_false, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true, bind_ok, not_true_eq_false, not_false_eq_true, hkS,
    Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, beq_self_eq_true, ite_self, uncurry_apply_pair,
    atS', atSS', atP', etP, sim_kb_circle_circle, sim_kb_circle_slider, sim_kb_circle_spinner, sim_kb_slider_circle, sim_kb_slider_slider, sim_kb_slider_spinner, sim_kb_spinner_circle, sim_kb_spinner_slider, sim_kb_spinner_spinner, sim_kb_head_circle, sim_kb_head_slider, sim_kb_head_spinner, sim_kb_tick_circle, sim_kb_tick_slider, sim_kb_tick_spinner, sim_kb_repeat_circle, sim_kb_repeat_slider, sim_kb_repeat_spinner, sim_kb_tail_circle, sim_kb_tail_slider, sim_kb_tail_spinner, sim_kb_spinnerTick_circle, sim_kb_spinnerTick_slider, sim_kb_spinnerTick_spinner, sim_kb_spinnerBonusTick_circle, sim_kb_spinnerBonusTick_slider, sim_kb_spinnerBonusTick_spinner] <;>
  refine ⟨_, _, by first | rfl | (simp; exact ⟨rfl, rfl⟩), ?_, ⟨_, rfl, ?_⟩⟩ <;>
  first
  | exact ⟨rfl, rfl, rfl, rfl, by
      first | exact simPosFr_refl _ | exact hfS | exact hfP | exact simPosFr_trans hfS hfSS⟩
  | (simp only [simRelM]
     rw [s3b_modifyInst_ok _ _ _ _ hk']
     exact sim_modify_insts' tn s k hk _ _ (by first | rfl | (cases ins; simp_all [abs, hobjS])))

theorem sim_ab_head (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (k : Usize) (hi : i.val < c.pb.objects.val.length) (hhi : i.val < c.head_idx.val.length)
    (hk : k.val < s.insts.val.length)
    (hhn : (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length) :
    ∃ res s', sim.step.apply_bindings c s i .Head k = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyBindings i.val (abs sim.step.Part.Head) k.val (simCtxS tn fo c) (simStS tn s)) ∧
      ∃ Y, s' = { s with insts := s.insts.set k Y } ∧ simABFr (s.insts.val[k.val]'hk) Y := by
  have hk' : k.val < (simStS tn s).insts.size := by simpa [simStS, abs] using hk
  have enj : ∀ S, OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) (c.head_idx.val[i.val]'hhi).val
      (simCtxS tn fo c) S = .ok (hobjS tn ((c.pb.objects.val[i.val]'hi).nested.val[(c.head_idx.val[i.val]'hhi).val]'hhn), S) := by
    intro S; simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hhn]
  have hNI : (c.pb.objects.val[i.val]'hi).nested.index_usize (c.head_idx.val[i.val]'hhi) =
    ok ((c.pb.objects.val[i.val]'hi).nested.val[(c.head_idx.val[i.val]'hhi).val]'hhn) := vec_index_usize_eq _ _ hhn
  have hpe : sim.step.Part.Insts.CoreCmpPartialEqPart.eq .Head .Top = ok false := by
    rw [part_eq_ok]; simp [sim.step.Part.read_discriminant]
  have hpt' : (abs sim.step.Part.Head == OsuModel.Sim.Sim.Part.top) = false := rfl
  have hpt : (partS sim.step.Part.Head == OsuModel.Sim.Sim.Part.top) = false := by decide
  generalize hh : (c.pb.objects.val[i.val]'hi).nested.val[(c.head_idx.val[i.val]'hhi).val]'hhn = h at enj hNI
  generalize hins : s.insts.val[k.val]'hk = ins
  have hinsS : (simStS tn s).insts[k.val]'hk' = abs ins := by rw [← hins]; simp [simStS, abs]
  obtain ⟨tS, etS, atS⟩ := sim.transforms.tobj_set_refines ins.tf .Position h.stacked
  obtain ⟨tP, etP, atP⟩ := sim.transforms.tobj_set_refines ins.tf .Position h.pos
  have atP' : (abs ins : OsuModel.Sim.Inst).tf.set .position (hobjS tn h).pos = abs tP := atP
  obtain ⟨tSS, etSS, atSS⟩ := sim.transforms.tobj_set_refines tS .Position h.stacked
  have hfS := sim_tobj_set_pos etS
  have hfSS := sim_tobj_set_pos etSS
  have hfP := sim_tobj_set_pos etP
  have atS' : (abs ins : OsuModel.Sim.Inst).tf.set .position (hobjS tn h).stacked = abs tS := atS
  have atSS' : (abs tS : OsuModel.Sim.TObj).set .position (hobjS tn h).stacked = abs tSS := atSS
  have hkS : (hobjS tn h).kind = kindS h.kind := rfl
  have hpcS : ∀ X : OsuModel.Sim.Inst, X = abs ins →
      ((X.boundPos.x == (hobjS tn h).pos.x || X.boundPos.x.isNaN && (hobjS tn h).pos.x.isNaN) &&
       (X.boundPos.y == (hobjS tn h).pos.y || X.boundPos.y.isNaN && (hobjS tn h).pos.y.isNaN)) =
      simVEq (abs ins.bound_pos) (abs h.pos) := by rintro X rfl; rfl
  have hscS : ∀ X : OsuModel.Sim.Inst, X = abs ins → (X.boundStack == (hobjS tn h).stackHeight) =
      decide (ins.bound_stack = h.stack_height) := by
    rintro X rfl
    show (ins.bound_stack.val == h.stack_height.val) = _
    by_cases e : ins.bound_stack = h.stack_height
    · simp [e]
    · have : ins.bound_stack.val ≠ h.stack_height.val := fun h' => e (IScalar.eq_of_val_eq h')
      simp [e, this]
  have hI64 : (ins.bound_stack == h.stack_height) = decide (ins.bound_stack = h.stack_height) := by
    by_cases e : ins.bound_stack = h.stack_height <;> simp [e]
  unfold sim.step.apply_bindings OsuModel.Sim.Sim.applyBindings
  simp only [simM_bind, s3a_topObj tn fo c _ i.val hi, Except.bind, vec_index_eq _ _ hi, bind_ok,
    s3a_instOf tn fo c s k.val hk, vec_index_mut_eq _ _ hk, sim_ehead tn fo c i hhi, hpe, hh,
    sim_v_eq_bindable, kind_eq_ok, hins, simM_pure, uncurry_apply_pair, vec_index_eq _ _ hhi, hNI, vec_index_eq _ _ hhn, enj, hpt, Bool.false_and,
    vec_index_usize_eq _ _ hhi, Bool.false_eq_true, ite_false]
  simp (config := {decide := true}) only [decide_true, ite_true, if_true, bind_ok, float.F32.eq,
    float.F32.is_nan, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, kind_eq_ok, bne,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, if_false, hkS]
  try simp only [simM_bind, simM_pure, Except.bind]
  rw [enj]
  simp only [simM_bind, simM_pure, Except.bind, s3a_instOf tn fo c s k.val hk, hins, hpt', Bool.false_and,
    Bool.false_eq_true, ite_false]

  simp only [hpcS _ rfl, hscS _ rfl, hI64]
  cases hkd : h.kind <;>
  by_cases hpc : simVEq (abs ins.bound_pos) (abs h.pos) = true <;>
  by_cases hsc : ins.bound_stack = h.stack_height <;>
  by_cases hsc2 : (ins.bound_scale == h.scale) = true <;> by_cases hn : F32.isNaN ins.bound_scale = true <;>
  simp (config := {decide := true}) only [hkd, kindS, kind_eq_ok, hpc, hsc, hsc2, hn, etS, etSS, decide_true, decide_false, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true, bind_ok, not_true_eq_false, not_false_eq_true, hkS,
    Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, beq_self_eq_true, ite_self, uncurry_apply_pair,
    atS', atSS', atP', etP, sim_kb_circle_circle, sim_kb_circle_slider, sim_kb_circle_spinner, sim_kb_slider_circle, sim_kb_slider_slider, sim_kb_slider_spinner, sim_kb_spinner_circle, sim_kb_spinner_slider, sim_kb_spinner_spinner, sim_kb_head_circle, sim_kb_head_slider, sim_kb_head_spinner, sim_kb_tick_circle, sim_kb_tick_slider, sim_kb_tick_spinner, sim_kb_repeat_circle, sim_kb_repeat_slider, sim_kb_repeat_spinner, sim_kb_tail_circle, sim_kb_tail_slider, sim_kb_tail_spinner, sim_kb_spinnerTick_circle, sim_kb_spinnerTick_slider, sim_kb_spinnerTick_spinner, sim_kb_spinnerBonusTick_circle, sim_kb_spinnerBonusTick_slider, sim_kb_spinnerBonusTick_spinner] <;>
  refine ⟨_, _, by first | rfl | (simp; exact ⟨rfl, rfl⟩), ?_, ⟨_, rfl, ?_⟩⟩ <;>
  first
  | exact ⟨rfl, rfl, rfl, rfl, by
      first | exact simPosFr_refl _ | exact hfS | exact hfP | exact simPosFr_trans hfS hfSS⟩
  | (simp only [simRelM]
     rw [s3b_modifyInst_ok _ _ _ _ hk']
     exact sim_modify_insts' tn s k hk _ _ (by first | rfl | (cases ins; simp_all [abs, hobjS])))

theorem sim_b4_bind {α} (a b c : Bool) (f : Bool → Result α) :
    ((if a = true then ok true else if b = true then ok c else ok false) >>= f) = f (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> simp
theorem sim_b4_bind' {α} (a b c : Bool) (f : Bool → Result α) :
    Aeneas.Std.bind (if a = true then ok true else if b = true then ok c else ok false) f = f (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> simp
theorem sim_s2_rel_ok {α β} {f : α → β} {E : Except String β} {a : α} (h : s2_rel f E (.Ok a)) : E = .ok (f a) := by
  cases E <;> simp_all [s2_rel]
theorem sim_s2_rel_err {α β} {f : α → β} {E : Except String β} {e} (h : s2_rel f E (.Err e)) : ∃ m, E = .error m := by
  cases E <;> simp_all [s2_rel]

set_option hygiene false in
macro "slfin" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (config := {decide := true}) only [$ts,*, bind_ok, bind_tc_ok, ite_true, ite_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, decide_true, decide_false, not_true_eq_false,
    not_false_eq_true, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    simM_bind, simM_pure, simM_throw, simM_read, OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.liftExcept, Except.bind,
    s3a_ctx_env, hargS, Option.map_some, Option.map_none, OsuModel.Sim.Sim.need, hkS, hsl0, kindS,
    sim_kb_slider_spinner, sim_kb_slider_circle, sim_kb_slider_slider, Bool.true_or, Bool.or_true, Bool.and_true,
    Bool.true_and, Bool.false_and, Bool.and_false, hpc, hsc] <;>
  refine ⟨_, _, by first | rfl | (simp; exact ⟨rfl, rfl⟩), ?_, ⟨_, rfl, ?_⟩⟩ <;>
  first
  | exact ⟨rfl, rfl, rfl, by first | rfl | exact hbl.symm | (simp only [Bool.not_eq_true] at hbl; exact hbl.symm), by first | exact simPosFr_refl _ | exact hfS | exact simPosFr_trans hfS hfSS⟩
  | (simp only [simRelM]
     first
     | exact ⟨_, rfl⟩
     | (rw [s3b_modifyInst_ok _ _ _ _ hk']
        exact sim_modify_insts' tn s k hk _ _ (by first | rfl | (cases ins; simp_all [abs, hobjS]))))))

theorem sim_ab_top_sl (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (k : Usize) (hi : i.val < c.pb.objects.val.length) (hhi : i.val < c.head_idx.val.length)
    (hk : k.val < s.insts.val.length)
    (hsl0 : (c.pb.objects.val[i.val]'hi).h.kind = .Slider) :
    ∃ res s', sim.step.apply_bindings c s i .Top k = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyBindings i.val (abs sim.step.Part.Top) k.val (simCtxS tn fo c) (simStS tn s)) ∧
      ∃ Y, s' = { s with insts := s.insts.set k Y } ∧ simABFr (s.insts.val[k.val]'hk) Y := by
  have hk' : k.val < (simStS tn s).insts.size := by simpa [simStS, abs] using hk
  have hsl1 := hsl0
  generalize hh : (c.pb.objects.val[i.val]'hi).h = h at hsl0
  generalize hins : s.insts.val[k.val]'hk = ins
  have hinsS : (simStS tn s).insts[k.val]'hk' = abs ins := by rw [← hins]; simp [simStS, abs]
  obtain ⟨tS, etS, atS⟩ := sim.transforms.tobj_set_refines ins.tf .Position h.stacked
  obtain ⟨tP, etP, atP⟩ := sim.transforms.tobj_set_refines ins.tf .Position h.pos
  have atP' : (abs ins : OsuModel.Sim.Inst).tf.set .position (hobjS tn h).pos = abs tP := atP
  obtain ⟨tSS, etSS, atSS⟩ := sim.transforms.tobj_set_refines tS .Position h.stacked
  have hfS := sim_tobj_set_pos etS
  have hfSS := sim_tobj_set_pos etSS
  have hfP := sim_tobj_set_pos etP
  have atS' : (abs ins : OsuModel.Sim.Inst).tf.set .position (hobjS tn h).stacked = abs tS := atS
  have atSS' : (abs tS : OsuModel.Sim.TObj).set .position (hobjS tn h).stacked = abs tSS := atSS
  have hhS : (topS tn (c.pb.objects.val[i.val]'hi)).h = hobjS tn h := by rw [← hh]; rfl
  have hkS : (hobjS tn h).kind = kindS h.kind := rfl
  have hpcS : ∀ X : OsuModel.Sim.Inst, X = abs ins →
      ((X.boundPos.x == (hobjS tn h).pos.x || X.boundPos.x.isNaN && (hobjS tn h).pos.x.isNaN) &&
       (X.boundPos.y == (hobjS tn h).pos.y || X.boundPos.y.isNaN && (hobjS tn h).pos.y.isNaN)) =
      simVEq (abs ins.bound_pos) (abs h.pos) := by rintro X rfl; rfl
  have hscS : ∀ X : OsuModel.Sim.Inst, X = abs ins → (X.boundStack == (hobjS tn h).stackHeight) =
      decide (ins.bound_stack = h.stack_height) := by
    rintro X rfl
    show (ins.bound_stack.val == h.stack_height.val) = _
    by_cases e : ins.bound_stack = h.stack_height
    · simp [e]
    · have : ins.bound_stack.val ≠ h.stack_height.val := fun h' => e (IScalar.eq_of_val_eq h')
      simp [e, this]
  have hI64 : (ins.bound_stack == h.stack_height) = decide (ins.bound_stack = h.stack_height) := by
    by_cases e : ins.bound_stack = h.stack_height <;> simp [e]
  unfold sim.step.apply_bindings OsuModel.Sim.Sim.applyBindings
  simp only [simM_bind, s3a_topObj tn fo c _ i.val hi, Except.bind, vec_index_eq _ _ hi, bind_ok,
    s3a_instOf tn fo c s k.val hk, vec_index_mut_eq _ _ hk, sim_ehead tn fo c i hhi, part_eq_ok,
    sim_v_eq_bindable, kind_eq_ok, hh, hins, hhS, simM_pure, uncurry_apply_pair]
  simp (config := {decide := true}) only [decide_true, ite_true, if_true, bind_ok, float.F32.eq,
    float.F32.is_nan, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, kind_eq_ok, bne,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, if_false, hkS]
  try simp only [simM_bind, simM_pure, Except.bind, s3a_instOf tn fo c s k.val hk, hins]

  simp only [hpcS _ rfl, hscS _ rfl, hI64]
  simp only [hsl0, hsl1, kindS, sim_kb_slider_circle, sim_kb_slider_slider, sim_kb_slider_spinner, ite_true, ite_false,
    Bool.false_eq_true, bind_ok, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.true_and, Bool.and_true]
  have hbrS : (abs ins : OsuModel.Sim.Inst).bodyRadius = ins.body_radius := rfl
  have hblS : (abs ins : OsuModel.Sim.Inst).bodyLoaded = ins.body_loaded := rfl
  have hbsS : (abs ins : OsuModel.Sim.Inst).boundScale = ins.bound_scale := rfl
  have hhsS : (hobjS tn h).scale = h.scale := rfl
  have hargS : (abs c.env : OsuModel.Sim.Env).argonPathRadius = c.env.argon_path_radius := rfl
  have hspS : (topS tn (c.pb.objects.val[i.val]'hi)).slider = (c.pb.objects.val[i.val]'hi).slider.map abs := rfl
  by_cases hpc : simVEq (abs ins.bound_pos) (abs h.pos) = true <;>
  by_cases hsc : ins.bound_stack = h.stack_height <;>
  simp only [hpc, hsc, etS, etSS, atS', atSS', decide_true, decide_false, Bool.not_true, Bool.not_false, ite_true,
    ite_false, Bool.false_eq_true, bind_ok, not_true_eq_false, not_false_eq_true, bind_tc_ok, ite_self,
    uncurry_apply_pair] <;>
  simp only [bind_tc_ok, sim_b4_bind, sim_b4_bind', hbrS, hblS, hbsS, hhsS, hspS, OsuModel.Sim.objectRadius, s2_geo_consts,
    float.F32.mul, bind_ok] <;>
  all_goals (
    cases hsd : (c.pb.objects.val[i.val]'hi).slider
    · have hsdR : sim.step.slider_data c i = ok (.Err (sim.err.SimErr.Internal sim.err.Internal.MissingSliderData)) := by
        simp [sim.step.slider_data, vec_index_eq _ _ hi, hsd]
      slfin [hsdR]
    rename_i sd
    have hsdR : sim.step.slider_data c i = ok (.Ok sd) := by
      simp [sim.step.slider_data, vec_index_eq _ _ hi, hsd]
    obtain ⟨x1, ex1, rx1⟩ := sim.geometry.body_refresh_refines sd (64 * h.scale)
    obtain ⟨x2, ex2, rx2⟩ := sim.geometry.body_refresh_refines sd (c.env.argon_path_radius * h.scale)
    by_cases hsc0 : (ins.bound_scale == h.scale || F32.isNaN ins.bound_scale && F32.isNaN h.scale) = true
    · by_cases hbl : ins.body_loaded = true
      · by_cases he2 : (ins.body_radius == c.env.argon_path_radius * h.scale) = true
        · slfin [hsdR, hsc0, hbl, he2]
        · rcases x2 with ⟨sz2, off2⟩ | e2
          · have hm2 := sim_s2_rel_ok rx2
            slfin [hsdR, hsc0, hbl, he2, ex2, hm2]
          · obtain ⟨m2, hm2⟩ := sim_s2_rel_err rx2
            slfin [hsdR, hsc0, hbl, he2, ex2, hm2]
      · slfin [hsdR, hsc0, hbl]
    · by_cases he1 : (ins.body_radius == 64 * h.scale) = true
      · by_cases hbl : ins.body_loaded = true
        · by_cases he2 : (ins.body_radius == c.env.argon_path_radius * h.scale) = true
          · slfin [hsdR, hsc0, he1, hbl, he2]
          · rcases x2 with ⟨sz2, off2⟩ | e2
            · have hm2 := sim_s2_rel_ok rx2
              slfin [hsdR, hsc0, he1, hbl, he2, ex2, hm2]
            · obtain ⟨m2, hm2⟩ := sim_s2_rel_err rx2
              slfin [hsdR, hsc0, he1, hbl, he2, ex2, hm2]
        · slfin [hsdR, hsc0, he1, hbl]
      · rcases x1 with ⟨sz1, off1⟩ | e1
        · have hm1 := sim_s2_rel_ok rx1
          by_cases hbl : ins.body_loaded = true
          · by_cases he3 : (64 * h.scale == c.env.argon_path_radius * h.scale) = true
            · slfin [hsdR, hsc0, he1, ex1, hm1, hbl, he3]
            · rcases x2 with ⟨sz2, off2⟩ | e2
              · have hm2 := sim_s2_rel_ok rx2
                slfin [hsdR, hsc0, he1, ex1, hm1, hbl, he3, ex2, hm2]
              · obtain ⟨m2, hm2⟩ := sim_s2_rel_err rx2
                slfin [hsdR, hsc0, he1, ex1, hm1, hbl, he3, ex2, hm2]
          · slfin [hsdR, hsc0, he1, ex1, hm1, hbl]
        · obtain ⟨m1, hm1⟩ := sim_s2_rel_err rx1
          slfin [hsdR, hsc0, he1, ex1, hm1])

-- NOT-CONDITIONAL: range premises only (hi/hhi/hk; hhn = the head index is in range for p = Head, a context fact)
theorem sim.step.apply_bindings_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (i : Usize) (p : sim.step.Part) (k : Usize) (hi : i.val < c.pb.objects.val.length)
    (hhi : i.val < c.head_idx.val.length) (hk : k.val < s.insts.val.length)
    (hhn : p = .Head → (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length) :
    ∃ res s', sim.step.apply_bindings c s i p k = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.applyBindings i.val (abs p) k.val (simCtxS tn fo c) (simStS tn s)) ∧
      ∃ Y, s' = { s with insts := s.insts.set k Y } ∧ simABFr (s.insts.val[k.val]'hk) Y := by
  cases p with
  | Top =>
    by_cases hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider
    · exact sim_ab_top_sl tn fo c s i k hi hhi hk hsl
    · exact sim_ab_top_ns tn fo c s i k hi hhi hk hsl
  | Head => exact sim_ab_head tn fo c s i k hi hhi hk (hhn rfl)

end OsuProofs
