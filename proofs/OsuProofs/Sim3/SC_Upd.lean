/-
Sim3c part 3: mod update hooks of `playfieldUpdate` over the alive objects: `depth_update` (`Sim.depthUpdate`,
`OsuModDepth`) and `magnet_update` (`Sim.magnetUpdate`, `OsuModMagnetised` / `OsuModRepel`).
-/
import OsuProofs.Sim3.SB_Upd2
import OsuProofs.Sim3.SA_Track
import OsuProofs.Sim3.SC_WA
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

/-! ## `depthUpdate` leaves -/
@[simp] theorem s3c_fb32_m200 : float.F32.from_bits 3276275712#u32 = ok (-200 : F32) := by
  simp [float.F32.from_bits] <;> decide +kernel
@[simp] theorem s3c_fb32_256 : float.F32.from_bits 1132462080#u32 = ok (256 : F32) := by
  simp [float.F32.from_bits] <;> decide +kernel
@[simp] theorem s3c_fb32_192 : float.F32.from_bits 1128267776#u32 = ok (192 : F32) := by
  simp [float.F32.from_bits] <;> decide +kernel
@[simp] theorem s3c_fb32_1_5 : float.F32.from_bits 1069547520#u32 = ok (1.5 : F32) := by
  simp [float.F32.from_bits] <;> decide +kernel

@[simp] theorem s3c_F32_1C : sim.step.F32_1C = ok (1 : F32) := by unfold sim.step.F32_1C; simp <;> decide +kernel
theorem s3c_clone_usize (v : alloc.vec.Vec Usize) : alloc.vec.CloneVec.clone core.clone.CloneUsize v = ok v :=
  s3b_clone_vec _ (fun _ => rfl) v

theorem sim.step.scale_for_depth_refines (z camZ : F32) :
    sim.step.scale_for_depth z camZ = ok (-camZ / F32.max 1 (z - camZ)) := by
  simp [sim.step.scale_for_depth, float.F32.neg, float.F32.sub, s3c_F32_1C, sim.netx.f32_max_refines, float.F32.div]

theorem sim.step.circle_depth_refines (h : sim.playable.HObj) (md : F32) (time : F64) :
    sim.step.circle_depth h md time = ok (md - F64.toF32 ((F64.max time (h.start - h.preempt) - (h.start - h.preempt)) *
      (F32.toF64 md / h.preempt))) := by
  simp [sim.step.circle_depth, float.F32.to_f64, float.F64.div, float.F64.sub, net.max_refines, float.F64.mul,
    float.F64.to_f32, float.F32.sub]


/-- the spec's slider `z` of `depthUpdate` (Step.lean, verbatim with `maxDepth`, `sliderMinDepth`, `time`, `dur`) -/
def s3c_sliderZ (h : sim.playable.HObj) (dur : F64) (maxDepth sliderMinDepth : F32) (time : F64) : F32 :=
  let circleZ : F32 :=
    let speed := F32.toF64 maxDepth / h.preempt
    let appear := h.start - h.preempt
    maxDepth - F64.toF32 ((F64.max time appear - appear) * speed)
  let baseSpeed := F32.toF64 maxDepth / h.preempt
  let appear := h.start - h.preempt
  let zEnd := maxDepth - F64.toF32 ((F64.max (h.start + dur) appear - appear) * baseSpeed)
  if sliderMinDepth < zEnd then circleZ else
  let offsetAfter := dur + 500
  let slowSpeed := F64.min (F32.toF64 (-sliderMinDepth) / offsetAfter) baseSpeed
  let decT := h.preempt * 0.2
  let decD : F32 := F64.toF32 (decT * (baseSpeed + slowSpeed) * 0.5)
  if time < h.start - decT then
      let full := decD + F64.toF32 (baseSpeed * (h.preempt - decT))
      full - F64.toF32 ((F64.max time appear - appear) * baseSpeed)
    else if time < h.start then
      let «to» := time - (h.start - decT)
      let dec := (slowSpeed - baseSpeed) / decT
      decD - F64.toF32 (baseSpeed * «to» + dec * «to» * «to» * 0.5)
    else
      let endT := h.start + offsetAfter
      Neg.neg (F64.toF32 ((F64.min time endT - h.start) * slowSpeed))

theorem sim.step.slider_depth_refines (h : sim.playable.HObj) (dur : F64) (md smd : F32) (time : F64) :
    sim.step.slider_depth h dur md smd time = ok (s3c_sliderZ h dur md smd time) := by
  unfold sim.step.slider_depth s3c_sliderZ
  simp only [float.F32.to_f64, float.F64.div, float.F64.sub, float.F64.add, net.max_refines, net.min_refines,
    float.F64.mul, float.F64.to_f32, float.F32.sub, float.F32.lt, float.F32.neg, float.F32.add, float.F64.lt,
    fb64_4647503709213818880, fb64_4596373779694328218, fb64_4602678819172646912, bind_ok,
    sim.step.circle_depth_refines]
  by_cases h1 : smd < md - F64.toF32 ((F64.max (h.start + dur) (h.start - h.preempt) - (h.start - h.preempt)) *
      (F32.toF64 md / h.preempt))
  · simp [h1]
  · simp only [h1, decide_false, Bool.false_eq_true, if_false]
    by_cases h2 : time < h.start - h.preempt * 0.2
    · simp [h2]
    · by_cases h3 : time < h.start
      · simp [h2, h3]
      · simp [h2, h3]

noncomputable def s3c_tset (o : sim.transforms.TObj) (m : sim.transforms.Member) (v : sim.basic.Vec2) :
    sim.transforms.TObj := Classical.choose (sim.transforms.tobj_set_refines o m v)
@[simp] theorem s3c_tset_eq (o : sim.transforms.TObj) (m : sim.transforms.Member) (v : sim.basic.Vec2) :
    sim.transforms.tobj_set o m v = ok (s3c_tset o m v) := (Classical.choose_spec (sim.transforms.tobj_set_refines o m v)).1
theorem s3c_tset_abs (o : sim.transforms.TObj) (m : sim.transforms.Member) (v : sim.basic.Vec2) :
    (abs (s3c_tset o m v) : OsuModel.Sim.TObj) = OsuModel.Sim.TObj.set (abs o) (abs m) (abs v) :=
  (Classical.choose_spec (sim.transforms.tobj_set_refines o m v)).2.symm

theorem s3c_dsd_ns (c' : sim.state.Ctx) (i : Usize) (hi : i.val < c'.pb.objects.val.length)
    (hk : (c'.pb.objects.val[i.val]'hi).h.kind ≠ .Slider) :
    sim.step.depth_slider_duration c' i = ok (.Ok 0) := by
  unfold sim.step.depth_slider_duration
  cases hK : (c'.pb.objects.val[i.val]'hi).h.kind <;> simp_all (config := {decide := true}) [vec_index_eq _ _ hi, kindS, sim.step.F64_0]
theorem s3c_dsd_s (c' : sim.state.Ctx) (i : Usize) (hi : i.val < c'.pb.objects.val.length)
    (hk : (c'.pb.objects.val[i.val]'hi).h.kind = .Slider) (sd : sim.playable.SliderData)
    (hs : (c'.pb.objects.val[i.val]'hi).slider = some sd) :
    sim.step.depth_slider_duration c' i = ok (.Ok sd.duration) := by
  unfold sim.step.depth_slider_duration
  simp (config := {decide := true}) [vec_index_eq _ _ hi, hk, kindS, sim.step.slider_data, hs, core.result.Result.Insts.CoreOpsTry.branch]
theorem s3c_dsd_e (c' : sim.state.Ctx) (i : Usize) (hi : i.val < c'.pb.objects.val.length)
    (hk : (c'.pb.objects.val[i.val]'hi).h.kind = .Slider) (hs : (c'.pb.objects.val[i.val]'hi).slider = none) :
    ∃ e, sim.step.depth_slider_duration c' i = ok (.Err e) := by
  unfold sim.step.depth_slider_duration
  simp (config := {decide := true}) [vec_index_eq _ _ hi, hk, kindS, sim.step.slider_data, hs,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- the abstract insts after writing instance `k` -/
theorem s3c_modify_insts (tn) (s : sim.state.St) (t : alloc.vec.Vec sim.state.Inst) (k : Nat)
    (hk : k < t.val.length) (Y : sim.state.Inst) (f : OsuModel.Sim.Inst → OsuModel.Sim.Inst)
    (hf : f (abs (t.val[k]'hk)) = abs Y) (kk : Usize) (hkk : kk.val = k) :
    { simStS tn { s with insts := t } with insts := (simStS tn { s with insts := t }).insts.modify k f } =
      simStS tn { s with insts := t.set kk Y } := by
  have e : (simStS tn { s with insts := t }).insts = (t.val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray := rfl
  rw [e, s3b_arr_modify_toArray _ _ _ hk, hf]
  show _ = { simStS tn { s with insts := t } with insts := ((t.set kk Y).val.map (fun x => (abs x : OsuModel.Sim.Inst))).toArray }
  rw [vec_set_val', hkk, List.map_set]

theorem s3c_modify_yield (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St) (t : alloc.vec.Vec sim.state.Inst) (kk : Usize)
    (hk : kk.val < t.val.length) (Y : sim.state.Inst) (f : OsuModel.Sim.Inst → OsuModel.Sim.Inst)
    (hf : f (abs (t.val[kk.val]'hk)) = abs Y) :
    (OsuModel.Sim.Sim.modifyInst kk.val f C (simStS tn { s with insts := t })).bind
      (fun p => (pure (ForInStep.yield PUnit.unit) : OsuModel.Sim.SimM (ForInStep PUnit)) C p.2) =
      .ok (.yield PUnit.unit, simStS tn { s with insts := t.set kk Y }) := by
  rw [s3b_modifyInst_ok _ _ _ _ (by simpa [simStS, abs] using hk)]
  simp only [s3b_ebok, simM_pure]
  rw [s3c_modify_insts tn s t kk.val hk Y f hf kk rfl]

theorem s3c_vset_set {α} (v : alloc.vec.Vec α) (k : Usize) (a b : α) : (v.set k a).set k b = v.set k b := by
  apply alloc.vec.Vec.ext; simp only [vec_set_val', List.set_set]

theorem s3c_dhf (I : sim.state.Inst) (p v : sim.basic.Vec2) (P V : OsuModel.Sim.Vec2) (hp : abs p = P) (hv : abs v = V) :
    ({ (abs I : OsuModel.Sim.Inst) with tf := ((abs I : OsuModel.Sim.Inst).tf.set .position P).set .scale V } : OsuModel.Sim.Inst) =
      abs ({ I with tf := s3c_tset (s3c_tset I.tf .Position p) .Scale v } : sim.state.Inst) := by
  subst hp hv
  show _ = ({ (abs I : OsuModel.Sim.Inst) with tf := (abs (s3c_tset (s3c_tset I.tf .Position p) .Scale v) : OsuModel.Sim.TObj) } : OsuModel.Sim.Inst)
  rw [s3c_tset_abs, s3c_tset_abs]; rfl

theorem s3c_ite_some {α} (p : Prop) [Decidable p] (a b : α) :
    (if p then some a else some b) = some (if p then a else b) := by split <;> rfl


/-! ## `magnetUpdate` leaves -/
/-- the spec's bounding-box fold step of `magnetUpdate` (`CalculatePossibleMovementBounds`) -/
def s3c_bbS : (F32 × F32 × F32 × F32) → OsuModel.Sim.Vec2 → (F32 × F32 × F32 × F32) := fun (a, b, c', d') v =>
  (F32.min a v.x, F32.max b v.x, F32.min c' v.y, F32.max d' v.y)
/-- the Rust-side fold step (projections) -/
def s3c_bbR (acc : F32 × F32 × F32 × F32) (v : sim.basic.Vec2) : F32 × F32 × F32 × F32 :=
  (F32.min acc.1 v.x, F32.max acc.2.1 v.x, F32.min acc.2.2.1 v.y, F32.max acc.2.2.2 v.y)

/-- the spec's `dest0` of `magnetUpdate` (Step.lean, verbatim) -/
def s3c_dest0S (repel : Bool) (o : OsuModel.Sim.TopObj) (pos cursorPos : OsuModel.Sim.Vec2) : OsuModel.Sim.Vec2 :=
  if !repel then cursorPos else
      let cl (v lo hi : OsuModel.Sim.Vec2) : OsuModel.Sim.Vec2 :=
        OsuModel.Sim.ofTK (OsuTK.Vector2.clamp (OsuModel.Sim.toTK v) (OsuModel.Sim.toTK lo) (OsuModel.Sim.toTK hi))
      let d := cl (OsuModel.Sim.Vec2.scale pos 2 - cursorPos) OsuModel.Sim.Vec2.zero ⟨512, 384⟩
      match o.slider with
      | some sd =>
        let r := F64.toF32 o.h.radius
        let (mnX, mxX, mnY, mxY) := sd.path.foldl s3c_bbS (F32.posInf, F32.negInf, F32.posInf, F32.negInf)
        let left := -(mnX - r)
        let right := (512 : F32) - (mxX + r)
        let top := -(mnY - r)
        let bottom := (384 : F32) - (mxY + r)
        let w := right - left
        let hh := bottom - top
        cl d ⟨left, top⟩ ⟨left + w, top + hh⟩
      | none => d

theorem s3c_f512 : (512.0 : F32) = 512 := by decide +kernel
theorem s3c_f384 : (384.0 : F32) = 384 := by decide +kernel

theorem s3c_rscl (sd : sim.playable.SliderData) : ∀ n (j : Usize) (a b c e : F32), sd.path.val.length - j.val = n →
    j.val ≤ sd.path.val.length →
    sim.step.repel_slider_clamp_loop sd a b c e j = ok ((sd.path.val.drop j.val).foldl s3c_bbR (a, b, c, e)) := by
  intro n
  induction n with
  | zero =>
    intro j a b c e hn hj
    have hlt : ¬ j < alloc.vec.Vec.len sd.path := by rw [vec_lt_len_iff]; omega
    unfold sim.step.repel_slider_clamp_loop; rw [loop_unfold]
    simp only [sim.step.repel_slider_clamp_loop.body, hlt, if_false, bind_ok]
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro j a b c e hn hj
    have hl : j.val < sd.path.val.length := by omega
    have hlt : j < alloc.vec.Vec.len sd.path := by rw [vec_lt_len_iff]; exact hl
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := sd.path.property; omega)
    have e1 := ih j1 (F32.min a (sd.path.val[j.val]'hl).x) (F32.max b (sd.path.val[j.val]'hl).x)
      (F32.min c (sd.path.val[j.val]'hl).y) (F32.max e (sd.path.val[j.val]'hl).y) (by omega) (by omega)
    unfold sim.step.repel_slider_clamp_loop at e1 ⊢; rw [loop_unfold]
    dsimp only
    rw [sim.step.repel_slider_clamp_loop.body]
    simp only [hlt, if_true, bind_ok, vec_index_eq _ _ hl,
      sim.netx.f32_min_refines, sim.netx.f32_max_refines, hj1]
    rw [List.drop_eq_getElem_cons hl, List.foldl_cons]
    rw [hj1v] at e1; exact e1

theorem s3c_bb_fold (l : List sim.basic.Vec2) : ∀ init,
    (l.map (fun v => (abs v : OsuModel.Sim.Vec2))).foldl s3c_bbS init = l.foldl s3c_bbR init := by
  induction l with
  | nil => intro _; rfl
  | cons v l ih => intro init; obtain ⟨a, b, c, e⟩ := init; simp only [List.map_cons, List.foldl_cons]; exact ih _

theorem s3c_dest0_rust (tn) (repel : Bool) (o : sim.playable.TopObj) (pos cp : sim.basic.Vec2) :
    ∃ d, (if repel then sim.step.repel_dest o pos cp else ok cp) = ok d ∧
      (abs d : OsuModel.Sim.Vec2) = s3c_dest0S repel (topS tn o) (abs pos) (abs cp) := by
  cases repel
  · exact ⟨cp, rfl, rfl⟩
  · cases hs : o.slider with
    | none =>
      simp [sim.step.repel_dest, hs, sim.transforms.to_tk, sim.transforms.of_tk, net.osutk.v2,
        net.osutk.v2_clamp_refines, sim.basic.Vec2.scale, sim.basic.Vec2.sub, float.F32.mul, float.F32.sub]
      simp only [s3c_dest0S, topS, hs, Option.map_none]
      rw [s3c_f512, s3c_f384]; rfl
    | some sd =>
      have hl := s3c_rscl sd _ 0#usize F32.posInf F32.negInf F32.posInf F32.negInf rfl (by simp)
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hl
      simp [sim.step.repel_dest, hs, sim.transforms.to_tk, sim.transforms.of_tk, net.osutk.v2,
        net.osutk.v2_clamp_refines, sim.basic.Vec2.scale, sim.basic.Vec2.sub, float.F32.mul, float.F32.sub,
        sim.step.repel_slider_clamp, hl, float.F64.to_f32, float.F32.neg, float.F32.add]
      simp only [s3c_dest0S, topS, hs, Option.map_some]
      have ef : ((abs sd : OsuModel.Sim.SliderData).path.foldl s3c_bbS (F32.posInf, F32.negInf, F32.posInf, F32.negInf)) =
          sd.path.val.foldl s3c_bbR (F32.posInf, F32.negInf, F32.posInf, F32.negInf) := by
        rw [← s3c_bb_fold]
        show Array.foldl s3c_bbS _ (List.map (fun v => (abs v : OsuModel.Sim.Vec2)) sd.path.val).toArray = _
        rw [← Array.foldl_toList]
      rw [ef]
      generalize sd.path.val.foldl s3c_bbR (F32.posInf, F32.negInf, F32.posInf, F32.negInf) = X
      obtain ⟨a, b, c, e⟩ := X
      simp only [uncurry_apply_pair]
      refine ⟨_, rfl, ?_⟩
      try simp only [s3c_f512, s3c_f384]
      rfl

theorem sim.step.magnet_damp_refines (c : sim.state.Ctx) (repel : Bool) (pos cp : sim.basic.Vec2) :
    sim.step.magnet_damp c repel pos cp = ok (if repel then
      F32.toF64 (OsuTK.Vector2.distance ⟨pos.x, pos.y⟩ ⟨cp.x, cp.y⟩) / (0.04 * F32.toF64 c.cfg.repel_strength + 0.04)
      else Framework.Interpolation.lerp 3000 40 (F32.toF64 c.cfg.magnet_strength)) := by
  cases repel <;> simp [sim.step.magnet_damp, net.framework.lerp_refines, sim.transforms.to_tk, net.osutk.v2,
    net.osutk.v2_distance_refines, v2S, float.F32.to_f64, float.F64.mul, float.F64.add, float.F64.div]

/-! ## loops over `active` that write only `insts` -/
/-- `s3b_loopR_forIn` (sim3b) with the invariant also at the exit -/
theorem s3c_loopR_forIn {T α : Type}
    (body : T × Usize → Result (ControlFlow (T × Usize) (core.result.Result Unit sim.err.SimErr × T)))
    (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : T → Prop) (hn : l.length ≤ Usize.max)
    (hstep : ∀ t (q : Usize) (h : q.val < l.length), Inv t → ∀ q1 : Usize, q1.val = q.val + 1 →
      (∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv t' ∧ F (l[q.val]'h) PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t')) ∨
      (∃ e t', body (t, q) = ok (.done (.Err e, t')) ∧ Inv t' ∧ ∃ m, F (l[q.val]'h) PUnit.unit C (A t) = .error m))
    (hend : ∀ t (q : Usize), l.length ≤ q.val → body (t, q) = ok (.done (.Ok (), t))) :
    ∀ n (q : Usize) t, l.length - q.val = n → Inv t → q.val ≤ l.length → ∃ res t', loop body (t, q) = ok (res, t') ∧
      s3b_rrel (fun _ => PUnit.unit) (A t') res (forIn (l.drop q.val) PUnit.unit F C (A t)) ∧ Inv t' := by
  intro n
  induction n with
  | zero =>
    intro q t hn0 hI hq
    refine ⟨.Ok (), t, by rw [loop_unfold, hend t q (by omega)]; simp only [bind_ok], ?_, hI⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro q t hn0 hI hq
    have hlt : q.val < l.length := by omega
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
    rw [List.drop_eq_getElem_cons hlt, List.forIn_cons]
    rcases hstep t q hlt hI q1 hq1v with ⟨t', hb, hI', hF⟩ | ⟨e, t', hb, hI', m, hF⟩
    · obtain ⟨res, t'', hl, hr, hI''⟩ := ih q1 t' (by omega) hI' (by omega)
      refine ⟨res, t'', by rw [loop_unfold, hb]; simpa using hl, ?_, hI''⟩
      simp only [simM_bind, hF, Except.bind]
      rw [hq1v] at hr; exact hr
    · refine ⟨.Err e, t', by rw [loop_unfold, hb]; simp only [bind_ok], ⟨m, ?_⟩, hI'⟩
      simp only [simM_bind, hF, Except.bind]

/-- the Rust/spec wrapper of a hook that loops over `active` writing only `insts` -/
theorem s3c_wrapI (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St)
    (B : alloc.vec.Vec sim.state.Inst × Usize → Result (ControlFlow (alloc.vec.Vec sim.state.Inst × Usize)
      (core.result.Result Unit sim.err.SimErr × alloc.vec.Vec sim.state.Inst)))
    (l : List Nat) (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (h : ∃ res t', loop B (s.insts, 0#usize) = ok (res, t') ∧
      s3b_rrel (fun _ => PUnit.unit) (simStS tn { s with insts := t' }) res
        (forIn (l.drop (0#usize : Usize).val) PUnit.unit F C (simStS tn { s with insts := s.insts })) ∧
      t'.val.length = s.insts.val.length) :
    ∃ r s', (do let (r, v) ← loop B (s.insts, 0#usize); ok (r, { s with insts := v })) = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r ((forIn l PUnit.unit F C (simStS tn s)).bind fun p => (pure () : OsuModel.Sim.SimM Unit) C p.2) ∧
      ∃ ins, s' = { s with insts := ins } ∧ ins.val.length = s.insts.val.length := by
  obtain ⟨res, t', h1, h2, h3⟩ := h
  refine ⟨res, { s with insts := t' }, by rw [h1]; simp only [bind_ok]; rfl, ?_, ⟨t', rfl, h3⟩⟩
  have e0 : l.drop (0#usize : Usize).val = l := by simp
  rw [e0] at h2
  cases res with
  | Ok u => cases u; rw [show s3b_rrel _ _ _ _ = _ from rfl] at h2; simp only [s3b_rrel]; rw [h2]; rfl
  | Err e => obtain ⟨m, hm⟩ := h2; exact ⟨m, by rw [hm]; rfl⟩

/-! ## `depthUpdate` -/
set_option maxHeartbeats 1600000 in
theorem sim.step.depth_update_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hact : ∀ x ∈ s.active.val, x.val < c.pb.objects.val.length)
    (hins : ∀ x ∈ s.active.val, ∀ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).inst.val < s.insts.val.length) :
    ∃ r s', sim.step.depth_update c s = ok (r, s') ∧ s3b_rrel (fun _ => ()) (simStS tn s') r
      (OsuModel.Sim.Sim.depthUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      ∃ ins, s' = { s with insts := ins } ∧ ins.val.length = s.insts.val.length := by
  unfold sim.step.depth_update sim.step.depth_update_loop
  simp only [s3c_fb32_m200, s3c_fb32_256, s3c_fb32_192, s3c_fb32_1_5, bind_ok, float.F32.neg, float.F32.div,
    float.F32.add, s3c_clone_usize]
  unfold OsuModel.Sim.Sim.depthUpdate
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok, OsuModel.Sim.Sim.st, simM_get]
  rw [← Array.forIn_toList]
  apply s3c_wrapI
  have hal : (simStS tn s).active.toList.length = s.active.val.length := by simp [simStS, abs]
  refine s3c_loopR_forIn _ _ _ _ (fun v => simStS tn { s with insts := v }) (fun v => v.val.length = s.insts.val.length)
    (by rw [hal]; exact s.active.property) ?hstep ?hend _ 0#usize s.insts rfl rfl (by simp)
  case hend =>
    intro t q hq
    have : ¬ q < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; rw [hal] at hq; omega
    simp only [sim.step.depth_update_loop.body, this, if_false]
  case hstep =>
    intro t q hq hI q1 hq1
    have hql : q.val < s.active.val.length := by rw [← hal]; exact hq
    have hlq : (simStS tn s).active.toList[q.val]'hq = (s.active.val[q.val]'hql).val := by simp [simStS, abs]
    obtain ⟨x, hx⟩ : ∃ x, s.active.val[q.val]'hql = x := ⟨_, rfl⟩
    have hxm : x ∈ s.active.val := hx ▸ List.getElem_mem hql
    have hxo := hact x hxm
    have hxs : x.val < s.objs.val.length := by rw [hinv.objs_len]; exact hxo
    have hk : (s.objs.val[x.val]'hxs).inst.val < t.val.length := by rw [hI]; exact hins x hxm hxs
    have eo := s3b_topObj tn fo c (simStS tn { s with insts := t }) x.val hxo
    have eos : OsuModel.Sim.Sim.ostate x.val (simCtxS tn fo c) (simStS tn { s with insts := t }) =
        .ok (ostateS (s.objs.val[x.val]'hxs), simStS tn { s with insts := t }) := by
      rw [simS_ostate _ _ _ (by simpa [simStS, abs] using hxs)]; simp [simStS, abs]
    have hqa : q < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; exact hql
    have hadd : q + 1#usize = ok q1 := by
      obtain ⟨z, hz, hv⟩ := usize_add_one q (by have := s.active.property; omega)
      rw [hz]; congr 1; exact UScalar.eq_of_val_eq (by rw [hv, hq1])
    rw [hlq, hx, s3b_bind_ok' _ _ _ _ _ _ eo]
    try dsimp only
    rw [s3b_bind_ok' _ _ _ _ _ _ eos]
    try dsimp only
    simp only [sim.step.depth_update_loop.body, hqa, if_true, vec_index_eq _ _ hql, hx, vec_index_eq _ _ hxo,
      vec_index_eq _ _ hxs, bind_ok]
    cases hK : (c.pb.objects.val[x.val]'hxo).h.kind
    case Circle =>
      have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = .circle := by
        simp [topS, hobjS, hK, kindS]
      have hk' : (s.objs.val[x.val]'hxs).inst.val < t.val.length := hk
      simp only [s3c_dsd_ns, hxo, hK, ne_eq, reduceCtorEq, not_false_eq_true,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok, sim.step.circle_depth_refines,
        sim.step.scale_for_depth_refines, sim.basic.Vec2.sub, sim.basic.Vec2.scale, sim.basic.Vec2.add,
        float.F32.sub, float.F32.mul, float.F32.add, vec_index_mut_eq _ _ hk', s3b_index_mut_set _ _ _ hk', s3c_tset_eq,
        hKs]
      simp only [uncurry_apply_pair]
      simp only [s3b_index_mut_set _ _ _ hk', bind_ok, hadd, uncurry_apply_pair, s3c_vset_set]
      refine Or.inl ⟨_, rfl, by simp only [vec_set_val', List.length_set, hI], ?_⟩
      simp (config := {decide := true}) only [if_false, simM_bind, simM_pure, s3b_ebok]
      exact s3c_modify_yield tn _ s t _ hk' _ _ (s3c_dhf _ _ _ _ _ rfl rfl)
    case Slider =>
      have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = .slider := by
        simp [topS, hobjS, hK, kindS]
      have hk' : (s.objs.val[x.val]'hxs).inst.val < t.val.length := hk
      cases hsd : (c.pb.objects.val[x.val]'hxo).slider with
      | none =>
        obtain ⟨e, he⟩ := s3c_dsd_e c x hxo hK hsd
        have hsl : (topS tn (c.pb.objects.val[x.val]'hxo)).slider = none := by simp [topS, hsd]
        rw [he]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        refine Or.inr ⟨e, t, (by simp [core.convert.FromSame.from]), hI, ?_⟩
        simp (config := {decide := true}) only [hKs, hsl, OsuModel.Sim.Sim.need, if_true, simM_bind]
        exact ⟨_, rfl⟩
      | some sd =>
        have hsl : (topS tn (c.pb.objects.val[x.val]'hxo)).slider = some (abs sd) := by simp [topS, hsd]
        rw [s3c_dsd_s c x hxo hK sd hsd]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, sim.step.slider_depth_refines,
          sim.step.scale_for_depth_refines, sim.basic.Vec2.sub, sim.basic.Vec2.scale, sim.basic.Vec2.add,
          float.F32.sub, float.F32.mul, float.F32.add, vec_index_mut_eq _ _ hk', s3c_tset_eq, hKs, hsl]
        simp only [uncurry_apply_pair]
        simp only [s3b_index_mut_set _ _ _ hk', bind_ok, hadd, uncurry_apply_pair, s3c_vset_set]
        refine Or.inl ⟨_, rfl, by simp only [vec_set_val', List.length_set, hI], ?_⟩
        simp (config := {decide := true}) only [if_true, simM_bind, simM_pure, s3b_ebok, OsuModel.Sim.Sim.need,
          s3c_ite_some]
        exact s3c_modify_yield tn _ s t _ hk' _ _ (s3c_dhf _ _ _ _ _ rfl rfl)
    all_goals
      have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = kindS (c.pb.objects.val[x.val]'hxo).h.kind := rfl
      rw [hK] at hKs
      simp only [kindS] at hKs
      rw [s3c_dsd_ns c x hxo (by simp [hK])]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hadd]
      refine Or.inl ⟨_, rfl, hI, ?_⟩
      simp (config := {decide := true}) only [hKs, if_false, simM_bind, simM_pure, s3b_ebok]


/-- a loop over `l` whose state is the whole Rust `St` and that cannot fail -/
theorem s3c_loopS_forIn {T α : Type} (body : T × Usize → Result (ControlFlow (T × Usize) T))
    (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : T → Prop)
    (hstep : ∀ t (q : Usize) (h : q.val < l.length), Inv t → ∀ q1 : Usize, q1.val = q.val + 1 →
      ∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv t' ∧ F (l[q.val]'h) PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t'))
    (hend : ∀ t (q : Usize), l.length ≤ q.val → body (t, q) = ok (.done t)) (hn : l.length ≤ Usize.max) :
    ∀ n (q : Usize) t, l.length - q.val = n → Inv t → q.val ≤ l.length → ∃ t', loop body (t, q) = ok t' ∧
      forIn (l.drop q.val) PUnit.unit F C (A t) = .ok (PUnit.unit, A t') ∧ Inv t' := by
  intro n
  induction n with
  | zero =>
    intro q t hn0 hI hq
    refine ⟨t, by rw [loop_unfold, hend t q (by omega)]; simp only [bind_ok], ?_, hI⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro q t hn0 hI hq
    have hlt : q.val < l.length := by omega
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
    rw [List.drop_eq_getElem_cons hlt, List.forIn_cons]
    obtain ⟨t', hb, hI', hF⟩ := hstep t q hlt hI q1 hq1v
    obtain ⟨t'', hl, hr, hI''⟩ := ih q1 t' (by omega) hI' (by omega)
    refine ⟨t'', by rw [loop_unfold, hb]; simpa using hl, ?_, hI''⟩
    simp only [simM_bind, hF, Except.bind]
    rw [hq1v] at hr; exact hr

theorem s3c_wrapS (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St)
    (B : sim.state.St × Usize → Result (ControlFlow (sim.state.St × Usize) sim.state.St))
    (l : List Nat) (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (h : ∃ t', loop B (s, 0#usize) = ok t' ∧
      forIn (l.drop (0#usize : Usize).val) PUnit.unit F C (simStS tn s) = .ok (PUnit.unit, simStS tn t') ∧
      ∃ ins, t' = { s with insts := ins } ∧ ins.val.length = s.insts.val.length) :
    ∃ s', loop B (s, 0#usize) = ok s' ∧
      ((forIn l PUnit.unit F C (simStS tn s)).bind fun p => (pure () : OsuModel.Sim.SimM Unit) C p.2) = .ok ((), simStS tn s') ∧
      ∃ ins, s' = { s with insts := ins } ∧ ins.val.length = s.insts.val.length := by
  obtain ⟨t', h1, h2, h3⟩ := h
  refine ⟨t', h1, ?_, h3⟩
  have e0 : l.drop (0#usize : Usize).val = l := by simp
  rw [e0] at h2; rw [h2]; rfl

theorem s3c_mhf (I : sim.state.Inst) (d : sim.basic.Vec2) (D : OsuModel.Sim.Vec2) (hd : (abs d : OsuModel.Sim.Vec2) = D)
    (damp el : F64) :
    ({ (abs I : OsuModel.Sim.Inst) with tf := (OsuModel.Sim.TObj.set (abs I : OsuModel.Sim.Inst).tf .position
        ({ x := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 (abs I : OsuModel.Sim.Inst).tf.pos.x) (F32.toF64 D.x) damp el),
           y := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 (abs I : OsuModel.Sim.Inst).tf.pos.y) (F32.toF64 D.y) damp el) } :
          OsuModel.Sim.Vec2)) } : OsuModel.Sim.Inst) =
      abs ({ I with tf := (s3c_tset I.tf .Position
        ({ x := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 I.tf.pos.x) (F32.toF64 d.x) damp el),
           y := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 I.tf.pos.y) (F32.toF64 d.y) damp el) } :
          sim.basic.Vec2)) } : sim.state.Inst) := by
  subst hd
  show _ = ({ (abs I : OsuModel.Sim.Inst) with tf := (abs (s3c_tset I.tf .Position _) : OsuModel.Sim.TObj) } : OsuModel.Sim.Inst)
  rw [s3c_tset_abs]; rfl


/-- the spec's `magnetUpdate` loop body (Step.lean, verbatim, with `dest0` = `s3c_dest0S`) -/
def s3c_magF (c : OsuModel.Sim.Ctx) (repel : Bool) (cursorPos : OsuModel.Sim.Vec2) (elapsed : F64) (i : Nat) (_ : PUnit.{1}) :
    OsuModel.Sim.SimM (ForInStep PUnit.{1}) := do
  let o := (← OsuModel.Sim.Sim.topObj i)
  let os ← OsuModel.Sim.Sim.ostate i
  let k := os.inst
  let ins ← OsuModel.Sim.Sim.instOf k
  let pos := ins.tf.pos
  let headJudged ← if o.h.kind == .slider then OsuModel.Sim.Sim.judged (i, ((← OsuModel.Sim.Sim.headIdxOf i) : Int))
    else pure false
  let dest0 : OsuModel.Sim.Vec2 := s3c_dest0S repel o pos cursorPos
  let target? : Option OsuModel.Sim.Vec2 := match o.h.kind with
    | .circle => some dest0
    | .slider => some (if headJudged then dest0 - ins.ballPos else dest0)
    | _ => none
  if let some dest := target? then
    let damp : F64 := if repel
      then F32.toF64 (OsuTK.Vector2.distance (OsuModel.Sim.toTK pos) (OsuModel.Sim.toTK cursorPos)) /
        (0.04 * F32.toF64 c.cfg.repelStrength + 0.04)
      else Framework.Interpolation.lerp 3000 40 (F32.toF64 c.cfg.magnetStrength)
    let x := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 pos.x) (F32.toF64 dest.x) damp elapsed)
    let y := F64.toF32 (Framework.Interpolation.dampContinuously (F32.toF64 pos.y) (F32.toF64 dest.y) damp elapsed)
    OsuModel.Sim.Sim.modifyInst k fun ins => { ins with tf := ins.tf.set .position ⟨x, y⟩ }
  return .yield PUnit.unit

set_option maxHeartbeats 1600000 in
theorem sim.step.magnet_one_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (ins : alloc.vec.Vec sim.state.Inst)
    (x : Usize) (repel : Bool) (el : F64) (hinv : SimInv c s) (hxo : x.val < c.pb.objects.val.length)
    (hxs : x.val < s.objs.val.length) (hk : (s.objs.val[x.val]'hxs).inst.val < ins.val.length)
    (hhd : (c.pb.objects.val[x.val]'hxo).h.kind = .Slider →
      ∃ hhi : x.val < c.head_idx.val.length, (c.head_idx.val[x.val]'hhi).val < (c.pb.objects.val[x.val]'hxo).nested.val.length) :
    ∃ ins', sim.step.magnet_one c { s with insts := ins } x repel s.cursor_pos el = ok { s with insts := ins' } ∧
      ins'.val.length = ins.val.length ∧
      s3c_magF (simCtxS tn fo c) repel (simStS tn s).cursorPos el x.val PUnit.unit (simCtxS tn fo c)
        (simStS tn { s with insts := ins }) = .ok (.yield PUnit.unit, simStS tn { s with insts := ins' }) := by
  have eo := s3b_topObj tn fo c (simStS tn { s with insts := ins }) x.val hxo
  have eos : OsuModel.Sim.Sim.ostate x.val (simCtxS tn fo c) (simStS tn { s with insts := ins }) =
      .ok (ostateS (s.objs.val[x.val]'hxs), simStS tn { s with insts := ins }) := by
    rw [simS_ostate _ _ _ (by simpa [simStS, abs] using hxs)]; simp [simStS, abs]
  have ein := s3a_instOf tn fo c { s with insts := ins } _ hk
  have hk' : (s.objs.val[x.val]'hxs).inst.val < ins.val.length := hk
  unfold s3c_magF
  simp only [simM_bind, eo, eos, s3b_ebok]
  simp only [show (ostateS (s.objs.val[x.val]'hxs)).inst = (s.objs.val[x.val]'hxs).inst.val from rfl, ein, s3b_ebok]
  unfold sim.step.magnet_one sim.step.magnet_head_judged
  simp only [vec_index_eq _ _ hxs, vec_index_eq _ _ hxo, vec_index_eq _ _ hk', bind_ok]
  obtain ⟨d, hd1, hd2⟩ := s3c_dest0_rust tn repel (c.pb.objects.val[x.val]'hxo) ((ins.val[(s.objs.val[x.val]'hxs).inst.val]'hk').tf.pos) s.cursor_pos
  rw [hd1]
  simp only [bind_ok]
  cases hK : (c.pb.objects.val[x.val]'hxo).h.kind
  case Circle =>
    have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = .circle := by
      simp [topS, hobjS, hK, kindS]
    simp (config := {decide := true}) only [kind_eq_ok, kindS, if_true, if_false, sim.step.magnet_damp_refines, net.framework.damp_continuously_refines, float.F32.to_f64,
      float.F64.to_f32, vec_index_mut_eq _ _ hk', s3c_tset_eq, bind_ok, uncurry_apply_pair, hKs]
    refine ⟨_, rfl, by simp only [vec_set_val', List.length_set], ?_⟩
    simp (config := {decide := true}) only [hKs, if_false, simM_bind, simM_pure, s3b_ebok]
    exact s3c_modify_yield tn _ s ins _ hk' _ _ (s3c_mhf _ d _ hd2 _ _)
  case Slider =>
    have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = .slider := by
      simp [topS, hobjS, hK, kindS]
    obtain ⟨hhi, hhb⟩ := hhd hK
    have hsm := hinv.nested_small _ (List.getElem_mem hxo)
    have hc : (UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)).val = ((c.head_idx.val[x.val]'hhi).val : Int) := by
      rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
    have hsr : simSRefOk { s with insts := ins } ⟨x, UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)⟩ := by
      refine ⟨hxs, fun _ => ?_⟩
      show (UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)).val.toNat < (s.objs.val[x.val]'hxs).nested.val.length
      rw [hc, hinv.nested_len _ hxs hxo]; simpa using hhb
    obtain ⟨b, hb1, eb1⟩ := sim.step.judged_refines tn fo c { s with insts := ins } _ hsr
    have habs : (abs (⟨x, UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
        (x.val, ((c.head_idx.val[x.val]'hhi).val : Int)) := by simp [abs, hc]
    rw [habs] at eb1
    have ehead : OsuModel.Sim.Sim.headIdxOf x.val (simCtxS tn fo c) (simStS tn { s with insts := ins }) =
        .ok ((c.head_idx.val[x.val]'hhi).val, simStS tn { s with insts := ins }) := by
      have hhi' : x.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
      simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]
    simp (config := {decide := true}) only [kind_eq_ok, kindS, if_true, if_false, vec_index_eq _ _ hhi, lift, bind_ok,
      hb1]
    cases b
    · simp (config := {decide := true}) only [if_true, if_false, sim.step.magnet_damp_refines, net.framework.damp_continuously_refines, float.F32.to_f64,
        float.F64.to_f32, vec_index_mut_eq _ _ hk', s3c_tset_eq, bind_ok, uncurry_apply_pair, hKs, Bool.false_eq_true]
      refine ⟨_, rfl, by simp only [vec_set_val', List.length_set], ?_⟩
      simp (config := {decide := true}) only [hKs, if_true, simM_bind, simM_pure, s3b_ebok, ehead, eb1]
      exact s3c_modify_yield tn _ s ins _ hk' _ _ (s3c_mhf _ d _ hd2 _ _)
    · simp (config := {decide := true}) only [if_true, if_false, sim.step.magnet_damp_refines, net.framework.damp_continuously_refines, float.F32.to_f64,
        float.F64.to_f32, vec_index_mut_eq _ _ hk', s3c_tset_eq, bind_ok, uncurry_apply_pair, hKs, sim.basic.Vec2.sub,
        float.F32.sub]
      refine ⟨_, rfl, by simp only [vec_set_val', List.length_set], ?_⟩
      simp (config := {decide := true}) only [hKs, if_true, simM_bind, simM_pure, s3b_ebok, ehead, eb1]
      exact s3c_modify_yield tn _ s ins _ hk' _ _ (s3c_mhf _ ⟨_, _⟩
        (s3c_dest0S repel (topS tn (c.pb.objects.val[x.val]'hxo))
          (abs ((ins.val[(s.objs.val[x.val]'hxs).inst.val]'hk').tf.pos)) (abs s.cursor_pos) -
          (abs (ins.val[(s.objs.val[x.val]'hxs).inst.val]'hk') : OsuModel.Sim.Inst).ballPos) (by rw [← hd2]; rfl) _ _)
  all_goals
    have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = kindS (c.pb.objects.val[x.val]'hxo).h.kind := rfl
    rw [hK] at hKs
    simp only [kindS] at hKs
    simp (config := {decide := true}) only [kind_eq_ok, kindS, if_true, if_false, bind_ok]
    refine ⟨ins, rfl, rfl, ?_⟩
    simp (config := {decide := true}) only [hKs, if_false, simM_bind, simM_pure, s3b_ebok]


/-! ## named `_refines` for the remaining `magnetUpdate` / `depthUpdate` callees -/
theorem sim.step.depth_slider_duration_refines (c : sim.state.Ctx) (i : Usize) (hi : i.val < c.pb.objects.val.length) :
    ∃ r, sim.step.depth_slider_duration c i = ok r ∧
      ((c.pb.objects.val[i.val]'hi).h.kind ≠ .Slider → r = .Ok 0) ∧
      (∀ sd, (c.pb.objects.val[i.val]'hi).h.kind = .Slider → (c.pb.objects.val[i.val]'hi).slider = some sd →
        r = .Ok sd.duration) ∧
      ((c.pb.objects.val[i.val]'hi).h.kind = .Slider → (c.pb.objects.val[i.val]'hi).slider = none → ∃ e, r = .Err e) := by
  by_cases hk : (c.pb.objects.val[i.val]'hi).h.kind = .Slider
  · cases hs : (c.pb.objects.val[i.val]'hi).slider with
    | none =>
      obtain ⟨e, he⟩ := s3c_dsd_e c i hi hk hs
      exact ⟨_, he, fun h => absurd hk h, fun _ _ h => (by cases h), fun _ _ => ⟨e, rfl⟩⟩
    | some sd =>
      exact ⟨_, s3c_dsd_s c i hi hk sd hs, fun h => absurd hk h, fun sd' _ h => (by cases h; rfl), fun _ h => (by cases h)⟩
  · exact ⟨_, s3c_dsd_ns c i hi hk, fun _ => rfl, fun _ h => absurd h hk, fun h => absurd h hk⟩

theorem sim.step.repel_slider_clamp_loop_refines (sd : sim.playable.SliderData) (a b c e : F32) (j : Usize)
    (hj : j.val ≤ sd.path.val.length) :
    sim.step.repel_slider_clamp_loop sd a b c e j = ok ((sd.path.val.drop j.val).foldl s3c_bbR (a, b, c, e)) :=
  s3c_rscl sd _ j a b c e rfl hj

/-- the spec's slider bounds clamp of `magnetUpdate` (repel; Step.lean, verbatim) -/
def s3c_rscS (sd : OsuModel.Sim.SliderData) (radius : F64) (d : OsuModel.Sim.Vec2) : OsuModel.Sim.Vec2 :=
  let cl (v lo hi : OsuModel.Sim.Vec2) : OsuModel.Sim.Vec2 :=
    OsuModel.Sim.ofTK (OsuTK.Vector2.clamp (OsuModel.Sim.toTK v) (OsuModel.Sim.toTK lo) (OsuModel.Sim.toTK hi))
  let r := F64.toF32 radius
  let (mnX, mxX, mnY, mxY) := sd.path.foldl s3c_bbS (F32.posInf, F32.negInf, F32.posInf, F32.negInf)
  let left := -(mnX - r)
  let right := (512 : F32) - (mxX + r)
  let top := -(mnY - r)
  let bottom := (384 : F32) - (mxY + r)
  let w := right - left
  let hh := bottom - top
  cl d ⟨left, top⟩ ⟨left + w, top + hh⟩

theorem sim.step.repel_slider_clamp_refines (sd : sim.playable.SliderData) (radius : F64) (d : sim.basic.Vec2) :
    ∃ r, sim.step.repel_slider_clamp sd radius d = ok r ∧
      (abs r : OsuModel.Sim.Vec2) = s3c_rscS (abs sd) radius (abs d) := by
  have hl := s3c_rscl sd _ 0#usize F32.posInf F32.negInf F32.posInf F32.negInf rfl (by simp)
  simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hl
  simp [sim.transforms.to_tk, sim.transforms.of_tk, net.osutk.v2, net.osutk.v2_clamp_refines,
    sim.step.repel_slider_clamp, hl, float.F64.to_f32, float.F32.neg, float.F32.add, float.F32.sub]
  simp only [s3c_rscS]
  have ef : ((abs sd : OsuModel.Sim.SliderData).path.foldl s3c_bbS (F32.posInf, F32.negInf, F32.posInf, F32.negInf)) =
      sd.path.val.foldl s3c_bbR (F32.posInf, F32.negInf, F32.posInf, F32.negInf) := by
    rw [← s3c_bb_fold]
    show Array.foldl s3c_bbS _ (List.map (fun v => (abs v : OsuModel.Sim.Vec2)) sd.path.val).toArray = _
    rw [← Array.foldl_toList]
  rw [ef]
  generalize sd.path.val.foldl s3c_bbR (F32.posInf, F32.negInf, F32.posInf, F32.negInf) = X
  obtain ⟨a, b, c, e⟩ := X
  simp only [uncurry_apply_pair]
  refine ⟨_, rfl, ?_⟩
  try simp only [s3c_f512, s3c_f384]
  rfl

theorem sim.step.repel_dest_refines (tn) (o : sim.playable.TopObj) (pos cp : sim.basic.Vec2) :
    ∃ d, sim.step.repel_dest o pos cp = ok d ∧
      (abs d : OsuModel.Sim.Vec2) = s3c_dest0S true (topS tn o) (abs pos) (abs cp) := by
  simpa using s3c_dest0_rust tn true o pos cp

theorem sim.step.magnet_head_judged_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (x : Usize) (hinv : SimInv c s)
    (hxo : x.val < c.pb.objects.val.length)
    (hhd : (c.pb.objects.val[x.val]'hxo).h.kind = .Slider →
      ∃ hhi : x.val < c.head_idx.val.length, (c.head_idx.val[x.val]'hhi).val < (c.pb.objects.val[x.val]'hxo).nested.val.length) :
    ∃ b, sim.step.magnet_head_judged c s x = ok b ∧
      (if (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind == .slider then
        (do let hj ← OsuModel.Sim.Sim.headIdxOf x.val; OsuModel.Sim.Sim.judged (x.val, (hj : Int)))
        else (pure false : OsuModel.Sim.SimM Bool)) (simCtxS tn fo c) (simStS tn s) = .ok (b, simStS tn s) := by
  have hxs : x.val < s.objs.val.length := by rw [hinv.objs_len]; exact hxo
  unfold sim.step.magnet_head_judged
  by_cases hK : (c.pb.objects.val[x.val]'hxo).h.kind = .Slider
  · have hKs : (topS tn (c.pb.objects.val[x.val]'hxo)).h.kind = .slider := by
      simp [topS, hobjS, hK, kindS]
    obtain ⟨hhi, hhb⟩ := hhd hK
    have hsm := hinv.nested_small _ (List.getElem_mem hxo)
    have hc : (UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)).val = ((c.head_idx.val[x.val]'hhi).val : Int) := by
      rw [UScalar.hcast_val_eq]; simp; rw [Int.bmod_eq_of_le] <;> omega
    have hsr : simSRefOk s ⟨x, UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)⟩ := by
      refine ⟨hxs, fun _ => ?_⟩
      show (UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)).val.toNat < (s.objs.val[x.val]'hxs).nested.val.length
      rw [hc, hinv.nested_len _ hxs hxo]; simpa using hhb
    obtain ⟨b, hb1, eb1⟩ := sim.step.judged_refines tn fo c s _ hsr
    have habs : (abs (⟨x, UScalar.hcast .I64 (c.head_idx.val[x.val]'hhi)⟩ : sim.step.Ref) : Nat × Int) =
        (x.val, ((c.head_idx.val[x.val]'hhi).val : Int)) := by simp [abs, hc]
    rw [habs] at eb1
    have ehead : OsuModel.Sim.Sim.headIdxOf x.val (simCtxS tn fo c) (simStS tn s) =
        .ok ((c.head_idx.val[x.val]'hhi).val, simStS tn s) := by
      have hhi' : x.val < (simCtxS tn fo c).headIdx.size := by simpa [simCtxS, abs] using hhi
      simp [OsuModel.Sim.Sim.headIdxOf, OsuModel.Sim.Sim.getA, OsuModel.Sim.Sim.ctx, hhi', Except.bind, simCtxS, abs, hhi]
    refine ⟨b, ?_, ?_⟩
    · simp (config := {decide := true}) only [vec_index_eq _ _ hxo, hK, kind_eq_ok, kindS, if_true, vec_index_eq _ _ hhi,
        lift, bind_ok, hb1]
    · simp (config := {decide := true}) only [hKs, if_true, simM_bind, ehead, s3b_ebok, eb1]
  · have hKs : ((topS tn (c.pb.objects.val[x.val]'hxo)).h.kind == .slider) = false := by
      show (kindS (c.pb.objects.val[x.val]'hxo).h.kind == .slider) = false
      cases hk : (c.pb.objects.val[x.val]'hxo).h.kind <;> simp_all (config := {decide := true}) [kindS]
    have hKr : (kindS (c.pb.objects.val[x.val]'hxo).h.kind == kindS .Slider) = false := hKs
    refine ⟨false, ?_, ?_⟩
    · simp only [vec_index_eq _ _ hxo, kind_eq_ok, hKr, bind_ok, Bool.false_eq_true, if_false]
    · simp only [hKs, Bool.false_eq_true, if_false, simM_pure]

/-! ## `magnetUpdate` -/
set_option maxHeartbeats 1600000 in
theorem sim.step.magnet_update_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (repel : Bool) (hinv : SimInv c s)
    (hact : ∀ x ∈ s.active.val, x.val < c.pb.objects.val.length)
    (hins : ∀ x ∈ s.active.val, ∀ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).inst.val < s.insts.val.length)
    (hhd : ∀ x ∈ s.active.val, ∀ h : x.val < c.pb.objects.val.length, (c.pb.objects.val[x.val]'h).h.kind = .Slider →
      ∃ hhi : x.val < c.head_idx.val.length, (c.head_idx.val[x.val]'hhi).val < (c.pb.objects.val[x.val]'h).nested.val.length)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) :
    ∃ s', sim.step.magnet_update c s repel = ok s' ∧
      OsuModel.Sim.Sim.magnetUpdate repel (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      ∃ ins, s' = { s with insts := ins } ∧ ins.val.length = s.insts.val.length := by
  have hstep' : (simStS tn s).k ≠ 0 → (simStS tn s).k - 1 < (simCtxS tn fo c).steps.size := by
    simpa [simStS, simCtxS, abs] using hstep
  unfold sim.step.magnet_update sim.step.magnet_update_loop
  rw [s3b_elapsed_rust tn fo c s hstep]
  simp only [bind_ok, uncurry_apply_pair, s3c_clone_usize]
  unfold OsuModel.Sim.Sim.magnetUpdate
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok, OsuModel.Sim.Sim.st, simM_get]
  rw [s3b_elapsedNow _ _ hstep']
  simp only [s3b_ebok]
  rw [← Array.forIn_toList]
  apply s3c_wrapS
  have hal : (simStS tn s).active.toList.length = s.active.val.length := by simp [simStS, abs]
  refine s3c_loopS_forIn _ _ _ _ (simStS tn) (fun t => ∃ ins, t = { s with insts := ins } ∧ ins.val.length = s.insts.val.length)
    ?hstep ?hend (by rw [hal]; exact s.active.property) _ 0#usize s rfl ⟨s.insts, rfl, rfl⟩ (by simp)
  case hend =>
    intro t q hq
    have : ¬ q < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; rw [hal] at hq; omega
    simp only [sim.step.magnet_update_loop.body, this, if_false]
  case hstep =>
    rintro t q hq ⟨ins, rfl, hI⟩ q1 hq1
    have hql : q.val < s.active.val.length := by rw [← hal]; exact hq
    have hlq : (simStS tn s).active.toList[q.val]'hq = (s.active.val[q.val]'hql).val := by simp [simStS, abs]
    obtain ⟨x, hx⟩ : ∃ x, s.active.val[q.val]'hql = x := ⟨_, rfl⟩
    have hxm : x ∈ s.active.val := hx ▸ List.getElem_mem hql
    have hxo := hact x hxm
    have hxs : x.val < s.objs.val.length := by rw [hinv.objs_len]; exact hxo
    have hk : (s.objs.val[x.val]'hxs).inst.val < ins.val.length := by rw [hI]; exact hins x hxm hxs
    have hqa : q < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; exact hql
    have hadd : q + 1#usize = ok q1 := by
      obtain ⟨z, hz, hv⟩ := usize_add_one q (by have := s.active.property; omega)
      rw [hz]; congr 1; exact UScalar.eq_of_val_eq (by rw [hv, hq1])
    obtain ⟨ins', h1, h2, h3⟩ := sim.step.magnet_one_refines tn fo c s ins x repel
      (if s.k.val = 0 then 0 else s.t - ((simCtxS tn fo c).steps[s.k.val - 1]!).time) hinv hxo hxs hk (hhd x hxm hxo)
    refine ⟨_, by simp only [sim.step.magnet_update_loop.body, hqa, if_true, vec_index_eq _ _ hql, hx, bind_ok]; rw [h1]; simp only [bind_ok, hadd],
      ⟨ins', rfl, h2.trans hI⟩, ?_⟩
    rw [hlq, hx]
    exact h3

end OsuProofs
