/-
sim3d: what `depth_update` / `magnet_update` do to the instances: only the position / scale of each transform object
changes (`s3d_TfPS`); needed to carry the transform invariant `s3b_TfInv` (inside `SimARInv`) across the playfield hooks.
`s3d_depth_ps`, `s3d_magnet_one_ps` and `s3d_magnet_ps` are sim3c's `depth_update_refines`, `magnet_one_refines` and
`magnet_update_refines` (Sim3/SC_Upd.lean), copied with the length invariant strengthened to `s3d_TfPS`.
-/
import OsuProofs.Sim3.SC_Upd
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- `v'` differs from `v` only in the position / scale of each instance's transform object -/
def s3d_TfPS (v v' : alloc.vec.Vec sim.state.Inst) : Prop :=
  v'.val.length = v.val.length ∧ ∀ j (h : j < v.val.length) (h' : j < v'.val.length),
    ∃ p q, v'.val[j]'h' = { v.val[j]'h with tf := { (v.val[j]'h).tf with pos := p, scale := q } }

theorem s3d_TfPS_refl (v : alloc.vec.Vec sim.state.Inst) : s3d_TfPS v v :=
  ⟨rfl, fun j h _ => ⟨(v.val[j]'h).tf.pos, (v.val[j]'h).tf.scale, rfl⟩⟩

theorem s3d_TfPS_trans {v1 v2 v3 : alloc.vec.Vec sim.state.Inst} (h1 : s3d_TfPS v1 v2) (h2 : s3d_TfPS v2 v3) :
    s3d_TfPS v1 v3 := by
  refine ⟨h2.1.trans h1.1, fun j h h' => ?_⟩
  have hm : j < v2.val.length := by rw [h1.1]; exact h
  obtain ⟨p1, q1, e1⟩ := h1.2 j h hm
  obtain ⟨p2, q2, e2⟩ := h2.2 j hm h'
  refine ⟨p2, q2, ?_⟩
  rw [e2]; simp only [e1]

theorem s3d_TfPS_set (v t : alloc.vec.Vec sim.state.Inst) (k : Usize) (hk : k.val < t.val.length) (X : sim.state.Inst)
    (hX : ∃ p q, X = { t.val[k.val]'hk with tf := { (t.val[k.val]'hk).tf with pos := p, scale := q } })
    (h : s3d_TfPS v t) : s3d_TfPS v (t.set k X) := by
  have hv : (t.set k X).val = t.val.set k.val X := vec_set_val' _ _ _
  refine ⟨by rw [hv, List.length_set]; exact h.1, fun j hj hj' => ?_⟩
  have hjt : j < t.val.length := by rw [h.1]; exact hj
  obtain ⟨p, q, e⟩ := h.2 j hj hjt
  have hg : (t.set k X).val[j]'hj' = if k.val = j then X else t.val[j]'hjt := by
    simp only [hv, List.getElem_set]
  rw [hg]
  split
  · rename_i hkj; subst hkj
    obtain ⟨p', q', eX⟩ := hX
    refine ⟨p', q', ?_⟩
    rw [eX]; simp only [e]
  · exact ⟨p, q, e⟩

theorem s3d_tset_ps (o : sim.transforms.TObj) (m : sim.transforms.Member) (w : sim.basic.Vec2)
    (hm : m = .Position ∨ m = .Scale) : ∃ p q, s3c_tset o m w = { o with pos := p, scale := q } := by
  have h := s3c_tset_eq o m w
  rcases hm with rfl | rfl
  · unfold sim.transforms.tobj_set at h
    simp only [sim.basic.Vec2.eq, float.F32.eq] at h
    cases h1 : (o.pos.x == w.x) <;> cases h2 : (o.pos.y == w.y) <;> simp only [h1, h2, bind_ok, Bool.false_eq_true,
      if_false, if_true, ↓reduceIte] at h <;>
      first | exact ⟨o.pos, o.scale, (Result.ok_injective h).symm⟩ | exact ⟨w, o.scale, (Result.ok_injective h).symm⟩
  · unfold sim.transforms.tobj_set at h
    simp only [sim.basic.Vec2.eq, float.F32.eq] at h
    cases h1 : (o.scale.x == w.x) <;> cases h2 : (o.scale.y == w.y) <;> simp only [h1, h2, bind_ok, Bool.false_eq_true,
      if_false, if_true, ↓reduceIte] at h <;>
      first | exact ⟨o.pos, o.scale, (Result.ok_injective h).symm⟩ | exact ⟨o.pos, w, (Result.ok_injective h).symm⟩

theorem s3d_psX1 (Y : sim.state.Inst) (w : sim.basic.Vec2) :
    ∃ p q, ({ Y with tf := s3c_tset Y.tf .Position w } : sim.state.Inst) =
      { Y with tf := { Y.tf with pos := p, scale := q } } := by
  obtain ⟨p, q, e⟩ := s3d_tset_ps Y.tf .Position w (Or.inl rfl)
  exact ⟨p, q, by rw [e]⟩

theorem s3d_psX2 (Y : sim.state.Inst) (w w' : sim.basic.Vec2) :
    ∃ p q, ({ Y with tf := s3c_tset (s3c_tset Y.tf .Position w) .Scale w' } : sim.state.Inst) =
      { Y with tf := { Y.tf with pos := p, scale := q } } := by
  obtain ⟨p, q, e⟩ := s3d_tset_ps Y.tf .Position w (Or.inl rfl)
  obtain ⟨p', q', e'⟩ := s3d_tset_ps (s3c_tset Y.tf .Position w) .Scale w' (Or.inr rfl)
  refine ⟨p', q', ?_⟩
  rw [e', e]

theorem s3d_wrapI (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St)
    (B : alloc.vec.Vec sim.state.Inst × Usize → Result (ControlFlow (alloc.vec.Vec sim.state.Inst × Usize)
      (core.result.Result Unit sim.err.SimErr × alloc.vec.Vec sim.state.Inst)))
    (l : List Nat) (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (h : ∃ res t', loop B (s.insts, 0#usize) = ok (res, t') ∧
      s3b_rrel (fun _ => PUnit.unit) (simStS tn { s with insts := t' }) res
        (forIn (l.drop (0#usize : Usize).val) PUnit.unit F C (simStS tn { s with insts := s.insts })) ∧
      s3d_TfPS s.insts t') :
    ∃ r s', (do let (r, v) ← loop B (s.insts, 0#usize); ok (r, { s with insts := v })) = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r ((forIn l PUnit.unit F C (simStS tn s)).bind fun p => (pure () : OsuModel.Sim.SimM Unit) C p.2) ∧
      ∃ ins, s' = { s with insts := ins } ∧ s3d_TfPS s.insts ins := by
  obtain ⟨res, t', h1, h2, h3⟩ := h
  obtain ⟨r, s', e1, e2, -⟩ := s3c_wrapI tn C s B l F ⟨res, t', h1, h2, h3.1⟩
  have e1' := e1
  rw [h1] at e1'; simp only [bind_ok] at e1'
  have hs' := (Result.ok_injective e1').symm
  simp only [Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  exact ⟨_, _, e1, e2, t', rfl, h3⟩

theorem s3d_wrapS (tn) (C : OsuModel.Sim.Ctx) (s : sim.state.St)
    (B : sim.state.St × Usize → Result (ControlFlow (sim.state.St × Usize) sim.state.St))
    (l : List Nat) (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (h : ∃ t', loop B (s, 0#usize) = ok t' ∧
      forIn (l.drop (0#usize : Usize).val) PUnit.unit F C (simStS tn s) = .ok (PUnit.unit, simStS tn t') ∧
      ∃ ins, t' = { s with insts := ins } ∧ s3d_TfPS s.insts ins) :
    ∃ s', loop B (s, 0#usize) = ok s' ∧
      ((forIn l PUnit.unit F C (simStS tn s)).bind fun p => (pure () : OsuModel.Sim.SimM Unit) C p.2) = .ok ((), simStS tn s') ∧
      ∃ ins, s' = { s with insts := ins } ∧ s3d_TfPS s.insts ins := by
  obtain ⟨t', h1, h2, h3⟩ := h
  refine ⟨t', h1, ?_, h3⟩
  have e0 : l.drop (0#usize : Usize).val = l := by simp
  rw [e0] at h2; rw [h2]; rfl

set_option maxHeartbeats 1600000 in
theorem s3d_depth_ps (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hact : ∀ x ∈ s.active.val, x.val < c.pb.objects.val.length)
    (hins : ∀ x ∈ s.active.val, ∀ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).inst.val < s.insts.val.length) :
    ∃ r s', sim.step.depth_update c s = ok (r, s') ∧ s3b_rrel (fun _ => ()) (simStS tn s') r
      (OsuModel.Sim.Sim.depthUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      ∃ ins, s' = { s with insts := ins } ∧ s3d_TfPS s.insts ins := by
  unfold sim.step.depth_update sim.step.depth_update_loop
  simp only [s3c_fb32_m200, s3c_fb32_256, s3c_fb32_192, s3c_fb32_1_5, bind_ok, float.F32.neg, float.F32.div,
    float.F32.add, s3c_clone_usize]
  unfold OsuModel.Sim.Sim.depthUpdate
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, s3b_ebok, OsuModel.Sim.Sim.st, simM_get]
  rw [← Array.forIn_toList]
  apply s3d_wrapI
  have hal : (simStS tn s).active.toList.length = s.active.val.length := by simp [simStS, abs]
  refine s3c_loopR_forIn _ _ _ _ (fun v => simStS tn { s with insts := v }) (fun v => s3d_TfPS s.insts v)
    (by rw [hal]; exact s.active.property) ?hstep ?hend _ 0#usize s.insts rfl (s3d_TfPS_refl _) (by simp)
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
    have hk : (s.objs.val[x.val]'hxs).inst.val < t.val.length := by rw [hI.1]; exact hins x hxm hxs
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
      refine Or.inl ⟨_, rfl, s3d_TfPS_set _ _ _ hk' _ (s3d_psX2 _ _ _) hI, ?_⟩
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
        refine Or.inl ⟨_, rfl, s3d_TfPS_set _ _ _ hk' _ (s3d_psX2 _ _ _) hI, ?_⟩
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



theorem s3d_magnet_one_ps (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (ins : alloc.vec.Vec sim.state.Inst)
    (x : Usize) (repel : Bool) (el : F64) (hinv : SimInv c s) (hxo : x.val < c.pb.objects.val.length)
    (hxs : x.val < s.objs.val.length) (hk : (s.objs.val[x.val]'hxs).inst.val < ins.val.length)
    (hhd : (c.pb.objects.val[x.val]'hxo).h.kind = .Slider →
      ∃ hhi : x.val < c.head_idx.val.length, (c.head_idx.val[x.val]'hhi).val < (c.pb.objects.val[x.val]'hxo).nested.val.length) :
    ∃ ins', sim.step.magnet_one c { s with insts := ins } x repel s.cursor_pos el = ok { s with insts := ins' } ∧
      s3d_TfPS ins ins' ∧
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
    refine ⟨_, rfl, s3d_TfPS_set _ _ _ hk' _ (s3d_psX1 _ _) (s3d_TfPS_refl _), ?_⟩
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
      refine ⟨_, rfl, s3d_TfPS_set _ _ _ hk' _ (s3d_psX1 _ _) (s3d_TfPS_refl _), ?_⟩
      simp (config := {decide := true}) only [hKs, if_true, simM_bind, simM_pure, s3b_ebok, ehead, eb1]
      exact s3c_modify_yield tn _ s ins _ hk' _ _ (s3c_mhf _ d _ hd2 _ _)
    · simp (config := {decide := true}) only [if_true, if_false, sim.step.magnet_damp_refines, net.framework.damp_continuously_refines, float.F32.to_f64,
        float.F64.to_f32, vec_index_mut_eq _ _ hk', s3c_tset_eq, bind_ok, uncurry_apply_pair, hKs, sim.basic.Vec2.sub,
        float.F32.sub]
      refine ⟨_, rfl, s3d_TfPS_set _ _ _ hk' _ (s3d_psX1 _ _) (s3d_TfPS_refl _), ?_⟩
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
    refine ⟨ins, rfl, s3d_TfPS_refl _, ?_⟩
    simp (config := {decide := true}) only [hKs, if_false, simM_bind, simM_pure, s3b_ebok]


set_option maxHeartbeats 1600000 in
theorem s3d_magnet_ps (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (repel : Bool) (hinv : SimInv c s)
    (hact : ∀ x ∈ s.active.val, x.val < c.pb.objects.val.length)
    (hins : ∀ x ∈ s.active.val, ∀ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).inst.val < s.insts.val.length)
    (hhd : ∀ x ∈ s.active.val, ∀ h : x.val < c.pb.objects.val.length, (c.pb.objects.val[x.val]'h).h.kind = .Slider →
      ∃ hhi : x.val < c.head_idx.val.length, (c.head_idx.val[x.val]'hhi).val < (c.pb.objects.val[x.val]'h).nested.val.length)
    (hstep : s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) :
    ∃ s', sim.step.magnet_update c s repel = ok s' ∧
      OsuModel.Sim.Sim.magnetUpdate repel (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      ∃ ins, s' = { s with insts := ins } ∧ s3d_TfPS s.insts ins := by
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
  apply s3d_wrapS
  have hal : (simStS tn s).active.toList.length = s.active.val.length := by simp [simStS, abs]
  refine s3c_loopS_forIn _ _ _ _ (simStS tn) (fun t => ∃ ins, t = { s with insts := ins } ∧ s3d_TfPS s.insts ins)
    ?hstep ?hend (by rw [hal]; exact s.active.property) _ 0#usize s rfl ⟨s.insts, rfl, s3d_TfPS_refl _⟩ (by simp)
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
    have hk : (s.objs.val[x.val]'hxs).inst.val < ins.val.length := by rw [hI.1]; exact hins x hxm hxs
    have hqa : q < alloc.vec.Vec.len s.active := by rw [vec_lt_len_iff]; exact hql
    have hadd : q + 1#usize = ok q1 := by
      obtain ⟨z, hz, hv⟩ := usize_add_one q (by have := s.active.property; omega)
      rw [hz]; congr 1; exact UScalar.eq_of_val_eq (by rw [hv, hq1])
    obtain ⟨ins', h1, h2, h3⟩ := s3d_magnet_one_ps tn fo c s ins x repel
      (if s.k.val = 0 then 0 else s.t - ((simCtxS tn fo c).steps[s.k.val - 1]!).time) hinv hxo hxs hk (hhd x hxm hxo)
    refine ⟨_, by simp only [sim.step.magnet_update_loop.body, hqa, if_true, vec_index_eq _ _ hql, hx, bind_ok]; rw [h1]; simp only [bind_ok, hadd],
      ⟨ins', rfl, s3d_TfPS_trans hI h2⟩, ?_⟩
    rw [hlq, hx]
    exact h3

end OsuProofs
