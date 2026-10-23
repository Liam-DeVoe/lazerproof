/-
sim3a (D37): `sim::step` mouse-move handlers (Rust loops over `St.active`) refine `OsuModel.Sim.Sim`
`sliderMouseMove` / `spinnerMouseMove` (Step.lean): each alive slider (spinner) gets `slider_mouse` (`spin_mouse`)
set; only `objs` changes (same length, same nested arrays), `insts`/`future_order` untouched.
-/
import OsuProofs.Sim3.SA_Track
import OsuProofs.Sim3.SB_State
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

/-- the loop-exit tuple of the Aeneas `St` loops (all fields, in declaration order) -/
def s3aTup (S : sim.state.St) := (S.k, S.t, S.objs, S.first_lifetime_update, S.next_future, S.future_order, S.active, S.dict_slots, S.free_list, S.child_counter, S.mouse_valid, S.mouse, S.last_replay, S.pressed, S.score, S.health, S.score_rp, S.health_rp, S.out, S.speed, S.as_target, S.as_recent, S.as_seen, S.clock_rate, S.relax_down, S.relax_was_left, S.relax_last, S.ap_frame, S.block_last, S.block_idx, S.insts, S.pools, S.br_rot, S.theta, S.cursor_pos)

/-- `forIn` over a list in `SimM` whose body is a Rust state step `R` (under an invariant `Q`) -/
theorem s3a_forIn_rust {X Y : Type} (tn : Nat → String) (C : OsuModel.Sim.Ctx) (g : X → Y) (l : List X)
    (F : Y → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (R : X → sim.state.St → sim.state.St)
    (Q : sim.state.St → Prop)
    (hF : ∀ x ∈ l, ∀ s, Q s → F (g x) PUnit.unit C (simStS tn s) = .ok (.yield PUnit.unit, simStS tn (R x s)))
    (hQ : ∀ x ∈ l, ∀ s, Q s → Q (R x s)) :
    ∀ s, Q s → forIn (l.map g) PUnit.unit F C (simStS tn s) =
      .ok (PUnit.unit, simStS tn (l.foldl (fun s x => R x s) s)) := by
  induction l with
  | nil => intro s _; rfl
  | cons x t ih =>
    intro s hs
    rw [List.map_cons, List.forIn_cons]
    simp only [simM_bind, hF x List.mem_cons_self s hs, Except.bind, List.foldl_cons]
    exact ih (fun y hy => hF y (List.mem_cons_of_mem _ hy)) (fun y hy => hQ y (List.mem_cons_of_mem _ hy)) _
      (hQ x List.mem_cons_self s hs)

/-! ## sliderMouseMove -/
/-- one iteration of `slider_mouse_move` (Rust state) -/
def s3aSMM (c : sim.state.Ctx) (m : sim.basic.Vec2) (s : sim.state.St) (i : Usize) : sim.state.St :=
  if h : i.val < s.objs.val.length then
    if (if h' : i.val < c.pb.objects.val.length then kindS (c.pb.objects.val[i.val]'h').h.kind == kindS .Slider else false) then
      { s with objs := alloc.vec.Vec.set s.objs i { s.objs.val[i.val]'h with slider_mouse := some m } }
    else s
  else s

theorem s3a_foldl_inv {X S : Type} (P : S → Prop) (f : S → X → S) (l : List X) (h : ∀ x ∈ l, ∀ s, P s → P (f s x)) :
    ∀ s, P s → P (l.foldl f s) := by
  induction l with
  | nil => intro s hs; exact hs
  | cons x t ih => intro s hs; exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _ (h x List.mem_cons_self s hs)

/-- the object fields the mouse-move / hover passes never write (instances, results, last pressed actions, lifetime,
spin count, tick slots) -/
def s3d_keepH (o : sim.state.OState) :=
  (o.inst, o.head_inst, o.tick_insts, o.result, o.nested, o.last_pressed, o.life, o.completed_spins,
   o.tick_live.val.length)

/-- the per-object `s3d_keepH` frame -/
def s3d_KH (s s' : sim.state.St) : Prop :=
  ∀ j (h : j < s'.objs.val.length) (h0 : j < s.objs.val.length),
    s3d_keepH (s'.objs.val[j]'h) = s3d_keepH (s.objs.val[j]'h0)

theorem s3d_KH_trans {s1 s2 s3 : sim.state.St} (l1 : s2.objs.val.length = s1.objs.val.length)
    (h1 : s3d_KH s1 s2) (h2 : s3d_KH s2 s3) : s3d_KH s1 s3 := by
  intro j h h0
  have hm : j < s2.objs.val.length := by rw [l1]; exact h0
  rw [h2 j h hm, h1 j hm h0]

theorem s3d_KH_set (s S : sim.state.St) (i : Usize) (X : sim.state.OState) (hi : i.val < S.objs.val.length)
    (hX : s3d_keepH X = s3d_keepH (S.objs.val[i.val]'hi)) (h : s3d_KH s S) :
    s3d_KH s { S with objs := alloc.vec.Vec.set S.objs i X } := by
  intro j hj h0
  have hj' : j < S.objs.val.length := by simpa [vec_set_val'] using hj
  show s3d_keepH ((alloc.vec.Vec.set S.objs i X).val[j]'hj) = _
  simp only [vec_set_val', List.getElem_set]
  split
  · rename_i hij; subst hij; rw [hX]; exact h _ hi h0
  · exact h j hj' h0

/-- the frame of a pass that only writes mouse-move / hover object fields (what `input_phase` composes) -/
def s3d_objsFr (s s' : sim.state.St) : Prop :=
  s3b_objFrame s s' ∧ s3b_frame s s' ∧ s'.pressed = s.pressed ∧ s'.block_last = s.block_last ∧
    s'.block_idx = s.block_idx ∧ ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      (s'.objs.val[j]'h').last_pressed = (s.objs.val[j]'h).last_pressed

theorem s3d_objsFr_of (s s' : sim.state.St) (ho : ∃ o, s' = { s with objs := o })
    (hl : s'.objs.val.length = s.objs.val.length) (hk : s3d_KH s s') : s3d_objsFr s s' := by
  obtain ⟨o, rfl⟩ := ho
  refine ⟨⟨hl, fun j h h' => ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    fun j h h' => ?_⟩
  · have e := hk j h' h
    simp only [s3d_keepH, Prod.mk.injEq] at e
    exact ⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1⟩
  · have e := hk j h' h
    simp only [s3d_keepH, Prod.mk.injEq] at e
    exact e.2.2.2.2.2.1

theorem s3d_smm_objs (c : sim.state.Ctx) (m : sim.basic.Vec2) (s : sim.state.St) (l : List Usize) :
    (∃ o, l.foldl (fun S i => s3aSMM c m S i) s = { s with objs := o }) ∧
      s3d_KH s (l.foldl (fun S i => s3aSMM c m S i) s) := by
  refine s3a_foldl_inv (fun S => (∃ o, S = { s with objs := o }) ∧ s3d_KH s S) _ l ?_ s ⟨⟨s.objs, rfl⟩, fun _ _ _ => rfl⟩
  rintro i - S ⟨⟨o, rfl⟩, hk⟩
  unfold s3aSMM
  split_ifs
  all_goals first | exact ⟨⟨_, rfl⟩, hk⟩ | exact ⟨⟨_, rfl⟩, s3d_KH_set s _ i _ (by assumption) rfl hk⟩

/-- what the mouse-move loops preserve -/
def s3aMM (c : sim.state.Ctx) (s0 s : sim.state.St) : Prop :=
  SimInv c s ∧ s.active = s0.active ∧ s.mouse = s0.mouse ∧ s.insts = s0.insts ∧ s.future_order = s0.future_order ∧
    s.objs.val.length = s0.objs.val.length ∧ s.k = s0.k ∧ s.br_rot = s0.br_rot ∧
    ∀ j (h : j < s.objs.val.length) (h0 : j < s0.objs.val.length),
      (s.objs.val[j]'h).inst = (s0.objs.val[j]'h0).inst ∧ (s.objs.val[j]'h).head_inst = (s0.objs.val[j]'h0).head_inst

theorem s3a_MM_set (c : sim.state.Ctx) (s0 s : sim.state.St) (i : Usize) (o' : sim.state.OState) (h : s3aMM c s0 s)
    (hi : i.val < s.objs.val.length) (hn : o'.nested = (s.objs.val[i.val]'hi).nested)
    (hk : o'.inst = (s.objs.val[i.val]'hi).inst ∧ o'.head_inst = (s.objs.val[i.val]'hi).head_inst) :
    s3aMM c s0 { s with objs := alloc.vec.Vec.set s.objs i o' } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨s3a_inv_set c s i o' h1 hi hn, h2, h3, h4, h5, by simp [vec_set_val', h6], h7, h8, ?_⟩
  intro j hj hj0
  have hv : (alloc.vec.Vec.set s.objs i o').val = s.objs.val.set i.val o' := vec_set_val' _ _ _
  have hj' : j < s.objs.val.length := by simpa [hv] using hj
  simp only [hv, List.getElem_set]
  split
  · rename_i e; subst e; rw [hk.1, hk.2]; exact h9 _ hi hj0
  · exact h9 _ hj' hj0

theorem s3a_SMM_MM (c : sim.state.Ctx) (s0 s : sim.state.St) (i : Usize) (h : s3aMM c s0 s) :
    s3aMM c s0 (s3aSMM c s0.mouse s i) := by
  unfold s3aSMM
  by_cases hi : i.val < s.objs.val.length
  · rw [dif_pos hi]
    repeat' split
    all_goals first | exact s3a_MM_set c s0 s i _ h hi rfl ⟨rfl, rfl⟩ | exact h
  · rw [dif_neg hi]; exact h

@[simp] theorem s3a_hobjS_kind (tn) (h : sim.playable.HObj) : (hobjS tn h).kind = kindS h.kind := rfl

theorem sim.step.slider_mouse_move_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hact : ∀ i ∈ s.active.val, i.val < s.objs.val.length) :
    ∃ s', sim.step.slider_mouse_move c s = ok s' ∧
      OsuModel.Sim.Sim.sliderMouseMove (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s'.objs.val.length = s.objs.val.length ∧ s'.insts = s.insts ∧ s'.future_order = s.future_order ∧
      s'.active = s.active ∧ s3d_objsFr s s' := by
  have hMM0 : s3aMM c s s := ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  let s' := s.active.val.foldl (fun S i => s3aSMM c s.mouse S i) s
  have hMM : s3aMM c s s' := s3a_foldl_inv (s3aMM c s) _ _ (fun i _ S h => s3a_SMM_MM c s S i h) s hMM0
  obtain ⟨hI, hA, -, hIn, hF, hL, -, -, -⟩ := hMM
  refine ⟨s', ?_, ?_, hI, hL, hIn, hF, hA,
    s3d_objsFr_of s s' (s3d_smm_objs c s.mouse s _).1 hL (s3d_smm_objs c s.mouse s _).2⟩
  · -- Rust loop
    have hlen := s.active.property
    obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.step.slider_mouse_move_loop.body c x.1 x.2) (·.2)
      s.active.val.length (by omega) (fun t => s3aMM c s t.1) (·.1)
      (fun k S => s3aSMM c s.mouse S (s.active.val[k]!)) (fun y S => y = s3aTup S)
      (by
        rintro ⟨S, k⟩ hInv hk j1 hj1 hj1v
        simp only at hInv hk ⊢
        obtain ⟨hI1, hI2, hI3, -, -, hI6, -, -, -⟩ := id hInv
        have hka : k.val < S.active.val.length := by rw [hI2]; exact hk
        have hi := hact _ (List.getElem_mem hk)
        have hio : (s.active.val[k.val]'hk).val < S.objs.val.length := by rw [hI6]; exact hi
        have hic : (s.active.val[k.val]'hk).val < c.pb.objects.val.length := by rw [← hI1.objs_len]; exact hio
        refine ⟨(s3aSMM c s.mouse S (s.active.val[k.val]!), j1), ?_, rfl, rfl, ?_⟩
        · simp only [sim.step.slider_mouse_move_loop.body, hI2]
          simp only [vec_lt_len_iff, hk, if_true, vec_index_eq _ _ hk, bind_ok, vec_index_eq _ _ hic, kind_eq_ok, hj1,
            getElem!_pos s.active.val k.val hk]
          unfold s3aSMM
          simp only [dif_pos hio, dif_pos hic]
          cases hs : (kindS (c.pb.objects.val[(s.active.val[k.val]'hk).val]'hic).h.kind == kindS .Slider)
          · simp only [Bool.false_eq_true, if_false, bind_ok]; rw [← hI2]
          · simp only [if_true, vec_index_mut_eq _ _ hio, bind_ok]
            simp only [hI2, hI3]
            first | (split; simp only [bind_ok]; rfl) | (simp only [bind_ok]; rfl) | (simp; done)
        · exact s3a_SMM_MM c s S _ hInv)
      (by
        rintro ⟨S, k⟩ hI hk
        simp only at hI hk ⊢
        have : ¬ k < alloc.vec.Vec.len S.active := by rw [vec_lt_len_iff, hI.2.1]; omega
        exact ⟨_, by simp only [sim.step.slider_mouse_move_loop.body, this, if_false]; rfl, rfl⟩)
      (s, 0#usize) hMM0 (by simp)
    unfold sim.step.slider_mouse_move sim.step.slider_mouse_move_loop
    simp only at hl hy
    rw [hl, hy, show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, ← foldl_iterR]
    simp only [bind_ok]
    rfl
  · -- spec
    unfold OsuModel.Sim.Sim.sliderMouseMove
    simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind]
    rw [← Array.forIn_toList, show (simStS tn s).active.toList = s.active.val.map (fun u => u.val) by simp [simStS, abs]]
    rw [s3a_forIn_rust tn _ (fun u : Usize => u.val) s.active.val _ (fun i S => s3aSMM c s.mouse S i) (s3aMM c s) ?_
      (fun i _ S h => s3a_SMM_MM c s S i h) s hMM0]
    · rfl
    · intro i hi' S hS
      obtain ⟨hS1, hS2, hS3, -, -, hS6, -, -, -⟩ := hS
      have hio : i.val < S.objs.val.length := by rw [hS6]; exact hact i hi'
      have hic : i.val < c.pb.objects.val.length := by rw [← hS1.objs_len]; exact hio
      simp only [simM_bind, s3a_topObj _ _ _ _ _ hic, Except.bind]
      unfold s3aSMM
      simp only [dif_pos hio, dif_pos hic]
      by_cases hc : ((topS tn (c.pb.objects.val[i.val]'hic)).h.kind == OsuModel.Sim.Kind.slider) = true
      · rw [simM_ite, if_pos hc]
        have hc' : (kindS (c.pb.objects.val[i.val]'hic).h.kind == kindS .Slider) = true := hc
        simp only [hc', if_true, simM_bind]
        rw [s3a_modifyObj tn fo c S i hio _ { S.objs.val[i.val]'hio with slider_mouse := some s.mouse } rfl]
        rfl
      · rw [simM_ite, if_neg hc]
        have hc' : (kindS (c.pb.objects.val[i.val]'hic).h.kind == kindS .Slider) = false := by simpa using (show ¬ ((kindS (c.pb.objects.val[i.val]'hic).h.kind == kindS .Slider) = true) from hc)
        simp only [hc', Bool.false_eq_true, if_false, simM_pure]

/-! ## spinnerMouseMove -/
/-- the `Ctx` record literal that the Aeneas loops rebuild from the destructured context -/
theorem s3a_ctx_lit (c : sim.state.Ctx) : ({ env := c.env, cfg := { policy := c.cfg.policy, classic_head_block := c.cfg.classic_head_block, legacy_health := c.cfg.legacy_health, fail_overrides := c.cfg.fail_overrides, easy_retries := c.cfg.easy_retries, fail_conds := c.cfg.fail_conds, acc_challenges := c.cfg.acc_challenges, rank_adjust := c.cfg.rank_adjust, rate_sources := c.cfg.rate_sources, dyn_rates := c.cfg.dyn_rates, score_multiplier := c.cfg.score_multiplier, updatables := c.cfg.updatables, input_blockers := c.cfg.input_blockers, spun_out := c.cfg.spun_out, strict_tracking := c.cfg.strict_tracking, lazer_replay := c.cfg.lazer_replay, rate_mods := c.cfg.rate_mods, vis_mods := c.cfg.vis_mods, depth_max := c.cfg.depth_max, magnet_strength := c.cfg.magnet_strength, repel_strength := c.cfg.repel_strength, barrel_roll := c.cfg.barrel_roll }, pb := c.pb, frames := c.frames, steps := c.steps, head_idx := c.head_idx, tail_idx := c.tail_idx, smax := c.smax, hcfg := c.hcfg, last_frame_time := c.last_frame_time, corner_pow := c.corner_pow, prec_end := c.prec_end, ap_frames := c.ap_frames, block_periods := c.block_periods, first_obj := c.first_obj } : sim.state.Ctx) = c := rfl

open Classical in
/-- one iteration of `spinner_mouse_move` (Rust state) -/
noncomputable def s3aSPM (c : sim.state.Ctx) (m : sim.basic.Vec2) (s : sim.state.St) (i : Usize) : sim.state.St :=
  if h : i.val < s.objs.val.length then
    if (if h' : i.val < c.pb.objects.val.length then kindS (c.pb.objects.val[i.val]'h').h.kind == kindS .Spinner else false) then
      if hg : ∃ g p, sim.step.cur_spinner_geom c s i = ok g ∧ sim.basic.to_local g.aspect m = ok p then
        { s with objs := (alloc.vec.Vec.set s.objs i
            { s.objs.val[i.val]'h with spin_mouse := some (Classical.choose (Classical.choose_spec hg)) }) }
      else s
    else s
  else s

theorem s3a_SPM_eq (c : sim.state.Ctx) (m : sim.basic.Vec2) (s : sim.state.St) (i : Usize)
    (g : sim.geometry.SpinnerGeom) (p : sim.basic.Vec2) (hg : sim.step.cur_spinner_geom c s i = ok g)
    (hp : sim.basic.to_local g.aspect m = ok p) (hex : ∃ g p, sim.step.cur_spinner_geom c s i = ok g ∧ sim.basic.to_local g.aspect m = ok p) :
    Classical.choose (Classical.choose_spec hex) = p := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec (Classical.choose_spec hex)
  generalize Classical.choose (Classical.choose_spec hex) = q at h2 ⊢
  have e1 : Classical.choose hex = g := Result.ok_injective (h1.symm.trans hg)
  rw [e1, hp] at h2
  exact (Result.ok_injective h2).symm

theorem s3a_SPM_MM (c : sim.state.Ctx) (s0 s : sim.state.St) (i : Usize) (h : s3aMM c s0 s) :
    s3aMM c s0 (s3aSPM c s0.mouse s i) := by
  unfold s3aSPM
  by_cases hi : i.val < s.objs.val.length
  · rw [dif_pos hi]
    repeat' split
    all_goals first | exact s3a_MM_set c s0 s i _ h hi rfl ⟨rfl, rfl⟩ | exact h
  · rw [dif_neg hi]; exact h

/-- the active objects' instances are in range (needed by `cur_spinner_geom`) -/
def s3aActOk (s : sim.state.St) : Prop := ∀ i ∈ s.active.val, s3aInstOk s i.val

theorem s3a_instOk_MM (c : sim.state.Ctx) (s0 s : sim.state.St) (i : Nat) (h : s3aMM c s0 s) (hi : s3aInstOk s0 i) :
    s3aInstOk s i := by
  obtain ⟨h0, h1, h2⟩ := hi
  obtain ⟨-, -, -, h4, -, h6, -, -, h9⟩ := h
  have hs : i < s.objs.val.length := by rw [h6]; exact h0
  obtain ⟨e1, e2⟩ := h9 i hs h0
  exact ⟨hs, by rw [e1, h4]; exact h1, by rw [e2, h4]; exact h2⟩

theorem s3d_spm_objs (c : sim.state.Ctx) (m : sim.basic.Vec2) (s : sim.state.St) (l : List Usize) :
    (∃ o, l.foldl (fun S i => s3aSPM c m S i) s = { s with objs := o }) ∧
      s3d_KH s (l.foldl (fun S i => s3aSPM c m S i) s) := by
  refine s3a_foldl_inv (fun S => (∃ o, S = { s with objs := o }) ∧ s3d_KH s S) _ l ?_ s ⟨⟨s.objs, rfl⟩, fun _ _ _ => rfl⟩
  rintro i - S ⟨⟨o, rfl⟩, hk⟩
  unfold s3aSPM
  split_ifs
  all_goals first | exact ⟨⟨_, rfl⟩, hk⟩ | exact ⟨⟨_, rfl⟩, s3d_KH_set s _ i _ (by assumption) rfl hk⟩

theorem sim.step.spinner_mouse_move_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hact : s3aActOk s) :
    ∃ s', sim.step.spinner_mouse_move c s = ok s' ∧
      OsuModel.Sim.Sim.spinnerMouseMove (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s'.objs.val.length = s.objs.val.length ∧ s'.insts = s.insts ∧ s'.future_order = s.future_order ∧
      s'.active = s.active ∧ s3d_objsFr s s' := by
  have hMM0 : s3aMM c s s := ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  by_cases hso : c.cfg.spun_out = true
  · refine ⟨s, by simp [sim.step.spinner_mouse_move, hso], ?_, hinv, rfl, rfl, rfl, rfl,
      s3d_objsFr_of s s ⟨s.objs, rfl⟩ rfl (fun _ _ _ => rfl)⟩
    unfold OsuModel.Sim.Sim.spinnerMouseMove
    simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind, s3a_ctx_spunOut,
      hso, simM_ite, if_true, simM_pure]
  have hso' : c.cfg.spun_out = false := by simpa using hso
  let s' := s.active.val.foldl (fun S i => s3aSPM c s.mouse S i) s
  have hMM : s3aMM c s s' := s3a_foldl_inv (s3aMM c s) _ _ (fun i _ S h => s3a_SPM_MM c s S i h) s hMM0
  obtain ⟨hI, hA, -, hIn, hF, hL, -, -, -⟩ := hMM
  refine ⟨s', ?_, ?_, hI, hL, hIn, hF, hA,
    s3d_objsFr_of s s' (s3d_spm_objs c s.mouse s _).1 hL (s3d_spm_objs c s.mouse s _).2⟩
  · -- Rust loop
    have hlen := s.active.property
    obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => sim.step.spinner_mouse_move_loop.body c.env c.cfg.policy c.cfg.classic_head_block c.cfg.legacy_health c.cfg.fail_overrides c.cfg.easy_retries c.cfg.fail_conds c.cfg.acc_challenges c.cfg.rank_adjust c.cfg.rate_sources c.cfg.dyn_rates c.cfg.score_multiplier c.cfg.updatables c.cfg.input_blockers c.cfg.spun_out c.cfg.strict_tracking c.cfg.lazer_replay c.cfg.rate_mods c.cfg.vis_mods c.cfg.depth_max c.cfg.magnet_strength c.cfg.repel_strength c.cfg.barrel_roll c.pb c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods c.first_obj x.1 x.2) (·.2)
      s.active.val.length (by omega) (fun t => s3aMM c s t.1) (·.1)
      (fun k S => s3aSPM c s.mouse S (s.active.val[k]!)) (fun y S => y = s3aTup S)
      (by
        rintro ⟨S, k⟩ hInv hk j1 hj1 hj1v
        simp only at hInv hk ⊢
        obtain ⟨hI1, hI2, hI3, -, -, hI6, -, -, -⟩ := id hInv
        have hi := hact _ (List.getElem_mem hk)
        have hio : (s.active.val[k.val]'hk).val < S.objs.val.length := by rw [hI6]; exact hi.1
        have hic : (s.active.val[k.val]'hk).val < c.pb.objects.val.length := by rw [← hI1.objs_len]; exact hio
        refine ⟨(s3aSPM c s.mouse S (s.active.val[k.val]!), j1), ?_, rfl, rfl, ?_⟩
        · simp only [sim.step.spinner_mouse_move_loop.body, hI2]
          rw [s3a_ctx_lit c]
          simp only [vec_lt_len_iff, hk, if_true, vec_index_eq _ _ hk, bind_ok, vec_index_eq _ _ hic, kind_eq_ok, hj1,
            getElem!_pos s.active.val k.val hk]
          unfold s3aSPM
          simp only [dif_pos hio, dif_pos hic]
          cases hs : (kindS (c.pb.objects.val[(s.active.val[k.val]'hk).val]'hic).h.kind == kindS .Spinner)
          · simp only [Bool.false_eq_true, if_false, bind_ok]; rw [← hI2]
          · obtain ⟨g, hg, -⟩ := sim.step.cur_spinner_geom_refines tn fo c S (s.active.val[k.val]'hk)
              (s3a_instOk_MM c s S _ hInv hi)
            obtain ⟨p, hp, -⟩ := sim.basic.to_local_refines g.aspect s.mouse
            have hex : ∃ g p, sim.step.cur_spinner_geom c S (s.active.val[k.val]'hk) = ok g ∧
                sim.basic.to_local g.aspect s.mouse = ok p := ⟨g, p, hg, hp⟩
            simp only [if_true]
            rw [dif_pos hex, s3a_SPM_eq c s.mouse S _ g p hg hp hex]
            simp only [hg, hI3, hp, bind_ok, vec_index_mut_eq _ _ hio]
            simp only [hI2]
            first | (split; simp only [bind_ok]; rfl) | (simp only [bind_ok]; rfl) | (simp; done)
        · exact s3a_SPM_MM c s S _ hInv)
      (by
        rintro ⟨S, k⟩ hI hk
        simp only at hI hk ⊢
        have : ¬ k < alloc.vec.Vec.len S.active := by rw [vec_lt_len_iff, hI.2.1]; omega
        exact ⟨_, by simp only [sim.step.spinner_mouse_move_loop.body, this, if_false]; rfl, rfl⟩)
      (s, 0#usize) hMM0 (by simp)
    unfold sim.step.spinner_mouse_move sim.step.spinner_mouse_move_loop
    simp only at hl hy
    rw [if_neg hso]
    rw [hl, hy, show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, ← foldl_iterR]
    simp only [bind_ok]
    rfl
  · -- spec
    unfold OsuModel.Sim.Sim.spinnerMouseMove
    simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind]
    rw [simM_ite, if_neg (by rw [s3a_ctx_spunOut, hso']; decide)]
    simp only [simM_bind]
    rw [← Array.forIn_toList, show (simStS tn s).active.toList = s.active.val.map (fun u => u.val) by simp [simStS, abs]]
    rw [s3a_forIn_rust tn _ (fun u : Usize => u.val) s.active.val _ (fun i S => s3aSPM c s.mouse S i) (s3aMM c s) ?_
      (fun i _ S h => s3a_SPM_MM c s S i h) s hMM0]
    · rfl
    · intro i hi' S hS
      have hiS := s3a_instOk_MM c s S _ hS (hact i hi')
      obtain ⟨hS1, hS2, hS3, -, -, hS6, -, -, -⟩ := hS
      have hio : i.val < S.objs.val.length := hiS.1
      have hic : i.val < c.pb.objects.val.length := by rw [← hS1.objs_len]; exact hio
      simp only [simM_bind, s3a_topObj _ _ _ _ _ hic, Except.bind]
      unfold s3aSPM
      simp only [dif_pos hio, dif_pos hic]
      by_cases hc : ((topS tn (c.pb.objects.val[i.val]'hic)).h.kind == OsuModel.Sim.Kind.spinner) = true
      · rw [simM_ite, if_pos hc]
        have hc' : (kindS (c.pb.objects.val[i.val]'hic).h.kind == kindS .Spinner) = true := hc
        obtain ⟨g, hg, eg⟩ := sim.step.cur_spinner_geom_refines tn fo c S i hiS
        obtain ⟨p, hp, ep⟩ := sim.basic.to_local_refines g.aspect s.mouse
        have hex : ∃ g p, sim.step.cur_spinner_geom c S i = ok g ∧ sim.basic.to_local g.aspect s.mouse = ok p :=
          ⟨g, p, hg, hp⟩
        simp only [hc', if_true]
        rw [dif_pos hex, s3a_SPM_eq c s.mouse S i g p hg hp hex]
        simp only [simM_bind, eg, Except.bind]
        rw [s3a_modifyObj tn fo c S i hio _ { S.objs.val[i.val]'hio with spin_mouse := some p } (by
          simp only [s3a_st_mouse]
          rw [show (abs g : OsuModel.Sim.SpinnerGeom).aspect = abs g.aspect from rfl, ep]
          rfl)]
        rfl
      · rw [simM_ite, if_neg hc]
        have hc' : (kindS (c.pb.objects.val[i.val]'hic).h.kind == kindS .Spinner) = false := by
          simpa using (show ¬ ((kindS (c.pb.objects.val[i.val]'hic).h.kind == kindS .Spinner) = true) from hc)
        simp only [hc', Bool.false_eq_true, if_false, simM_pure]

end OsuProofs
