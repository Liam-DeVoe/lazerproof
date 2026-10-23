/-
sim3d (D59): `sim::step` mod update hooks of `playfieldUpdate` over the alive objects (Rust) refine
`OsuModel.Sim.Sim` (Step.lean): `update_hover` (`updateHover`, needed by Autopilot), `autopilot_update`
(`autopilotUpdate`). Helpers `s3d_*`. The generic lockstep `s3d_loopV` relates a Rust index loop to a spec
`forIn (List.range' ..)` in `SimM`; `s3d_loopV0` fixes the spec body by unification through an equation.
-/
import OsuProofs.Sim3.SA_Mouse
import OsuProofs.Sim3.SB_Basic
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

/-- generic lockstep: a Rust index loop `body` (no early exit) vs a spec `forIn (List.range' q (n - q))` in `SimM` -/
theorem s3d_loopV {T V : Type} (body : T × Usize → Result (ControlFlow (T × Usize) V)) (n : Nat)
    (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : Nat → T → Prop) (fin : T → V) (hn : n ≤ Usize.max)
    (hstep : ∀ t (q : Usize), q.val < n → Inv q.val t → ∀ q1 : Usize, q1.val = q.val + 1 →
      ∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv (q.val + 1) t' ∧
        F q.val PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t'))
    (hend : ∀ t (q : Usize), n ≤ q.val → body (t, q) = ok (.done (fin t))) :
    ∀ m (q : Usize) t, n - q.val = m → Inv q.val t → q.val ≤ n → ∃ t', loop body (t, q) = ok (fin t') ∧
      Inv n t' ∧ forIn (List.range' q.val (n - q.val)) PUnit.unit F C (A t) = .ok (PUnit.unit, A t') := by
  intro m
  induction m with
  | zero =>
    intro q t hm hI hq
    have hqn : q.val = n := by omega
    refine ⟨t, by rw [loop_unfold, hend t q (by omega)]; simp only [bind_ok], hqn ▸ hI, ?_⟩
    rw [show n - q.val = 0 by omega]; rfl
  | succ m ih =>
    intro q t hm hI hq
    have hlt : q.val < n := by omega
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
    obtain ⟨t', hb, hI', hF⟩ := hstep t q hlt hI q1 hq1v
    obtain ⟨t'', hl, hI'', hr⟩ := ih q1 t' (by omega) (hq1v ▸ hI') (by omega)
    refine ⟨t'', by rw [loop_unfold, hb]; simpa using hl, hI'', ?_⟩
    rw [show n - q.val = (n - q1.val) + 1 by omega, List.range'_succ, List.forIn_cons]
    simp only [simM_bind, hF, Except.bind]
    rw [← hq1v]; exact hr

/-- `s3d_loopV` from index 0, with the spec loop given through an equation (fixes `F` by unification) -/
theorem s3d_loopV0 {T V : Type} (body : T × Usize → Result (ControlFlow (T × Usize) V)) (n : Nat)
    (F : Nat → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : Nat → T → Prop) (fin : T → V) (hn : n ≤ Usize.max)
    (hstep : ∀ t (q : Usize), q.val < n → Inv q.val t → ∀ q1 : Usize, q1.val = q.val + 1 →
      ∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv (q.val + 1) t' ∧
        F q.val PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t'))
    (hend : ∀ t (q : Usize), n ≤ q.val → body (t, q) = ok (.done (fin t)))
    (t0 : T) (h0 : Inv 0 t0) (X : Except String (PUnit × OsuModel.Sim.St))
    (hX : forIn (List.range' 0 n) PUnit.unit F C (A t0) = X) :
    ∃ t', loop body (t0, 0#usize) = ok (fin t') ∧ Inv n t' ∧ X = .ok (PUnit.unit, A t') := by
  obtain ⟨t', h1, h2, h3⟩ := s3d_loopV body n F C A Inv fin hn hstep hend n 0#usize t0 (by simp) h0 (by simp)
  refine ⟨t', h1, h2, ?_⟩
  rw [← hX]; simpa using h3


/-- instances in range for the alive-dictionary entries (sim core's `simIK`), plus: alive objects and active
entries are in the alive dictionary (D67b: never-alive objects have no instances) -/
def s3d_IK (s : sim.state.St) : Prop :=
  (∀ x, some x ∈ s.dict_slots.val → s3aInstOk s x.val) ∧
  (∀ i (h : i < s.objs.val.length), (s.objs.val[i]'h).life = .Alive → ∃ x, some x ∈ s.dict_slots.val ∧ x.val = i) ∧
  (∀ x ∈ s.active.val, some x ∈ s.dict_slots.val)

theorem s3d_IK.alive {s : sim.state.St} (h : s3d_IK s) {i : Nat} (hi : i < s.objs.val.length)
    (hal : (s.objs.val[i]'hi).life = .Alive) : s3aInstOk s i := by
  obtain ⟨x, hx, rfl⟩ := h.2.1 i hi hal
  exact h.1 x hx

theorem s3d_IK.act {s : sim.state.St} (h : s3d_IK s) {x : Usize} (hx : x ∈ s.active.val) : s3aInstOk s x.val :=
  h.1 x (h.2.2 x hx)

/-- `update_hover` loop invariant at position `q`: same objects as `s` up to `hovered`; objects `≥ q` untouched -/
def s3d_UHInv (s : sim.state.St) (q : Nat) (v : alloc.vec.Vec sim.state.OState) : Prop :=
  v.val.length = s.objs.val.length ∧ ∀ j (h : j < v.val.length) (h0 : j < s.objs.val.length),
    v.val[j]'h = { s.objs.val[j]'h0 with hovered := (v.val[j]'h).hovered } ∧ (q ≤ j → v.val[j]'h = s.objs.val[j]'h0)

theorem s3d_UH_inv (c : sim.state.Ctx) (s : sim.state.St) (q : Nat) (v : alloc.vec.Vec sim.state.OState)
    (hinv : SimInv c s) (h : s3d_UHInv s q v) : SimInv c { s with objs := v } := by
  obtain ⟨hl, hv⟩ := h
  obtain ⟨a, b, d, e, f⟩ := hinv
  refine ⟨by simp [hl, a], ?_, d, e, f⟩
  intro i h1 h2
  have h0 : i < s.objs.val.length := by rw [← hl]; exact h1
  rw [(hv i h1 h0).1]; exact b i h0 h2

theorem s3d_UH_instOk (s : sim.state.St) (q : Nat) (v : alloc.vec.Vec sim.state.OState) (h : s3d_UHInv s q v)
    (i : Nat) (hi : s3aInstOk s i) : s3aInstOk { s with objs := v } i := by
  obtain ⟨h0, h1, h2⟩ := hi
  have hv : i < v.val.length := by rw [h.1]; exact h0
  have e := (h.2 i hv h0).1
  refine ⟨hv, ?_, ?_⟩
  · show (v.val[i]'hv).inst.val < s.insts.val.length; rw [e]; exact h1
  · show (v.val[i]'hv).head_inst.val < s.insts.val.length; rw [e]; exact h2

theorem s3d_UH_step (s : sim.state.St) (q : Usize) (v : alloc.vec.Vec sim.state.OState) (h : s3d_UHInv s q.val v)
    (hq : q.val < v.val.length) (hov : Bool) :
    s3d_UHInv s (q.val + 1) (if hov ≠ (v.val[q.val]'hq).hovered then
      alloc.vec.Vec.set v q { v.val[q.val]'hq with hovered := hov } else v) := by
  obtain ⟨hl, hv⟩ := h
  split
  · refine ⟨by simp [vec_set_val', hl], ?_⟩
    intro j hj hj0
    have hj' : j < v.val.length := by simpa [vec_set_val'] using hj
    simp only [vec_set_val', List.getElem_set]
    split
    · rename_i e; subst e
      have := (hv q.val hq hj0).2 (le_refl _)
      refine ⟨by rw [this], fun h => by omega⟩
    · exact ⟨(hv j hj' hj0).1, fun h => (hv j hj' hj0).2 (by omega)⟩
  · exact ⟨hl, fun j hj hj0 => ⟨(hv j hj hj0).1, fun h => (hv j hj hj0).2 (by omega)⟩⟩

theorem s3d_getA_objs (tn) (s : sim.state.St) (i : Nat) (h : i < s.objs.val.length) (C : OsuModel.Sim.Ctx)
    (S : OsuModel.Sim.St) :
    OsuModel.Sim.Sim.getA (simStS tn s).objs i "objs" C S = .ok (ostateS (s.objs.val[i]'h), S) := by
  have h' : i < (simStS tn s).objs.size := by simpa [simStS, abs] using h
  simp only [OsuModel.Sim.Sim.getA, simM_dite, dif_pos h', simM_pure]
  congr 2; simp [simStS, abs]

/-- the spec tail of `updateHover`'s body (`if hov != os.hovered then modifyObj ..`) -/
theorem s3d_uh_tail_spec (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (t : alloc.vec.Vec sim.state.OState)
    (q : Usize) (hq : q.val < t.val.length) (hov : Bool) :
    ((if (hov != (ostateS (t.val[q.val]'hq)).hovered) = true then
        OsuModel.Sim.Sim.modifyObj q.val (fun os => { os with hovered := hov }) >>= fun (_ : PUnit) =>
          pure (ForInStep.yield PUnit.unit) else pure (ForInStep.yield PUnit.unit)) : OsuModel.Sim.SimM (ForInStep PUnit))
      (simCtxS tn fo c) (simStS tn { s with objs := t }) =
    .ok (.yield PUnit.unit, simStS tn { s with objs := (if hov ≠ (t.val[q.val]'hq).hovered then
      alloc.vec.Vec.set t q { t.val[q.val]'hq with hovered := hov } else t) }) := by
  have e : (ostateS (t.val[q.val]'hq)).hovered = (t.val[q.val]'hq).hovered := rfl
  rw [e]
  by_cases hh : hov = (t.val[q.val]'hq).hovered
  · simp [hh]
  · have hb : (hov != (t.val[q.val]'hq).hovered) = true := by simpa using hh
    rw [if_pos hb, if_pos hh]
    simp only [simM_bind]
    rw [s3a_modifyObj tn fo c { s with objs := t } q hq _ { t.val[q.val]'hq with hovered := hov } rfl]
    rfl

theorem s3d_life_ne (a : sim.state.Life) :
    core.cmp.PartialEq.ne.trait_default sim.state.Life.Insts.CoreCmpPartialEqLife a sim.state.Life.Alive =
      ok (lifeS a != OsuModel.Sim.Life.alive) := by
  cases a <;> simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    sim.state.Life.Insts.CoreCmpPartialEqLife.eq, sim.state.Life.read_discriminant, lifeS] <;> decide

theorem s3d_match_ok {X : Except String (PUnit × OsuModel.Sim.St)} {C : OsuModel.Sim.Ctx} {S' : OsuModel.Sim.St}
    (h : X = .ok (PUnit.unit, S')) :
    (match X with | Except.error e => Except.error e | Except.ok v => (pure () : OsuModel.Sim.SimM Unit) C v.2) = .ok ((), S') := by
  rw [h]; rfl

theorem sim.step.update_hover_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hik : s3d_IK s) (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) :
    ∃ s', sim.step.update_hover c s = ok s' ∧
      OsuModel.Sim.Sim.updateHover (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      (∃ v, s' = { s with objs := v } ∧ s3d_UHInv s s.objs.val.length v) ∧ s3d_objsFr s s' := by
  have hn : c.pb.objects.val.length ≤ Usize.max := by have := c.pb.objects.property; omega
  have hlen : s.objs.val.length = c.pb.objects.val.length := hinv.objs_len
  suffices H : ∃ v, sim.step.update_hover_loop c s.k s.t s.objs s.first_lifetime_update
      s.next_future s.future_order s.active s.dict_slots s.free_list
      s.child_counter s.mouse_valid s.mouse s.last_replay s.pressed s.score
      s.health s.score_rp s.health_rp s.out s.speed s.as_target s.as_recent
      s.as_seen s.clock_rate s.relax_down s.relax_was_left s.relax_last
      s.ap_frame s.block_last s.block_idx s.insts s.pools s.br_rot s.theta
      s.cursor_pos s.mouse 0#usize = ok v ∧ s3d_UHInv s c.pb.objects.val.length v ∧
      OsuModel.Sim.Sim.updateHover (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn { s with objs := v }) by
    obtain ⟨v, hl, hI, hs⟩ := H
    refine ⟨{ s with objs := v }, by unfold sim.step.update_hover; rw [hl]; simp only [bind_ok], hs, ⟨v, rfl,
      by rw [hlen]; exact hI⟩, s3d_objsFr_of s _ ⟨v, rfl⟩ hI.1 (fun j h h0 => ?_)⟩
    show s3d_keepH (v.val[j]'h) = _
    rw [(hI.2 j h h0).1]; rfl
  unfold OsuModel.Sim.Sim.updateHover
  simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind,
    Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : [:(simCtxS tn fo c).pb.objects.size].size = c.pb.objects.val.length := by
    simp [Std.Legacy.Range.size, simCtxS, playableS, abs]
  rw [hsz]
  generalize hX : forIn (m := OsuModel.Sim.SimM) (List.range' 0 c.pb.objects.val.length) PUnit.unit _ (simCtxS tn fo c) (simStS tn s) = X
  have hK := s3d_loopV0 (fun x => sim.step.update_hover_loop.body c s.k s.t s.first_lifetime_update
      s.next_future s.future_order s.active s.dict_slots s.free_list
      s.child_counter s.mouse_valid s.mouse s.last_replay s.pressed s.score
      s.health s.score_rp s.health_rp s.out s.speed s.as_target s.as_recent
      s.as_seen s.clock_rate s.relax_down s.relax_was_left s.relax_last
      s.ap_frame s.block_last s.block_idx s.insts s.pools s.br_rot s.theta
      s.cursor_pos s.mouse x.1 x.2) c.pb.objects.val.length _ (simCtxS tn fo c)
    (fun v => simStS tn { s with objs := v }) (s3d_UHInv s) id hn ?hs
    (by
      intro t q hq
      have : ¬ q < alloc.vec.Vec.len c.pb.objects := by rw [vec_lt_len_iff]; omega
      simp only [sim.step.update_hover_loop.body, this, if_false]; rfl)
    s.objs ⟨rfl, fun j h h0 => ⟨rfl, fun _ => rfl⟩⟩ X hX
  · obtain ⟨v, hl, hI, hF⟩ := hK
    refine ⟨v, by unfold sim.step.update_hover_loop; exact hl, hI, ?_⟩
    rw [hF]; rfl
  case hs =>
    intro t q hq hI q1 hq1
    have hqo : q.val < s.objs.val.length := by omega
    have hqt : q.val < t.val.length := by rw [hI.1]; exact hqo
    have et : t.val[q.val]'hqt = s.objs.val[q.val]'hqo := (hI.2 q.val hqt hqo).2 (le_refl _)
    have hinvS : SimInv c { s with objs := t } := s3d_UH_inv c s q.val t hinv hI
    simp only [s3d_getA_objs tn s q.val hqo, simM_bind, Except.bind, s3a_topObj _ _ _ _ _ hq]
    rw [← et]
    simp only [sim.step.update_hover_loop.body, vec_lt_len_iff, hq, if_true, vec_index_eq _ _ hqt, bind_ok,
      vec_index_eq _ _ hq, s3d_life_ne]
    obtain ⟨z, hz, hzv⟩ := usize_add_one q (by omega)
    have hzq : z = q1 := UScalar.eq_of_val_eq (by omega)
    subst hzq
    have hlS : (ostateS (t.val[q.val]'hqt)).life = lifeS (t.val[q.val]'hqt).life := rfl
    have hhS : (ostateS (t.val[q.val]'hqt)).headAlive = (t.val[q.val]'hqt).head_alive := rfl
    rw [hlS]
    by_cases hal : (lifeS (t.val[q.val]'hqt).life != OsuModel.Sim.Life.alive) = true
    · refine ⟨_, ?_, s3d_UH_step s q t hI hqt false, ?_⟩
      · cases hh : (t.val[q.val]'hqt).hovered <;> simp [hal, hh, vec_index_mut_eq _ _ hqt, hz]
      · rw [if_pos hal]; exact s3d_uh_tail_spec tn fo c s t q hqt false
    rw [if_neg hal]
    have hal' : (t.val[q.val]'hqt).life = .Alive := by
      revert hal; cases (t.val[q.val]'hqt).life <;>
        first | (intro _; rfl) | (intro h; exfalso; apply h; decide) | (intro h; exfalso; exact h rfl)
    have hikq : s3aInstOk { s with objs := t } q.val :=
      s3d_UH_instOk s q.val t hI q.val (hik.alive hqo (by rw [← et]; exact hal'))
    simp only [hal, Bool.false_eq_true, if_false, s3a_topS_h, s3a_hobjS_kind]
    cases hk : (c.pb.objects.val[q.val]'hq).h.kind
    case Circle =>
      obtain ⟨d, hd, ed⟩ := sim.step.cur_circle_receptor_refines tn fo c { s with objs := t } q hinvS hikq
      obtain ⟨r, hr, er⟩ := sim.geometry.receptor_contains_refines d s.mouse c.corner_pow hcp
      refine ⟨_, ?_, s3d_UH_step s q t hI hqt r, ?_⟩
      · by_cases hh : r = (t.val[q.val]'hqt).hovered <;> simp [hd, hr, hh, vec_index_mut_eq _ _ hqt, hz]
      · simp only [kindS, simM_bind, ed, Except.bind, simM_pure, s3a_st_mouse, er]
        exact s3d_uh_tail_spec tn fo c s t q hqt r
    case Slider =>
      rw [hhS]
      cases hha : (t.val[q.val]'hqt).head_alive
      · refine ⟨_, ?_, s3d_UH_step s q t hI hqt false, ?_⟩
        · simp only [hha, Bool.false_eq_true, if_false, bind_ok]
          cases hh : (t.val[q.val]'hqt).hovered <;> simp [hh, vec_index_mut_eq _ _ hqt, hz] <;> simp only [hha]
        · simp only [kindS, Bool.not_false, if_true, simM_bind, simM_pure]
          exact s3d_uh_tail_spec tn fo c s t q hqt false
      · obtain ⟨g, hg, eg⟩ := sim.step.cur_slider_geom_refines tn fo c { s with objs := t } q hinvS hikq
        obtain ⟨r, hr, er⟩ := sim.geometry.receptor_contains_refines g.head_receptor s.mouse c.corner_pow hcp
        refine ⟨_, ?_, s3d_UH_step s q t hI hqt r, ?_⟩
        · by_cases hh : r = (t.val[q.val]'hqt).hovered <;> simp [hg, hr, hh, vec_index_mut_eq _ _ hqt, hz]
        · simp only [kindS, Bool.not_true, Bool.false_eq_true, if_false, simM_bind, eg, Except.bind, simM_pure,
            s3a_st_mouse]
          rw [show (abs g : OsuModel.Sim.SliderGeom).headReceptor = abs g.head_receptor from rfl, er]
          exact s3d_uh_tail_spec tn fo c s t q hqt r
    all_goals
      refine ⟨_, ?_, s3d_UH_step s q t hI hqt false, ?_⟩
      · cases hh : (t.val[q.val]'hqt).hovered <;> simp [hh, vec_index_mut_eq _ _ hqt, hz]
      · simp only [kindS, simM_bind, simM_pure]
        exact s3d_uh_tail_spec tn fo c s t q hqt false

/-- `slider_mouse_move` computes the fold of `s3aSMM` (the Rust half of `slider_mouse_move_refines`) -/
theorem s3d_smm_eq (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hact : ∀ i ∈ s.active.val, i.val < s.objs.val.length) :
    sim.step.slider_mouse_move c s = ok (s.active.val.foldl (fun S i => s3aSMM c s.mouse S i) s) := by
  have hMM0 : s3aMM c s s := ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
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

/-- `spinner_mouse_move` computes the fold of `s3aSPM` (the Rust half of `spinner_mouse_move_refines`) -/
theorem s3d_spm_eq (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s) (hact : s3aActOk s) :
    sim.step.spinner_mouse_move c s =
      ok (if c.cfg.spun_out then s else s.active.val.foldl (fun S i => s3aSPM c s.mouse S i) s) := by
  have hMM0 : s3aMM c s s := ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  by_cases hso : c.cfg.spun_out = true
  · simp [sim.step.spinner_mouse_move, hso]
  rw [if_neg hso]
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

/-- only `objs` changes, instances/nested arrays kept -/
def s3d_OK (c : sim.state.Ctx) (s s' : sim.state.St) : Prop :=
  (∃ o, s' = { s with objs := o }) ∧ SimInv c s' ∧ s'.objs.val.length = s.objs.val.length ∧
    (∀ j (h : j < s'.objs.val.length) (h0 : j < s.objs.val.length),
      (s'.objs.val[j]'h).inst = (s.objs.val[j]'h0).inst ∧ (s'.objs.val[j]'h).head_inst = (s.objs.val[j]'h0).head_inst) ∧
    s3d_KH s s'

theorem s3d_OK_trans (c : sim.state.Ctx) (s1 s2 s3 : sim.state.St) (h1 : s3d_OK c s1 s2) (h2 : s3d_OK c s2 s3) :
    s3d_OK c s1 s3 := by
  obtain ⟨⟨o1, e1⟩, -, l1, k1, q1⟩ := h1
  obtain ⟨⟨o2, e2⟩, i2, l2, k2, q2⟩ := h2
  refine ⟨⟨o2, by rw [e2, e1]⟩, i2, by rw [l2, l1], fun j h h0 => ?_, s3d_KH_trans l1 q1 q2⟩
  have hm : j < s2.objs.val.length := by rw [l1]; exact h0
  rw [(k2 j h hm).1, (k2 j h hm).2, (k1 j hm h0).1, (k1 j hm h0).2]; exact ⟨rfl, rfl⟩

theorem s3d_OK_IK (c : sim.state.Ctx) (s s' : sim.state.St) (h : s3d_OK c s s') (hik : s3d_IK s) : s3d_IK s' := by
  obtain ⟨⟨o, e⟩, -, hl, hk, hkh⟩ := h
  have hins : s'.insts = s.insts := by rw [e]
  have hds : s'.dict_slots = s.dict_slots := by rw [e]
  have hac : s'.active = s.active := by rw [e]
  refine ⟨fun x hx => ?_, fun i hi hal => ?_, fun x hx => ?_⟩
  · rw [hds] at hx
    obtain ⟨hh, h1, h2⟩ := hik.1 x hx
    have hi : x.val < s'.objs.val.length := by rw [hl]; exact hh
    refine ⟨hi, ?_, ?_⟩
    · rw [(hk _ hi hh).1, hins]; exact h1
    · rw [(hk _ hi hh).2, hins]; exact h2
  · have hi0 : i < s.objs.val.length := by rw [← hl]; exact hi
    have ek := hkh i hi hi0
    simp only [s3d_keepH, Prod.mk.injEq] at ek
    rw [hds]
    exact hik.2.1 i hi0 (by rw [← ek.2.2.2.2.2.2.1]; exact hal)
  · rw [hds]; rw [hac] at hx; exact hik.2.2 x hx

theorem s3d_OK_of_MM (c : sim.state.Ctx) (s s' : sim.state.St) (h : s3aMM c s s')
    (ho : (∃ o, s' = { s with objs := o }) ∧ s3d_KH s s') : s3d_OK c s s' := by
  obtain ⟨h1, -, -, -, -, h6, -, -, h9⟩ := h
  exact ⟨ho.1, h1, h6, h9, ho.2⟩

theorem s3d_smm_OK (c : sim.state.Ctx) (s s' : sim.state.St) (hinv : SimInv c s)
    (hact : ∀ i ∈ s.active.val, i.val < s.objs.val.length) (h : sim.step.slider_mouse_move c s = ok s') :
    s3d_OK c s s' ∧ s'.active = s.active ∧ s'.mouse = s.mouse := by
  obtain rfl := Result.ok_injective (h.symm.trans (s3d_smm_eq c s hinv hact))
  have hMM0 : s3aMM c s s := ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hMM := s3a_foldl_inv (s3aMM c s) (fun S i => s3aSMM c s.mouse S i) s.active.val (fun i _ S h => s3a_SMM_MM c s S i h) s hMM0
  exact ⟨s3d_OK_of_MM c s _ hMM (s3d_smm_objs c s.mouse s _), hMM.2.1, hMM.2.2.1⟩

theorem s3d_spm_OK (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s s' : sim.state.St) (hinv : SimInv c s) (hact : s3aActOk s)
    (h : sim.step.spinner_mouse_move c s = ok s') :
    s3d_OK c s s' ∧ s'.active = s.active ∧ s'.mouse = s.mouse := by
  obtain rfl := Result.ok_injective (h.symm.trans (s3d_spm_eq tn fo c s hinv hact))
  have hMM0 : s3aMM c s s := ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  split
  · exact ⟨s3d_OK_of_MM c s s hMM0 ⟨⟨s.objs, rfl⟩, fun _ _ _ => rfl⟩, rfl, rfl⟩
  · have hMM := s3a_foldl_inv (s3aMM c s) (fun S i => s3aSPM c s.mouse S i) s.active.val (fun i _ S h => s3a_SPM_MM c s S i h) s hMM0
    exact ⟨s3d_OK_of_MM c s _ hMM (s3d_spm_objs c s.mouse s _), hMM.2.1, hMM.2.2.1⟩

theorem s3d_uh_OK (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s) (hik : s3d_IK s)
    (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) :
    ∃ s', sim.step.update_hover c s = ok s' ∧
      OsuModel.Sim.Sim.updateHover (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧ s3d_OK c s s' := by
  obtain ⟨s', h1, h2, ⟨v, rfl, hv⟩, -⟩ := sim.step.update_hover_refines tn fo c s hinv hik hcp
  refine ⟨_, h1, h2, ⟨v, rfl⟩, s3d_UH_inv c s _ v hinv hv, hv.1, fun j h h0 => ?_, fun j h h0 => ?_⟩
  · have e := (hv.2 j h h0).1
    exact ⟨by rw [e], by rw [e]⟩
  · have e := (hv.2 j h h0).1
    show s3d_keepH (v.val[j]'h) = _
    rw [e]; rfl

theorem s3d_apGet (tn fo) (c : sim.state.Ctx) (n : Nat) (h : n < c.ap_frames.val.length) (S : OsuModel.Sim.St) :
    OsuModel.Sim.Sim.getA (simCtxS tn fo c).apFrames n "autopilot frames" (simCtxS tn fo c) S =
      .ok (((c.ap_frames.val[n]'h).time, abs (c.ap_frames.val[n]'h).pos), S) := by
  have h' : n < (simCtxS tn fo c).apFrames.size := by simpa [simCtxS] using h
  simp only [OsuModel.Sim.Sim.getA, simM_dite, dif_pos h', simM_pure]
  simp [simCtxS]

theorem s3d_vidx {α : Type} (v : alloc.vec.Vec α) (u : Usize) (m : Nat) (hu : u.val = m) (h : m < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v u = ok (v.val[m]'h) := by
  subst hu; exact vec_index_eq _ _ h

@[simp] theorem s3d_st_mouseValid (tn) (s : sim.state.St) : (simStS tn s).mouseValid = s.mouse_valid := rfl

/-- the mouse-move chain of `autopilotUpdate` (slider/spinner mouse move, hover) -/
theorem s3d_mm_chain (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s1 : sim.state.St)
    (hinv : SimInv c s1) (hik : s3d_IK s1) (hact : ∀ i ∈ s1.active.val, i.val < s1.objs.val.length)
    (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) :
    ∃ s2 s3 s4, sim.step.slider_mouse_move c s1 = ok s2 ∧ sim.step.spinner_mouse_move c s2 = ok s3 ∧
      sim.step.update_hover c s3 = ok s4 ∧
      OsuModel.Sim.Sim.sliderMouseMove (simCtxS tn fo c) (simStS tn s1) = .ok ((), simStS tn s2) ∧
      OsuModel.Sim.Sim.spinnerMouseMove (simCtxS tn fo c) (simStS tn s2) = .ok ((), simStS tn s3) ∧
      OsuModel.Sim.Sim.updateHover (simCtxS tn fo c) (simStS tn s3) = .ok ((), simStS tn s4) ∧
      s3d_OK c s1 s4 := by
  obtain ⟨s2, r2, e2, -⟩ := sim.step.slider_mouse_move_refines tn fo c s1 hinv hact
  obtain ⟨k2, a2, -⟩ := s3d_smm_OK c s1 s2 hinv hact r2
  have hinv2 := k2.2.1
  have hik2 := s3d_OK_IK c s1 s2 k2 hik
  have hact2 : s3aActOk s2 := fun i hi => hik2.act hi
  obtain ⟨s3, r3, e3, -⟩ := sim.step.spinner_mouse_move_refines tn fo c s2 hinv2 hact2
  obtain ⟨k3, -, -⟩ := s3d_spm_OK tn fo c s2 s3 hinv2 hact2 r3
  obtain ⟨s4, r4, e4, k4⟩ := s3d_uh_OK tn fo c s3 k3.2.1 (s3d_OK_IK c s2 s3 k3 hik2) hcp
  exact ⟨s2, s3, s4, r2, r3, r4, e2, e3, e4, s3d_OK_trans c s1 s3 s4 (s3d_OK_trans c s1 s2 s3 k2 k3) k4⟩

theorem s3d_stS_apFrame (tn) (s : sim.state.St) (i2 : I64) (h : i2.val = s.ap_frame.val + 1) :
    ({ simStS tn s with apFrame := s.ap_frame.val + 1 } : OsuModel.Sim.St) = simStS tn { s with ap_frame := i2 } := by
  simp [simStS, h]

theorem s3d_stS_mouse (tn) (s : sim.state.St) (scr v : sim.basic.Vec2) :
    ({ simStS tn s with mouseValid := true, mouse := abs scr, cursorPos := abs v } : OsuModel.Sim.St) =
      simStS tn { s with mouse_valid := true, mouse := scr, cursor_pos := v } := by
  simp [simStS]

/-- what `autopilot_update` changes: the frame index, the mouse, the cursor and (mouse-move/hover) object fields -/
def s3d_APPost (c : sim.state.Ctx) (s s' : sim.state.St) : Prop :=
  (∃ af mv m cp o, s' = { s with ap_frame := af, mouse_valid := mv, mouse := m, cursor_pos := cp, objs := o }) ∧
    SimInv c s' ∧ s3d_IK s' ∧ s'.objs.val.length = s.objs.val.length ∧
    -1 ≤ s'.ap_frame.val ∧ s'.ap_frame.val < c.ap_frames.val.length ∧ s3d_KH s s'

set_option hygiene false in
/-- the advance branch of `autopilotUpdate` (shared by the `cur < 0` and the closer-frame cases) -/
macro "s3d_ap_adv" : tactic => `(tactic| (
  obtain ⟨d, hd, ed⟩ := sim.step.cur_env_hoc_refines tn fo c { s with ap_frame := i2 }
  obtain ⟨scr, hscr, escr⟩ := sim.basic.to_screen_refines d (c.ap_frames.val[(s.ap_frame.val + 1).toNat]'hnxl).pos
  obtain ⟨v, hv, ev⟩ := sim.basic.to_local_refines d scr
  obtain ⟨b, hb, eb⟩ := sim.basic.Vec2.eq_refines s.mouse scr
  simp only [simM_bind, simM_modify, Except.bind]
  rw [s3d_stS_apFrame tn s i2 hi2v]
  simp only [ed, hd, bind_ok, s3d_apGet tn fo c _ hnxl, simM_get, hscr]
  simp only [escr, s3d_st_mouseValid, s3a_st_mouse, eb]
  have hS1 : SimInv c { s with ap_frame := i2 } := s3b_inv_of hinv rfl rfl
  by_cases hmb : s.mouse_valid = true ∧ b = true
  · obtain ⟨hm1, hm2⟩ := hmb
    have hc : (!s.mouse_valid || !(abs b : Bool)) = false := by simp [hm1, hm2, abs]
    simp only [hc, Bool.false_eq_true, if_false, simM_pure]
    rw [if_pos hm1]
    simp only [hb, hm2, bind_ok, if_true]
    exact ⟨_, rfl, rfl, ⟨⟨_, _, _, _, _, rfl⟩, hS1, hik, rfl, by show -1 ≤ i2.val; rw [hi2v]; omega,
      by show i2.val < _; rw [hi2v]; omega, fun _ _ _ => rfl⟩⟩
  · have hc : (!s.mouse_valid || !(abs b : Bool)) = true := by
      cases h1 : s.mouse_valid <;> cases h2 : b <;> simp_all [abs]
    simp only [hc, if_true, simM_bind, ed, Except.bind, simM_modify]
    simp only [escr, ev]
    rw [s3d_stS_mouse tn { s with ap_frame := i2 } scr v]
    obtain ⟨s2, s3, s4, r2, r3, r4, e2, e3, e4, k4⟩ := s3d_mm_chain tn fo c
      { ({ s with ap_frame := i2 } : sim.state.St) with mouse_valid := true, mouse := scr, cursor_pos := v }
      (s3b_inv_of hinv rfl rfl) hik hact hcp
    simp only [e2, e3, e4]
    refine ⟨s4, ?_, rfl, ?_⟩
    · have r2' : sim.step.slider_mouse_move c
          { s with mouse_valid := true, mouse := scr, ap_frame := i2, cursor_pos := v } = ok s2 := r2
      cases hmv : s.mouse_valid
      · simp only [Bool.false_eq_true, if_false, hv, bind_ok, r2', r3, r4]
      · have hb' : b = false := by simpa [hmv] using hmb
        simp only [if_true, hb, hb', Bool.false_eq_true, if_false, hv, bind_ok, r2', r3, r4]
    · obtain ⟨⟨o, ho⟩, k2, k3, k5, k6⟩ := k4
      refine ⟨⟨_, _, _, _, o, ho⟩, k2, s3d_OK_IK c _ _ ⟨⟨o, ho⟩, k2, k3, k5, k6⟩ hik, k3, ?_, ?_, k6⟩
      · rw [ho]; show -1 ≤ i2.val; rw [hi2v]; omega
      · rw [ho]; show i2.val < _; rw [hi2v]; omega))

theorem sim.step.autopilot_update_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s) (hik : s3d_IK s)
    (hact : ∀ i ∈ s.active.val, i.val < s.objs.val.length) (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow)
    (hap : c.ap_frames.val.length < 2 ^ 62) (hf0 : -1 ≤ s.ap_frame.val)
    (hf1 : s.ap_frame.val < c.ap_frames.val.length) :
    ∃ s', sim.step.autopilot_update c s = ok s' ∧
      OsuModel.Sim.Sim.autopilotUpdate (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      s3d_APPost c s s' := by
  have hpost0 : s3d_APPost c s s :=
    ⟨⟨_, _, _, _, _, rfl⟩, hinv, hik, rfl, hf0, hf1, fun _ _ _ => rfl⟩
  unfold sim.step.autopilot_update OsuModel.Sim.Sim.autopilotUpdate
  simp only [OsuModel.Sim.Sim.ctx, OsuModel.Sim.Sim.st, simM_bind, simM_read, simM_get, Except.bind, lift, bind_ok]
  have hnv : (UScalar.hcast IScalarTy.I64 (alloc.vec.Vec.len c.ap_frames)).val = (c.ap_frames.val.length : Int) := by
    rw [sim_usize_to_i64 _ (by simp; omega)]; simp
  obtain ⟨i1, hi1, hi1v⟩ := i64_sub_one (UScalar.hcast IScalarTy.I64 (alloc.vec.Vec.len c.ap_frames))
    (by rw [hnv]; omega) (by rw [hnv]; omega)
  rw [hi1]; simp only [bind_ok]
  have hsz : ((simCtxS tn fo c).apFrames.size : Int) = c.ap_frames.val.length := by simp [simCtxS]
  have hapS : (simStS tn s).apFrame = s.ap_frame.val := rfl
  rw [hsz, hapS]
  by_cases hA : s.ap_frame.val = (c.ap_frames.val.length : Int) - 1
  · have : s.ap_frame = i1 := IScalar.eq_of_val_eq (by rw [hi1v, hnv, hA])
    refine ⟨s, by simp [this], by simp [hA], hpost0⟩
  have hne : s.ap_frame ≠ i1 := fun h => hA (by rw [h, hi1v, hnv])
  simp only [hne, if_false, beq_iff_eq, hA]
  have hlt : s.ap_frame.val + 1 < c.ap_frames.val.length := by omega
  obtain ⟨i2, hi2, hi2v⟩ := i64_add_one s.ap_frame (by omega) (by omega)
  have hnx : (IScalar.hcast UScalarTy.Usize i2).val = (s.ap_frame.val + 1).toNat := by
    rw [sp_hcast_usize i2 h64 (by omega) (by omega), hi2v]
  have hnxl : (s.ap_frame.val + 1).toNat < c.ap_frames.val.length := by omega
  simp only [hi2, bind_ok, s3d_vidx c.ap_frames _ _ hnx hnxl, s3d_apGet tn fo c _ hnxl]
  by_cases hneg : s.ap_frame.val < 0
  · have hlt0 : s.ap_frame < 0#i64 := by scalar_tac
    simp only [hlt0, if_true, bind_ok, if_pos hneg, simM_bind, simM_pure, Except.bind]
    s3d_ap_adv
  · have hlt0 : ¬ s.ap_frame < 0#i64 := by scalar_tac
    have hc0 : (IScalar.hcast UScalarTy.Usize s.ap_frame).val = s.ap_frame.val.toNat :=
      sp_hcast_usize s.ap_frame h64 (by omega) (by omega)
    have hc0l : s.ap_frame.val.toNat < c.ap_frames.val.length := by omega
    simp (config := { proj := false }) only [hlt0, if_false, if_neg hneg, s3d_vidx c.ap_frames _ _ hc0 hc0l,
      s3d_apGet tn fo c _ hc0l, simM_bind, Except.bind, simM_pure, float.F64.sub, float.F64.abs, float.F64.le, bind_ok,
      s3d_apGet tn fo c _ hnxl]
    by_cases hadv : (F64.abs ((c.ap_frames.val[(s.ap_frame.val + 1).toNat]'hnxl).time - s.t) ≤
        F64.abs ((c.ap_frames.val[s.ap_frame.val.toNat]'hc0l).time - s.t))
    · have hadv' : F64.abs ((((c.ap_frames.val[(s.ap_frame.val + 1).toNat]'hnxl).time,
          (abs (c.ap_frames.val[(s.ap_frame.val + 1).toNat]'hnxl).pos : OsuModel.Sim.Vec2)), simStS tn s).1.1 -
          (simStS tn s, simStS tn s).1.t) ≤
        F64.abs ((((c.ap_frames.val[s.ap_frame.val.toNat]'hc0l).time,
          (abs (c.ap_frames.val[s.ap_frame.val.toNat]'hc0l).pos : OsuModel.Sim.Vec2)), simStS tn s).1.1 -
          (simStS tn s, simStS tn s).1.t) := hadv
      rw [if_pos (decide_eq_true hadv), if_pos (decide_eq_true hadv')]
      dsimp only
      s3d_ap_adv
    · have hadv' : ¬ F64.abs ((((c.ap_frames.val[(s.ap_frame.val + 1).toNat]'hnxl).time,
          (abs (c.ap_frames.val[(s.ap_frame.val + 1).toNat]'hnxl).pos : OsuModel.Sim.Vec2)), simStS tn s).1.1 -
          (simStS tn s, simStS tn s).1.t) ≤
        F64.abs ((((c.ap_frames.val[s.ap_frame.val.toNat]'hc0l).time,
          (abs (c.ap_frames.val[s.ap_frame.val.toNat]'hc0l).pos : OsuModel.Sim.Vec2)), simStS tn s).1.1 -
          (simStS tn s, simStS tn s).1.t) := hadv
      rw [if_neg (fun h => hadv (of_decide_eq_true h)), if_neg (fun h => hadv' (of_decide_eq_true h))]
      exact ⟨s, rfl, rfl, hpost0⟩
end OsuProofs
