/-
sim3d (D59): `playfield_update` (`Sim.playfieldUpdate`): the updatables loop over dyn-rate / depth / magnet / repel /
barrel roll / relax / autopilot / input-block hooks, with the state invariant `s3d_PInv` preserved on normal exit
and the context facts `s3d_PCtx`. CONDITIONAL only on `trigger_pressed` (sim core) through `s3d_TPOk` (relax).
-/
import OsuProofs.Sim3.SD_Relax
import OsuProofs.Sim3.SC_Upd
import OsuProofs.Sim3.SD_PS
import OsuProofs.Sim3.SB_Dyn
import OsuProofs.Sim3.SB_Upd2
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

/-- state invariant for `playfield_update` (and its hooks); preserved by every hook (`relax_update` given
`trigger_pressed` preserves it, `s3d_TPOk`) -/
def s3d_PInv (c : sim.state.Ctx) (s : sim.state.St) : Prop :=
  SimInv c s ∧ s3d_IK s ∧ (∀ x ∈ s.active.val, x.val < c.pb.objects.val.length) ∧
  (s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) ∧
  (-1 ≤ s.ap_frame.val ∧ s.ap_frame.val < c.ap_frames.val.length) ∧ s.pressed.len.val ≤ 3 ∧
  (∀ k, sim.mods.Updatable.DynRate k ∈ c.cfg.updatables.val → ∃ hk : k.val < c.cfg.dyn_rates.val.length,
     k.val < s.speed.val.length ∧ (s3b_isAd (c.cfg.dyn_rates.val[k.val]'hk) →
       ((c.cfg.dyn_rates.val.take k.val).filter s3b_isAd).length < s.as_target.val.length)) ∧
  (∀ k, sim.mods.Updatable.InputBlock k ∈ c.cfg.updatables.val →
     k.val < s.block_idx.val.length ∧ k.val < s.block_last.val.length) ∧
  (c.block_periods.val.length ≠ 0 → ∀ j (h : j < s.block_idx.val.length),
     (s.block_idx.val[j]'h).val < c.block_periods.val.length)

/-- context facts `playfield_update` needs (receptor corner power, autopilot frame count, relax head indices / paths) -/
def s3d_PCtx (c : sim.state.Ctx) : Prop :=
  c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow ∧ c.ap_frames.val.length < 2 ^ 62 ∧ s3d_RCtx c

theorem s3d_IK_of {s s' : sim.state.St} (ho : s'.objs = s.objs) (hi : s'.insts.val.length = s.insts.val.length)
    (ha : s'.active = s.active) (hd : s'.dict_slots = s.dict_slots)
    (h : s3d_IK s) : s3d_IK s' := by
  unfold s3d_IK s3aInstOk at *
  rw [ho, hi, ha, hd]; exact h

theorem s3d_PInv_mk {c : sim.state.Ctx} {s s' : sim.state.St} (h : s3d_PInv c s) (hinv : SimInv c s')
    (hik : s3d_IK s') (ha : s'.active = s.active) (hk : s'.k = s.k)
    (hap : -1 ≤ s'.ap_frame.val ∧ s'.ap_frame.val < c.ap_frames.val.length) (hp : s'.pressed.len.val ≤ 3)
    (hsp : s'.speed.val.length = s.speed.val.length) (has : s'.as_target = s.as_target)
    (hbi : s'.block_idx.val.length = s.block_idx.val.length) (hbl : s'.block_last.val.length = s.block_last.val.length)
    (hbp : c.block_periods.val.length ≠ 0 → ∀ j (h : j < s'.block_idx.val.length),
      (s'.block_idx.val[j]'h).val < c.block_periods.val.length) : s3d_PInv c s' := by
  obtain ⟨_, _, h3, h4, _, _, h7, h8, _⟩ := h
  refine ⟨hinv, hik, by rw [ha]; exact h3, by rw [hk]; exact h4, hap, hp, ?_, ?_, hbp⟩
  · intro k hk'
    obtain ⟨a, b, d⟩ := h7 k hk'
    exact ⟨a, by rw [hsp]; exact b, by rw [has]; exact d⟩
  · intro k hk'
    obtain ⟨a, b⟩ := h8 k hk'
    exact ⟨by rw [hbi]; exact a, by rw [hbl]; exact b⟩

theorem s3d_PInv_relaxCl (c : sim.state.Ctx) : s3d_RelaxCl (s3d_PInv c) := by
  refine ⟨fun s h => h.2.2.2.2.2.1, fun s d l w p h hp _ => ?_⟩
  exact s3d_PInv_mk h (s3b_inv_of h.1 rfl rfl) (s3d_IK_of rfl rfl rfl rfl h.2.1) rfl rfl h.2.2.2.2.1 hp rfl rfl rfl rfl
    h.2.2.2.2.2.2.2.2

/-- `s3b_loopR_forIn` (sim3b) with the invariant at a normal exit -/
theorem s3d_loopR {T α : Type}
    (body : T × Usize → Result (ControlFlow (T × Usize) (core.result.Result Unit sim.err.SimErr × T)))
    (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : T → Prop) (hn : l.length ≤ Usize.max)
    (hstep : ∀ t (q : Usize) (h : q.val < l.length), Inv t → ∀ q1 : Usize, q1.val = q.val + 1 →
      (∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv t' ∧ F (l[q.val]'h) PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t')) ∨
      (∃ e t', body (t, q) = ok (.done (.Err e, t')) ∧ ∃ m, F (l[q.val]'h) PUnit.unit C (A t) = .error m))
    (hend : ∀ t (q : Usize), l.length ≤ q.val → body (t, q) = ok (.done (.Ok (), t))) :
    ∀ n (q : Usize) t, l.length - q.val = n → Inv t → q.val ≤ l.length → ∃ res t', loop body (t, q) = ok (res, t') ∧
      s3b_rrel (fun _ => PUnit.unit) (A t') res (forIn (l.drop q.val) PUnit.unit F C (A t)) ∧
      (res = .Ok () → Inv t') := by
  intro n
  induction n with
  | zero =>
    intro q t hn0 hI hq
    refine ⟨.Ok (), t, by rw [loop_unfold, hend t q (by omega)]; simp only [bind_ok], ?_, fun _ => hI⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro q t hn0 hI hq
    have hlt : q.val < l.length := by omega
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
    rw [List.drop_eq_getElem_cons hlt, List.forIn_cons]
    rcases hstep t q hlt hI q1 hq1v with ⟨t', hb, hI', hF⟩ | ⟨e, t', hb, m, hF⟩
    · obtain ⟨res, t'', hl, hr, hI''⟩ := ih q1 t' (by omega) hI' (by omega)
      refine ⟨res, t'', by rw [loop_unfold, hb]; simpa using hl, ?_, hI''⟩
      simp only [simM_bind, hF, Except.bind]
      rw [hq1v] at hr; exact hr
    · refine ⟨.Err e, t', by rw [loop_unfold, hb]; simp only [bind_ok], ⟨m, ?_⟩, by simp⟩
      simp only [simM_bind, hF, Except.bind]

/-- `s3d_loopR` from index 0 with the spec body fixed by unification through `hX` -/
theorem s3d_loopR0 {T α : Type}
    (body : T × Usize → Result (ControlFlow (T × Usize) (core.result.Result Unit sim.err.SimErr × T)))
    (l : List α) (F : α → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)) (C : OsuModel.Sim.Ctx)
    (A : T → OsuModel.Sim.St) (Inv : T → Prop) (hn : l.length ≤ Usize.max)
    (hstep : ∀ t (q : Usize) (h : q.val < l.length), Inv t → ∀ q1 : Usize, q1.val = q.val + 1 →
      (∃ t', body (t, q) = ok (.cont (t', q1)) ∧ Inv t' ∧ F (l[q.val]'h) PUnit.unit C (A t) = .ok (.yield PUnit.unit, A t')) ∨
      (∃ e t', body (t, q) = ok (.done (.Err e, t')) ∧ ∃ m, F (l[q.val]'h) PUnit.unit C (A t) = .error m))
    (hend : ∀ t (q : Usize), l.length ≤ q.val → body (t, q) = ok (.done (.Ok (), t)))
    (t0 : T) (hI : Inv t0) (X : Except String (PUnit × OsuModel.Sim.St)) (hX : forIn l PUnit.unit F C (A t0) = X) :
    ∃ res t', loop body (t0, 0#usize) = ok (res, t') ∧ s3b_rrel (fun _ => PUnit.unit) (A t') res X ∧
      (res = .Ok () → Inv t') := by
  obtain ⟨res, t', h1, h2, h3⟩ := s3d_loopR body l F C A Inv hn hstep hend _ 0#usize t0 rfl hI (by simp)
  rw [show (0#usize : Usize).val = 0 from rfl, List.drop_zero, hX] at h2
  exact ⟨res, t', h1, h2, h3⟩

theorem s3d_set_bound (v : alloc.vec.Vec Usize) (k x : Usize) (B : Nat)
    (hv : ∀ j (h : j < v.val.length), (v.val[j]'h).val < B) (hx : x.val < B) :
    ∀ j (h : j < (v.set k x).val.length), ((v.set k x).val[j]'h).val < B := by
  intro j h
  have h' : j < v.val.length := by simpa [alloc.vec.Vec.set_val_eq] using h
  simp only [alloc.vec.Vec.set_val_eq, List.getElem_set]
  split
  · exact hx
  · exact hv j h'

/-- `input_block_update` keeps the block vectors' lengths and the stored period indices in range -/
theorem s3d_ib_post (c : sim.state.Ctx) (s s' : sim.state.St) (k : Usize) (hk1 : k.val < s.block_last.val.length)
    (hk2 : k.val < s.block_idx.val.length)
    (hb : c.block_periods.val.length ≠ 0 → ∀ j (h : j < s.block_idx.val.length),
      (s.block_idx.val[j]'h).val < c.block_periods.val.length)
    (h : sim.step.input_block_update c s k = ok s') :
    s'.block_idx.val.length = s.block_idx.val.length ∧ s'.block_last.val.length = s.block_last.val.length ∧
    (c.block_periods.val.length ≠ 0 → ∀ j (h : j < s'.block_idx.val.length),
      (s'.block_idx.val[j]'h).val < c.block_periods.val.length) := by
  obtain ⟨r, hr, er⟩ := sim.scoring.period_is_in_any_refines (alloc.vec.Vec.deref c.block_periods)
    (s.block_idx.val[k.val]'hk2) s.t (fun h0 => by simpa using hb (by simpa using h0) k.val hk2)
  have hr2 : c.block_periods.val.length ≠ 0 → r.2.val < c.block_periods.val.length := by
    intro h0
    have hl : (simPS (alloc.vec.Vec.deref c.block_periods)).length = c.block_periods.val.length := by simp [simPS]
    have hi0 : (s.block_idx.val[k.val]'hk2).val < (simPS (alloc.vec.Vec.deref c.block_periods)).length := by
      rw [hl]; exact hb h0 k.val hk2
    rw [simS_periodIsInAny _ _ _ hi0] at er
    simp only [Except.ok.injEq, Prod.mk.injEq] at er
    rw [← hl, ← er.2]
    split
    · exact sim_fwd_lt _ _ _ _ hi0
    · exact sim_bwd_lt _ _ _ _ hi0
  obtain ⟨ia, idx⟩ := r
  unfold sim.step.input_block_update at h
  cases hbs : (s.block_last.val[k.val]'hk1).isSome <;> cases ia <;>
    simp [vec_index_eq _ _ hk1, vec_index_eq _ _ hk2, hr, vec_index_mut_eq _ _ hk2, vec_index_mut_eq _ _ hk1,
      hbs] at h
  all_goals first | subst h | (have e := (Result.ok_injective h).symm; subst e)
  all_goals refine ⟨by simp [alloc.vec.Vec.set], by simp [alloc.vec.Vec.set], fun h0 j hj => ?_⟩
  all_goals first
    | exact hb h0 j hj
    | exact s3d_set_bound s.block_idx k idx _ (hb h0) (hr2 h0) j _
@[simp] theorem s3d_absU_dyn (k : Usize) : (abs (sim.mods.Updatable.DynRate k) : OsuModel.Sim.Updatable) = .dynRate k.val := rfl
@[simp] theorem s3d_absU_depth : (abs sim.mods.Updatable.Depth : OsuModel.Sim.Updatable) = .depth := rfl
@[simp] theorem s3d_absU_mag : (abs sim.mods.Updatable.Magnetised : OsuModel.Sim.Updatable) = .magnetised := rfl
@[simp] theorem s3d_absU_rep : (abs sim.mods.Updatable.Repel : OsuModel.Sim.Updatable) = .repel := rfl
@[simp] theorem s3d_absU_br : (abs sim.mods.Updatable.BarrelRoll : OsuModel.Sim.Updatable) = .barrelRoll := rfl
@[simp] theorem s3d_absU_relax : (abs sim.mods.Updatable.Relax : OsuModel.Sim.Updatable) = .relax := rfl
@[simp] theorem s3d_absU_ap : (abs sim.mods.Updatable.Autopilot : OsuModel.Sim.Updatable) = .autopilot := rfl
@[simp] theorem s3d_absU_ib (k : Usize) : (abs (sim.mods.Updatable.InputBlock k) : OsuModel.Sim.Updatable) = .inputBlock k.val := rfl

/-- the state changes of the non-relax playfield hooks (dyn rate: `speed`; depth / magnet: transform position and
scale; barrel roll: `br_rot`; autopilot: frame index, mouse, cursor and the mouse-move / hover object fields;
input block: the blocker trackers) -/
def s3d_HookFr (c : sim.state.Ctx) (s s' : sim.state.St) : Prop :=
  (∃ sp, s' = { s with speed := sp } ∧ sp.val.length = s.speed.val.length) ∨
  (∃ ins, s' = { s with insts := ins } ∧ s3d_TfPS s.insts ins) ∨
  (∃ r, s' = { s with br_rot := r }) ∨
  ((∃ af mv m cp o, s' = { s with ap_frame := af, mouse_valid := mv, mouse := m, cursor_pos := cp, objs := o }) ∧
    SimInv c s' ∧ s'.objs.val.length = s.objs.val.length ∧ s3d_KH s s') ∨
  (∃ bl bi, s' = { s with block_last := bl, block_idx := bi } ∧ bl.val.length = s.block_last.val.length ∧
    bi.val.length = s.block_idx.val.length ∧
    (c.block_periods.val.length ≠ 0 → ∀ j (h : j < bi.val.length), (bi.val[j]'h).val < c.block_periods.val.length))

/-- `playfield_update` for any caller invariant `I` that implies `s3d_PInv`, is closed under the hook frames
(`s3d_HookFr`) and the relax writes (`s3d_RelaxCl`), and is kept by `trigger_pressed` (`s3d_TPOk`) -/
theorem s3d_playfield_gen (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (I : sim.state.St → Prop) (hP : I s)
    (hIP : ∀ s, I s → s3d_PInv c s) (hfr : ∀ s s', I s → s3d_PInv c s' → s3d_HookFr c s s' → I s')
    (hcl : s3d_RelaxCl I) (hC : s3d_PCtx c) (htp : s3d_TPOk tn fo c I) :
    ∃ r s', sim.step.playfield_update c s = ok (r, s') ∧
      s3b_rrel (fun _ => ()) (simStS tn s') r (OsuModel.Sim.Sim.playfieldUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → I s') := by
  unfold sim.step.playfield_update sim.step.playfield_update_loop OsuModel.Sim.Sim.playfieldUpdate
  simp only [simM_bind, OsuModel.Sim.Sim.ctx, simM_read, Except.bind]
  rw [← Array.forIn_toList]
  generalize hX : forIn (m := OsuModel.Sim.SimM) (simCtxS tn fo c).cfg.updatables.toList PUnit.unit _ (simCtxS tn fo c) (simStS tn s) = X
  have hlen : (simCtxS tn fo c).cfg.updatables.toList.length = c.cfg.updatables.val.length := by
    simp [simCtxS, abs, configS]
  have hK := s3d_loopR0 (fun x => sim.step.playfield_update_loop.body c x.1 x.2) _ _ _ (simStS tn) I
    ?hn ?hstep ?hend s hP X hX
  case hn => rw [hlen]; exact c.cfg.updatables.property
  case hend =>
    intro t q hq
    have : ¬ q < alloc.vec.Vec.len c.cfg.updatables := by rw [vec_lt_len_iff]; rw [hlen] at hq; omega
    simp only [sim.step.playfield_update_loop.body, this, if_false]
  case hstep =>
    intro t q hq hI0 q1 hq1
    have hI := hIP t hI0
    have hql : q.val < c.cfg.updatables.val.length := by rw [← hlen]; exact hq
    have hlq : (simCtxS tn fo c).cfg.updatables.toList[q.val]'hq = abs (c.cfg.updatables.val[q.val]'hql) := by
      simp [simCtxS, abs, configS]
    have hqa : q < alloc.vec.Vec.len c.cfg.updatables := by rw [vec_lt_len_iff]; exact hql
    have hadd : q + 1#usize = ok q1 := by
      obtain ⟨z, hz, hv⟩ := usize_add_one q (by have := c.cfg.updatables.property; omega)
      rw [hz]; congr 1; exact UScalar.eq_of_val_eq (by rw [hv, hq1])
    have hmem : c.cfg.updatables.val[q.val]'hql ∈ c.cfg.updatables.val := List.getElem_mem hql
    rw [hlq]
    simp only [sim.step.playfield_update_loop.body, hqa, if_true, vec_index_eq _ _ hql, bind_ok]
    generalize c.cfg.updatables.val[q.val]'hql = u at hmem ⊢
    have hins : ∀ x ∈ t.active.val, ∀ h : x.val < t.objs.val.length,
        (t.objs.val[x.val]'h).inst.val < t.insts.val.length := fun x hx _ => (hI.2.1.act hx).2.1
    have hhd : ∀ x ∈ t.active.val, ∀ h : x.val < c.pb.objects.val.length,
        (c.pb.objects.val[x.val]'h).h.kind = .Slider →
        ∃ hhi : x.val < c.head_idx.val.length, (c.head_idx.val[x.val]'hhi).val < (c.pb.objects.val[x.val]'h).nested.val.length :=
      fun x _ h hk => let ⟨hhi, _, h2⟩ := hC.2.2.1 x.val h; ⟨hhi, h2 hk⟩
    cases u with
    | DynRate k =>
      simp only [s3d_absU_dyn]
      obtain ⟨hk, hsp, has⟩ := hI.2.2.2.2.2.2.1 k hmem
      obtain ⟨r, s', hr, er, ⟨sp, hs'⟩, hinv', _⟩ :=
        sim.step.dyn_rate_update_refines tn fo c t k hI.1 hk hsp hI.2.2.2.1 has
      have hspl : sp.val.length = t.speed.val.length := by
        have e := s3b_dyn_rust tn fo c t k hk hsp hI.2.2.2.1 has
        rw [hr] at e
        have e' := Result.ok_injective e
        rw [hs'] at e'
        split at e'
        · have := congrArg (fun p => p.2.speed.val.length) e'
          simpa [alloc.vec.Vec.set] using this
        · have := congrArg (fun p => p.2.speed.val.length) e'
          simpa using this
      subst hs'
      have hP' : s3d_PInv c { t with speed := sp } :=
        s3d_PInv_mk hI hinv' (s3d_IK_of (s := t) rfl rfl rfl rfl hI.2.1) rfl rfl hI.2.2.2.2.1 hI.2.2.2.2.2.1 hspl rfl rfl rfl
          hI.2.2.2.2.2.2.2.2
      cases r with
      | Ok u =>
        have er' : OsuModel.Sim.Sim.dynRateUpdate k.val (simCtxS tn fo c) (simStS tn t) =
            .ok ((), simStS tn { t with speed := sp }) := er
        refine Or.inl ⟨{ t with speed := sp }, by simp [hr, core.result.Result.Insts.CoreOpsTry.branch, hadd],
          hfr t _ hI0 hP' (Or.inl ⟨sp, rfl, hspl⟩), ?_⟩
        simp only [simM_bind, er', Except.bind]; rfl
      | Err e =>
        obtain ⟨m, hm⟩ := er
        refine Or.inr ⟨e, { t with speed := sp }, by simp [hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], m, ?_⟩
        simp only [simM_bind, hm, Except.bind]
    | Depth =>
      simp only [s3d_absU_depth]
      obtain ⟨r, s', hr, er, ins, hs', hl⟩ := sim.step.depth_update_refines tn fo c t hI.1 hI.2.2.1 hins
      subst hs'
      obtain ⟨r2, s2, hr2, -, ins2, hs2, hps⟩ := s3d_depth_ps tn fo c t hI.1 hI.2.2.1 hins
      have hii : ins2 = ins := by
        have := congrArg (fun p => p.2.insts) (Result.ok_injective (hr2.symm.trans hr))
        simp only [hs2] at this; exact this
      subst hii
      have hP' : s3d_PInv c { t with insts := ins2 } :=
        s3d_PInv_mk hI (s3b_inv_of hI.1 rfl rfl) (s3d_IK_of (s := t) rfl hl rfl rfl hI.2.1) rfl rfl hI.2.2.2.2.1 hI.2.2.2.2.2.1 rfl
          rfl rfl rfl hI.2.2.2.2.2.2.2.2
      cases r with
      | Ok u =>
        have er' : OsuModel.Sim.Sim.depthUpdate (simCtxS tn fo c) (simStS tn t) =
            .ok ((), simStS tn { t with insts := ins2 }) := er
        refine Or.inl ⟨{ t with insts := ins2 }, by simp [hr, core.result.Result.Insts.CoreOpsTry.branch, hadd],
          hfr t _ hI0 hP' (Or.inr (Or.inl ⟨ins2, rfl, hps⟩)), ?_⟩
        simp only [simM_bind, er', Except.bind]; rfl
      | Err e =>
        obtain ⟨m, hm⟩ := er
        refine Or.inr ⟨e, { t with insts := ins2 }, by simp [hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], m, ?_⟩
        simp only [simM_bind, hm, Except.bind]
    | Magnetised =>
      simp only [s3d_absU_mag]
      obtain ⟨s', hr, er, ins, hs', hl⟩ :=
        sim.step.magnet_update_refines tn fo c t false hI.1 hI.2.2.1 hins hhd hI.2.2.2.1
      subst hs'
      obtain ⟨s2, hr2, -, ins2, hs2, hps⟩ := s3d_magnet_ps tn fo c t false hI.1 hI.2.2.1 hins hhd hI.2.2.2.1
      have hii : ins2 = ins := by
        have := congrArg (fun p => p.insts) (Result.ok_injective (hr2.symm.trans hr))
        simp only [hs2] at this; exact this
      subst hii
      refine Or.inl ⟨{ t with insts := ins2 }, by simp [hr, hadd], hfr t _ hI0 (s3d_PInv_mk hI (s3b_inv_of hI.1 rfl rfl)
        (s3d_IK_of (s := t) rfl hl rfl rfl hI.2.1) rfl rfl hI.2.2.2.2.1 hI.2.2.2.2.2.1 rfl rfl rfl rfl hI.2.2.2.2.2.2.2.2)
        (Or.inr (Or.inl ⟨ins2, rfl, hps⟩)), ?_⟩
      simp only [simM_bind, er, Except.bind]; rfl
    | Repel =>
      simp only [s3d_absU_rep]
      obtain ⟨s', hr, er, ins, hs', hl⟩ :=
        sim.step.magnet_update_refines tn fo c t true hI.1 hI.2.2.1 hins hhd hI.2.2.2.1
      subst hs'
      obtain ⟨s2, hr2, -, ins2, hs2, hps⟩ := s3d_magnet_ps tn fo c t true hI.1 hI.2.2.1 hins hhd hI.2.2.2.1
      have hii : ins2 = ins := by
        have := congrArg (fun p => p.insts) (Result.ok_injective (hr2.symm.trans hr))
        simp only [hs2] at this; exact this
      subst hii
      refine Or.inl ⟨{ t with insts := ins2 }, by simp [hr, hadd], hfr t _ hI0 (s3d_PInv_mk hI (s3b_inv_of hI.1 rfl rfl)
        (s3d_IK_of (s := t) rfl hl rfl rfl hI.2.1) rfl rfl hI.2.2.2.2.1 hI.2.2.2.2.2.1 rfl rfl rfl rfl hI.2.2.2.2.2.2.2.2)
        (Or.inr (Or.inl ⟨ins2, rfl, hps⟩)), ?_⟩
      simp only [simM_bind, er, Except.bind]; rfl
    | BarrelRoll =>
      simp only [s3d_absU_br]
      have hr := sim.step.barrel_roll_update_refines c t
      cases hb : c.cfg.barrel_roll with
      | none =>
        rw [hb] at hr
        refine Or.inl ⟨t, by simp [hr, hadd], hI0, ?_⟩
        simp only [simM_bind, simM_read, Except.bind, s3a_ctx_br, hb, OsuModel.Sim.Sim.st, simM_get, simM_modify]; rfl
      | some p =>
        obtain ⟨speed, ccw⟩ := p
        rw [hb] at hr
        refine Or.inl ⟨{ t with br_rot := F32.ofInt ((if ccw then -1 else 1) * 360) * F64.toF32 (t.t / 60000 * speed) }, by simp only [hr, bind_ok, hadd], hfr t _ hI0 (s3d_PInv_mk hI (s3b_inv_of hI.1 rfl rfl)
          (s3d_IK_of (s := t) rfl rfl rfl rfl hI.2.1) rfl rfl hI.2.2.2.2.1 hI.2.2.2.2.2.1 rfl rfl rfl rfl hI.2.2.2.2.2.2.2.2)
          (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))), ?_⟩
        simp only [simM_bind, simM_read, Except.bind, s3a_ctx_br, hb, OsuModel.Sim.Sim.st, simM_get, simM_modify]; rfl
    | Relax =>
      simp only [s3d_absU_relax]
      obtain ⟨r, s', hr, er, hIs⟩ := s3d_relax_update_gen h64 tn fo c t I hI0 hcl
        htp hI.1 hI.2.1 hC.2.2
      cases r with
      | Ok u =>
        have er' : OsuModel.Sim.Sim.relaxUpdate (simCtxS tn fo c) (simStS tn t) = .ok ((), simStS tn s') := er
        refine Or.inl ⟨s', by simp [hr, core.result.Result.Insts.CoreOpsTry.branch, hadd], hIs rfl, ?_⟩
        simp only [simM_bind, er', Except.bind]; rfl
      | Err e =>
        obtain ⟨m, hm⟩ := er
        refine Or.inr ⟨e, s', by simp [hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], m, ?_⟩
        simp only [simM_bind, hm, Except.bind]
    | Autopilot =>
      simp only [s3d_absU_ap]
      obtain ⟨s', hr, er, ⟨⟨af, mv, mo, cp, ob, hs'⟩, hinv', hik', hol, hf0, hf1, hkh⟩⟩ :=
        sim.step.autopilot_update_refines h64 tn fo c t hI.1 hI.2.1
          (fun i hi => hI.1.objs_len ▸ hI.2.2.1 i hi) hC.1 hC.2.1 hI.2.2.2.2.1.1 hI.2.2.2.2.1.2
      subst hs'
      refine Or.inl ⟨{ t with ap_frame := af, mouse_valid := mv, mouse := mo, cursor_pos := cp, objs := ob }, by simp [hr, hadd], hfr t _ hI0 (s3d_PInv_mk hI hinv' hik' rfl rfl ⟨hf0, hf1⟩ hI.2.2.2.2.2.1 rfl rfl rfl rfl
        hI.2.2.2.2.2.2.2.2) (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨_, _, _, _, _, rfl⟩, hinv', hol, hkh⟩)))), ?_⟩
      simp only [simM_bind, er, Except.bind]; rfl
    | InputBlock k =>
      simp only [s3d_absU_ib]
      obtain ⟨hk2, hk1⟩ := hI.2.2.2.2.2.2.2.1 k hmem
      obtain ⟨s', hr, er, ⟨bl, bi, hs'⟩, hinv', _⟩ := sim.step.input_block_update_refines tn fo c t k hI.1 hk1 hk2
        (fun h0 => hI.2.2.2.2.2.2.2.2 h0 k.val hk2)
      obtain ⟨l1, l2, l3⟩ := s3d_ib_post c t s' k hk1 hk2 hI.2.2.2.2.2.2.2.2 hr
      subst hs'
      refine Or.inl ⟨{ t with block_last := bl, block_idx := bi }, by simp [hr, hadd], hfr t _ hI0 (s3d_PInv_mk hI hinv' (s3d_IK_of (s := t) rfl rfl rfl rfl hI.2.1) rfl rfl hI.2.2.2.2.1
        hI.2.2.2.2.2.1 rfl rfl l1 l2 l3) (Or.inr (Or.inr (Or.inr (Or.inr ⟨bl, bi, rfl, l2, l1, l3⟩)))), ?_⟩
      simp only [simM_bind, er, Except.bind]; rfl
  obtain ⟨res, t', h1, h2, h3⟩ := hK
  refine ⟨res, t', h1, ?_, h3⟩
  cases res with
  | Ok u =>
    have h2' : X = .ok (PUnit.unit, simStS tn t') := h2
    subst h2'; rfl
  | Err e =>
    obtain ⟨m, hm⟩ := h2
    subst hm; exact ⟨m, rfl⟩
end OsuProofs
