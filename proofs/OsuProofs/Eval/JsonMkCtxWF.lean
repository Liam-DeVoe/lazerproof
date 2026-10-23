/-
`sim.step.mk_ctx_wf` (json agent, D67): the context built by `mk_ctx` is well-formed (`ev_ctxWF`, Sim/CtxWF.lean,
incl. sim3d's `s3d_PCtx`), under `ev_mkBounds` (E2EBase; TRUSTED row `PlayableBounds.simCtx`).
-/
import OsuProofs.Eval.JsonMkCtx2
import OsuProofs.Sim7.Loops
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem js_fi_lt {α : Type} (p : α → Bool) : ∀ (l : List α) j, l.findIdx? p = some j → j < l.length := by
  intro l; induction l with
  | nil => intro j h; simp at h
  | cons a l ih =>
    intro j h
    rw [List.findIdx?_cons] at h
    split at h
    · simp at h; subst h; simp
    · cases e : l.findIdx? p with
      | none => rw [e] at h; simp at h
      | some x => rw [e] at h; simp at h; subst h; have := ih x e; simp; omega

theorem js_lf (k : OsuModel.Sim.Kind) : ∀ (l : List OsuModel.Sim.Kind) j r x, simLastFrom k l j r = some x →
    r = some x ∨ (j ≤ x ∧ x < j + l.length) := by
  intro l; induction l with
  | nil => intro j r x h; simp [simLastFrom] at h; exact Or.inl h
  | cons a l ih =>
    intro j r x h
    simp only [simLastFrom] at h
    rcases ih _ _ _ h with h1 | h1
    · split at h1
      · simp at h1; subst h1; right; simp
      · exact Or.inl h1
    · right; simp; omega

theorem js_idxS (o : OsuModel.Sim.TopObj) (K : OsuModel.Sim.Kind) (last : Bool) (j : Nat)
    (h : simIdxOfS o K last = .ok j) :
    (o.h.kind ≠ .slider → j = 0) ∧ (o.h.kind = .slider → j < o.nested.size) := by
  unfold simIdxOfS at h
  by_cases hs : o.h.kind = .slider
  · have : (o.h.kind != OsuModel.Sim.Kind.slider) = false := by rw [hs]; rfl
    rw [this] at h; simp only [Bool.false_eq_true, if_false] at h
    refine ⟨fun h' => absurd hs h', fun _ => ?_⟩
    split at h
    · rename_i j' hj
      simp at h; subst h
      have hl : (o.nested.toList.map (·.kind)).length = o.nested.size := by simp
      cases last
      · simp at hj; have := js_fi_lt _ _ _ hj; simpa using this
      · simp at hj
        rcases js_lf K _ 0 none j' hj with h1 | h1
        · simp at h1
        · simpa using h1.2
    · simp at h
  · have : (o.h.kind != OsuModel.Sim.Kind.slider) = true := by
      cases hk : o.h.kind <;> first | exact absurd hk hs | rfl
    rw [this] at h; simp at h
    exact ⟨fun _ => by omega, fun h' => absurd h' hs⟩

theorem js_mapM_get {α β : Type} (f : α → Except String β) : ∀ (l : List α) (L : List β), l.mapM f = .ok L →
    L.length = l.length ∧ ∀ i (hi : i < l.length) (hL : i < L.length), f l[i] = .ok L[i] := by
  intro l; induction l with
  | nil => intro L h; simp [Pure.pure, Except.pure] at h; subst h; simp
  | cons a l ih =>
    intro L h
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; simp [Bind.bind, Except.bind] at h
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
      | ok bs =>
        rw [hl] at h; simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h; subst h
        obtain ⟨h1, h2⟩ := ih bs hl
        refine ⟨by simp [h1], ?_⟩
        intro i hi hL
        cases i with
        | zero => simpa using ha
        | succ i => simpa using h2 i (by simpa using hi) (by simpa using hL)

theorem js_kind_sl (k : sim.playable.Kind) : kindS k = .slider ↔ k = .Slider := by
  cases k <;> simp [kindS]

/-- per-object facts of a successful `idx_list` -/
theorem js_idx_list_ok (pb : sim.playable.Playable) (k : sim.playable.Kind) (last : Bool) (v : alloc.vec.Vec Usize)
    (h : sim.step.idx_list pb k last = ok (.Ok v)) :
    ∀ i (hi : i < pb.objects.val.length), ∃ hv : i < v.val.length,
      ((pb.objects.val[i]'hi).h.kind ≠ .Slider → (v.val[i]'hv).val = 0) ∧
      ((pb.objects.val[i]'hi).h.kind = .Slider → (v.val[i]'hv).val < (pb.objects.val[i]'hi).nested.val.length) := by
  obtain ⟨R, hR, hrel⟩ := sim.step.idx_list_refines ev_tn pb k last
  rw [h] at hR
  have := (Result.ok_injective hR); subst this
  simp only [simRel] at hrel
  obtain ⟨hlen, hget⟩ := js_mapM_get _ _ _ hrel
  simp only [List.length_map] at hlen
  intro i hi
  have hv : i < v.val.length := by omega
  refine ⟨hv, ?_⟩
  have e := hget i (by simpa using hi) (by simpa using hv)
  simp only [List.getElem_map] at e
  have := js_idxS _ _ _ _ e
  simp only [topS, hobjS] at this
  refine ⟨fun h1 => this.1 (fun h2 => h1 ((js_kind_sl _).1 h2)), fun h1 => ?_⟩
  have := this.2 ((js_kind_sl _).2 h1); simpa using this

theorem js_ok_ne {α ε : Type} (e : ε) (c : α) : ok (core.result.Result.Err e) ≠ ok (core.result.Result.Ok c) := by
  intro h; have := Result.ok_injective h; cases this

theorem js_ok_ok {α ε : Type} {a b : α} (h : ok (core.result.Result.Ok a : core.result.Result α ε) = ok (.Ok b)) :
    a = b := by
  have := Result.ok_injective h; cases this; rfl

theorem js_top_kind (c : sim.state.Ctx) (r : sim.step.Ref) (ht : r.top.val < c.pb.objects.val.length)
    (hneg : r.nested.val < 0) : simHobj c r = (c.pb.objects.val[r.top.val]'ht).h := by
  unfold simHobj; rw [if_pos hneg]; simp [getElem!_def, ht]

theorem js_nested_kind (c : sim.state.Ctx) (r : sim.step.Ref) (ht : r.top.val < c.pb.objects.val.length)
    (hneg : ¬ r.nested.val < 0) (hnl : r.nested.val.toNat < (c.pb.objects.val[r.top.val]'ht).nested.val.length) :
    simHobj c r = (c.pb.objects.val[r.top.val]'ht).nested.val[r.nested.val.toNat]'hnl := by
  unfold simHobj; rw [if_neg hneg]; simp [getElem!_def, ht, hnl]

theorem js_wf_build (h64 : System.Platform.numBits = 64) (pb : sim.playable.Playable)
    (fs : alloc.vec.Vec replay.frames.Frame) (c : sim.mods.Config) (ctx : sim.state.Ctx) (hB : ev_mkBounds pb fs)
    (hpb : ctx.pb = pb) (hcf : ctx.cfg = c)
    (hhi : sim.step.idx_list pb .Head false = ok (.Ok ctx.head_idx))
    (hti : sim.step.idx_list pb .Tail true = ok (.Ok ctx.tail_idx))
    (hcp : ctx.corner_pow = OsuModel.Sim.receptorCornerRadiusPow)
    (hfo : ctx.first_obj.val.length = c.vis_mods.val.length)
    (hpe : (∃ d ∈ c.dyn_rates.val, s3b_isAd d = true) → ctx.prec_end.val.length = pb.objects.val.length ∧
      ∀ i (h1 : i < ctx.prec_end.val.length) (h2 : i < pb.objects.val.length),
        (ctx.prec_end.val[i]'h1).nested.val.length = (pb.objects.val[i]'h2).nested.val.length)
    (hap : ctx.ap_frames.val.length < 2^62) (hfr : ctx.frames = fs) : ev_ctxWF ctx := by
  obtain ⟨hfs, hob, hsum, hbr, hsd, hnest, hkind, hgen, hst, hac, htk⟩ := hB
  have hU := usize_max_64 h64
  have hU64 : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)
  cases ctx; simp only at hpb hcf hhi hti hcp hfo hpe hap hfr ⊢; subst hpb hcf hfr
  rename_i env cfg pb frames steps head_idx tail_idx smax hcfg lft cp pe ap bp fo
  have hH := js_idx_list_ok pb .Head false _ hhi
  have hT := js_idx_list_ok pb .Tail true _ hti
  have hhd : ∀ i (hi : i < pb.objects.val.length), ∃ hv : i < head_idx.val.length, (head_idx.val[i]'hv).val < 2 ^ 63 ∧
      ((pb.objects.val[i]'hi).h.kind = .Slider → (head_idx.val[i]'hv).val < (pb.objects.val[i]'hi).nested.val.length) := by
    intro i hi
    obtain ⟨hv, h0, h1⟩ := hH i hi
    refine ⟨hv, ?_, h1⟩
    by_cases hs : (pb.objects.val[i]'hi).h.kind = .Slider
    · have := h1 hs; have := hnest _ (List.getElem_mem hi); omega
    · rw [h0 hs]; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hob, hnest, ?_, by simp only at hfo ⊢; omega, ⟨hcp, hap, ⟨?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hv, h2, h1⟩ := hhd i hi
    refine ⟨hv, h2, ?_⟩
    rintro (hs | ⟨r, ⟨ht, hn⟩, htop, hk⟩)
    · exact h1 hs
    · by_cases hs : (pb.objects.val[i]'hi).h.kind = .Slider
      · exact h1 hs
      · obtain ⟨_, h0, _⟩ := hH i hi
        rw [h0 hs]
        subst htop
        by_cases hneg : r.nested.val < 0
        · rw [js_top_kind _ r ht hneg] at hk
          rcases hkind _ (List.getElem_mem ht) with h | h | h <;> simp_all
        · have := hn (by omega); omega
  · intro r hr hd
    obtain ⟨hl, hn⟩ := hpe hd
    obtain ⟨ht, hnn⟩ := hr
    simp only [s3b_precOk] at ht hnn ⊢
    refine ⟨by omega, fun h0 => ?_⟩
    rw [hn _ _ ht]; exact hnn h0
  · intro r ⟨ht, hn⟩ hk
    by_contra hneg
    rw [js_top_kind _ r ht (by omega)] at hk
    rcases hkind _ (List.getElem_mem ht) with h | h | h <;> simp_all
  · simp only; omega
  · intro i hi hs
    obtain ⟨hv, -, h1⟩ := hT i hi
    exact ⟨hv, h1 hs⟩
  · exact hhd
  · intro i h sd hsd'
    exact hsd _ (List.getElem_mem h) sd hsd'
  · intro i hi j hj
    exact hst _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  · simp only; omega
  · exact hac
  · exact hsum
  · exact h64
  · intro r ⟨ht, hn⟩ hk j hj htop
    subst htop
    by_cases hneg : r.nested.val < 0
    · rw [js_top_kind _ r ht hneg] at hk
      rcases hkind _ (List.getElem_mem ht) with h | h | h <;> simp_all
    · by_contra hs
      have hnl := hn (by omega)
      rw [js_nested_kind _ r ht hneg hnl] at hk
      have := htk _ (List.getElem_mem ht) hs _ (List.getElem_mem hnl)
      rcases hk with hk | hk <;> simp_all

theorem js_isAd_abs (d : sim.mods.DynRate) : js_isAd (abs d) = s3b_isAd d := by
  cases d <;> rfl

theorem js_pe_sizes (h64 : System.Platform.numBits = 64) (pb : sim.playable.Playable) (PE : alloc.vec.Vec sim.state.PrecEnd)
    (h : OsuModel.Sim.precedingEndTimes (playableS ev_tn pb) = .ok (js_peS PE)) :
    PE.val.length = pb.objects.val.length ∧
      ∀ i (h1 : i < PE.val.length) (h2 : i < pb.objects.val.length),
        (PE.val[i]'h1).nested.val.length = (pb.objects.val[i]'h2).nested.val.length := by
  obtain ⟨E, hE, -⟩ := js_precS (playableS ev_tn pb)
  rw [hE] at h
  have e : (playableS ev_tn pb).objects.map (js_entryS E) = js_peS PE := by
    have := h; simp only [Except.ok.injEq] at this; exact this
  have e2 := congrArg Array.toList e
  simp only [js_peS, playableS, Array.toList_map, List.toList_toArray, List.map_map] at e2
  have hl := congrArg List.length e2
  simp only [List.length_map] at hl
  refine ⟨hl.symm, fun i h1 h2 => ?_⟩
  have := congrArg (fun l => (l[i]?).map (fun p => p.2.size)) e2
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.map_some,
    Option.some.injEq, Function.comp_def, js_entryS, topS, Array.size_map, List.size_toArray, List.length_map] at this
  simpa using this.symm

/-- `mk_ctx` establishes `ev_ctxWF` (incl. `s3d_PCtx`) for the context it builds (D67; the `mkCtxWF` field of
`js_EvalOpen`). Premises as `js_mk_ctx_full`. -/
theorem sim.step.mk_ctx_wf (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env) (c : sim.mods.Config)
    (pb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame) (k : sim.schedule.ScheduleKind)
    (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C) (hB : ev_mkBounds pb fs) (ctx : sim.state.Ctx)
    (h : sim.step.mk_ctx env c pb fs k = ok (.Ok ctx)) : ev_ctxWF ctx := by
  have hB' := hB
  obtain ⟨hfs, hob, hsum, hbr, hsd, hnest, hkind, hgen, hst, hac, -⟩ := hB'
  have hmax : (2:Nat)^62 < Usize.max := by simp [Usize.max, h64, Usize.numBits]
  have hcap : (pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < Usize.max := by omega
  obtain ⟨A, hA, hArel⟩ := sim.step.ap_frames_of_refines h64 pb c hob hsd
  obtain ⟨S, hS, -⟩ := sim.schedule.steps_refines h64 k pb (alloc.vec.Vec.deref fs) (by simpa using hfs)
  obtain ⟨H, hH, -⟩ := sim.scoring.mk_health_cfg_refines ev_tn pb c.legacy_health hcap
  obtain ⟨B, hBp, -⟩ := sim.step.input_block_periods_refines ev_tn pb hbr
  obtain ⟨I1, hI1, -⟩ := sim.step.idx_list_refines ev_tn pb .Head false
  obtain ⟨I2, hI2, -⟩ := sim.step.idx_list_refines ev_tn pb .Tail true
  obtain ⟨M, hM, -⟩ := sim.scoring.score_maxima_refines ev_tn pb c.score_multiplier c.rank_adjust hcap
  obtain ⟨FO, hFO, hFOrel⟩ := sim.step.first_objects_refines ev_tn c pb
  obtain ⟨PE, hPE, hPErel⟩ := sim.step.preceding_end_times_refines h64 pb
    (by have := js_flat_wtsR_len pb.objects.val; omega)
    (fun o ho => by have := js_mem_le_sum _ o ho; omega)
    (by have := js_len_le_sum pb.objects.val; omega)
  have hfo : FO.val.length = c.vis_mods.val.length := by
    have := congrArg _root_.Array.size hFOrel; simpa [configS, abs] using this
  have hpe : (∃ d ∈ c.dyn_rates.val, s3b_isAd d = true) → (configS c).dynRates.any js_isAd = true := by
    rintro ⟨d, hd, hd'⟩
    simp only [configS, abs, Array.any_eq_true, List.getElem_toArray]
    simp only [List.size_toArray, List.length_map, List.getElem_map]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    refine ⟨i, hi, ?_⟩
    generalize c.dyn_rates.val[i] = d at hd' ⊢
    cases d <;> simp_all [js_isAd, s3b_isAd]
  have hPEs := js_pe_sizes h64 pb PE hPErel
  have hApB : ∀ v, A = .Ok v → v.val.length < 2^62 := by
    intro v hv; subst hv
    obtain ⟨G, hG, hGv⟩ := hArel
    have := congrArg _root_.Array.size hGv
    simp [js_apS] at this
    have := hgen _ _ hG; omega
  unfold sim.step.mk_ctx at h
  rw [sim.step.has_autopilot_refines c js_isAP (by intro u; cases u <;> rfl),
    sim.step.has_adaptive_refines c js_isAd (by intro u; cases u <;> rfl)] at h
  simp only [bind_ok, hA, hS, hH, hBp, hI1, hI2, hM, hFO, hPE, js_lft,
    sim.geometry.receptor_corner_radius_pow_refines] at h
  rcases Bool.eq_false_or_eq_true ((configS c).updatables.any js_isAP) with hb | hb <;>
  rcases Bool.eq_false_or_eq_true ((configS c).dynRates.any js_isAd) with hd | hd <;>
  by_cases hi0 : alloc.vec.Vec.len c.input_blockers = 0#usize <;>
  simp only [hb, hd, hi0, ↓reduceIte, Bool.false_eq_true, bind_ok] at h <;>
  cases A <;> try simp only [js_br_ok, js_br_err, js_fr, bind_ok] at h
  all_goals (first | exact absurd h (js_ok_ne _ _) | skip)
  all_goals (cases S <;> try simp only [js_br_ok, js_br_err, js_fr, bind_ok] at h)
  all_goals (first | exact absurd h (js_ok_ne _ _) | skip)
  all_goals (cases H <;> try simp only [js_br_ok, js_br_err, js_fr, bind_ok] at h)
  all_goals (first | exact absurd h (js_ok_ne _ _) | skip)
  all_goals (cases B <;> try simp only [js_br_ok, js_br_err, js_fr, bind_ok] at h)
  all_goals (first | exact absurd h (js_ok_ne _ _) | skip)
  all_goals (cases I1 <;> try simp only [js_br_ok, js_br_err, js_fr, bind_ok] at h)
  all_goals (first | exact absurd h (js_ok_ne _ _) | skip)
  all_goals (cases I2 <;> try simp only [js_br_ok, js_br_err, js_fr, bind_ok] at h)
  all_goals (first | exact absurd h (js_ok_ne _ _) | skip)
  all_goals (
    obtain rfl := js_ok_ok h
    refine js_wf_build h64 pb fs c _ hB rfl rfl hI1 hI2 rfl hfo ?_ ?_ rfl
    · intro hx
      first
        | exact hPEs
        | exact absurd (hpe hx) (by simp [hd])
    · first
        | exact hApB _ rfl
        | simp)

theorem js_tn_strict (t : Nat) : (ev_tn t == "StrictTrackingSliderTailCircle") = (t == 9) := by
  unfold ev_tn; split <;> simp_all

/-- `ev_ctxWF.strict` is sim7's `s7StrictOk` for the eval type-name table -/
theorem js_s7StrictOk (c : sim.state.Ctx) (hc : ev_ctxWF c) (i : Nat) : s7StrictOk ev_tn c i := by
  intro hi j hj
  rw [hc.strict i hi j hj, js_tn_strict]

end OsuProofs
