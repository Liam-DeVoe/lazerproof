/-
Lifetime: `became_alive` against `OsuModel.Sim.Sim.becameAlive` (pool_get frame with `simPoolOk`, `spinner_ticks_get`,
dictionary/free-list step, the per-kind tails, and `sim.step.became_alive_refines`).
-/
import OsuProofs.Sim.Bindings
set_option maxHeartbeats 400000  -- = the shared REPL default
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- every pooled instance index is in range -/
def simPoolOk (s : sim.state.St) : Prop :=
  ∀ p ∈ s.pools.val, ∀ j : Usize, some j ∈ p.val → j.val < s.insts.val.length

/-- the transformable predicate of `s3b_TfInv` survives position-only changes and holds for fresh pool instances -/
structure simTfX (P : Nat → sim.transforms.TObj → Prop) : Prop where
  pos : ∀ b a a', simPosFr a a' → P b a → P b a'
  new : ∀ b, b + 1 < Usize.max → P b s3b_instNew.tf ∧ P b s3b_instNew.body_tf

theorem sim_poolOk_set (s : sim.state.St) (pk : Usize) (hpk : pk.val < s.pools.val.length)
    (Q : alloc.vec.Vec (Option Usize)) (hQ : ∀ x ∈ Q.val, x ∈ (s.pools.val[pk.val]'hpk).val)
    (ins : alloc.vec.Vec sim.state.Inst) (hins : s.insts.val.length ≤ ins.val.length) (hP : simPoolOk s) :
    ∀ p ∈ (s.pools.set pk Q).val, ∀ j : Usize, some j ∈ p.val → j.val < ins.val.length := by
  intro p hp j hj
  rw [vec_set_val'] at hp
  rcases List.mem_or_eq_of_mem_set hp with hp | hp
  · exact Nat.lt_of_lt_of_le (hP p hp j hj) hins
  · subst hp
    exact Nat.lt_of_lt_of_le (hP _ (List.getElem_mem hpk) j (hQ _ hj)) hins

theorem sim_pool_get_ok (s : sim.state.St) (pk : Usize) (hpk : pk.val < s.pools.val.length)
    (hcap : s.insts.val.length < Usize.max) (hP : simPoolOk s) :
    ∃ k s', sim.step.pool_get s pk = ok (k, s') ∧
      (∃ ins' pl', s' = { s with insts := ins', pools := pl' }) ∧ s'.pools.val.length = s.pools.val.length ∧
      s.insts.val <+: s'.insts.val ∧ k.val < s'.insts.val.length ∧ simPoolOk s' ∧
      (∀ q (hq : q < s.pools.val.length) (hq' : q < s'.pools.val.length), q ≠ pk.val →
        s'.pools.val[q]'hq' = s.pools.val[q]'hq) ∧
      (∀ ins ∈ s'.insts.val, ins ∈ s.insts.val ∨ ins = s3b_instNew) := by
  unfold sim.step.pool_get
  rw [vec_index_mut_eq _ _ hpk]
  simp only [bind_ok, alloc.vec.Vec.pop]
  obtain ⟨v', k, hv', hk, hv'v, hkv⟩ := s3b_push_last s.insts s3b_instNew hcap
  have hpre : s.insts.val <+: v'.val := by rw [hv'v]; exact List.prefix_append _ _
  have hlen' : s.insts.val.length ≤ v'.val.length := hpre.length_le
  have hkl : k.val < v'.val.length := by rw [hkv, hv'v]; simp
  have hnw : ∀ ins ∈ v'.val, ins ∈ s.insts.val ∨ ins = s3b_instNew := by
    intro ins h; rw [hv'v] at h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · simp at h; exact Or.inr h
  have hdl : ∀ (P : alloc.vec.Vec (Option Usize)) pf, ∀ x ∈ (alloc.vec.Vec.from P.val.dropLast pf).val, x ∈ P.val := by
    intro P pf x hx; rw [alloc.vec.Vec.from_val] at hx; exact List.dropLast_subset _ hx
  have hother : ∀ Q : alloc.vec.Vec (Option Usize), ∀ q (hq : q < s.pools.val.length)
      (hq' : q < (s.pools.set pk Q).val.length), q ≠ pk.val → (s.pools.set pk Q).val[q]'hq' = s.pools.val[q]'hq := by
    intro Q q hq hq' hne; simp [List.getElem_set, Ne.symm hne]
  have hsl : ∀ Q : alloc.vec.Vec (Option Usize), (s.pools.set pk Q).val.length = s.pools.val.length := by
    intro Q; simp [vec_set_val']
  have hok := fun Q (hQ : ∀ x ∈ Q.val, x ∈ (s.pools.val[pk.val]'hpk).val) ins (hi : s.insts.val.length ≤ ins.val.length) =>
    sim_poolOk_set s pk hpk Q hQ ins hi hP
  generalize hPv : s.pools.val[pk.val]'hpk = P at hdl hok ⊢
  rcases hlast : P.val.getLast? with _ | x
  · simp only [uncurry_apply_pair, hlast, s3b_inst_new, hv', hk, bind_ok]
    exact ⟨k, _, rfl, ⟨_, _, rfl⟩, hsl _, hpre, hkl, hok _ (hdl P _) v' hlen', fun q hq hq' hne => hother _ q hq hq' hne,
      hnw⟩
  · rcases x with _ | j
    · simp only [uncurry_apply_pair, hlast, s3b_inst_new, hv', hk, bind_ok]
      exact ⟨k, _, rfl, ⟨_, _, rfl⟩, hsl _, hpre, hkl, hok _ (hdl P _) v' hlen', fun q hq hq' hne => hother _ q hq hq' hne,
      hnw⟩
    · simp only [uncurry_apply_pair, hlast]
      refine ⟨j, _, rfl, ⟨_, _, rfl⟩, hsl _, List.prefix_refl _, ?_, hok _ (hdl P _) s.insts (le_refl _),
        fun q hq hq' hne => hother _ q hq hq' hne, fun ins h => Or.inl h⟩
      exact hP _ (hPv ▸ List.getElem_mem hpk) j (List.mem_of_getLast? hlast)

@[reducible] def simSTG0 (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (tis : alloc.vec.Vec Usize)
    (live : alloc.vec.Vec Bool) (j : Usize) (hi : i.val < c.pb.objects.val.length) :=
  sim.step.spinner_ticks_get_loop0 c.pb.objects s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) tis live j

def simTisS (tis : alloc.vec.Vec Usize) : Array Nat := (tis.val.map (·.val)).toArray

theorem sim_stg0_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize)
    (hi : i.val < c.pb.objects.val.length)
    (hsm : (c.pb.objects.val[i.val]'hi).nested.val.length < 2 ^ 63)
    (F : Nat → Array Nat → OsuModel.Sim.SimM (ForInStep (Array Nat)))
    (hF : ∀ j r, F j r = (do
      let x ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
      let tk ← OsuModel.Sim.Sim.poolGet (if (x.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5 else 4)
      pure (ForInStep.yield (r.push tk)))) :
    ∀ m (j : Usize) (s : sim.state.St) (tis : alloc.vec.Vec Usize) (live : alloc.vec.Vec Bool),
      (c.pb.objects.val[i.val]'hi).nested.val.length - j.val = m →
      j.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length →
      tis.val.length = j.val → live.val = List.replicate j.val false →
      6 ≤ s.pools.val.length → s.insts.val.length + m < Usize.max → simPoolOk s →
      (∀ x ∈ tis.val, x.val < s.insts.val.length) →
      ∃ s' tis' live', simSTG0 c s i tis live j hi = ok (s', tis', live') ∧
        forIn (m := OsuModel.Sim.SimM) (List.range' j.val m) (simTisS tis) F (simCtxS tn fo c) (simStS tn s) =
          .ok (simTisS tis', simStS tn s') ∧
        tis'.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length ∧
        live'.val = List.replicate (c.pb.objects.val[i.val]'hi).nested.val.length false ∧
        (∃ ins pl, s' = { s with insts := ins, pools := pl }) ∧ s'.pools.val.length = s.pools.val.length ∧
        s.insts.val <+: s'.insts.val ∧ simPoolOk s' ∧ (∀ x ∈ tis'.val, x.val < s'.insts.val.length) ∧
        (∀ ins ∈ s'.insts.val, ins ∈ s.insts.val ∨ ins = s3b_instNew) := by
  intro m
  induction m with
  | zero =>
    intro j s tis live hm hj htl hlv hpl hcap hP htis
    have hge : ¬ j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
    have hjn : j.val = (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    refine ⟨s, tis, live, ?_, by simp, by rw [htl, hjn], by rw [hlv, hjn], ⟨_, _, rfl⟩, rfl, List.prefix_refl _, hP, htis,
      fun ins h => Or.inl h⟩
    unfold simSTG0 sim.step.spinner_ticks_get_loop0
    rw [loop_unfold]
    simp [sim.step.spinner_ticks_get_loop0.body, hge]
  | succ m ih =>
    intro j s tis live hm hj htl hlv hpl hcap hP htis
    have hjl : j.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    have hlt : j < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; exact hjl
    have hnp := (c.pb.objects.val[i.val]'hi).nested.property
    obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by omega)
    have hn : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.playable.HObj)
      (c.pb.objects.val[i.val]'hi).nested j = ok ((c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl) :=
      vec_index_eq _ _ hjl
    generalize hhd : (c.pb.objects.val[i.val]'hi).nested.val[j.val]'hjl = hd at hn
    have enj : OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j.val (simCtxS tn fo c) (simStS tn s) =
        .ok (hobjS tn hd, simStS tn s) := by
      rw [← hhd]; simp [OsuModel.Sim.Sim.nestedOf, OsuModel.Sim.Sim.getA, topS, hjl]
    have hpkS : ∀ b : Bool, (if b = true then (5 : Nat) else 4) = (if b = true then (5#usize : Usize) else 4#usize).val := by
      intro b; cases b <;> rfl
    set pk : Usize := if (kindS hd.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5#usize else 4#usize with hpk
    have hpk6 : pk.val < s.pools.val.length := by
      have : pk.val ≤ 5 := by rw [hpk]; split <;> decide
      omega
    obtain ⟨k, s1, epg, rpg⟩ := sim.step.pool_get_refines tn fo c s pk hpk6 (by omega)
    obtain ⟨k', s1', epg', hfr, hpl1, hpre, hkl, hP1, -, hnw⟩ := sim_pool_get_ok s pk hpk6 (by omega) hP
    rw [epg] at epg'
    simp only [ok.injEq, Prod.mk.injEq] at epg'
    obtain ⟨rfl, rfl⟩ := epg'
    obtain ⟨tis1, htis1⟩ : ∃ v, alloc.vec.Vec.push tis k = ok v ∧ v.val = tis.val ++ [k] :=
      ⟨_, vec_push_ok tis k (by omega), by simp⟩
    obtain ⟨live1, hlive1⟩ : ∃ v, alloc.vec.Vec.push live false = ok v ∧ v.val = live.val ++ [false] :=
      ⟨_, vec_push_ok live false (by rw [hlv]; simp; omega), by simp⟩
    have hb : sim.step.spinner_ticks_get_loop0.body c.pb.objects i
        (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s tis live j = ok (.cont (s1, tis1, live1, j1)) := by
      simp only [sim.step.spinner_ticks_get_loop0.body, hlt, ite_true, vec_index_eq _ _ hi, bind_ok, hn, kind_eq_ok]
      have : (kindS sim.playable.Kind.SpinnerBonusTick) = OsuModel.Sim.Kind.spinnerBonusTick := rfl
      simp only [this]
      rw [show (if (kindS hd.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then ok 5#usize else ok 4#usize : Result Usize) = ok pk by
        rw [hpk]; split <;> rfl]
      simp only [bind_ok, epg, uncurry_apply_pair, htis1.1, hlive1.1, hj1]
    have hstep : simSTG0 c s i tis live j hi = simSTG0 c s1 i tis1 live1 j1 hi := by
      unfold simSTG0 sim.step.spinner_ticks_get_loop0
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
    obtain ⟨ins1, pl1, hs1⟩ := hfr
    have htis1' : ∀ x ∈ tis1.val, x.val < s1.insts.val.length := by
      intro x hx; rw [htis1.2] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Nat.lt_of_lt_of_le (htis x hx) hpre.length_le
      · simp at hx; subst hx; exact hkl
    obtain ⟨s', tis', live', e', r', l1, l2, l3, l4, l5, l6, l7, l8⟩ := ih j1 s1 tis1 live1 (by omega) (by omega)
      (by rw [htis1.2]; simp; omega) (by rw [hlive1.2, hlv, hj1v, List.replicate_succ']) (by omega)
      (by rcases rpg.2.2.2.1 with h | ⟨h, _⟩ <;> rw [h] <;> (try simp) <;> omega) hP1 htis1'
    refine ⟨s', tis', live', by rw [hstep]; exact e', ?_, l1, l2, ?_, by omega, hpre.trans l5, l6, l7, ?_⟩
    · rw [List.range'_succ, List.forIn_cons, hF]
      simp only [simM_bind, enj, Except.bind]
      have hkS : (hobjS tn hd).kind = kindS hd.kind := rfl
      rw [hkS, hpkS, ← hpk, rpg.1]
      simp only [simM_pure]
      have : (simTisS tis).push k.val = simTisS tis1 := by simp [simTisS, htis1.2]
      rw [this, show j.val + 1 = j1.val from hj1v.symm]
      exact r'
    · obtain ⟨a, b, hsa⟩ := l3; rw [hsa, hs1]; exact ⟨a, b, rfl⟩
    · intro ins h
      rcases l8 ins h with h | h
      · exact hnw ins h
      · exact Or.inr h

@[reducible] def simSTG1 (c : sim.state.Ctx) (s : sim.state.St) (i n q : Usize) :=
  sim.step.spinner_ticks_get_loop1 c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in c.pb.difficulty
    c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects c.frames c.steps
    c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames c.block_periods
    c.first_obj s i n q

/-- the body of becameAlive's tick-state loop (membership proof dropped) -/
def simSTG1G (i : Nat) (T : Array Nat) (a : Nat) (_ : PUnit) : OsuModel.Sim.SimM (ForInStep PUnit) := do
  let x ← OsuModel.Sim.Sim.instOf T[a]!
  if x.loaded = true then do
    OsuModel.Sim.Sim.tickState i a 1 OsuModel.Sim.Armed.idle true
    pure (ForInStep.yield PUnit.unit)
  else pure (ForInStep.yield PUnit.unit)

theorem sim_stg1_loop (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (TI : alloc.vec.Vec Usize)
    (hTI : TI.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length) :
    ∀ m (q : Usize) (s : sim.state.St), (c.pb.objects.val[i.val]'hi).nested.val.length - q.val = m →
      q.val ≤ (c.pb.objects.val[i.val]'hi).nested.val.length → SimInv c s →
      (∀ hio : i.val < s.objs.val.length, (s.objs.val[i.val]'hio).tick_insts = TI) →
      (∀ x ∈ TI.val, x.val < s.insts.val.length) →
      ∀ (L : List Nat) (f : (a : Nat) → a ∈ L → PUnit → OsuModel.Sim.SimM (ForInStep PUnit)),
      L = List.range' q.val m → (∀ a h u, f a h u = simSTG1G i.val (simTisS TI) a u) →
      ∃ s', simSTG1 c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) q = ok s' ∧
        forIn' (m := OsuModel.Sim.SimM) L PUnit.unit f (simCtxS tn fo c) (simStS tn s) = .ok (PUnit.unit, simStS tn s') ∧
        SimInv c s' ∧ s'.objs = s.objs ∧ s'.insts.val.length = s.insts.val.length ∧
        (∃ ins th, s' = { s with insts := ins, theta := th }) ∧
        (∀ (P : Nat → sim.transforms.TObj → Prop) B, s3b_TfInv P B s → s3b_TfInv P B s') := by
  have hc : (⟨c.env, c.cfg, ⟨c.pb.beatmap_version, c.pb.audio_lead_in, c.pb.difficulty, c.pb.base_difficulty,
      c.pb.slider_multiplier, c.pb.slider_tick_rate, c.pb.breaks, c.pb.objects⟩, c.frames, c.steps, c.head_idx,
      c.tail_idx, c.smax, c.hcfg, c.last_frame_time, c.corner_pow, c.prec_end, c.ap_frames, c.block_periods,
      c.first_obj⟩ : sim.state.Ctx) = c := rfl
  intro m
  induction m with
  | zero =>
    intro q s hm hq hinv hti htk L f hL hf
    subst hL
    refine ⟨s, ?_, by simp, hinv, rfl, rfl, ⟨_, _, rfl⟩, fun _ _ h => h⟩
    have hge : ¬ q < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; omega
    unfold simSTG1 sim.step.spinner_ticks_get_loop1
    rw [loop_unfold]
    simp [sim.step.spinner_ticks_get_loop1.body, hge]
  | succ m ih =>
    intro q s hm hq hinv hti htk L f hL hf
    rw [List.range'_succ] at hL
    subst hL
    have hql : q.val < (c.pb.objects.val[i.val]'hi).nested.val.length := by omega
    have hlt : q < alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested := by rw [vec_lt_len_iff]; exact hql
    have hnp := (c.pb.objects.val[i.val]'hi).nested.property
    obtain ⟨q1, hq1, hq1v⟩ := usize_add_one q (by omega)
    have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
    have htis := hti ho
    have htj : q.val < (s.objs.val[i.val]'ho).tick_insts.val.length := by rw [htis, hTI]; exact hql
    have hqT : q.val < TI.val.length := by rw [hTI]; exact hql
    have htkq : ((s.objs.val[i.val]'ho).tick_insts.val[q.val]'htj).val < s.insts.val.length := by
      have : (s.objs.val[i.val]'ho).tick_insts.val[q.val]'htj = TI.val[q.val]'hqT := by simp [htis]
      rw [this]; exact htk _ (List.getElem_mem _)
    have hTq : (simTisS TI)[q.val]! = (TI.val[q.val]'hqT).val := by
      simp [simTisS, hqT]
    have hkS : (TI.val[q.val]'hqT).val < s.insts.val.length := htk _ (List.getElem_mem _)
    have hti' : (s.objs.val[i.val]'ho).tick_insts.val[q.val]'htj = TI.val[q.val]'hqT := by simp [htis]
    rw [List.forIn'_cons, hf]
    simp only [simSTG1G, simM_bind, hTq, s3a_instOf tn fo c s _ hkS, Except.bind]
    have hstep : ∀ s1, sim.step.spinner_ticks_get_loop1.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
        c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects
        c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
        c.block_periods c.first_obj i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s q = ok (.cont (s1, q1)) →
        simSTG1 c s i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) q =
          simSTG1 c s1 i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) q1 := by
      intro s1 hb
      unfold simSTG1 sim.step.spinner_ticks_get_loop1
      rw [loop_unfold]; dsimp only; rw [hb]; simp only [bind_ok]
    have hloaded : (abs (s.insts.val[(TI.val[q.val]'hqT).val]'hkS) : OsuModel.Sim.Inst).loaded =
      (s.insts.val[(TI.val[q.val]'hqT).val]'hkS).loaded := rfl
    rw [hloaded]
    by_cases hld : (s.insts.val[(TI.val[q.val]'hqT).val]'hkS).loaded = true
    · obtain ⟨s1, e1, r1, ⟨ins1, th1, hs1⟩, hl1, hinv1, -, ho1, -⟩ :=
        sim.step.tick_state_refines tn fo c s i q 1#u64 .Idle true hinv hi hql ho htj htkq
      have hb : sim.step.spinner_ticks_get_loop1.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
          c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects
          c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
          c.block_periods c.first_obj i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s q =
          ok (.cont (s1, q1)) := by
        simp only [sim.step.spinner_ticks_get_loop1.body, hlt, ite_true, vec_index_eq _ _ ho, vec_index_eq _ _ htj,
          bind_ok, hti', vec_index_eq _ _ hkS, hld, hc, e1, hq1]
      rw [hstep s1 hb, hld]
      simp only [ite_true, simM_bind]
      have hab : (abs (sim.state.Armed.Idle) : OsuModel.Sim.Armed) = .idle := rfl
      rw [show ((1#u64 : U64).val) = 1 from rfl] at r1
      rw [← hab, r1]
      simp only [Except.bind, simM_pure]
      have hti1 : ∀ hio : i.val < s1.objs.val.length, (s1.objs.val[i.val]'hio).tick_insts = TI := by
        intro hio; have := ho1 ▸ hti; exact this hio
      have htf1 := sim.step.tick_state_tfSame c s i q 1#u64 .Idle true hinv hi hql ho htj htkq s1 e1
      obtain ⟨s', e', r', i', o', l', f', t'⟩ := ih q1 s1 (by omega) (by omega) hinv1 hti1 (by rw [hl1]; exact htk)
        (List.range' (q.val + 1) m) (fun a h u => f a (List.mem_cons_of_mem _ h) u) (by rw [hq1v])
        (fun a h u => hf a _ u)
      refine ⟨s', e', r', i', o'.trans ho1, l'.trans hl1, ?_, fun P B h => t' P B (s3b_tfinv_of_tfSame htf1 h)⟩
      · obtain ⟨a, b, hab'⟩ := f'; rw [hab', hs1]; exact ⟨a, b, rfl⟩
    · have hb : sim.step.spinner_ticks_get_loop1.body c.env c.cfg c.pb.beatmap_version c.pb.audio_lead_in
          c.pb.difficulty c.pb.base_difficulty c.pb.slider_multiplier c.pb.slider_tick_rate c.pb.breaks c.pb.objects
          c.frames c.steps c.head_idx c.tail_idx c.smax c.hcfg c.last_frame_time c.corner_pow c.prec_end c.ap_frames
          c.block_periods c.first_obj i (alloc.vec.Vec.len (c.pb.objects.val[i.val]'hi).nested) s q =
          ok (.cont (s, q1)) := by
        simp only [sim.step.spinner_ticks_get_loop1.body, hlt, ite_true, vec_index_eq _ _ ho, vec_index_eq _ _ htj,
          bind_ok, hti', vec_index_eq _ _ hkS, hld, hq1, Bool.false_eq_true, ite_false]
      rw [hstep s hb]
      simp only [hld, Bool.false_eq_true, ite_false, simM_pure]
      obtain ⟨s', e', r', i', o', l', f', t'⟩ := ih q1 s (by omega) (by omega) hinv hti htk
        (List.range' (q.val + 1) m) (fun a h u => f a (List.mem_cons_of_mem _ h) u) (by rw [hq1v])
        (fun a h u => hf a _ u)
      exact ⟨s', e', r', i', o', l', f', t'⟩

-- FRAGMENT-OF: OsuModel.Sim.Sim.becameAlive (its spinner tick-instance block, stated verbatim; bridged in became_alive_refines)
theorem sim.step.spinner_ticks_get_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (i : Usize) (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s)
    (hpl : 6 ≤ s.pools.val.length)
    (hcap : s.insts.val.length + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max) (hP : simPoolOk s) :
    ∃ s', sim.step.spinner_ticks_get c s i = ok s' ∧
      (do
        let tis ← forIn (m := OsuModel.Sim.SimM) [:(topS tn (c.pb.objects.val[i.val]'hi)).nested.size] (#[] : Array Nat)
          (fun j r => do
            let x ← OsuModel.Sim.Sim.nestedOf (topS tn (c.pb.objects.val[i.val]'hi)) j
            let tk ← OsuModel.Sim.Sim.poolGet (if (x.kind == OsuModel.Sim.Kind.spinnerBonusTick) = true then 5 else 4)
            pure (ForInStep.yield (r.push tk)))
        OsuModel.Sim.Sim.modifyObj i.val fun os =>
          { os with tickInsts := tis, tickLive := Array.map (fun _ => false) tis }
        forIn' (m := OsuModel.Sim.SimM) [:tis.size] PUnit.unit fun j h _ => do
          let x ← OsuModel.Sim.Sim.instOf tis[j]
          if x.loaded = true then do
            OsuModel.Sim.Sim.tickState i.val j 1 OsuModel.Sim.Armed.idle true
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)) (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      SimInv c s' ∧ s'.pools.val.length = s.pools.val.length ∧ simPoolOk s' ∧
      s.insts.val.length ≤ s'.insts.val.length ∧
      (∀ (P : Nat → sim.transforms.TObj → Prop), simTfX P → ∀ B, B + 1 < Usize.max → s3b_TfInv P B s → s3b_TfInv P B s') ∧
      (∀ (h : i.val < s.objs.val.length) (h' : i.val < s'.objs.val.length),
        (s'.objs.val[i.val]'h').inst = (s.objs.val[i.val]'h).inst ∧
        (s'.objs.val[i.val]'h').head_inst = (s.objs.val[i.val]'h).head_inst) := by
  have hsm := hinv.nested_small _ (List.getElem_mem hi)
  have hsz : (topS tn (c.pb.objects.val[i.val]'hi)).nested.size = (c.pb.objects.val[i.val]'hi).nested.val.length := by
    simp [topS]
  have hnew : simTisS (alloc.vec.Vec.new Usize) = #[] := rfl
  obtain ⟨s1, tis, live, e0, r0, htl, hlv, ⟨ins1, pl1, hs1⟩, hpl1, hpre, hP1, htis, hnw0⟩ :=
    sim_stg0_loop tn fo c i hi (by omega) _ (fun _ _ => rfl) (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s (alloc.vec.Vec.new Usize)
      (alloc.vec.Vec.new Bool) (by simp) (by simp) (by simp) (by simp) hpl (by simpa using hcap) hP (by simp)
  have h00 : (0#usize).val = 0 := rfl
  simp only [h00, hnew] at r0
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  have ho1 : i.val < s1.objs.val.length := by rw [hs1]; exact ho
  have hinv1 : SimInv c s1 := by rw [hs1]; exact ⟨hinv.objs_len, hinv.nested_len, hinv.nested_small, hinv.dict_in, hinv.dict_small⟩
  set o := s1.objs.val[i.val]'ho1 with ho_def
  let o' : sim.state.OState := { o with tick_insts := tis, tick_live := live }
  let s2 : sim.state.St := { s1 with objs := s1.objs.set i o' }
  have hinv2 : SimInv c s2 := ⟨by simp [s2, vec_set_val', hinv1.objs_len], fun j h1 h2 => by
      simp only [s2, vec_set_val'] at h1 ⊢
      by_cases e : j = i.val
      · subst e; simp [o', o]; exact hinv1.nested_len _ ho1 h2
      · simp [List.getElem_set, Ne.symm e]; exact hinv1.nested_len _ _ h2, hinv1.nested_small, hinv1.dict_in,
      hinv1.dict_small⟩
  have hti2 : ∀ hio : i.val < s2.objs.val.length, (s2.objs.val[i.val]'hio).tick_insts = tis := by
    intro hio; simp [s2, vec_set_val', o']
  have htk2 : ∀ x ∈ tis.val, x.val < s2.insts.val.length := htis
  have hsimS : ((simTisS tis).size) = (c.pb.objects.val[i.val]'hi).nested.val.length := by simp [simTisS, htl]
  obtain ⟨s', e1, r1, i1, o1', l1, f1, t1⟩ := sim_stg1_loop tn fo c i hi tis htl
    (c.pb.objects.val[i.val]'hi).nested.val.length 0#usize s2 (by simp) (by simp) hinv2 hti2 htk2
    (List.range' 0 (c.pb.objects.val[i.val]'hi).nested.val.length)
    (fun a h u => (do
          let x ← OsuModel.Sim.Sim.instOf ((simTisS tis)[a]'(by simp at h; rw [hsimS]; omega))
          if x.loaded = true then do
            OsuModel.Sim.Sim.tickState i.val a 1 OsuModel.Sim.Armed.idle true
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit) : OsuModel.Sim.SimM (ForInStep PUnit)))
    (by simp) (fun a h u => by
      simp at h
      simp only [simSTG1G, getElem!_pos (simTisS tis) a (by rw [hsimS]; omega)])
  refine ⟨s', ?_, ?_, i1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sim.step.spinner_ticks_get
    simp only [simSTG0] at e0
    simp only [vec_index_eq _ _ hi, bind_ok, e0, uncurry_apply_pair, vec_index_mut_eq _ _ ho1]
    rw [vec_index_mut_eq _ _ (by simp [vec_set_val']; exact ho1)]
    simp only [bind_ok, uncurry_apply_pair]
    simp only [simSTG1] at e1
    convert e1 using 2
    simp only [s2, o', o]
    congr 1
    apply alloc.vec.Vec.ext
    simp [vec_set_val']
  · rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsz]
    simp only [simM_bind, r0, Except.bind]
    rw [sim_modifyObj_stS tn _ s1 i ho1 o' _ (by
      simp only [ostateS, o', o]
      congr 1
      all_goals simp [abs, simTisS, hlv, htl]) _ rfl]
    simp only [Except.bind]
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    simp only [Std.Legacy.Range.size, Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel, hsimS]
    exact r1
  · obtain ⟨a, b, hab⟩ := f1; rw [hab]; exact hpl1
  · obtain ⟨a, b, hab⟩ := f1
    intro p hp j hj
    have hp' : p ∈ s1.pools.val := by rw [hab] at hp; exact hp
    rw [l1]; exact hP1 p hp' j hj
  · rw [l1]; exact hpre.length_le
  · intro P X B hB h
    apply t1 P B
    intro ins hm
    rcases hnw0 ins hm with hm | hm
    · exact h ins hm
    · subst hm; exact X.new B hB
  · intro h h'
    have e2 : s'.objs.val = (s1.objs.set i o').val := by rw [o1']
    have hh : (s'.objs.val[i.val]'h') = o' := by simp only [e2, vec_set_val', List.getElem_set_self]
    rw [hh]
    have hs1o : s1.objs = s.objs := by rw [hs1]
    simp only [o', o, hs1o]
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl | simp


theorem sim_u64_add_one (i : U64) (h : i.val + 1 ≤ U64.max) : ∃ z, i + 1#u64 = ok z ∧ z.val = i.val + 1 := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.add_spec (x := i) (y := 1#u64) (by simpa using h))
  exact ⟨z, hz, by simpa using hv⟩

/-- the dictionary-slot update of `became_alive` (free list popped from the end = the spec's list head) -/
theorem sim_ba_dict2 (tn) (s : sim.state.St) (i : Usize) (hsmall : s.dict_slots.val.length < Usize.max)
    (hfree : ∀ x ∈ s.free_list.val, x.val < s.dict_slots.val.length) :
    ∃ v1, (match s.free_list.val.getLast? with
        | none => alloc.vec.Vec.push s.dict_slots (some i)
        | some slot => do
          let (_, index_mut_back) ←
            alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Option Usize)) s.dict_slots slot
          ok (index_mut_back (some i))) = ok v1 ∧
      ((simStS tn s).freeList = [] → (simStS tn s).dictSlots.push (some i.val) = (abs v1 : _root_.Array (Option Nat)) ∧
        ([] : List Nat) = (s.free_list.val.dropLast.map (·.val)).reverse) ∧
      (∀ slot rest, (simStS tn s).freeList = slot :: rest →
        (∀ C S, OsuModel.Sim.Sim.setA (simStS tn s).dictSlots slot (some i.val) "dictionary entries" C S =
          .ok ((abs v1 : _root_.Array (Option Nat)), S)) ∧ rest = (s.free_list.val.dropLast.map (·.val)).reverse) ∧
      ∀ o ∈ v1.val, o ∈ s.dict_slots.val ∨ o = some i := by
  have hfl : (simStS tn s).freeList = (s.free_list.val.map (·.val)).reverse := rfl
  have hds : (simStS tn s).dictSlots = (abs s.dict_slots : _root_.Array (Option Nat)) := rfl
  rw [hfl, hds]
  rcases List.eq_nil_or_concat s.free_list.val with h | ⟨L, x, h⟩
  · simp only [h, List.getLast?_nil, List.map_nil, List.reverse_nil, List.dropLast_nil]
    refine ⟨_, vec_push_ok _ _ hsmall, fun _ => ⟨by simp [abs], by simp⟩, fun _ _ h => absurd h (by simp), ?_⟩
    intro o ho; simp at ho; rcases ho with ho | ho
    · exact Or.inl ho
    · exact Or.inr ho
  · have hx : x.val < s.dict_slots.val.length := hfree x (by rw [h]; simp)
    simp only [h, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.dropLast_concat]
    refine ⟨s.dict_slots.set x (some i), by simp [vec_index_mut_eq _ _ hx], fun h => by simp at h, ?_, ?_⟩
    · intro slot rest hsr
      simp at hsr
      obtain ⟨rfl, rfl⟩ := hsr
      refine ⟨fun C S => ?_, by simp⟩
      simp [OsuModel.Sim.Sim.setA, abs, hx, vec_set_val', List.map_set]
    · intro o ho
      rw [vec_set_val'] at ho
      rcases List.mem_or_eq_of_mem_set ho with ho | ho
      · exact Or.inl ho
      · exact Or.inr ho

/-- the part of `became_alive` after the main `pool_get` (verbatim copy of the generated body) -/
def simBATailR (c : sim.state.Ctx) (s1 : sim.state.St) (i : Std.Usize) («to» : sim.playable.TopObj)
    (cid : Std.U64) (k : Std.Usize) : Result ((core.result.Result Unit sim.err.SimErr) × sim.state.St) := do
  let b ←
    sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq «to».h.kind
      sim.playable.Kind.Slider
  let (s2, hk) ←
    if b
    then do
         let (hk1, s3) ← sim.step.pool_get s1 2#usize
         ok (s3, hk1)
    else ok (s1, 0#usize)
  let i2 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice sim.state.Inst)
      s2.insts k
  let ha0 ←
    if b
    then
      do
      let i3 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          sim.state.Inst) s2.insts hk
      ok i3.armed
    else ok sim.state.Armed.Idle
  let (os, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      sim.state.OState) s2.objs i
  let f ← sim.netx.F64_POS_INF
  let f1 ← sim.basic.F32_0
  let f2 ← sim.netx.F64_NEG_INF
  if b
  then
    let v3 :=
      index_mut_back
        {
          os
            with
            life := sim.state.Life.Alive,
            child_id := cid,
            hit_action := none,
            hovered := false,
            head_lifetime_end := f,
            head_alive := false,
            tracking := false,
            inst := k,
            head_inst := hk,
            armed := i2.armed,
            head_armed := ha0,
            accept_any_after := none,
            last_pressed := replay.frames.ACTLIST_EMPTY,
            slider_mouse := none,
            spin_tracking := false,
            spin_mouse := none,
            last_angle := none,
            total_accumulated := f1,
            accumulated_at_last_completion := f1,
            current_spin_max := f1,
            completed_spins := 0#u64,
            last_report_time := f2,
            completed_full_spins := 0#i64
        }
    let (r, s3) ←
      sim.step.apply_bindings c { s2 with objs := v3 } i sim.step.Part.Head hk
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i3 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          sim.state.Inst) s3.insts hk
      let s4 ←
        if i3.loaded
        then sim.step.update_state_from_result c s3 i sim.step.Part.Head 1#u64
        else ok s3
      let b1 ←
        sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq «to».h.kind
          sim.playable.Kind.Spinner
      let s5 ← if b1
                 then sim.step.spinner_ticks_get c s4 i
                 else ok s4
      let (r1, s6) ← sim.step.apply_bindings c s5 i sim.step.Part.Top k
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let i4 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            sim.state.Inst) s6.insts k
        if i4.loaded
        then
          let s7 ←
            sim.step.update_state_from_result c s6 i sim.step.Part.Top 1#u64
          ok (core.result.Result.Ok (), s7)
        else ok (core.result.Result.Ok (), s6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame sim.err.SimErr) residual
        ok (r2, s6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r1, s3)
  else
    let b1 ←
      sim.playable.Kind.Insts.CoreCmpPartialEqKind.eq «to».h.kind
        sim.playable.Kind.Spinner
    let s3 ←
      if b1
      then
        let v3 :=
          index_mut_back
            {
              os
                with
                life := sim.state.Life.Alive,
                child_id := cid,
                hit_action := none,
                hovered := false,
                head_lifetime_end := f,
                head_alive := false,
                tracking := false,
                inst := k,
                head_inst := hk,
                armed := i2.armed,
                head_armed := ha0,
                accept_any_after := none,
                last_pressed := replay.frames.ACTLIST_EMPTY,
                slider_mouse := none,
                spin_tracking := false,
                spin_mouse := none,
                last_angle := none,
                total_accumulated := f1,
                accumulated_at_last_completion := f1,
                current_spin_max := f1,
                completed_spins := 0#u64,
                last_report_time := f2,
                completed_full_spins := 0#i64
            }
        sim.step.spinner_ticks_get c { s2 with objs := v3 } i
      else
        let v3 :=
          index_mut_back
            {
              os
                with
                life := sim.state.Life.Alive,
                child_id := cid,
                hit_action := none,
                hovered := false,
                head_lifetime_end := f,
                head_alive := false,
                tracking := false,
                inst := k,
                head_inst := hk,
                armed := i2.armed,
                head_armed := ha0,
                accept_any_after := none,
                last_pressed := replay.frames.ACTLIST_EMPTY,
                slider_mouse := none,
                spin_tracking := false,
                spin_mouse := none,
                last_angle := none,
                total_accumulated := f1,
                accumulated_at_last_completion := f1,
                current_spin_max := f1,
                completed_spins := 0#u64,
                last_report_time := f2,
                completed_full_spins := 0#i64
            }
        ok { s2 with objs := v3 }
    let (r, s4) ← sim.step.apply_bindings c s3 i sim.step.Part.Top k
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i3 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          sim.state.Inst) s4.insts k
      if i3.loaded
      then
        let s5 ←
          sim.step.update_state_from_result c s4 i sim.step.Part.Top 1#u64
        ok (core.result.Result.Ok (), s5)
      else ok (core.result.Result.Ok (), s4)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame sim.err.SimErr) residual
      ok (r1, s4)

theorem sim_ba_split (c s i) : sim.step.became_alive c s i = (do
  let «to» ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      sim.playable.TopObj) c.pb.objects i
  let (o, v) ← alloc.vec.Vec.pop alloc.alloc.Global s.free_list
  let v1 ←
    match o with
    | none => alloc.vec.Vec.push s.dict_slots (some i)
    | some slot =>
      do
      let (_, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Option
          Std.Usize)) s.dict_slots slot
      ok (index_mut_back (some i))
  let cid ← s.child_counter + 1#u64
  let v2 ← alloc.vec.Vec.push s.active i
  let i1 ← sim.step.pool_kind «to».h.kind
  let (k, s1) ←
    sim.step.pool_get
      {
        s
          with
          active := v2, dict_slots := v1, free_list := v, child_counter := cid
      } i1
  simBATailR c s1 i «to» cid k) := rfl

open OsuModel.Net OsuModel.Replay OsuModel.Sim OsuModel.Sim.Sim in
/-- the part of `becameAlive` after the dictionary/active update (verbatim copy of the spec body) -/
def simBATailS (i : Nat) (o : OsuModel.Sim.TopObj) (cid k : Nat) : OsuModel.Sim.SimM Unit := do
  let hk ← if o.h.kind == .slider then poolGet 2 else pure 0
  let a0 := (← instOf k).armed
  let ha0 := (← instOf hk).armed
  modifyObj i fun os => { os with armed := a0, headArmed := if o.h.kind == .slider then ha0 else .idle }
  modifyObj i fun os =>
    { os with
      life := .alive, childId := cid, hitAction := none, inst := k, headInst := hk
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 }
  -- `Apply` runs `updateStateFromResult` only `if (IsLoaded)` (`DrawableHitObject.cs:311-319`); pool instances are only
  -- `LoadComponents`-loaded (`LoadState.Ready`, `DrawablePool.cs:53-61`) until their first `UpdateSubTree`, so a fresh
  -- instance gets its first state update from `LoadComplete` instead
  if o.h.kind == .slider then
    applyBindings i .head hk
    if (← instOf hk).loaded then updateStateFromResult i .head 1
  if o.h.kind == .spinner then
    let mut tis : Array Nat := #[]
    for j in [0:o.nested.size] do
      let tk ← poolGet (if (← nestedOf o j).kind == .spinnerBonusTick then 5 else 4)
      tis := tis.push tk
    modifyObj i fun os => { os with tickInsts := tis, tickLive := tis.map fun _ => false }
    for h : j in [0:tis.size] do
      if (← instOf (tis[j]'h.upper)).loaded then tickState i j 1 .idle true
  applyBindings i .top k
  if (← instOf k).loaded then updateStateFromResult i .top 1


open OsuModel.Net OsuModel.Replay OsuModel.Sim OsuModel.Sim.Sim in
theorem sim_ba_splitS (i : Nat) : OsuModel.Sim.Sim.becameAlive i = (do
  let o ← topObj i
  let s ← st
  let (slots, free) ← match s.freeList with
    | slot :: rest => do pure (← setA s.dictSlots slot (some i) "dictionary entries", rest)
    | [] => pure (s.dictSlots.push (some i), [])
  set { s with childCounter := s.childCounter + 1, dictSlots := slots, freeList := free, active := s.active.push i }
  let cid := (← st).childCounter
  let k ← poolGet (poolKind o.h.kind)
  simBATailS i o cid k) := rfl

theorem sim_stS_ba (tn) (s : sim.state.St) (i : Usize) (v1 : alloc.vec.Vec (Option Usize)) (FL v2 : alloc.vec.Vec Usize)
    (cid : U64) (hv2 : v2.val = s.active.val ++ [i]) (hcid : cid.val = s.child_counter.val + 1) :
    simStS tn { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } =
      { simStS tn s with
          childCounter := (simStS tn s).childCounter + 1
          dictSlots := (abs v1 : _root_.Array (Option Nat))
          freeList := (FL.val.map (fun x => x.val)).reverse
          active := (simStS tn s).active.push i.val } := by
  simp only [simStS, hcid]
  congr 1
  simp [abs, hv2]

theorem sim_tf_pg {P : Nat → sim.transforms.TObj → Prop} (X : simTfX P) {B : Nat} (hB : B + 1 < Usize.max) {s s' : sim.state.St}
    (h : s3b_TfInv P B s) (hi : s'.insts.val = s.insts.val ∨ (s'.insts.val = s.insts.val ++ [s3b_instNew] ∧ True)) :
    s3b_TfInv P B s' := by
  intro ins hm
  rcases hi with hi | ⟨hi, -⟩ <;> rw [hi] at hm
  · exact h ins hm
  · rcases List.mem_append.1 hm with hm | hm
    · exact h ins hm
    · simp at hm; subst hm; exact X.new B hB

theorem sim_tf_ab {P : Nat → sim.transforms.TObj → Prop} (X : simTfX P) {B : Nat} {s : sim.state.St} {k : Usize}
    (hk : k.val < s.insts.val.length) {Y : sim.state.Inst}
    (h : s3b_TfInv P B s) (hY : simABFr (s.insts.val[k.val]'hk) Y) :
    s3b_TfInv P B { s with insts := s.insts.set k Y } := by
  intro ins hm
  simp only [vec_set_val'] at hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact h ins hm
  · subst hm
    have := h _ (List.getElem_mem hk)
    exact ⟨X.pos _ _ _ hY.tf this.1, hY.body_tf ▸ this.2⟩

theorem sim_tf_mono {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) {B B' : Nat} {s : sim.state.St}
    (h : s3b_TfInv P B s) (hb : B' ≤ B) : s3b_TfInv P B' s :=
  fun ins hm => ⟨E.mono _ _ _ hb (h ins hm).1, E.mono _ _ _ hb (h ins hm).2⟩

theorem sim_inv_objs_set {c : sim.state.Ctx} {s : sim.state.St} {i : Usize} (h : SimInv c s) (O : sim.state.OState)
    (ho : i.val < s.objs.val.length) (hn : O.nested.val.length = (s.objs.val[i.val]'ho).nested.val.length) :
    SimInv c { s with objs := s.objs.set i O } := by
  refine ⟨by simpa [vec_set_val'] using h.objs_len, ?_, h.nested_small, h.dict_in, h.dict_small⟩
  intro j h1 h2
  simp only [vec_set_val'] at h1 ⊢
  by_cases hj : i.val = j
  · subst hj; simp only [List.getElem_set_self]; rw [hn]; exact h.nested_len _ ho h2
  · rw [List.getElem_set_ne hj]; exact h.nested_len _ _ h2

theorem sim_ex_bind3 {ε α β γ δ : Type} (A : Except ε α) (M : α → Except ε β) (F : α → β → Except ε γ) (r : γ)
    (h : (A.bind fun v => (M v).bind (F v)) = .ok r) (K : γ → Except ε δ) :
    (A.bind fun v => (M v).bind fun v1 => (F v v1).bind K) = K r := by
  cases hA : A with
  | error e => rw [hA] at h; simp [Except.bind] at h
  | ok a =>
    rw [hA] at h; simp only [Except.bind] at h ⊢
    cases hM : M a with
    | error e => rw [hM] at h; simp at h
    | ok b =>
      rw [hM] at h; simp only at h ⊢
      rw [h]

theorem sim_vset_set {α} (v : alloc.vec.Vec α) (i : Usize) (x y : α) : (v.set i x).set i y = v.set i y := by
  apply alloc.vec.Vec.ext; simp [vec_set_val']

set_option hygiene false in
/-- `became_alive` from the Top `apply_bindings` on (state `sT`) -/
macro "ba_top" : tactic => `(tactic| (
  obtain ⟨r2, s6, ea2, sa2, Y2, hY2, fY2⟩ := sim.step.apply_bindings_refines tn fo c sT i .Top k hi hhi hkT
    (fun h => by cases h)
  simp only [ea2, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch]
  cases r2 with
  | Err e =>
    obtain ⟨m, hm⟩ := sa2
    refine ⟨.Err e, s6, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
      ⟨m, ?_⟩, fun h => by cases h⟩
    have hm' : OsuModel.Sim.Sim.applyBindings i.val .top k.val (simCtxS tn fo c) (simStS tn sT) = .error m := hm
    simp only [hm', simM_bind, Except.bind]
  | Ok u =>
    have sa2' : OsuModel.Sim.Sim.applyBindings i.val .top k.val (simCtxS tn fo c) (simStS tn sT) =
      .ok ((), simStS tn s6) := sa2
    subst hY2
    have hk6 : k.val < (sT.insts.set k Y2).val.length := by simpa [vec_set_val'] using hkT
    have hl6 : ((sT.insts.set k Y2).val[k.val]'hk6).loaded = (sT.insts.val[k.val]'hkT).loaded := by
      simp only [vec_set_val', List.getElem_set_self]; exact fY2.loaded
    simp only [sa2', simM_bind, Except.bind, s3a_instOf tn fo c { sT with insts := sT.insts.set k Y2 } _ hk6, vec_index_eq _ _ hk6, hl6, bind_ok]
    have hlS6 : (abs ((sT.insts.set k Y2).val[k.val]'hk6) : OsuModel.Sim.Inst).loaded =
      (sT.insts.val[k.val]'hkT).loaded := hl6
    rw [hlS6]
    by_cases hl : (sT.insts.val[k.val]'hkT).loaded = true
    · have hTf6 : s3b_TfInv P (b + n + n + 4) { sT with insts := sT.insts.set k Y2 } := sim_tf_ab X hkT hTfT fY2
      obtain ⟨s7, eu, su, hinv7, hTf7, -⟩ := sim.step.update_state_from_result_refines tn fo E b n c
        { sT with insts := sT.insts.set k Y2 } i .Top 1#u64
        ⟨hinvT.objs_len, hinvT.nested_len, hinvT.nested_small, hinvT.dict_in, hinvT.dict_small⟩ hTf6
        (fun ns => hCS i .Top ns hi hhi hhb (fun h => by cases h)) hioT
        (by simpa [vec_set_val'] using hk1T) (by simpa [vec_set_val'] using hk2T) hhi hhb hhnT
      have su' : OsuModel.Sim.Sim.updateStateFromResult i.val .top 1 (simCtxS tn fo c)
        (simStS tn { sT with insts := sT.insts.set k Y2 }) = .ok ((), simStS tn s7) := su
      refine ⟨.Ok (), s7, by simp [hl, eu], ?_, fun _ => ⟨hinv7, hTf7⟩⟩
      simp only [hl, if_true, su']
      rfl
    · refine ⟨.Ok (), { sT with insts := sT.insts.set k Y2 }, by simp [hl], ?_, fun _ =>
        ⟨⟨hinvT.objs_len, hinvT.nested_len, hinvT.nested_small, hinvT.dict_in, hinvT.dict_small⟩,
         sim_tf_ab X hkT (sim_tf_mono E hTfT (by omega)) fY2⟩⟩
      simp only [hl, Bool.false_eq_true, if_false, simM_pure, simRelM]))

theorem sim_ba_tail_slider (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider) (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s) (hB : b + n + n + 4 + (n + n + 4) + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s') := by
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  unfold simBATailR simBATailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  rw [hkS, hsl]
  obtain ⟨hk1, s3, e1', ⟨ins3, pl3, hs3⟩, hpl3, hpre3, hk1l, hP3, -⟩ := sim_pool_get_ok s 2#usize (by simp; omega)
    (by omega) hP
  obtain ⟨hk1', s3', e1, s1e, -, -, hins, -⟩ := sim.step.pool_get_refines tn fo c s 2#usize (by simp; omega)
    (by omega)
  rw [e1] at e1'; simp only [ok.injEq, Prod.mk.injEq] at e1'; obtain ⟨h1', h2'⟩ := e1'; subst hk1'; subst s3'
  have s1e' : OsuModel.Sim.Sim.poolGet 2 (simCtxS tn fo c) (simStS tn s) = .ok (hk1.val, simStS tn s3) := s1e
  have hk3 : k.val < s3.insts.val.length := Nat.lt_of_lt_of_le hk hpre3.length_le
  have ho3 : i.val < s3.objs.val.length := by rw [hs3]; exact ho
  simp only [simM_bind, Except.bind, kindS, sim_kb_slider_slider, sim_kb_slider_spinner, kind_eq_ok, bind_ok,
    if_true, if_false, e1, s1e', uncurry_apply_pair, Bool.false_eq_true,
    vec_index_eq _ _ hk3, vec_index_eq _ _ hk1l, vec_index_mut_eq _ _ ho3, netx_F64_POS_INF, netx_F64_NEG_INF,
    sim_basic_F32_0, s3a_instOf tn fo c s3 _ hk3, s3a_instOf tn fo c s3 _ hk1l]
  generalize hO1 : s3.objs.val[i.val]'ho3 = O1
  rw [sim_modifyObj_stS tn _ s3 i ho3 { O1 with
      armed := (s3.insts.val[k.val]'hk3).armed
      head_armed := (s3.insts.val[hk1.val]'hk1l).armed } _ (by rw [hO1]; rfl) _ rfl]
  set O1' : sim.state.OState := { O1 with
      armed := (s3.insts.val[k.val]'hk3).armed
      head_armed := (s3.insts.val[hk1.val]'hk1l).armed } with hO1'
  set O2 : sim.state.OState := { O1 with
      life := sim.state.Life.Alive
      child_id := cid
      hit_action := none
      hovered := false
      head_lifetime_end := F64.posInf
      head_alive := false
      tracking := false
      inst := k
      head_inst := hk1
      armed := (s3.insts.val[k.val]'hk3).armed
      head_armed := (s3.insts.val[hk1.val]'hk1l).armed
      accept_any_after := none
      last_pressed := replay.frames.ACTLIST_EMPTY
      slider_mouse := none
      spin_tracking := false
      spin_mouse := none
      last_angle := none
      total_accumulated := 0
      accumulated_at_last_completion := 0
      current_spin_max := 0
      completed_spins := 0#u64
      last_report_time := F64.negInf
      completed_full_spins := 0#i64 } with hO2
  have ho3' : i.val < (s3.objs.set i O1').val.length := by simpa [vec_set_val'] using ho3
  have h2m := sim_modifyObj_stS tn (simCtxS tn fo c) { s3 with objs := s3.objs.set i O1' } i ho3' O2
    (fun os => { os with
      life := OsuModel.Sim.Life.alive, childId := cid.val, hitAction := none, inst := k.val, headInst := hk1.val
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 })
    (by simp only [vec_set_val', List.getElem_set_self]; first | rfl | (simp [ostateS, hO2, hO1']; exact ⟨rfl, s2_abs_empty⟩) ) _ rfl
  simp only [h2m, sim_vset_set]
  clear h2m hO1' ho3'
  clear_value O1' O2
  obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
  have hhn' := hhn (Or.inl hsl)
  have hk1l4 : hk1.val < ({ s3 with objs := s3.objs.set i O2 } : sim.state.St).insts.val.length := hk1l
  obtain ⟨r1, s5, ea1, sa1, Y1, hY1, fY1⟩ := sim.step.apply_bindings_refines tn fo c { s3 with objs := s3.objs.set i O2 }
    i .Head hk1 hi hhi hk1l4 (fun _ => hhn')
  have sa1' := sa1
  simp only [ea1, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch]
  cases r1 with
  | Err e =>
    obtain ⟨m, hm⟩ := sa1
    simp only [abs, sim.step.Part.Head] at hm
    refine ⟨.Err e, s5, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual],
      ⟨m, ?_⟩, fun h => by cases h⟩
    have hm' : OsuModel.Sim.Sim.applyBindings i.val .head hk1.val (simCtxS tn fo c)
      (simStS tn { s3 with objs := s3.objs.set i O2 }) = .error m := hm
    simp only [hm']
  | Ok u =>
    have sa1' : OsuModel.Sim.Sim.applyBindings i.val .head hk1.val (simCtxS tn fo c)
      (simStS tn { s3 with objs := s3.objs.set i O2 }) = .ok ((), simStS tn s5) := sa1
    subst hY1
    have hk15 : hk1.val < (s3.insts.set hk1 Y1).val.length := by simpa [vec_set_val'] using hk1l
    have hl5 : ((s3.insts.set hk1 Y1).val[hk1.val]'hk15).loaded = (s3.insts.val[hk1.val]'hk1l).loaded := by
      simp only [vec_set_val', List.getElem_set_self]; exact fY1.loaded
    simp only [sa1', simM_bind, Except.bind, s3a_instOf tn fo c { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } _ hk15,
      vec_index_eq _ _ hk15, hl5, bind_ok]
    have hlS : (abs ((s3.insts.set hk1 Y1).val[hk1.val]'hk15) : OsuModel.Sim.Inst).loaded =
      (s3.insts.val[hk1.val]'hk1l).loaded := hl5
    rw [hlS]
    have hinv3 : SimInv c s3 := by
      rw [hs3]; exact ⟨hinv.objs_len, hinv.nested_len, hinv.nested_small, hinv.dict_in, hinv.dict_small⟩
    have hinv4 : SimInv c { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } := by
      have := sim_inv_objs_set (s := s3) hinv3 O2 ho3 (by rw [hO1, hO2])
      exact ⟨this.objs_len, this.nested_len, this.nested_small, this.dict_in, this.dict_small⟩
    have hTf3 : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s3 := sim_tf_pg X hB hTf (by
      rcases hins with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, trivial⟩)
    have hTf4 : s3b_TfInv P (b + n + n + 4 + (n + n + 4))
        { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } := sim_tf_ab X hk1l hTf3 fY1
    have ho4 : i.val < (s3.objs.set i O2).val.length := by simpa [vec_set_val'] using ho3
    have hO2i : (s3.objs.set i O2).val[i.val]'ho4 = O2 := by simp [vec_set_val']
    have hhnT : sim.step.Part.Top = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'hi).h.kind = .Slider →
        (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length := fun _ => hhn'
    by_cases hl : (s3.insts.val[hk1.val]'hk1l).loaded = true
    · obtain ⟨s5, eu, su, hinv5, hTf5, hil5, hol5, -, -, hof5⟩ := sim.step.update_state_from_result_refines tn fo E
        (b + n + n + 4) n c { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } i .Head 1#u64 hinv4
        (by simpa [Nat.add_assoc] using hTf4)
        (fun ns => hCS i .Head ns hi hhi hhb (fun _ => hhn')) ho4
        (by simpa [vec_set_val', hO2] using hk3)
        (by simpa [vec_set_val', hO2] using hk1l) hhi hhb (fun _ => hhn')
      have su' : OsuModel.Sim.Sim.updateStateFromResult i.val .head 1 (simCtxS tn fo c)
        (simStS tn { s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 }) = .ok ((), simStS tn s5) := su
      simp only [hl, if_true, eu, bind_ok, su', simM_bind, Except.bind]
      have hioT : i.val < s5.objs.val.length := by rw [hol5]; exact ho4
      have hkT : k.val < s5.insts.val.length := by rw [hil5]; simpa [vec_set_val'] using hk3
      have hk1T : ((s5.objs.val[i.val]'hioT).inst.val) < s5.insts.val.length := by
        rw [(hof5.2 i.val ho4 hioT).1, hil5]; simpa [vec_set_val', hO2] using hk3
      have hk2T : ((s5.objs.val[i.val]'hioT).head_inst.val) < s5.insts.val.length := by
        rw [(hof5.2 i.val ho4 hioT).2.1, hil5]; simpa [vec_set_val', hO2] using hk1l
      generalize s5 = sT at *
      have hinvT := hinv5
      have hTfT := hTf5
      ba_top
    · simp only [hl, Bool.false_eq_true, if_false, bind_ok]
      have hTfT : s3b_TfInv P (b + n + n + 4) ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St) :=
        sim_tf_mono E hTf4 (by omega)
      have hkT : k.val < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).insts.val.length := by simpa [vec_set_val'] using hk3
      have hioT : i.val < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).objs.val.length := ho4
      have hk1T : ((({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).objs.val[i.val]'hioT).inst.val) < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).insts.val.length := by
        simpa [vec_set_val', hO2] using hk3
      have hk2T : ((({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).objs.val[i.val]'hioT).head_inst.val) < ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St).insts.val.length := by
        simpa [vec_set_val', hO2] using hk1l
      have hinvT := hinv4
      generalize hsT : ({ s3 with objs := s3.objs.set i O2, insts := s3.insts.set hk1 Y1 } : sim.state.St) = sT at *
      ba_top

theorem sim_ba_tail_other (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hns : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Slider) (hnsp : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Spinner)
    (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4) s) (hB : b + n + n + 4 + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s') := by
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  unfold simBATailR simBATailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  have hb1 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.slider) = false := by
    revert hns; cases (c.pb.objects.val[i.val]'hi).h.kind <;> simp [kindS] <;> decide
  have hb2 : (kindS (c.pb.objects.val[i.val]'hi).h.kind == OsuModel.Sim.Kind.spinner) = false := by
    revert hnsp; cases (c.pb.objects.val[i.val]'hi).h.kind <;> simp [kindS] <;> decide
  have hb1' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Slider) = false := hb1
  have hb2' : (kindS (c.pb.objects.val[i.val]'hi).h.kind == kindS sim.playable.Kind.Spinner) = false := hb2
  rw [hkS]
  have hk0 : (0 : Nat) < s.insts.val.length := by omega
  simp only [simM_bind, Except.bind, hb1, hb2, hb1', hb2', kind_eq_ok, bind_ok, simM_pure,
    Bool.false_eq_true, if_false, uncurry_apply_pair,
    vec_index_eq _ _ hk, vec_index_mut_eq _ _ ho, netx_F64_POS_INF, netx_F64_NEG_INF,
    sim_basic_F32_0, s3a_instOf tn fo c s _ hk, s3a_instOf tn fo c s _ hk0]
  generalize hO1 : s.objs.val[i.val]'ho = O1
  set O1' : sim.state.OState := { O1 with
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle } with hO1'
  rw [sim_modifyObj_stS tn _ s i ho O1' _ (by rw [hO1]; rfl) _ rfl]
  set O2 : sim.state.OState := { O1 with
      life := sim.state.Life.Alive
      child_id := cid
      hit_action := none
      hovered := false
      head_lifetime_end := F64.posInf
      head_alive := false
      tracking := false
      inst := k
      head_inst := 0#usize
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle
      accept_any_after := none
      last_pressed := replay.frames.ACTLIST_EMPTY
      slider_mouse := none
      spin_tracking := false
      spin_mouse := none
      last_angle := none
      total_accumulated := 0
      accumulated_at_last_completion := 0
      current_spin_max := 0
      completed_spins := 0#u64
      last_report_time := F64.negInf
      completed_full_spins := 0#i64 } with hO2
  have ho' : i.val < (s.objs.set i O1').val.length := by simpa [vec_set_val'] using ho
  have h2m := sim_modifyObj_stS tn (simCtxS tn fo c) { s with objs := s.objs.set i O1' } i ho' O2
    (fun os => { os with
      life := OsuModel.Sim.Life.alive, childId := cid.val, hitAction := none, inst := k.val, headInst := 0
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 })
    (by simp only [vec_set_val', List.getElem_set_self]; first | rfl | (simp [ostateS, hO2, hO1']; exact ⟨rfl, s2_abs_empty⟩) ) _ rfl
  simp only [h2m, sim_vset_set]
  clear h2m hO1' ho'
  clear_value O1' O2
  obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
  have ho4 : i.val < (s.objs.set i O2).val.length := by simpa [vec_set_val'] using ho
  have hhnT : sim.step.Part.Top = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'hi).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length := by
    rintro (h | h); · cases h
    · exact absurd h hns
  have hinv4 : SimInv c { s with objs := s.objs.set i O2 } := sim_inv_objs_set hinv O2 ho (by rw [hO1, hO2])
  have hTfT : s3b_TfInv P (b + n + n + 4) ({ s with objs := s.objs.set i O2 } : sim.state.St) := hTf
  have hkT : k.val < ({ s with objs := s.objs.set i O2 } : sim.state.St).insts.val.length := hk
  have hioT : i.val < ({ s with objs := s.objs.set i O2 } : sim.state.St).objs.val.length := ho4
  have hk1T : ((({ s with objs := s.objs.set i O2 } : sim.state.St).objs.val[i.val]'hioT).inst.val) <
      ({ s with objs := s.objs.set i O2 } : sim.state.St).insts.val.length := by
    simpa [vec_set_val', hO2] using hk
  have hk2T : ((({ s with objs := s.objs.set i O2 } : sim.state.St).objs.val[i.val]'hioT).head_inst.val) <
      ({ s with objs := s.objs.set i O2 } : sim.state.St).insts.val.length := by
    simpa [vec_set_val', hO2] using hk0
  have hinvT := hinv4
  generalize hsT : ({ s with objs := s.objs.set i O2 } : sim.state.St) = sT at *
  ba_top

theorem sim_ba_tail_spinner (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner)
    (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4) s) (hB : b + n + n + 4 + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s') := by
  have ho : i.val < s.objs.val.length := by rw [hinv.objs_len]; exact hi
  unfold simBATailR simBATailS
  have hkS : (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = kindS (c.pb.objects.val[i.val]'hi).h.kind := rfl
  have hns : (c.pb.objects.val[i.val]'hi).h.kind ≠ .Slider := by rw [hsp]; intro h; cases h
  rw [hkS, hsp]
  have hk0 : (0 : Nat) < s.insts.val.length := by omega
  simp only [simM_bind, Except.bind, kindS, sim_kb_spinner_slider, sim_kb_spinner_spinner, kind_eq_ok, bind_ok, simM_pure,
    if_true,
    Bool.false_eq_true, if_false, uncurry_apply_pair,
    vec_index_eq _ _ hk, vec_index_mut_eq _ _ ho, netx_F64_POS_INF, netx_F64_NEG_INF,
    sim_basic_F32_0, s3a_instOf tn fo c s _ hk, s3a_instOf tn fo c s _ hk0]
  generalize hO1 : s.objs.val[i.val]'ho = O1
  set O1' : sim.state.OState := { O1 with
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle } with hO1'
  rw [sim_modifyObj_stS tn _ s i ho O1' _ (by rw [hO1]; rfl) _ rfl]
  set O2 : sim.state.OState := { O1 with
      life := sim.state.Life.Alive
      child_id := cid
      hit_action := none
      hovered := false
      head_lifetime_end := F64.posInf
      head_alive := false
      tracking := false
      inst := k
      head_inst := 0#usize
      armed := (s.insts.val[k.val]'hk).armed
      head_armed := .Idle
      accept_any_after := none
      last_pressed := replay.frames.ACTLIST_EMPTY
      slider_mouse := none
      spin_tracking := false
      spin_mouse := none
      last_angle := none
      total_accumulated := 0
      accumulated_at_last_completion := 0
      current_spin_max := 0
      completed_spins := 0#u64
      last_report_time := F64.negInf
      completed_full_spins := 0#i64 } with hO2
  have ho' : i.val < (s.objs.set i O1').val.length := by simpa [vec_set_val'] using ho
  have h2m := sim_modifyObj_stS tn (simCtxS tn fo c) { s with objs := s.objs.set i O1' } i ho' O2
    (fun os => { os with
      life := OsuModel.Sim.Life.alive, childId := cid.val, hitAction := none, inst := k.val, headInst := 0
      hovered := false, tracking := false, acceptAnyAfter := none, lastPressed := [], sliderMouse := none
      headAlive := false, headLifetimeEnd := F64.posInf
      spinTracking := false, spinMouse := none, lastAngle := none, totalAccumulated := 0
      accumulatedAtLastCompletion := 0, currentSpinMax := 0, completedSpins := 0, lastReportTime := F64.negInf
      completedFullSpins := 0 })
    (by simp only [vec_set_val', List.getElem_set_self]; first | rfl | (simp [ostateS, hO2, hO1']; exact ⟨rfl, s2_abs_empty⟩) ) _ rfl
  simp only [h2m, sim_vset_set]
  clear h2m hO1' ho'
  clear_value O1' O2
  obtain ⟨hhi, hhb, hhn⟩ := hC.hd i.val hi
  have ho4 : i.val < (s.objs.set i O2).val.length := by simpa [vec_set_val'] using ho
  have hinv4 : SimInv c { s with objs := s.objs.set i O2 } := sim_inv_objs_set hinv O2 ho (by rw [hO1, hO2])
  obtain ⟨s5, es, rs, hinv5, hpl5, hP5, hil5, htf5, hio5⟩ := sim.step.spinner_ticks_get_refines tn fo c
    { s with objs := s.objs.set i O2 } i hi hinv4 hpl (by simp; omega) hP
  simp only [simM_bind] at rs
  have key := sim_ex_bind3 (δ := Unit × OsuModel.Sim.St) _ _ _ _ rs
  simp only [Except.bind] at key
  rw [key]
  simp only [es, bind_ok]
  have hhnT : sim.step.Part.Top = sim.step.Part.Head ∨ (c.pb.objects.val[i.val]'hi).h.kind = .Slider →
      (c.head_idx.val[i.val]'hhi).val < (c.pb.objects.val[i.val]'hi).nested.val.length := by
    rintro (h | h); · cases h
    · exact absurd h hns
  have hTfT : s3b_TfInv P (b + n + n + 4) s5 := htf5 P X _ (by omega) hTf
  have hkT : k.val < s5.insts.val.length := Nat.lt_of_lt_of_le hk hil5
  have hioT : i.val < s5.objs.val.length := by rw [hinv5.objs_len]; exact hi
  have hio5' := hio5 ho4 hioT
  have hk1T : ((s5.objs.val[i.val]'hioT).inst.val) < s5.insts.val.length := by
    rw [hio5'.1]; simpa [vec_set_val', hO2] using hkT
  have hk2T : ((s5.objs.val[i.val]'hioT).head_inst.val) < s5.insts.val.length := by
    rw [hio5'.2]; simp [vec_set_val', hO2]; omega
  have hinvT := hinv5
  generalize s5 = sT at *
  ba_top

theorem sim_ba_tail (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s) (cid : U64) (k : Usize)
    (hk : k.val < s.insts.val.length) (hpl : 6 ≤ s.pools.val.length) (hP : simPoolOk s)
    (hcap : s.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max) (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s) (hB : b + n + n + 4 + (n + n + 4) + 1 < Usize.max) :
    ∃ res s', simBATailR c s i (c.pb.objects.val[i.val]'hi) cid k = ok (res, s') ∧
      simRelM tn s' res (simBATailS i.val (topS tn (c.pb.objects.val[i.val]'hi)) cid.val k.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s') := by
  by_cases hsl : (c.pb.objects.val[i.val]'hi).h.kind = .Slider
  · exact sim_ba_tail_slider tn fo c s i hi hinv cid k hk hpl hP hcap hsl hC E X b n hCS hTf hB
  by_cases hsp : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner
  · exact sim_ba_tail_spinner tn fo c s i hi hinv cid k hk hpl hP (by omega) hsp hC E X b n hCS (sim_tf_mono E hTf (by omega)) (by omega)
  · exact sim_ba_tail_other tn fo c s i hi hinv cid k hk hpl hP (by omega) hsl hsp hC E X b n hCS (sim_tf_mono E hTf (by omega)) (by omega)

-- CONDITIONAL: step-invariant premises (free list in range, capacities, 6 pools, simPoolOk, simTfX + transformable budget for the two updateStateFromResult calls); hC/hCS are context premises (ev_ctxWF / sim_ar_cs)
theorem sim.step.became_alive_refines (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (s : sim.state.St) (i : Usize)
    (hi : i.val < c.pb.objects.val.length) (hinv : SimInv c s)
    (hfree : ∀ x ∈ s.free_list.val, x.val < s.dict_slots.val.length)
    (hds : s.dict_slots.val.length + 1 < Usize.max)
    (hact : s.active.val.length < Usize.max) (hcc : s.child_counter.val + 1 ≤ U64.max)
    (hpl : 6 ≤ s.pools.val.length) (hcap : s.insts.val.length + 2 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max)
    (hP : simPoolOk s) (hC : SimARCtx c)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n : Nat) (hCS : simCSH P n tn fo c)
    (hTf : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s) (hB : b + n + n + 4 + (n + n + 4) + 1 < Usize.max) :
    ∃ res s', sim.step.became_alive c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → SimInv c s' ∧ s3b_TfInv P b s') := by
  rw [sim_ba_split, sim_ba_splitS]
  obtain ⟨v1, ev1, snil, scons, mv1⟩ := sim_ba_dict2 tn s i hinv.dict_small hfree
  obtain ⟨FL, epop, hFL⟩ : ∃ FL, alloc.vec.Vec.pop alloc.alloc.Global s.free_list =
      ok (s.free_list.val.getLast?, FL) ∧ FL.val = s.free_list.val.dropLast :=
    ⟨_, rfl, by simp [alloc.vec.Vec.from_val]⟩
  obtain ⟨cid, ecid, vcid⟩ := sim_u64_add_one s.child_counter hcc
  obtain ⟨v2, ev2, vv2⟩ : ∃ v, alloc.vec.Vec.push s.active i = ok v ∧ v.val = s.active.val ++ [i] :=
    ⟨_, vec_push_ok _ _ hact, by simp⟩
  obtain ⟨pk, epk, spk⟩ := sim.step.pool_kind_refines (c.pb.objects.val[i.val]'hi).h.kind
  simp only [simM_bind, s3b_topObj tn fo c _ i.val hi, Except.bind, OsuModel.Sim.Sim.st, simM_get,
    vec_index_eq _ _ hi, bind_ok, epop, uncurry_apply_pair]
  have hfl : (simStS tn s).freeList = (s.free_list.val.map (·.val)).reverse := rfl
  have hS0 := sim_stS_ba tn s i v1 FL v2 cid vv2 vcid
  rcases hg : s.free_list.val.getLast? with _ | x
  on_goal 1 =>
    rw [List.getLast?_eq_none_iff] at hg
    have hfl0 : (simStS tn s).freeList = [] := by rw [hfl, hg]; rfl
    obtain ⟨h1, -⟩ := snil hfl0
    have hFL0 : (FL.val.map (fun x => x.val)).reverse = [] := by simp [hFL, hg]
    rw [hFL0] at hS0
    simp only [hg, List.getLast?_nil] at ev1
    have hv1l : v1.val.length ≤ s.dict_slots.val.length + 1 := by
      have e := ev1; rw [vec_push_ok _ _ hinv.dict_small] at e; simp only [ok.injEq] at e; rw [← e]; simp
    simp only [ev1, ecid, ev2, epk, bind_ok, hfl0, simM_bind, simM_pure, h1, Except.bind, ← hS0, simM_set, simM_get]
  on_goal 2 =>
    have hx : x.val < s.dict_slots.val.length := hfree x (List.mem_of_getLast? hg)
    obtain ⟨L, hL⟩ : ∃ L, s.free_list.val = L ++ [x] := ⟨_, (List.dropLast_append_getLast? _ hg).symm⟩
    have hfl1 : (simStS tn s).freeList = x.val :: (L.map (·.val)).reverse := by rw [hfl, hL]; simp
    obtain ⟨h1, h2⟩ := scons _ _ hfl1
    have hFL1 : (FL.val.map (fun x => x.val)).reverse = (L.map (·.val)).reverse := by simp [hFL, hL]
    rw [hFL1] at hS0
    simp only [hg] at ev1
    have hv1l : v1.val.length ≤ s.dict_slots.val.length + 1 := by
      have e := ev1; simp only [vec_index_mut_eq _ _ hx, bind_ok, uncurry_apply_pair, ok.injEq] at e; rw [← e]; simp [vec_set_val']
    simp only [ev1, ecid, ev2, epk, bind_ok, hfl1, simM_bind, simM_pure, h1, Except.bind, ← hS0, simM_set, simM_get]
  all_goals
    have hpk : pk.val < 6 := by
      cases hkd : (c.pb.objects.val[i.val]'hi).h.kind <;> rw [hkd] at epk <;>
        simp [sim.step.pool_kind] at epk <;> subst epk <;> decide
    obtain ⟨k, s1, ek, sk, hfr, hpl1, hins, hk⟩ := sim.step.pool_get_refines tn fo c
      { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } pk (by simp; omega)
      (by simp; omega)
    have hpkS : OsuModel.Sim.Sim.poolKind (topS tn (c.pb.objects.val[i.val]'hi)).h.kind = pk.val := by
      first | exact spk | simpa [abs] using spk
    obtain ⟨k', s1', ek', -, -, -, hkl', hP1, -⟩ := sim_pool_get_ok
      { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } pk (by simp; omega)
      (by simp; omega) hP
    rw [ek] at ek'; simp only [ok.injEq, Prod.mk.injEq] at ek'; obtain ⟨hk', hs1'⟩ := ek'; subst hk'; subst hs1'
    simp only [ek, bind_ok, uncurry_apply_pair, hpkS, sk]
    obtain ⟨ins1, pl1, hs1⟩ := hfr
    have hinv1 : SimInv c s1 := by
      rw [hs1]
      refine ⟨hinv.objs_len, hinv.nested_len, hinv.nested_small, ?_, by simp; omega⟩
      intro o ho x hx
      rcases mv1 o ho with ho | ho
      · exact hinv.dict_in o ho x hx
      · subst ho; cases hx; exact hi
    have hTf1 : s3b_TfInv P (b + n + n + 4 + (n + n + 4)) s1 := sim_tf_pg X hB hTf (by
      rcases hins with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, trivial⟩)
    have hcap1 : s1.insts.val.length + 1 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max := by
      rcases hins with h | ⟨h, -⟩ <;> rw [h] <;> simp <;> omega
    exact sim_ba_tail tn fo c s1 i hi hinv1 cid k hkl' (by rw [hpl1]; exact hpl) hP1 hcap1 hC E X b n hCS hTf1 hB

end OsuProofs
