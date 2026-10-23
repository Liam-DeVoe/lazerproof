/-
simcore3 (D73): the concrete step invariant of `sim::step::run` and the instantiation of simcore2's generic step
loop (Sim/StepLoop, Sim/StepOnce): `step_once_refines`, `run_refines`, `run_with_refines`, `simulate_refines`.
Part 1: transfer of sim8's `simLifeInv` across the non-lifetime frames, the playfield invariant `s3d_PI` from it,
`update_order` facts, the custom-state cost on spec values.
-/
import OsuProofs.Sim.StepOnce
import OsuProofs.Sim.LifetimeInv
import OsuProofs.Sim.ProcFrame
import OsuProofs.Sim.CtxWF
import OsuProofs.Sim.LifetimeUpd
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

/-! ## transfer of the lifetime invariant -/

/-- the per-object fields `simLifeInv` reads (besides `nested`, fixed by `SimInv`) -/
def sc3KO (o : sim.state.OState) := (o.life, o.tick_insts, o.tick_live.val.length)

/-- the state fields `simLifeInv` reads (besides `objs`) -/
def sc3KS (s : sim.state.St) :=
  (s.dict_slots, s.free_list, s.active, s.child_counter, s.first_lifetime_update, s.future_order, s.next_future,
   s.pools, s.insts.val.length)

theorem sc3_map_eq {β : Type} (f : sim.state.OState → β) {l l' : List sim.state.OState} (hl : l'.length = l.length)
    (h : ∀ j (h : j < l.length) (h' : j < l'.length), f (l'[j]'h') = f (l[j]'h)) : l'.map f = l.map f := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map]
  exact h j (by simpa using h2) (by simpa using h1)

theorem sc3_simFut_eq {s s' : sim.state.St} (hl : s'.objs.val.length = s.objs.val.length)
    (hk : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      (s'.objs.val[j]'h').life = (s.objs.val[j]'h).life) : simFut s' = simFut s := by
  unfold simFut
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map]
  rw [hk j (by simpa using h2) (by simpa using h1)]

theorem sc3_simFutW_eq {s s' : sim.state.St} (hl : s'.objs.val.length = s.objs.val.length)
    (hk : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      (s'.objs.val[j]'h').life = (s.objs.val[j]'h).life ∧
      (s'.objs.val[j]'h').nested.val.length = (s.objs.val[j]'h).nested.val.length) : simFutW s' = simFutW s := by
  unfold simFutW
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map]
  rw [(hk j (by simpa using h2) (by simpa using h1)).1, (hk j (by simpa using h2) (by simpa using h1)).2]

theorem sc3_nested_eq {c : sim.state.Ctx} {s s' : sim.state.St} (hi : SimInv c s) (hi' : SimInv c s')
    (j : Nat) (h : j < s.objs.val.length) (h' : j < s'.objs.val.length) :
    (s'.objs.val[j]'h').nested.val.length = (s.objs.val[j]'h).nested.val.length := by
  have hc : j < c.pb.objects.val.length := by rw [← hi.objs_len]; exact h
  rw [hi'.nested_len j h' hc, hi.nested_len j h hc]

/-- `simLifeInv` survives any frame that keeps `sc3KS`, the object count and `sc3KO`, given the new `SimARInv`,
`simLP` and spin-count bound -/
theorem sc3_life_tr {tn fo} {P : Nat → sim.transforms.TObj → Prop} {b n CS : Nat} {c : sim.state.Ctx}
    {s s' : sim.state.St} (hL : simLifeInv tn fo P b n CS c s) {b' CS' : Nat}
    (hA : SimARInv tn fo P (b' + simFut s' * (4 * n + 8)) n c s' 0 0 0) (hLP : simLP s')
    (hcs : ∀ j (h : j < s'.objs.val.length), (s'.objs.val[j]'h).completed_spins.val ≤ CS')
    (hlen : s'.objs.val.length = s.objs.val.length)
    (hko : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), sc3KO (s'.objs.val[j]'h') = sc3KO (s.objs.val[j]'h))
    (hks : sc3KS s' = sc3KS s) : simLifeInv tn fo P b' n CS' c s' := by
  simp only [sc3KS, Prod.mk.injEq] at hks
  obtain ⟨hd, hf, ha, hcc, hfl, hfo, hnf, hp, hil⟩ := hks
  have hko' : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      (s'.objs.val[j]'h').life = (s.objs.val[j]'h).life ∧ (s'.objs.val[j]'h').tick_insts = (s.objs.val[j]'h).tick_insts ∧
      (s'.objs.val[j]'h').tick_live.val.length = (s.objs.val[j]'h).tick_live.val.length := by
    intro j h h'
    have e := hko j h h'
    simp only [sc3KO, Prod.mk.injEq] at e
    exact e
  have hlt : ∀ j, j < s'.objs.val.length → j < s.objs.val.length := fun j h => by rw [← hlen]; exact h
  have hnest := sc3_nested_eq hL.ar.inv hA.inv
  have hF : simFut s' = simFut s := sc3_simFut_eq hlen (fun j h h' => (hko' j h h').1)
  have hFW : simFutW s' = simFutW s := sc3_simFutW_eq hlen (fun j h h' => ⟨(hko' j h h').1, hnest j h h'⟩)
  refine ⟨⟨hA, hLP, ?pl, ?pool, ?dnd, ?dal, ?ald, ?frl, ?frn, ?nfr, ?dlen, ?actl, ?actnd, ?actnf, ?aal, ?cc, ?ins,
    hcs, ?tk, ?tkv, ?spt, ?ftr, ?fut⟩, ?aact⟩
  case pl => rw [hp]; exact hL.pl
  case pool => unfold simPoolOk; rw [hp, hil]; exact hL.pool
  case dnd => rw [hd]; exact hL.dnd
  case dal =>
    intro x hx
    rw [hd] at hx
    obtain ⟨h, hal⟩ := hL.dal x hx
    have h' : x.val < s'.objs.val.length := by rw [hlen]; exact h
    exact ⟨h', by rw [(hko' _ h h').1]; exact hal⟩
  case ald =>
    intro j h' hal
    rw [hd]
    exact hL.ald j (hlt j h') (by rw [← (hko' j (hlt j h') h').1]; exact hal)
  case frl => rw [hf, hd]; exact hL.frl
  case frn => rw [hf]; exact hL.frn
  case nfr => rw [hd, hf]; exact hL.nfr
  case dlen => rw [hd, hlen]; exact hL.dlen
  case actl => rw [ha, hlen]; exact hL.actl
  case actnd => rw [ha]; exact hL.actnd
  case actnf =>
    intro x hx h'
    rw [ha] at hx
    rw [(hko' _ (hlt _ h') h').1]; exact hL.actnf x hx _
  case aal =>
    intro j h' hal
    rw [ha]
    exact hL.aal j (hlt j h') (by rw [← (hko' j (hlt j h') h').1]; exact hal)
  case cc => rw [hcc, hF, hlen]; exact hL.cc
  case ins => rw [hil, hFW]; exact hL.ins
  case tk =>
    intro j h'
    rw [(hko' j (hlt j h') h').2.1, hnest j (hlt j h') h']; exact hL.tk j (hlt j h')
  case tkv =>
    intro j h' x hx
    rw [(hko' j (hlt j h') h').2.1] at hx
    rw [hil]; exact hL.tkv j (hlt j h') x hx
  case spt =>
    intro j h' hj hal hk
    have e := hko' j (hlt j h') h'
    obtain ⟨a, b⟩ := hL.spt j (hlt j h') hj (by rw [← e.1]; exact hal) hk
    exact ⟨by rw [e.2.2]; exact a, by rw [e.2.1]; exact b⟩
  case ftr =>
    intro hf1 j h'
    rw [(hko' j (hlt j h') h').1]
    exact hL.ftr (by rw [← hfl]; exact hf1) j (hlt j h')
  case fut =>
    intro hf0
    obtain ⟨f1, f2, f3⟩ := hL.fut (by rw [← hfl]; exact hf0)
    refine ⟨?_, ?_, ?_⟩
    · rw [hfo, hlen]; exact f1
    · intro k hk hnk h'
      have hk0 : k < s.future_order.val.length := by rw [← hfo]; exact hk
      have e1 : s'.future_order.val[k]'hk = s.future_order.val[k]'hk0 := by simp only [hfo]
      have h0 : (s.future_order.val[k]'hk0).val < s.objs.val.length := by rw [← e1, ← hlen]; exact h'
      have := f2 k hk0 (by rw [← hnf]; exact hnk) h0
      have e2 := (hko' _ h0 (by rw [hlen]; exact h0)).1
      simp only [e1]
      rw [e2]; exact this
    · rw [hfo, hnf]; exact f3
  case aact =>
    intro x hx h'
    rw [ha] at hx
    rw [(hko' _ (hlt _ h') h').1]; exact hL.aact x hx _

/-! ## the rest of the step invariant, and the playfield invariant `s3d_PI` -/

/-- state facts of the step invariant outside `simLifeInv` (step index, autopilot frame, input-blocker trackers,
duplicate-free `pressed`, small `last_replay`) -/
def sc3X (c : sim.state.Ctx) (s : sim.state.St) : Prop :=
  (s.k.val ≠ 0 → s.k.val - 1 < c.steps.val.length) ∧
  (-1 ≤ s.ap_frame.val ∧ s.ap_frame.val < c.ap_frames.val.length) ∧ s6Blk c s ∧ (actListS s.pressed).Nodup ∧
  (∀ l, s.last_replay = some l → l.len.val ≤ 3)

/-- config facts (mod-index ranges) the step needs: dynamic-rate and input-blocker indices of the updatables and
rate sources are in range -/
structure sc3Cfg (c : sim.state.Ctx) : Prop where
  dyn : ∀ k, sim.mods.Updatable.DynRate k ∈ c.cfg.updatables.val → k.val < c.cfg.dyn_rates.val.length
  blk : ∀ k, sim.mods.Updatable.InputBlock k ∈ c.cfg.updatables.val → k.val < c.cfg.input_blockers.val.length
  rs : ∀ x ∈ c.cfg.rate_sources.val, ∀ k, x.val = .Dyn k → k.val < c.cfg.dyn_rates.val.length

theorem sc3_nodup_len (l : List Usize) (m : Nat) (hn : l.Nodup) (hl : ∀ x ∈ l, x.val < m) : l.length ≤ m := by
  have h1 : (l.map (·.val)).Nodup := hn.map (fun a b h => UScalar.eq_of_val_eq h)
  have h2 : (l.map (·.val)) ⊆ List.range m := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (hl y hy)
  have := (h1.subperm h2).length_le
  simpa using this

/-- the active list is small -/
theorem sc3_act_small {tn fo P b n CS c s} (hL : simLifeInv tn fo P b n CS c s)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (h64 : System.Platform.numBits = 64) :
    s.active.val.length < Usize.max := by
  have h1 := sc3_nodup_len s.active.val s.objs.val.length hL.actnd hL.actl
  have h2 := hL.ar.inv.objs_len
  have : Usize.max = U64.max := by
    rw [usize_max_64 h64]; first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl) | decide
  omega

/-- active entries are in the alive dictionary -/
theorem sc3_act_dict {tn fo P b n CS c s} (hL : simLifeInv tn fo P b n CS c s) :
    ∀ x ∈ s.active.val, some x ∈ s.dict_slots.val := by
  intro x hx
  have h := hL.actl x hx
  obtain ⟨y, hy, hyx⟩ := hL.ald x.val h (hL.aact x hx h)
  rwa [show y = x from UScalar.eq_of_val_eq hyx] at hy

/-- `s3d_PInv` from the lifetime invariant and `sc3X` -/
theorem sc3_PInv {tn fo P b n CS c s} (hL : simLifeInv tn fo P b n CS c s) (hX : sc3X c s) (hG : sc3Cfg c) :
    s3d_PInv c s := by
  obtain ⟨hx1, hx2, hB, hN, -⟩ := hX
  have hI := hL.ar
  refine ⟨hI.inv, ⟨fun x hx => ?_, hL.ald, sc3_act_dict hL⟩, fun x hx => ?_, hx1, hx2, hL.lp.1, fun k hk => ?_,
    fun k hk => ?_, fun h0 j hj => ?_⟩
  · obtain ⟨h, h1, h2, -⟩ := hI.ik x hx
    exact ⟨h, h1, h2⟩
  · rw [← hI.inv.objs_len]; exact hL.actl x hx
  · have hk1 := hG.dyn k hk
    refine ⟨hk1, by have := hI.sp; omega, fun had => ?_⟩
    have := s6_filter_take_lt s3b_isAd c.cfg.dyn_rates.val k.val hk1 had
    have := hI.cnt.1
    omega
  · have := hG.blk k hk
    exact ⟨by have := hB.2.1; omega, by have := hB.1; omega⟩
  · exact hB.2.2 h0 _ (List.getElem_mem hj)

/-- the playfield invariant `s3d_PI` (sim3d/sim6) at the lifetime budget -/
theorem sc3_PI {tn fo P b n CS c s} (hL : simLifeInv tn fo P b n CS c s) (hX : sc3X c s) (hG : sc3Cfg c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (h64 : System.Platform.numBits = 64) :
    s3d_PI tn fo P (b + simFut s * (4 * n + 8)) n c 0 s :=
  ⟨sc3_PInv hL hX hG, hL.ar, hL.lp, hX.2.2.1, hX.2.2.2.1, sc3_act_small hL hlen h64⟩

/-- the transform predicate `s2_tfOk` only reads the trackers -/
theorem sc3_tfPos_s2 : s3d_TfPosOk s2_tfOk := by
  intro b o p q h
  unfold s2_tfOk s2_tfOkS at *
  exact h

/-! ## `update_order`: a permutation of the active list (reversed input order) -/

theorem sc3_update_order (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s)
    (hx : ∀ e ∈ s.active.val, e.val < c.pb.objects.val.length) (hl : s.active.val.length < Usize.max) :
    ∃ v, sim.step.update_order c s = ok v ∧
      OsuModel.Sim.Sim.updateOrder (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) ∧
      v.val.length = s.active.val.length ∧ ∀ x ∈ v.val, x.val < c.pb.objects.val.length := by
  obtain ⟨v, hv, ev⟩ := sim.step.update_order_refines tn fo c s hinv hx hl
  obtain ⟨io, hio, hiov⟩ := sim.step.input_order_refines_list c s hinv hx hl
  obtain ⟨w, hw, hwv⟩ := sim_update_order_loop io io.val.length (alloc.vec.Vec.len io) (alloc.vec.Vec.new Usize)
    (by simp) (by simp) (by simp)
  have hw' : sim.step.update_order c s = ok w := by simp only [sim.step.update_order, hio, bind_ok]; exact hw
  rw [hv] at hw'
  obtain rfl := Result.ok_injective hw'
  have hp := s8_sortL_perm (simInLt c s) (s.active.val.map (·.val))
  rw [← hiov] at hp
  have hwv' : v.val = io.val.reverse := by
    rw [hwv]; simp [List.take_of_length_le]
  refine ⟨v, hv, ev, ?_, fun x hx' => ?_⟩
  · rw [hwv', List.length_reverse]
    have := hp.length_eq
    simpa using this
  · rw [hwv', List.mem_reverse] at hx'
    have h1 : x.val ∈ io.val.map (·.val) := List.mem_map_of_mem hx'
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (hp.subset h1)
    rw [← hyx]; exact hx y hy

/-! ## the invariant of the first three phases (processors, input, playfield) -/

/-- the lifetime invariant at transform budget `B` and spin bound `CS`, the rest `sc3X`, the step index in range,
and the number of Future objects fixed to `F` (it only changes in the lifetime phase) -/
def sc3Q (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (B CS F : Nat) (s : sim.state.St) : Prop :=
  simLifeInv tn fo s2_tfOk B (sc2N c) CS c s ∧ sc3X c s ∧ s.k.val < c.steps.val.length ∧ simFut s = F

/-- `sc3Q` plus proc's drain-cursor bound -/
def sc3P (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (B CS F : Nat) (s : sim.state.St) : Prop :=
  pr_HB c s ∧ sc3Q tn fo c B CS F s

/-- rebuilding `sc3Q` across a frame that keeps the lifetime fields -/
theorem sc3_Q_fr {tn fo c B CS F} {s s' : sim.state.St} (hP : sc3Q tn fo c B CS F s)
    (hA : SimARInv tn fo s2_tfOk (B + F * (4 * sc2N c + 8)) (sc2N c) c s' 0 0 0) (hLP : simLP s')
    (hB : s6Blk c s') (hN : (actListS s'.pressed).Nodup)
    (hap : -1 ≤ s'.ap_frame.val ∧ s'.ap_frame.val < c.ap_frames.val.length)
    (hlr : ∀ l, s'.last_replay = some l → l.len.val ≤ 3)
    (hlen : s'.objs.val.length = s.objs.val.length)
    (hko : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      sc3KO (s'.objs.val[j]'h') = sc3KO (s.objs.val[j]'h) ∧
      (s'.objs.val[j]'h').completed_spins = (s.objs.val[j]'h).completed_spins)
    (hks : sc3KS s' = sc3KS s) (hk : s'.k = s.k) : sc3Q tn fo c B CS F s' := by
  obtain ⟨hL, hX, hkN, hF⟩ := hP
  have hF' : simFut s' = F := by
    rw [← hF]
    exact sc3_simFut_eq hlen (fun j h h' => by
      have e := (hko j h h').1
      simp only [sc3KO, Prod.mk.injEq] at e
      exact e.1)
  refine ⟨sc3_life_tr hL (by rw [hF']; exact hA) hLP (fun j h' => ?_) hlen (fun j h h' => (hko j h h').1) hks,
    ⟨by rw [hk]; exact hX.1, hap, hB, hN, hlr⟩, by rw [hk]; exact hkN, hF'⟩
  have h0 : j < s.objs.val.length := by rw [← hlen]; exact h'
  rw [(hko j h0 h').2]; exact hL.cs j h0

/-- rebuilding `sc3P` across a frame that keeps the lifetime fields -/
theorem sc3_P_fr {tn fo c B CS F} {s s' : sim.state.St} (hP : sc3P tn fo c B CS F s)
    (hA : SimARInv tn fo s2_tfOk (B + F * (4 * sc2N c + 8)) (sc2N c) c s' 0 0 0) (hLP : simLP s')
    (hB : s6Blk c s') (hN : (actListS s'.pressed).Nodup)
    (hap : -1 ≤ s'.ap_frame.val ∧ s'.ap_frame.val < c.ap_frames.val.length)
    (hlr : ∀ l, s'.last_replay = some l → l.len.val ≤ 3)
    (hlen : s'.objs.val.length = s.objs.val.length)
    (hko : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      sc3KO (s'.objs.val[j]'h') = sc3KO (s.objs.val[j]'h) ∧
      (s'.objs.val[j]'h').completed_spins = (s.objs.val[j]'h).completed_spins)
    (hks : sc3KS s' = sc3KS s) (hk : s'.k = s.k) (hhb : pr_HB c s') : sc3P tn fo c B CS F s' :=
  ⟨hhb, sc3_Q_fr hP.2 hA hLP hB hN hap hlr hlen hko hks hk⟩

theorem sc3_P_PI {tn fo c B CS F} {s : sim.state.St} (hG : sc3Cfg c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (h64 : System.Platform.numBits = 64) (hP : sc3P tn fo c B CS F s) :
    s3d_PI tn fo s2_tfOk (B + F * (4 * sc2N c + 8)) (sc2N c) c 0 s := by
  obtain ⟨-, hL, hX, -, hF⟩ := hP
  rw [← hF]; exact sc3_PI hL hX hG hlen h64

/-- closure under the playfield hook frames -/
theorem sc3_hookfr {tn fo c B CS F} (hG : sc3Cfg c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (h64 : System.Platform.numBits = 64) :
    ∀ s s', sc3P tn fo c B CS F s → s3d_PInv c s' → s3d_HookFr c s s' → sc3P tn fo c B CS F s' := by
  intro s s' hP hP' hF
  have hPI := sc3_P_PI hG hlen h64 hP
  have hPI' := s3d_PI_hook tn fo sc3_tfPos_s2 _ _ c 0 s s' hPI hP' hF
  obtain ⟨-, hA', hL', hB', hN', -⟩ := hPI'
  have hap := hP'.2.2.2.2.1
  have hlr := hP.2.2.1.2.2.2.2
  rcases hF with ⟨sp, rfl, hsp⟩ | ⟨ins, rfl, hps⟩ | ⟨r, rfl⟩ | ⟨⟨af, mv, m, cp, o, rfl⟩, hinv', hol, hkh⟩ |
    ⟨bl, bi, rfl, hbl, hbi, hbb⟩
  · exact sc3_P_fr hP hA' hL' hB' hN' hap hlr rfl (fun _ _ _ => ⟨rfl, rfl⟩) rfl rfl hP.1
  · exact sc3_P_fr hP hA' hL' hB' hN' hap hlr rfl (fun _ _ _ => ⟨rfl, rfl⟩) (by simp only [sc3KS, hps.1]) rfl hP.1
  · exact sc3_P_fr hP hA' hL' hB' hN' hap hlr rfl (fun _ _ _ => ⟨rfl, rfl⟩) rfl rfl hP.1
  · refine sc3_P_fr hP hA' hL' hB' hN' hap hlr hol (fun j h h' => ?_) rfl rfl hP.1
    have e := hkh j h' h
    simp only [s3d_keepH, Prod.mk.injEq] at e
    exact ⟨by simp only [sc3KO, e.2.2.2.2.2.2.1, e.2.2.1, e.2.2.2.2.2.2.2.2], e.2.2.2.2.2.2.2.1⟩
  · exact sc3_P_fr hP hA' hL' hB' hN' hap hlr rfl (fun _ _ _ => ⟨rfl, rfl⟩) rfl rfl hP.1

/-- closure under the relax writes -/
theorem sc3_relaxCl {tn fo c B CS F} (hG : sc3Cfg c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (h64 : System.Platform.numBits = 64) : s3d_RelaxCl (sc3P tn fo c B CS F) := by
  refine ⟨fun s h => h.2.1.lp.1, fun s d l w p h hp hsl => ?_⟩
  have hPI := sc3_P_PI hG hlen h64 h
  obtain ⟨-, hA', hL', hB', hN', -⟩ := (s3d_PI_relaxCl tn fo s2_tfOk _ _ c 0).2 s d l w p hPI hp hsl
  exact sc3_P_fr h hA' hL' hB' hN' h.2.2.1.2.1 h.2.2.1.2.2.2.2 rfl (fun _ _ _ => ⟨rfl, rfl⟩) rfl rfl h.1

/-- closure under the `last_replay` write of `input_phase` -/
theorem sc3_lr {tn fo c B CS F} (hG : sc3Cfg c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (h64 : System.Platform.numBits = 64) :
    ∀ s (l : replay.frames.ActList), sc3P tn fo c B CS F s → l.len.val ≤ 3 →
      sc3P tn fo c B CS F { s with last_replay := some l } := by
  intro s l h hl
  obtain ⟨-, hA, hL, hB, hN, -⟩ := sc3_P_PI hG hlen h64 h
  have hA' := sim_ar_inv_hook tn fo s2_tfOk _ (sc2N c) c s 0 0 0 0 hA { s with last_replay := some l }
    (s3b_inv_of hA.inv rfl rfl) (s3b_objFrame_of_eq rfl) rfl hA.tf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine sc3_P_fr h hA' hL hB hN h.2.2.1.2.1 (fun l' e => ?_) rfl (fun _ _ _ => ⟨rfl, rfl⟩) rfl rfl h.1
  simp only [Option.some.injEq] at e
  subst e; exact hl

/-- `trigger_pressed` (sim6) keeps `sc3P` -/
theorem sc3_tp {tn fo c B CS F} (hG : sc3Cfg c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (h64 : System.Platform.numBits = 64) (hC : SimARCtx c) (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i) : s3d_TPOk tn fo c (sc3P tn fo c B CS F) := by
  intro s a hP
  obtain ⟨hPv, hA, hLP, hB, hN, hAl⟩ := sc3_P_PI hG hlen h64 hP
  obtain ⟨res, s', e1, r1, i1⟩ := sim.step.trigger_pressed_refines h64 tn fo s3b_tfEng_s2 _ (sc2N c) c hC
    (sim_ar_cs tn fo c hfo) hlen hp s a 0 hA hLP hB hN hPv.2.2.1 hAl hPv.2.1.2.2
  refine ⟨res, s', e1, by cases res <;> exact r1, fun h => ?_⟩
  obtain ⟨j1, j2, j3, j4, j5⟩ := i1 h
  have hPv' := s6_pinv hPv j1 j2 j4 j3
  have k := j4.keep
  simp only [s6KeepT, Prod.mk.injEq] at k
  refine sc3_P_fr hP j1 j2 j3 j5 hPv'.2.2.2.2.1 (by rw [k.2.2.2.2.2.2.2.2.2.2.2.1]; exact hP.2.2.1.2.2.2.2) j4.len
    (fun j h h' => ?_) (by simp only [sc3KS, k.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.1, k.2.2.2.2.2.1, k.2.2.2.2.2.2.2.2.1, k.2.2.1, k.2.2.2.2.1, k.2.2.2.1, k.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, j4.il])
    k.1 (pr_HB_s6keep j4.keep hP.1)
  have e := j4.ow j h h'
  simp only [s6KeepO, Prod.mk.injEq] at e
  exact ⟨by simp only [sc3KO, e.1, e.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.1], e.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- the `input_phase` caller-invariant package for `sc3P` -/
theorem sc3_IPI {tn fo c B CS F} (hG : sc3Cfg c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (h64 : System.Platform.numBits = 64) (hC : SimARCtx c) (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i) : sc2IPI tn fo c (sc3P tn fo c B CS F) :=
  ⟨fun s h => (sc3_P_PI hG hlen h64 h).1, sc3_hookfr hG hlen h64, sc3_relaxCl hG hlen h64, sc3_tp hG hlen h64 hC hfo hp,
    sc3_lr hG hlen h64, fun s h => h.2.2.1.2.2.2.2⟩

/-- `SimARInv` across the processors frame (only score/health values and the clock rate change) -/
theorem sc3_ar_pfr {tn fo P b n c} {s s' : sim.state.St} (hI : SimARInv tn fo P b n c s 0 0 0) (h : pr_PFr s s') :
    SimARInv tn fo P b n c s' 0 0 0 := by
  obtain ⟨ss, ss1, hs, hs1, cr, rfl, e1, e2, e3, e4⟩ := h
  generalize ss.has_completed = x1 at e1
  generalize ss1.has_completed = x2 at e2
  generalize hs.health = y1 at e3
  generalize hs.nearest_index = z1 at e3
  generalize hs1.health = y2 at e4
  generalize hs1.nearest_index = z2 at e4
  subst e1 e2 e3 e4
  exact ⟨s3b_inv_of hI.inv rfl rfl, hI.tf, hI.ik, hI.em, hI.sp, hI.cnt, hI.seen,
    sim_enum_transfer tn fo c s _ hI.inv rfl hI.enum⟩

/-! ## the contracts of the first three phases -/

theorem sc3_proc_phc (tn fo) (c : sim.state.Ctx) (B CS F : Nat) (hG : sc3Cfg c) :
    sc2PhC tn fo c sim.step.processors_phase OsuModel.Sim.Sim.processorsPhase
      (sc3P tn fo c B CS F) (sc3P tn fo c B CS F) := by
  refine pr_proc_phc tn fo c (sc3Q tn fo c B CS F) (fun s h => ⟨h.2.1.1, fun x hx k hk => ?_⟩) (fun s s' h hf => ?_)
  · have := hG.rs x hx k hk
    have := h.1.ar.sp
    omega
  · obtain ⟨hL, hX, hk, hF⟩ := h
    have hA := sc3_ar_pfr hL.ar hf
    obtain ⟨ss, ss1, hs, hs1, cr, rfl, -⟩ := hf
    exact sc3_Q_fr ⟨hL, hX, hk, hF⟩ (by rw [← hF]; exact hA) hL.lp hX.2.2.1 hX.2.2.2.1 hX.2.1 hX.2.2.2.2 rfl
      (fun _ _ _ => ⟨rfl, rfl⟩) rfl rfl

theorem sc3_input_phc (tn fo) (c : sim.state.Ctx) (B CS F : Nat) (hG : sc3Cfg c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (h64 : System.Platform.numBits = 64) (hC : SimARCtx c)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length) (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (hcp : c.corner_pow = OsuModel.Sim.receptorCornerRadiusPow) (hfl : c.frames.val.length < 2 ^ 63)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hfa : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3) :
    sc2PhC tn fo c sim.step.input_phase OsuModel.Sim.Sim.inputPhase (sc3P tn fo c B CS F) (sc3P tn fo c B CS F) := by
  intro s h
  obtain ⟨r, s', e, rr, ii⟩ := sim.step.input_phase_refines tn fo c _ (sc3_IPI hG hlen h64 hC hfo hp) hcp hfl hfi hfa s
    h.2.2.2.1 h
  exact ⟨r, s', e, by cases r <;> exact rr, ii⟩

theorem sc3_play_phc (tn fo) (c : sim.state.Ctx) (B CS F : Nat) (hG : sc3Cfg c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (h64 : System.Platform.numBits = 64) (hC : SimARCtx c)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length) (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (hPC : s3d_PCtx c) :
    sc2PhC tn fo c sim.step.playfield_update OsuModel.Sim.Sim.playfieldUpdate (sc3P tn fo c B CS F)
      (sc3P tn fo c B CS F) := by
  intro s h
  obtain ⟨r, s', e, rr, ii⟩ := s3d_playfield_gen h64 tn fo c s _ h (fun s h => (sc3_P_PI hG hlen h64 h).1)
    (sc3_hookfr hG hlen h64) (sc3_relaxCl hG hlen h64) hPC (sc3_tp hG hlen h64 hC hfo hp)
  exact ⟨r, s', e, by cases r <;> exact rr, ii⟩

/-! ## phase-contract plumbing -/

theorem sc3_phc_mono {tn fo c f F} {A B A' B' : sim.state.St → Prop} (h : sc2PhC tn fo c f F A B)
    (hA : ∀ s, A' s → A s) (hB : ∀ s, B s → B' s) : sc2PhC tn fo c f F A' B' := by
  intro s hs
  obtain ⟨r, s', e, rr, ii⟩ := h s (hA s hs)
  exact ⟨r, s', e, rr, fun hr => hB _ (ii hr)⟩

/-- adding a spec trace `T` (the spec states reached so far) to a phase contract -/
theorem sc3_phc_tr {tn fo c f F} {A B : sim.state.St → Prop} (h : sc2PhC tn fo c f F A B)
    (T : OsuModel.Sim.St → Prop) :
    sc2PhC tn fo c f F (fun s => A s ∧ T (simStS tn s))
      (fun s => B s ∧ ∃ S', T S' ∧ F (simCtxS tn fo c) S' = .ok ((), simStS tn s)) := by
  intro s ⟨hA, hT⟩
  obtain ⟨r, s', e, rr, ii⟩ := h s hA
  refine ⟨r, s', e, rr, fun hr => ⟨ii hr, simStS tn s, hT, ?_⟩⟩
  subst hr; exact rr

/-! ## the update-loop invariant -/

/-- what the per-object updates keep (the reflexive-transitive closure of `sc2DFr`, without the spin counts) -/
structure sc3UF (s₀ s : sim.state.St) : Prop where
  keep : simKeepS s = simKeepS s₀
  len : s.objs.val.length = s₀.objs.val.length
  ko : ∀ j (h : j < s₀.objs.val.length) (h' : j < s.objs.val.length), sc2KO (s.objs.val[j]'h') = sc2KO (s₀.objs.val[j]'h)
  il : s.insts.val.length = s₀.insts.val.length

theorem sc3UF_refl (s : sim.state.St) : sc3UF s s := ⟨rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem sc3UF_dfr {i : Nat} {s₀ s s' : sim.state.St} (h : sc3UF s₀ s) (F : sc2DFr i s s') : sc3UF s₀ s' :=
  ⟨F.keep.trans h.keep, F.len.trans h.len,
   fun j h0 h' => (F.ko j (by rw [h.len]; exact h0) h').trans (h.ko j h0 _), F.il.trans h.il⟩

/-- the caller predicate of the update loop: reached from a lifetime-invariant state by update frames -/
def sc3Y (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (F : Nat) (s : sim.state.St) : Prop :=
  ∃ s₀ B₀ CS₀, simLifeInv tn fo s2_tfOk B₀ (sc2N c) CS₀ c s₀ ∧ sc3X c s₀ ∧ pr_HB c s₀ ∧ simFut s₀ = F ∧ sc3UF s₀ s

theorem sc3Y_fr {tn fo c F} : ∀ i s s', sc3Y tn fo c F s → sc2DFr i s s' → sc3Y tn fo c F s' :=
  fun _ _ _ ⟨s₀, B, C, a, b, d, e, f⟩ F => ⟨s₀, B, C, a, b, d, e, sc3UF_dfr f F⟩

/-- the per-step share of the run budget (`RunBudgetS` on Rust context values, with `R` updates left) -/
def sc3Unj (c : sim.state.Ctx) : Nat := (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum

def sc3Bud (c : sim.state.Ctx) (R : Nat) : Prop :=
  (2 * R + sc3Unj c + 1) * (sc2N c + sc2N c + 4) + c.pb.objects.val.length * (4 * sc2N c + 8) + 1 < 2 ^ 64 - 1 ∧
  (R + 1) * 2000000 ≤ 2 ^ 54

theorem sc3Bud_mono {c : sim.state.Ctx} {R R' : Nat} (h : R' ≤ R) (hb : sc3Bud c R) : sc3Bud c R' := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨lt_of_le_of_lt ?_ h1, le_trans (by nlinarith) h2⟩
  have : (2 * R' + sc3Unj c + 1) * (sc2N c + sc2N c + 4) ≤ (2 * R + sc3Unj c + 1) * (sc2N c + sc2N c + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- the update-loop invariant with `b` updates left -/
def sc3J (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (b : Nat) (s : sim.state.St) : Prop :=
  ∃ F, sc2J tn fo c (F * (4 * sc2N c + 8)) (sc3Y tn fo c F) b s ∧ sc3Bud c b

theorem sc3J_mono {tn fo c} : ∀ b s, sc3J tn fo c (b + 1) s → sc3J tn fo c b s := by
  intro b s ⟨F, ⟨hA, hLP, hAD, hTK, hCS, hst, hd, hY⟩, hb⟩
  refine ⟨F, ⟨sim_ar_weak s3b_tfEng_s2 ?_ hA, hLP, hAD, hTK, fun j h => ?_, hst, hd, hY⟩, sc3Bud_mono (by omega) hb⟩
  · have : b * (2 * (sc2N c + sc2N c + 4)) ≤ (b + 1) * (2 * (sc2N c + sc2N c + 4)) := Nat.mul_le_mul_right _ (by omega)
    omega
  · exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ b)) _) (hCS j h)

theorem sc3_updC (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx)
    (hC : SimARCtx c) (hlen : c.pb.objects.val.length + 4 ≤ U64.max)
    (hfo : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (hsl : ∀ i (hi : i < c.pb.objects.val.length), (c.pb.objects.val[i]'hi).h.kind = .Slider →
      ∃ hti : i < c.tail_idx.val.length, (c.tail_idx.val[i]'hti).val < (c.pb.objects.val[i]'hi).nested.val.length)
    (hST : ∀ i, s7StrictOk tn c i) : sc2UpdC tn fo c (sc3J tn fo c) := by
  intro b s i hi ⟨F, hJ, hb⟩ hal
  obtain ⟨r, s', e, rr, ii⟩ := sc2_upd h64 tn fo c hC hlen hfo hp hsl hST (F * (4 * sc2N c + 8)) (sc3Y tn fo c F)
    sc3Y_fr b s i hi hJ hal
  exact ⟨r, s', e, rr, fun h => let ⟨a, l⟩ := ii h; ⟨⟨F, a, sc3Bud_mono (by omega) hb⟩, l⟩⟩

/-- leaving the update loop with `b` updates left: the next step's invariant pieces -/
theorem sc3_J_end {tn fo c b} {s : sim.state.St} (hJ : sc3J tn fo c b s) :
    simLifeInv tn fo s2_tfOk (b * (2 * (sc2N c + sc2N c + 4))) (sc2N c) (2 ^ 54 - b * 2000000) c s ∧ sc3X c s ∧
      pr_HB c s ∧ sc3Bud c b := by
  obtain ⟨F, ⟨hA, hLP, hAD, hTK, hCS, hst, hd, ⟨s₀, B₀, C₀, hL₀, hX₀, hH₀, hF₀, U⟩⟩, hb⟩ := hJ
  have hko : ∀ j (h : j < s₀.objs.val.length) (h' : j < s.objs.val.length),
      (s.objs.val[j]'h').life = (s₀.objs.val[j]'h).life ∧ (s.objs.val[j]'h').tick_insts = (s₀.objs.val[j]'h).tick_insts ∧
      (s.objs.val[j]'h').tick_live.val.length = (s₀.objs.val[j]'h).tick_live.val.length := by
    intro j h h'
    have e := U.ko j h h'
    simp only [sc2KO, Prod.mk.injEq] at e
    exact ⟨e.1, e.2.2.2.2.1, e.2.2.2.2.2⟩
  have hF : simFut s = F := by rw [← hF₀]; exact sc3_simFut_eq U.len (fun j h h' => (hko j h h').1)
  have k := U.keep
  have ek : s.k = s₀.k := congrArg (fun x => x.1) k
  have ef : s.first_lifetime_update = s₀.first_lifetime_update := congrArg (fun x => x.2.2.1) k
  have enf : s.next_future = s₀.next_future := congrArg (fun x => x.2.2.2.1) k
  have efo : s.future_order = s₀.future_order := congrArg (fun x => x.2.2.2.2.1) k
  have ea : s.active = s₀.active := congrArg (fun x => x.2.2.2.2.2.1) k
  have ed : s.dict_slots = s₀.dict_slots := congrArg (fun x => x.2.2.2.2.2.2.1) k
  have efl : s.free_list = s₀.free_list := congrArg (fun x => x.2.2.2.2.2.2.2.1) k
  have ecc : s.child_counter = s₀.child_counter := congrArg (fun x => x.2.2.2.2.2.2.2.2.1) k
  have elr : s.last_replay = s₀.last_replay := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.1) k
  have epr : s.pressed = s₀.pressed := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.1) k
  have eap : s.ap_frame = s₀.ap_frame := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) k
  have ebl : s.block_last = s₀.block_last := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) k
  have ebi : s.block_idx = s₀.block_idx := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) k
  have epo : s.pools = s₀.pools := congrArg (fun x => x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) k
  refine ⟨sc3_life_tr hL₀ (b' := b * (2 * (sc2N c + sc2N c + 4))) ?_ hLP (fun j h => ?_) U.len
    (fun j h h' => by simp only [sc3KO, (hko j h h').1, (hko j h h').2.1, (hko j h h').2.2])
    (by simp only [sc3KS, ed, efl, ea, ecc, ef, efo, enf, epo, U.il]),
    ⟨by rw [ek]; exact hX₀.1, by rw [eap]; exact hX₀.2.1, by unfold s6Blk; rw [ebl, ebi]; exact hX₀.2.2.1,
     by rw [epr]; exact hX₀.2.2.2.1, by rw [elr]; exact hX₀.2.2.2.2⟩, pr_HB_keep U.keep hH₀, hb⟩
  · rw [hF, show b * (2 * (sc2N c + sc2N c + 4)) + F * (4 * sc2N c + 8) =
      F * (4 * sc2N c + 8) + b * (2 * (sc2N c + sc2N c + 4)) by ring]
    exact hA
  · have := hCS j h
    omega

/-- the lifetime-phase target: the lifetime invariant, `sc3X`, the cursor bound, the step index -/
def sc3L4 (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (B CS : Nat) (s : sim.state.St) : Prop :=
  pr_HB c s ∧ simLifeInv tn fo s2_tfOk B (sc2N c) CS c s ∧ sc3X c s ∧ s.k.val < c.steps.val.length

theorem sc3_P_L4 {tn fo c B CS F} {s : sim.state.St} (h : sc3P tn fo c B CS F s) : sc3L4 tn fo c B CS s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- `update_order` and the update-loop invariant after the lifetime phase -/
theorem sc3_hO (h64 : System.Platform.numBits = 64) (tn fo) (c : sim.state.Ctx) (hG : sc3Cfg c)
    (hlen : c.pb.objects.val.length + 4 ≤ U64.max) (R Rn : Nat) (s : sim.state.St)
    (h : sc3L4 tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000) s)
    (hR : R = s.active.val.length + Rn) (hb : sc3Bud c R) :
    ∃ v, sim.step.update_order c s = ok v ∧
      OsuModel.Sim.Sim.updateOrder (simCtxS tn fo c) (simStS tn s) = .ok (abs v, simStS tn s) ∧
      (∀ x ∈ v.val, x.val < s.objs.val.length) ∧ sc3J tn fo c (Rn + v.val.length) s := by
  obtain ⟨hH, hL, hX, hk⟩ := h
  have hol := hL.ar.inv.objs_len
  obtain ⟨v, e, E, hvl, hvx⟩ := sc3_update_order tn fo c s hL.ar.inv (fun x hx => by rw [← hol]; exact hL.actl x hx)
    (sc3_act_small hL hlen h64)
  refine ⟨v, e, E, fun x hx => by rw [hol]; exact hvx x hx, simFut s, ⟨?_, hL.lp, hL.ald, hL.spt, fun j hj => ?_, hX.1,
    fun x hx k hk => ?_, ⟨s, _, _, hL, hX, hH, rfl, sc3UF_refl s⟩⟩, by rw [hvl, Nat.add_comm, ← hR]; exact hb⟩
  · have e1 : R * (2 * (sc2N c + sc2N c + 4)) + simFut s * (4 * sc2N c + 8) =
        simFut s * (4 * sc2N c + 8) + (Rn + v.val.length) * (2 * (sc2N c + sc2N c + 4)) := by
      rw [hR, hvl]; ring
    rw [← e1]; exact hL.ar
  · have h1 := hL.cs j hj
    have h2 := hb.2
    rw [hvl]; rw [hR] at h1 h2
    have : (s.active.val.length + Rn) * 2000000 = s.active.val.length * 2000000 + Rn * 2000000 := by ring
    have : (Rn + s.active.val.length) * 2000000 = s.active.val.length * 2000000 + Rn * 2000000 := by ring
    omega
  · have := hG.rs x hx k hk
    have := hL.ar.sp
    omega

/-! ## the step invariant and `step_once` -/

/-- the lifetime-phase contract (sim8's `lifetime_update_refines`, instantiated at the step invariant) -/
def sc3LifeC (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) : Prop :=
  ∀ (B CS : Nat) (s : sim.state.St),
    B + c.pb.objects.val.length * (4 * sc2N c + 8) + sc3Unj c * (sc2N c + sc2N c + 4) + 1 < Usize.max →
    CS ≤ 2 ^ 54 → sc3L4 tn fo c B CS s →
    ∃ r s', sim.step.lifetime_update c s = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.lifetimeUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (r = .Ok () → sc3L4 tn fo c B CS s')

/-- the indexed spec schedule (as in `runBudgetNeed`) -/
def sc3L (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) : List (Nat × OsuModel.Sim.Step) :=
  (List.range (simCtxS tn fo c).steps.size).zip (simCtxS tn fo c).steps.toList

/-- the per-object updates the spec run still performs from step `k` on (state `s` before step `k`) -/
def sc3R (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (k : Nat) (s : sim.state.St) : Nat :=
  sc2UnitsRun (simCtxS tn fo c) ((sc3L tn fo c).drop k) (simStS tn s)

/-- **the step invariant** of `run` before step `k`: sim8's lifetime invariant with the transform budget and spin
headroom of the `sc3R` remaining updates (2 units of `n+n+4` and `2·10^6` spins each), the rest `sc3X`, proc's
drain-cursor bound and the remaining run budget -/
def sc3Inv (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (k : Nat) (s : sim.state.St) : Prop :=
  pr_HB c s ∧
  simLifeInv tn fo s2_tfOk (sc3R tn fo c k s * (2 * (sc2N c + sc2N c + 4))) (sc2N c)
    (2 ^ 54 - sc3R tn fo c k s * 2000000) c s ∧
  sc3X c s ∧ sc3Bud c (sc3R tn fo c k s)

theorem sc3L_drop (tn fo) (c : sim.state.Ctx) (k : Nat) (hk : k < c.steps.val.length) :
    (sc3L tn fo c).drop k = (k, (abs (c.steps.val[k]'hk) : OsuModel.Sim.Step)) :: (sc3L tn fo c).drop (k + 1) := by
  have hsz : (simCtxS tn fo c).steps.size = c.steps.val.length := by simp [simCtxS, abs]
  have hl : (sc3L tn fo c).length = c.steps.val.length := by simp [sc3L, hsz, simCtxS, abs]
  rw [List.drop_eq_getElem_cons (by rw [hl]; exact hk)]
  congr 1
  simp [sc3L, List.getElem_zip, simCtxS, abs]

theorem sc3_usize_max (h64 : System.Platform.numBits = 64) : Usize.max = 2 ^ 64 - 1 := usize_max_64 h64

/-- the per-step contract of the `run` loop for the step invariant `sc3Inv`, given the lifetime contract -/
theorem sc3_step (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) (hW : ev_ctxWF c) (hG : sc3Cfg c) (hfl : c.frames.val.length < 2 ^ 63)
    (hfa : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hST : ∀ i, s7StrictOk tn c i) (hLC : sc3LifeC tn fo c) :
    sc2StepC tn fo c (sc3Inv tn fo c) := by
  intro k hk s hI
  obtain ⟨hH, hL, hX, hb⟩ := hI
  have hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i := fun i _ => hW.play.2.2.2 i
  generalize hS0 : simStS tn { s with k := k, t := (c.steps.val[k.val]'hk).time } = S0
  generalize hRn : (match OsuModel.Sim.Sim.stepOnce (simCtxS tn fo c) S0 with
    | .ok (_, S2) => sc2UnitsRun (simCtxS tn fo c) ((sc3L tn fo c).drop (k.val + 1)) S2
    | .error _ => 0) = Rn
  have hRdef : sc3R tn fo c k.val s = (match sc2PreDho (simCtxS tn fo c) S0 with
      | .error _ => 0 | .ok (_, SL) => SL.active.size + Rn) := by
    unfold sc3R
    rw [sc3L_drop tn fo c k.val hk, ← hRn, ← hS0]
    rfl
  generalize hR : sc3R tn fo c k.val s = R at hL hb hRdef
  have hbud : R * (2 * (sc2N c + sc2N c + 4)) + c.pb.objects.val.length * (4 * sc2N c + 8) +
      sc3Unj c * (sc2N c + sc2N c + 4) + 1 < Usize.max := by
    rw [sc3_usize_max h64]
    have e : (2 * R + sc3Unj c + 1) * (sc2N c + sc2N c + 4) =
        R * (2 * (sc2N c + sc2N c + 4)) + sc3Unj c * (sc2N c + sc2N c + 4) + (sc2N c + sc2N c + 4) := by ring
    have := hb.1
    omega
  have hP0 : sc3P tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000) (simFut s)
      { s with k := k, t := (c.steps.val[k.val]'hk).time } := by
    refine ⟨hH, sc3_life_tr hL ?_ hL.lp hL.cs rfl (fun _ _ _ => rfl) rfl,
      ⟨fun _ => by show k.val - 1 < c.steps.val.length; omega, hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2⟩, hk, rfl⟩
    exact sim_ar_inv_hook tn fo s2_tfOk _ (sc2N c) c s 0 0 0 0 hL.ar _ (s3b_inv_of hL.ar.inv rfl rfl)
      (s3b_objFrame_of_eq rfl) rfl hL.ar.tf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h1 := sc3_phc_tr (sc3_proc_phc tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000) (simFut s) hG)
    (fun S => S = S0)
  have h2 := sc3_phc_tr (sc3_input_phc tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000) (simFut s)
    hG hW.fuel h64 hW.ar hW.vis_first hp hW.play.1 hfl hfi hfa)
    (fun S => ∃ T0, T0 = S0 ∧ OsuModel.Sim.Sim.processorsPhase (simCtxS tn fo c) T0 = .ok ((), S))
  have h3 := sc3_phc_tr (sc3_play_phc tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000) (simFut s)
    hG hW.fuel h64 hW.ar hW.vis_first hp hW.play)
    (fun S => ∃ T1, (∃ T0, T0 = S0 ∧ OsuModel.Sim.Sim.processorsPhase (simCtxS tn fo c) T0 = .ok ((), T1)) ∧
      OsuModel.Sim.Sim.inputPhase (simCtxS tn fo c) T1 = .ok ((), S))
  have h4L : sc2PhC tn fo c sim.step.lifetime_update OsuModel.Sim.Sim.lifetimeUpdate
      (sc3P tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000) (simFut s))
      (sc3L4 tn fo c (R * (2 * (sc2N c + sc2N c + 4))) (2 ^ 54 - R * 2000000)) :=
    fun s' h => hLC _ _ s' hbud (Nat.sub_le _ _) (sc3_P_L4 h)
  have h4 := sc3_phc_tr h4L
    (fun S => ∃ T2, (∃ T1, (∃ T0, T0 = S0 ∧ OsuModel.Sim.Sim.processorsPhase (simCtxS tn fo c) T0 = .ok ((), T1)) ∧
      OsuModel.Sim.Sim.inputPhase (simCtxS tn fo c) T1 = .ok ((), T2)) ∧
      OsuModel.Sim.Sim.playfieldUpdate (simCtxS tn fo c) T2 = .ok ((), S))
  have key := sc2_step_once tn fo c _ _ _ _ _ (sc3J tn fo c) Rn h1 h2 h3 h4 ?hO
    (sc3_updC h64 tn fo c hW.ar hW.fuel hW.vis_first hp hW.tail hST) sc3J_mono
  case hO =>
    rintro s4 ⟨h4s, T3, ⟨T2, ⟨T1, ⟨T0, rfl, e1⟩, e2⟩, e3⟩, e4⟩
    have hpre : sc2PreDho (simCtxS tn fo c) T0 = .ok ((), simStS tn s4) := by
      simp only [sc2PreDho, simM_bind, e1, e2, e3, e4, Except.bind]
    have hR2 : R = s4.active.val.length + Rn := by
      rw [hRdef, hpre]; simp [simStS, abs]
    exact sc3_hO h64 tn fo c hG hW.fuel R Rn s4 h4s hR2 hb
  obtain ⟨r, s', e, rr, ii⟩ := key _ ⟨hP0, hS0⟩
  refine ⟨r, s', e, by rw [← hS0]; exact rr, fun hr => ?_⟩
  obtain ⟨hL', hX', hH', hb'⟩ := sc3_J_end (ii hr)
  have hR' : sc3R tn fo c (k.val + 1) s' = Rn := by
    subst hr
    simp only [simRelM] at rr
    rw [← hRn, ← hS0, rr]
    rfl
  unfold sc3Inv
  rw [hR']
  exact ⟨hH', hL', hX', hb'⟩

/-! ## the run budget on Rust values (D70) -/

theorem sc3_vmCost (v : sim.mods.VisMod) : sc2VmCostS (abs v) = s3b_vmCost v := by
  cases v <;> rfl

/-- the custom-state cost on spec values is the Rust-side `s3b_csCostFrom vis_mods 0` -/
theorem sc3_csCost (cfg : sim.mods.Config) : sc2CsCostS (abs cfg) = s3b_csCostFrom cfg.vis_mods.val 0 := by
  unfold sc2CsCostS s3b_csCostFrom
  show ((cfg.vis_mods.val.map abs).toArray.toList.map sc2VmCostS).sum = _
  simp only [List.toList_toArray, List.map_map, List.drop_zero]
  congr 1
  apply List.map_congr_left
  intro v _
  exact sc3_vmCost v

theorem sc3_csCost_ctx (tn fo) (c : sim.state.Ctx) : sc2CsCostS (simCtxS tn fo c).cfg = sc2N c :=
  sc3_csCost c.cfg

/-- `RunBudgetS` at the abstract context gives the step budget `sc3Bud` of the whole run -/
theorem sc3_bud_of (tn fo) (c : sim.state.Ctx) (S0 : OsuModel.Sim.St) (h : RunBudgetS (simCtxS tn fo c) S0) :
    sc3Bud c (runBudgetNeed (simCtxS tn fo c) S0) := by
  have hn := sc3_csCost_ctx tn fo c
  have ho : (simCtxS tn fo c).pb.objects.size = c.pb.objects.val.length := by simp [simCtxS, playableS]
  have hu : ((simCtxS tn fo c).pb.objects.toList.map (fun o => o.nested.size + 1)).sum = sc3Unj c := by
    simp [simCtxS, playableS, sc3Unj, topS, Function.comp_def]
  unfold RunBudgetS at h
  simp only [hn, ho, hu] at h
  exact h

theorem sc3R_zero (tn fo) (c : sim.state.Ctx) (s : sim.state.St) :
    sc3R tn fo c 0 s = runBudgetNeed (simCtxS tn fo c) (simStS tn s) := by
  simp [sc3R, runBudgetNeed, sc3L]

/-! ## `run`, `run_with` (given the lifetime contract and the initial invariant) -/

theorem sc3_run (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) (hW : ev_ctxWF c) (hG : sc3Cfg c) (hfl : c.frames.val.length < 2 ^ 63)
    (hfa : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hST : ∀ i, s7StrictOk tn c i) (hLC : sc3LifeC tn fo c) (s : sim.state.St) (h0 : sc3Inv tn fo c 0 s) :
    ∃ r s', sim.step.run c s = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.run (simCtxS tn fo c) (simStS tn s)) :=
  sc2_run tn fo c (sc3Inv tn fo c) (sc3_step h64 tn fo c hW hG hfl hfa hfi hST hLC) s h0

/-- the initial-state invariant from its pieces (sim8's lifetime invariant at init, the init shape, `RunBudgetS`) -/
theorem sc3_inv0 (tn fo) (c : sim.state.Ctx) (s0 : sim.state.St)
    (hB : RunBudgetS (simCtxS tn fo c) (simStS tn s0))
    (hL : ∀ B CS, simLifeInv tn fo s2_tfOk B (sc2N c) CS c s0)
    (hX : sc3X c s0) (hH : pr_HB c s0) : sc3Inv tn fo c 0 s0 := by
  have hb := sc3_bud_of tn fo c _ hB
  rw [← sc3R_zero] at hb
  exact ⟨hH, hL _ _, hX, hb⟩

/-! ## the initial state: `sc3X` and the cursor bound (from `init_state_refines`) -/

theorem sc3_init (tn : Nat → String) (c : sim.state.Ctx) (s0 : sim.state.St)
    (h : sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0)) : sc3X c s0 ∧ pr_HB c s0 := by
  obtain ⟨R, eR, hR⟩ := sim.step.init_state_refines tn c.cfg c.pb c.smax.init_without_mods
  rw [h] at eR
  obtain rfl := (Result.ok_injective eR).symm
  simp only [simRel] at hR
  unfold OsuModel.Sim.initState at hR
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hR
  split at hR
  · cases hR
  split at hR
  · cases hR
  have hS := (Except.ok.inj hR)
  have ek := congrArg OsuModel.Sim.St.k hS
  have eap := congrArg OsuModel.Sim.St.apFrame hS
  have epr := congrArg OsuModel.Sim.St.pressed hS
  have elr := congrArg OsuModel.Sim.St.lastReplay hS
  have ebl := congrArg (fun S => S.blockLast.size) hS
  have ebi := congrArg OsuModel.Sim.St.blockIdx hS
  have eh := congrArg (fun S => S.health.nearestIndex) hS
  have ehr := congrArg (fun S => S.healthRP.nearestIndex) hS
  simp only [simStS] at ek eap epr elr ebl ebi eh ehr
  have hbl : s0.block_last.val.length = c.cfg.input_blockers.val.length := by
    simp [abs, configS] at ebl; omega
  have hbi1 : s0.block_idx.val.length = c.cfg.input_blockers.val.length := by
    have := congrArg Array.size ebi
    simp [abs, configS] at this; omega
  have hbi2 : ∀ x ∈ s0.block_idx.val, x.val = 0 := by
    intro x hx
    have hx' : x.val ∈ (abs s0.block_idx : Array Nat) := by simp [abs]; exact ⟨x, hx, rfl⟩
    rw [← ebi] at hx'
    simp at hx'
    exact hx'.2
  have hp0 : actListS s0.pressed = [] := by
    have := congrArg Array.toList epr
    simpa using this.symm
  refine ⟨⟨fun hk => by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega, fun h0 x hx => by rw [hbi2 x hx]; omega⟩,
    by rw [hp0]; exact List.nodup_nil, fun l hl => by rw [hl] at elr; simp at elr⟩, fun h0 => ?_, fun h0 => ?_⟩
  · simp [abs] at eh; omega
  · simp [abs] at ehr; omega

/-- `run_with` given the lifetime contract and sim8's initial lifetime invariant -/
theorem sc3_run_with (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) (hW : ev_ctxWF c) (hG : sc3Cfg c) (hfl : c.frames.val.length < 2 ^ 63)
    (hfa : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hST : ∀ i, s7StrictOk tn c i) (hLC : sc3LifeC tn fo c)
    (hIL : ∀ s0, sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0) → ∀ B CS, simLifeInv tn fo s2_tfOk B (sc2N c) CS c s0)
    (hB : ∀ S0, OsuModel.Sim.initState (abs c.cfg) (playableS tn c.pb) c.smax.init_without_mods.val = .ok S0 → RunBudgetS (simCtxS tn fo c) S0) :
    ∃ R, sim.step.run_with c = ok R ∧
      simRel (simStS tn) R (OsuModel.Sim.runWith (simCtxS tn fo c) (abs c.cfg) (playableS tn c.pb)) := by
  refine sc2_run_with tn fo c (sc3Inv tn fo c) (sc3_step h64 tn fo c hW hG hfl hfa hfi hST hLC)
    (sim.step.init_state_refines tn c.cfg c.pb c.smax.init_without_mods) (fun s0 h => ?_)
  obtain ⟨hX, hH⟩ := sc3_init tn c s0 h
  obtain ⟨R, eR, hR⟩ := sim.step.init_state_refines tn c.cfg c.pb c.smax.init_without_mods
  rw [h] at eR
  obtain rfl := (Result.ok_injective eR).symm
  exact sc3_inv0 tn fo c s0 (hB _ hR) (hIL s0 h) hX hH

/-- the lifetime phase keeps `sc3L4` given sim8's invariant and its `s8LuKeep` frame -/
theorem sc3_L4_of_lk {tn fo c B CS} {s s' : sim.state.St} (h : sc3L4 tn fo c B CS s)
    (hL' : simLifeInv tn fo s2_tfOk B (sc2N c) CS c s') (hk : s8LuKeep s' = s8LuKeep s) : sc3L4 tn fo c B CS s' := by
  obtain ⟨hH, -, hX, hkN⟩ := h
  simp only [s8LuKeep, Prod.mk.injEq] at hk
  obtain ⟨ek, -, -, -, elr, epr, -, -, -, -, -, eap, ebl, ebi, -, -, eni, enr⟩ := hk
  refine ⟨pr_HB_of_ni eni enr hH, hL', ⟨by rw [ek]; exact hX.1, by rw [eap]; exact hX.2.1,
    by unfold s6Blk; rw [ebl, ebi]; exact hX.2.2.1, by rw [epr]; exact hX.2.2.2.1, by rw [elr]; exact hX.2.2.2.2⟩,
    by rw [ek]; exact hkN⟩


/-- the lifetime contract, from sim8's `lifetime_update_refines` -/
theorem sc3_lifeC (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) (hW : ev_ctxWF c) (hTK : s8TKCtx c) : sc3LifeC tn fo c := by
  intro B CS s hb hcs h
  have hCSb : CS * 360 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 360 hcs) (by norm_num)
  obtain ⟨r, s', e, rr, ii⟩ := sim.step.lifetime_update_refines h64 tn fo s3b_tfEng_s2 sc2_tfX_s2 B (sc2N c) CS c
    hW.ar (sim_ar_cs tn fo c hW.vis_first) hTK hW.objs_small hW.nested_small (fun i _ => hW.play.2.2.2 i) hW.tail
    (by rw [s8Umax_eq]; exact hb) hCSb s h.2.1
  exact ⟨r, s', e, rr, fun hr => let ⟨a, b, _⟩ := ii hr; sc3_L4_of_lk h a b⟩

/-! ## the named refinements -/

/-- `step_once` (Rust) refines `Sim.stepOnce` from the step invariant before step `k` and re-establishes it before
step `k+1` -/
-- NOT-CONDITIONAL: ev_ctxWF / sc3Cfg / s8TKCtx / s7StrictOk are context premises; hfi is the schedule's frame-index
-- range (named row SchedFramesIn); the run budget is inside sc3Inv (from RunBudgetS, named row RunBudgetIn)
theorem sim.step.step_once_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) (hW : ev_ctxWF c) (hG : sc3Cfg c) (hTK : s8TKCtx c)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hST : ∀ i, s7StrictOk tn c i) (k : Usize) (hk : k.val < c.steps.val.length) (s : sim.state.St)
    (hI : sc3Inv tn fo c k.val s) :
    ∃ r s', sim.step.step_once c { s with k := k, t := (c.steps.val[k.val]'hk).time } = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.stepOnce (simCtxS tn fo c)
        (simStS tn { s with k := k, t := (c.steps.val[k.val]'hk).time })) ∧
      (r = .Ok () → sc3Inv tn fo c (k.val + 1) s') :=
  sc3_step h64 tn fo c hW hG hW.frames_small hW.acts hfi hST (sc3_lifeC h64 tn fo c hW hTK) k hk s hI

/-- `run` (Rust) refines `Sim.run` from the step invariant at step 0 -/
-- NOT-CONDITIONAL: context premises as step_once_refines
theorem sim.step.run_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    (c : sim.state.Ctx) (hW : ev_ctxWF c) (hG : sc3Cfg c) (hTK : s8TKCtx c)
    (hfi : ∀ st ∈ c.steps.val, -1 ≤ st.frame_index.val ∧ st.frame_index.val < (c.frames.val.length : Int))
    (hST : ∀ i, s7StrictOk tn c i) (s : sim.state.St) (h0 : sc3Inv tn fo c 0 s) :
    ∃ r s', sim.step.run c s = ok (r, s') ∧
      simRelM tn s' r (OsuModel.Sim.Sim.run (simCtxS tn fo c) (simStS tn s)) :=
  sc3_run h64 tn fo c hW hG hW.frames_small hW.acts hfi hST (sc3_lifeC h64 tn fo c hW hTK) s h0

end OsuProofs
