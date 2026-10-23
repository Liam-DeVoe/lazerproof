import OsuProofs.Sim.StepMain
import OsuProofs.Eval.E2EBase
/-
sim9: the initial lifetime invariant (`js_EvalOpen.initLife`, STATE "[e2e2 -> sim8]"): `init_state` establishes
`simLifeInv` for every budget `B`/`CS` (everything Future, nothing active, dictionary/free list/instances empty,
counters 0). `s9_init_facts`: Rust-level facts of the initial state (from `init_state_refines` via `simStS`);
`s9_initLife`: the invariant under the context facts `s9Ctx`; `sim.step.init_state_lifeInv`: the e2e form at
`ev_tn`/empty future order for an `ev_ctxWF` ctx related to a spec ctx with `e2CfgIdx` (incl. `s9EasyOk`, every
`Config.ofMods`), given the D77 acc-challenge budget `s9AccBudS` on spec values (fail_triggers is a u64 bumped up to
1 + 2·#AC times per judgement; not derivable from the trusted bounds). `s9_init_shape`: simcore3's init-state shape facts.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s9_mapM_size {α β ε} (f : α → Except ε β) : ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length := by
  intro l; induction l with
  | nil => intro r h; simp [List.mapM_nil, Pure.pure, Except.pure] at h; subst h; rfl
  | cons a t ih =>
    intro r h
    rw [List.mapM_cons] at h
    cases hf : f a with
    | error e => rw [hf] at h; cases h
    | ok b =>
      cases ht : t.mapM f with
      | error e => rw [hf, ht] at h; cases h
      | ok r' =>
        rw [hf, ht] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        subst h; simp [ih r' ht]

theorem s9_amapM_size {α β ε} (f : α → Except ε β) (a : Array α) (b : Array β) (h : a.mapM f = .ok b) :
    b.size = a.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases e : a.toList.mapM f with
  | error x => rw [e] at h; cases h
  | ok r =>
    rw [e] at h
    simp [Functor.map, Except.map] at h
    subst h; simp [s9_mapM_size f _ r e]

theorem s9_netStr_size {α β} (f : α → Except NetExn β) (a : Array α) (b : Array β)
    (h : OsuModel.Sim.netStr (a.mapM f) = .ok b) : b.size = a.size := by
  unfold OsuModel.Sim.netStr at h
  split at h
  · rename_i v hv; cases h; exact s9_amapM_size f a _ hv
  · cases h

theorem s9_simAdL_len (L : List sim.mods.DynRate) : (simAdL L).length = (L.filter s3b_isAd).length := by
  induction L with
  | nil => rfl
  | cons d t ih => cases d <;> simp [simAdL, s3b_isAd, List.filter_cons, List.filterMap_cons] at ih ⊢ <;> omega

set_option linter.unusedSimpArgs false

/-- Rust-level facts of the initial state -/
structure s9I (c : sim.state.Ctx) (s0 : sim.state.St) : Prop where
  olen : s0.objs.val.length = c.pb.objects.val.length
  obj : ∀ j (h : j < s0.objs.val.length) (h' : j < c.pb.objects.val.length),
    (s0.objs.val[j]'h).life = .Future ∧ (s0.objs.val[j]'h).result = none ∧
    (s0.objs.val[j]'h).nested.val.length = (c.pb.objects.val[j]'h').nested.val.length ∧
    (∀ x ∈ (s0.objs.val[j]'h).nested.val, x = none) ∧ (s0.objs.val[j]'h).completed_spins.val = 0 ∧
    (s0.objs.val[j]'h).tick_insts.val = [] ∧ (s0.objs.val[j]'h).last_pressed.len.val = 0
  first : s0.first_lifetime_update = true
  dict : s0.dict_slots.val = []
  free : s0.free_list.val = []
  act : s0.active.val = []
  insts : s0.insts.val = []
  cc : s0.child_counter.val = 0
  out : s0.out.val = []
  pr : s0.pressed.len.val = 0
  pl : s0.pools.val.length = 6
  pn : ∀ p ∈ s0.pools.val, ∀ x ∈ p.val, x = none
  sc : ∀ ss, (ss = s0.score ∨ ss = s0.score_rp) → ss.judged_hits.val = 0 ∧ ss.combo.val = 0 ∧
    ss.current_accuracy_judgement_count.val = 0 ∧ ∀ k, k < 18 → (ss.stats.val.getD k 0#u64).val = 0
  hl : ∀ hh, (hh = s0.health ∨ hh = s0.health_rp) → hh.fail_triggers.val = 0 ∧
    hh.retries.val.length = c.cfg.easy_retries.val.length
  sp : s0.speed.val.length = c.cfg.dyn_rates.val.length
  atg : s0.as_target.val.length = (c.cfg.dyn_rates.val.filter s3b_isAd).length
  arc : s0.as_recent.val.length = (c.cfg.dyn_rates.val.filter s3b_isAd).length
  asc : s0.as_seen.val.length = (c.cfg.dyn_rates.val.filter s3b_isAd).length
  asn : ∀ l ∈ s0.as_seen.val, l.val = []

theorem s9_obj_facts (tn : Nat → String) (o : sim.state.OState) (t : sim.playable.TopObj)
    (l1 : OsuModel.Sim.Life.future = lifeS o.life) (l2 : (none : Option OsuModel.Sim.Res) = Option.map abs o.result)
    (l3 : (Array.map (fun _ => (none : Option OsuModel.Sim.Res)) (topS tn t).nested).toList =
      List.map (fun x => Option.map (abs : sim.state.Res → OsuModel.Sim.Res) x) o.nested.val)
    (l4 : 0 = o.completed_spins.val) (l5 : (#[] : Array Nat) = abs o.tick_insts)
    (l6 : [] = actListS o.last_pressed) :
    o.life = .Future ∧ o.result = none ∧ o.nested.val.length = t.nested.val.length ∧
    (∀ x ∈ o.nested.val, x = none) ∧ o.completed_spins.val = 0 ∧ o.tick_insts.val = [] ∧ o.last_pressed.len.val = 0 := by
  refine ⟨?_, ?_, ?_, ?_, l4.symm, ?_, ?_⟩
  · revert l1; cases o.life <;> simp [lifeS]
  · revert l2; cases o.result <;> simp
  · have := congrArg List.length l3; simp [topS] at this; omega
  · intro x hx
    have hm : Option.map (abs : sim.state.Res → OsuModel.Sim.Res) x ∈ List.map (fun x => Option.map (abs : sim.state.Res → OsuModel.Sim.Res) x) o.nested.val := List.mem_map_of_mem hx
    rw [← l3] at hm
    simp at hm
    revert hm; cases x <;> simp
  · simp [abs] at l5; exact l5
  · have hl3 := s2_items_len o.last_pressed
    simp only [actListS] at l6
    have := congrArg List.length l6
    simp at this
    omega

theorem s9_vnil {α β} [AbsTo α β] (v : alloc.vec.Vec α) (h : (#[] : Array β) = abs v) : v.val = [] := by
  have := congrArg Array.size h; simp [abs] at this; exact this

theorem s9_score (ss : sim.scoring.ScoreSt) (r : OsuModel.Sim.Rank) (hp) (w : Int)
    (e : ({ stats_size := hp, rank := r, totalScoreWithoutMods := w } : OsuModel.Sim.ScoreSt) = abs ss) :
    ss.judged_hits.val = 0 ∧ ss.combo.val = 0 ∧
    ss.current_accuracy_judgement_count.val = 0 ∧ ∀ k, k < 18 → (ss.stats.val.getD k 0#u64).val = 0 := by
  have e1 := congrArg OsuModel.Sim.ScoreSt.judgedHits e
  have e2 := congrArg OsuModel.Sim.ScoreSt.combo e
  have e3 := congrArg OsuModel.Sim.ScoreSt.currentAccuracyJudgementCount e
  have e4 := congrArg OsuModel.Sim.ScoreSt.stats e
  simp only [abs, scoreS] at e1 e2 e3 e4
  rw [show OsuModel.Sim.nStats = 100 from rfl] at e4
  have hl : ss.stats.val.length = 18 := by simpa using ss.stats.property
  refine ⟨e1.symm, e2.symm, e3.symm, fun k hk => ?_⟩
  by_cases h17 : k = 17
  · subst h17
    have := congrArg (fun a : Array Nat => a[99]?) e4
    simp [statsS, OsuModel.Sim.nStats] at this
    rw [List.getD_eq_getElem _ _ (by rw [hl]; omega)]; exact this
  · have := congrArg (fun a : Array Nat => a[k]?) e4
    simp [statsS, OsuModel.Sim.nStats, show k < 100 by omega, show k < 17 by omega, show k ≠ 99 by omega] at this
    rw [List.getElem?_eq_getElem (by rw [hl]; omega)] at this
    rw [List.getD_eq_getElem _ _ (by rw [hl]; omega)]; simpa using this

theorem s9_health (hh : sim.scoring.HealthSt) (R : Array Nat) (e : ({ retries := R } : OsuModel.Sim.HealthSt) = abs hh) :
    hh.fail_triggers.val = 0 ∧ hh.retries.val.length = R.size := by
  have e1 := congrArg OsuModel.Sim.HealthSt.failTriggers e
  have e2 := congrArg (fun h => h.retries.size) e
  simp [abs] at e1 e2
  exact ⟨by omega, by omega⟩

theorem s9_init_facts (tn : Nat → String) (c : sim.state.Ctx) (s0 : sim.state.St)
    (h : sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0)) : s9I c s0 := by
  obtain ⟨R, eR, hR⟩ := sim.step.init_state_refines tn c.cfg c.pb c.smax.init_without_mods
  rw [h] at eR
  obtain rfl := (Result.ok_injective eR).symm
  simp only [simRel] at hR
  unfold OsuModel.Sim.initState at hR
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hR
  split at hR
  · cases hR
  rename_i asI hAS
  split at hR
  · cases hR
  rename_i spI hSP
  have hS := (Except.ok.inj hR)
  have hAd0 : ∀ f : OsuModel.Sim.DynRate → Option F64,
      (∀ d : sim.mods.DynRate, f (abs d) = (match d with | .Adaptive ir => some ir | _ => none)) →
      Array.filterMap f (abs c.cfg : OsuModel.Sim.Config).dynRates = (simAdL c.cfg.dyn_rates.val).toArray := by
    intro f hf
    simp only [abs, configS, simAdL, List.filterMap_toArray, List.filterMap_map, Function.comp_def]
    congr 1; congr 1; funext d; exact hf d
  rw [hAd0 _ (by intro d; cases d <;> rfl)] at hS
  have hAd := s9_simAdL_len c.cfg.dyn_rates.val
  have eo := congrArg OsuModel.Sim.St.objs hS
  have ef := congrArg OsuModel.Sim.St.firstLifetimeUpdate hS
  have ed := congrArg OsuModel.Sim.St.dictSlots hS
  have efl := congrArg OsuModel.Sim.St.freeList hS
  have ea := congrArg OsuModel.Sim.St.active hS
  have ei := congrArg OsuModel.Sim.St.insts hS
  have ec := congrArg OsuModel.Sim.St.childCounter hS
  have eout := congrArg (fun S => S.out.size) hS
  have epr := congrArg OsuModel.Sim.St.pressed hS
  have epo := congrArg OsuModel.Sim.St.pools hS
  have esc := congrArg OsuModel.Sim.St.score hS
  have escr := congrArg OsuModel.Sim.St.scoreRP hS
  have ehl := congrArg OsuModel.Sim.St.health hS
  have ehr := congrArg OsuModel.Sim.St.healthRP hS
  have esp := congrArg (fun S => S.speed.size) hS
  have eat := congrArg (fun S => S.asTarget.size) hS
  have ear := congrArg (fun S => S.asRecent.size) hS
  have eas := congrArg OsuModel.Sim.St.asSeen hS
  simp only [simStS] at eo ef ed efl ea ei ec eout epr epo esc escr ehl ehr esp eat ear eas
  have eo' := congrArg Array.toList eo
  simp only [abs, playableS, Array.toList_map, List.toList_toArray, List.map_map] at eo'
  have hol : s0.objs.val.length = c.pb.objects.val.length := by
    have := congrArg List.length eo'; simp at this; omega
  refine ⟨hol, ?_, ef.symm, ?_, ?_, ?_, ?_, ec.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h h'
    have e1 := congrArg (fun l => l[j]?) eo'
    simp only [List.getElem?_map, List.getElem?_eq_getElem h, List.getElem?_eq_getElem h', Option.map_some,
      Option.some.injEq, Function.comp_def] at e1
    have l1 := congrArg OsuModel.Sim.OState.life e1
    have l2 := congrArg OsuModel.Sim.OState.result e1
    have l3 := congrArg (fun o => o.nested.toList) e1
    have l4 := congrArg OsuModel.Sim.OState.completedSpins e1
    have l5 := congrArg OsuModel.Sim.OState.tickInsts e1
    have l6 := congrArg OsuModel.Sim.OState.lastPressed e1
    simp only [ostateS] at l1 l2 l3 l4 l5 l6
    exact s9_obj_facts _ _ _ l1 l2 l3 l4 l5 l6
  · exact s9_vnil _ ed
  · simpa using efl.symm
  · exact s9_vnil _ ea
  · exact s9_vnil _ ei
  · simpa using eout.symm
  · have hl3 := s2_items_len s0.pressed
    have := congrArg Array.size epr
    simp [actListS] at this
    omega
  · have := congrArg Array.size epo
    simp [OsuModel.Sim.poolInitial] at this
    omega
  · intro p hp x hx
    have hm : (p.val.map (fun x => Option.map (fun x => x.val) x)).reverse ∈
        (s0.pools.val.map (fun l => (l.val.map (fun x => Option.map (fun x => x.val) x)).reverse)).toArray :=
      by simpa using ⟨p, hp, rfl⟩
    rw [← epo] at hm
    simp only [Array.mem_map] at hm
    obtain ⟨n, -, hn⟩ := hm
    have hx' : Option.map (fun x => x.val) x ∈ (p.val.map (fun x => Option.map (fun x => x.val) x)).reverse := by
      simpa using ⟨x, hx, rfl⟩
    rw [← hn] at hx'
    have := List.eq_of_mem_replicate hx'
    revert this; cases x <;> simp
  · rintro ss (rfl | rfl)
    · exact s9_score _ _ _ _ esc
    · exact s9_score _ _ _ _ escr
  · rintro hh (rfl | rfl)
    · have := s9_health _ _ ehl; simpa [abs, configS] using this
    · have := s9_health _ _ ehr; simpa [abs, configS] using this
  · have := s9_netStr_size _ _ _ hSP
    simp [abs, configS] at this esp; omega
  · rw [hAd0 _ (by intro d; cases d <;> rfl)] at hAS
    have := s9_netStr_size _ _ _ hAS
    simp [abs] at this eat; omega
  · simp [abs] at ear; omega
  · have := congrArg Array.size eas; simp at this; omega
  · intro l hl
    have hm : (l.val.map (fun r => (abs r : Nat × Int))).reverse ∈
        (s0.as_seen.val.map (fun l => (l.val.map (fun r => (abs r : Nat × Int))).reverse)).toArray := by
      simpa using ⟨l, hl, rfl⟩
    rw [← eas] at hm
    simp only [Array.mem_map] at hm
    obtain ⟨n, -, hn⟩ := hm
    simpa using hn.symm
/-- the context facts `initLife` needs (all in `ev_ctxWF`) -/
structure s9Ctx (c : sim.state.Ctx) : Prop where
  h64 : System.Platform.numBits = 64
  nsum : (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < 2 ^ 62
  easy : ∀ k, sim.mods.FailOverride.Easy k ∈ c.cfg.fail_overrides.val → k.val < c.cfg.easy_retries.val.length
  acc : (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum * (1 + 2 * c.cfg.acc_challenges.val.length) ≤ U64.max
  nested_small : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32

theorem s9_obj_mem {c : sim.state.Ctx} {s0 : sim.state.St} (hI : s9I c s0) :
    ∀ o ∈ s0.objs.val, o.life = .Future ∧ o.result = none ∧ (∀ x ∈ o.nested.val, x = none) ∧
      o.completed_spins.val = 0 ∧ o.tick_insts.val = [] ∧ o.last_pressed.len.val = 0 := by
  intro o ho
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
  obtain ⟨a1, a2, -, a4, a5, a6, a7⟩ := hI.obj j hj (by rw [← hI.olen]; exact hj)
  exact ⟨a1, a2, a4, a5, a6, a7⟩

theorem s9_unjO (o : sim.state.OState) (h1 : o.result = none) (h2 : ∀ x ∈ o.nested.val, x = none) :
    simUnjO o = o.nested.val.length + 1 := by
  unfold simUnjO
  rw [h1, List.filter_eq_self.mpr (fun x hx => by rw [h2 x hx]; rfl)]
  simp; omega

theorem s9_unj {c : sim.state.Ctx} {s0 : sim.state.St} (hI : s9I c s0) :
    simUnj s0 = (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum := by
  unfold simUnj
  congr 1
  apply List.ext_getElem (by simp [hI.olen])
  intro i h1 h2
  simp only [List.getElem_map]
  have hi : i < s0.objs.val.length := by simpa using h1
  have hi' : i < c.pb.objects.val.length := by simpa using h2
  obtain ⟨-, a2, a3, a4, -⟩ := hI.obj i hi hi'
  rw [s9_unjO _ a2 a4, a3]

theorem s9_fut {c : sim.state.Ctx} {s0 : sim.state.St} (hI : s9I c s0) : simFut s0 = s0.objs.val.length := by
  unfold simFut
  rw [List.map_congr_left (g := fun _ => 1) (fun o ho => by rw [(s9_obj_mem hI o ho).1])]
  simp

theorem s9_futW {c : sim.state.Ctx} {s0 : sim.state.St} (hI : s9I c s0) :
    simFutW s0 = simUnj s0 + s0.objs.val.length := by
  unfold simFutW simUnj
  rw [List.map_congr_left (g := fun o => simUnjO o + 1) (fun o ho => by
    obtain ⟨a1, a2, a3, -⟩ := s9_obj_mem hI o ho
    rw [a1, s9_unjO o a2 a3])]
  rw [List.sum_map_add]
  simp

theorem s9_initLife (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) (hC : s9Ctx c)
    (s0 : sim.state.St) (h : sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0)) (B n CS : Nat) :
    simLifeInv tn fo s2_tfOk B n CS c s0 := by
  have hI := s9_init_facts tn c s0 h
  have hU := usize_max_64 hC.h64
  have hU64 : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)
  have hunj := s9_unj hI
  have hfut := s9_fut hI
  have hfw := s9_futW hI
  have hM := s9_obj_mem hI
  have hsum := hC.nsum
  have hsum' : (c.pb.objects.val.map (fun o => o.nested.val.length)).sum + c.pb.objects.val.length < 2 ^ 62 := by
    have := hC.nsum; rw [List.sum_map_add] at this; simpa using this
  have hacc := hC.acc
  have hlen : c.pb.objects.val.length ≤ (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum := by
    have : ∀ l : List sim.playable.TopObj, l.length ≤ (l.map (fun o => o.nested.val.length + 1)).sum := by
      intro l; induction l with
      | nil => simp
      | cons a t ih => simp; omega
    exact this _
  have hD := hI.dict
  have hA := hI.act
  have hF := hI.free
  have hIn := hI.insts
  have hsc0 := hI.sc s0.score (Or.inl rfl)
  have hsc1 := hI.sc s0.score_rp (Or.inr rfl)
  have hh0 := hI.hl s0.health (Or.inl rfl)
  have hh1 := hI.hl s0.health_rp (Or.inr rfl)
  have hinv : SimInv c s0 := by
    refine ⟨hI.olen, fun i h1 h2 => (hI.obj i h1 h2).2.2.1, fun o ho => by have := hC.nested_small o ho; omega,
      fun o ho => by rw [hD] at ho; simp at ho, by rw [hD]; simp; omega⟩
  refine ⟨⟨⟨hinv, ?tf, ?ik, ?em, ?sp, ?cnt, ?seen, ?enum⟩, ?lp, ?pl, ?pool, ?dnd, ?dal, ?ald, ?frl, ?frn, ?nfr, ?dlen,
    ?actl, ?actnd, ?actnf, ?aal, ?cc, ?ins, ?cs, ?tk, ?tkv, ?spt, ?ftr, ?fut⟩, ?aact⟩
  case tf => intro ins hins; rw [hIn] at hins; simp at hins
  case ik => intro x hx; rw [hD] at hx; simp at hx
  case em =>
    rw [hunj]
    refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hC.easy k hk; rw [hh0.2, hh1.2]; exact ⟨this, this⟩
    · rw [hh0.1, Nat.add_zero]; omega
    · rw [hh1.1, Nat.add_zero]; omega
    · obtain ⟨a, b, d, e⟩ := hsc0
      exact ⟨by omega, fun k hk => by rw [e k hk]; omega, by omega, by omega⟩
    · obtain ⟨a, b, d, e⟩ := hsc1
      exact ⟨by omega, fun k hk => by rw [e k hk]; omega, by omega, by omega⟩
    · rw [hI.out]; simp; omega
  case sp => rw [hI.sp]
  case cnt => rw [hI.atg, hI.arc, hI.asc]; exact ⟨le_rfl, le_rfl, le_rfl⟩
  case seen => intro l hl; rw [hI.asn l hl, hunj]; simp; omega
  case enum =>
    intro target v hv
    rw [simS_enumerateUpTo _ _ _ (by simp [simStS, abs, hD])] at hv
    simp only [Except.ok.injEq, Prod.mk.injEq] at hv
    rw [← hv.1]
    simp [simStS, abs, hD, simSortL, simEnumL]
    omega
  case lp =>
    refine ⟨by rw [hI.pr]; omega, fun j hj => by rw [(hM _ (List.getElem_mem hj)).2.2.2.2.2]; omega⟩
  case pl => rw [hI.pl]
  case pool => intro p hp j hj; have := hI.pn p hp _ hj; cases this
  case dnd => rw [hD]; simp
  case dal => intro x hx; rw [hD] at hx; simp at hx
  case ald => intro j hj hl; rw [(hM _ (List.getElem_mem hj)).1] at hl; cases hl
  case frl => intro x hx; rw [hF] at hx; simp at hx
  case frn => rw [hF]; simp
  case nfr => intro x hx; rw [hD] at hx; simp at hx
  case dlen => rw [hD]; simp
  case actl => intro x hx; rw [hA] at hx; simp at hx
  case actnd => rw [hA]; simp
  case actnf => intro x hx; rw [hA] at hx; simp at hx
  case aal => intro j hj hl; rw [(hM _ (List.getElem_mem hj)).1] at hl; cases hl
  case cc => rw [hI.cc, hfut]; omega
  case ins => rw [hIn, hfw, hunj, hI.olen]; simp; omega
  case cs => intro j hj; rw [(hM _ (List.getElem_mem hj)).2.2.2.1]; omega
  case tk => intro j hj; rw [(hM _ (List.getElem_mem hj)).2.2.2.2.1]; simp
  case tkv => intro j hj x hx; rw [(hM _ (List.getElem_mem hj)).2.2.2.2.1] at hx; simp at hx
  case spt => intro j hj _ hl; rw [(hM _ (List.getElem_mem hj)).1] at hl; cases hl
  case ftr => intro _ j hj; exact (hM _ (List.getElem_mem hj)).1
  case fut => intro hf; rw [hI.first] at hf; cases hf
  case aact => intro x hx; rw [hA] at hx; simp at hx
/-! ## the e2e form -/

/-- the acc-challenge budget: every unjudged slot may bump both `fail_triggers` by `1 + 2·#AC` -/
def s9AccOk (c : sim.state.Ctx) : Prop :=
  (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum * (1 + 2 * c.cfg.acc_challenges.val.length) ≤ U64.max

theorem s9_easy_rust (c : sim.mods.Config) (C : OsuModel.Sim.Config) (hc : ev_cfgRel c C) (hE : s9EasyOk C) :
    ∀ k, sim.mods.FailOverride.Easy k ∈ c.fail_overrides.val → k.val < c.easy_retries.val.length := by
  intro k hk
  have e1 := congrArg OsuModel.Sim.Config.failOverrides hc
  have e2 := congrArg (fun C => C.easyRetries.size) hc
  simp only [configS] at e1 e2
  have hm : (abs (sim.mods.FailOverride.Easy k) : OsuModel.Sim.FailOverride) ∈
      (abs c.fail_overrides : Array OsuModel.Sim.FailOverride) := by
    simp only [abs, List.mem_toArray, List.mem_map]; exact ⟨_, hk, rfl⟩
  rw [e1] at hm
  have := hE k.val hm
  simp [abs] at e2; omega

/-- D77: the acc-challenge budget on spec values (checked on the corpus with RunBudget): every judgement slot
(object + nested) may bump `fail_triggers` (a u64) by `1 + 2·#AC` -/
def s9AccBudS (C : OsuModel.Sim.Config) (P : OsuModel.Sim.Playable) : Prop :=
  (P.objects.toList.map (fun o => o.nested.size + 1)).sum * (1 + 2 * C.accChallenges.size) ≤ 2 ^ 64 - 1

theorem s9_accBud (c : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx) (hrel : ev_ctxRel c CTX)
    (hA : s9AccBudS CTX.cfg CTX.pb) : s9AccOk c := by
  have hpb : CTX.pb = playableS ev_tn c.pb := by
    have := congrArg OsuModel.Sim.Ctx.pb hrel.2; simpa [simCtxS] using this.symm
  have hac : CTX.cfg.accChallenges.size = c.cfg.acc_challenges.val.length := by
    have := congrArg (fun C => C.accChallenges.size) hrel.1; simpa [configS, abs] using this.symm
  have hU64 : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)
  unfold s9AccBudS at hA
  rw [hpb, hac] at hA
  unfold s9AccOk; rw [hU64]
  simpa [playableS, topS, List.map_map, Function.comp_def] using hA

/-- `js_EvalOpen.initLife` (sim9, D77): the initial lifetime invariant for an `ev_ctxWF` ctx related to a spec ctx
whose config has the `Config.ofMods` facts `e2CfgIdx` (as `EvalAssumptions.runWith`), given the acc-challenge budget
`s9AccBudS` on spec values -/
theorem sim.step.init_state_lifeInv (c : sim.state.Ctx) (CTX : OsuModel.Sim.Ctx) (hrel : ev_ctxRel c CTX)
    (hW : ev_ctxWF c) (hidx : e2CfgIdx CTX.cfg) (hA : s9AccBudS CTX.cfg CTX.pb) :
    ∀ s0, sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0) →
      ∀ B CS, simLifeInv ev_tn (alloc.vec.Vec.new _) s2_tfOk B (sc2N c) CS c s0 :=
  fun s0 h B CS => s9_initLife ev_tn _ c ⟨hW.h64, hW.nsum, s9_easy_rust _ _ hrel.1 hidx.2, s9_accBud c CTX hrel hA,
    hW.nested_small⟩ s0 h B _ CS

/-! ## simcore3's init-state shape facts -/

theorem s9_init_shape (tn : Nat → String) (c : sim.state.Ctx) (s0 : sim.state.St)
    (h : sim.step.init_state c.cfg c.pb c.smax.init_without_mods = ok (.Ok s0)) :
    s0.k.val = 0 ∧ s0.ap_frame.val = -1 ∧ s0.pressed.len.val = 0 ∧ s0.last_replay = none ∧
    s0.block_last.val.length = c.cfg.input_blockers.val.length ∧
    s0.block_idx.val.length = c.cfg.input_blockers.val.length ∧ (∀ x ∈ s0.block_idx.val, x.val = 0) ∧
    s0.health.nearest_index.val = 0 ∧ s0.health_rp.nearest_index.val = 0 := by
  have hpr := (s9_init_facts tn c s0 h).pr
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
  have elr := congrArg OsuModel.Sim.St.lastReplay hS
  have ebl := congrArg (fun S => S.blockLast.size) hS
  have ebi := congrArg OsuModel.Sim.St.blockIdx hS
  have eh := congrArg (fun S => S.health.nearestIndex) hS
  have ehr := congrArg (fun S => S.healthRP.nearestIndex) hS
  simp only [simStS] at ek eap elr ebl ebi eh ehr
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
  refine ⟨by omega, by omega, hpr, ?_, hbl, hbi1, hbi2, ?_, ?_⟩
  · cases e : s0.last_replay with
    | none => rfl
    | some l => rw [e] at elr; simp at elr
  · simp [abs] at eh; omega
  · simp [abs] at ehr; omega

end OsuProofs
