import OsuProofs.Sim.LifetimeBA

/-
  sim8: the lifetime chain end to end: Future->Past / Future->Alive / Alive->Past preserve the core lifetime
  invariant s8LC (s8LC_past / s8LC_alive / s8LC_dead), the active filter restores simLifeInv (s8LC_filt), and
  sim.step.lifetime_update_refines: simLifeInv b n CS in and out, plus the s8LuKeep frame and first_lifetime_update = false.
-/
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuImpl OsuModel.Net

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem s8_set_get (v : alloc.vec.Vec sim.state.OState) (j : Usize) (O : sim.state.OState) (x : Nat)
    (h : x < (v.set j O).val.length) (h' : x < v.val.length) :
    (v.set j O).val[x]'h = if j.val = x then O else v.val[x]'h' := by
  simp only [vec_set_val', List.getElem_set]

theorem s8_set_len (v : alloc.vec.Vec sim.state.OState) (j : Usize) (O : sim.state.OState) :
    (v.set j O).val.length = v.val.length := by simp [vec_set_val']

theorem s8_nodup_lt (l : List Nat) (hnd : l.Nodup) (N : Nat) (hl : ∀ x ∈ l, x < N) : l.length ≤ N := by
  have h1 : l.toFinset ⊆ Finset.range N := by intro x hx; simp at hx; simpa using hl x hx
  have := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hnd] at this; simpa using this

theorem s8_nodup_lt' (l : List Nat) (hnd : l.Nodup) (N e : Nat) (he : e < N) (hne : e ∉ l)
    (hl : ∀ x ∈ l, x < N) : l.length < N := by
  have h1 : l.toFinset ⊆ (Finset.range N).erase e := by
    intro x hx; simp at hx; simp; exact ⟨fun h => hne (h ▸ hx), hl x hx⟩
  have := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hnd, Finset.card_erase_of_mem (by simpa using he)] at this; simp at this; omega

def s8FutF (o : sim.state.OState) : Nat := match o.life with | .Future => 1 | _ => 0
def s8FutWF (o : sim.state.OState) : Nat := match o.life with | .Future => o.nested.val.length + 2 | _ => 0

theorem s8_simFut_eq (s : sim.state.St) : simFut s = (s.objs.val.map s8FutF).sum := rfl
theorem s8_simFutW_eq (s : sim.state.St) : simFutW s = (s.objs.val.map s8FutWF).sum := rfl

theorem s8_fut_set (l : List sim.state.OState) (j : Nat) (hj : j < l.length) (O : sim.state.OState)
    (hF : (l[j]'hj).life = .Future) (hO : O.life ≠ .Future) :
    ((l.set j O).map s8FutF).sum + 1 = (l.map s8FutF).sum ∧
    ((l.set j O).map s8FutWF).sum + ((l[j]'hj).nested.val.length + 2) = (l.map s8FutWF).sum := by
  have a := sim_sum_map_set s8FutF l j hj O
  have b := sim_sum_map_set s8FutWF l j hj O
  have e1 : s8FutF (l[j]'hj) = 1 := by unfold s8FutF; rw [hF]
  have e2 : s8FutWF (l[j]'hj) = (l[j]'hj).nested.val.length + 2 := by unfold s8FutWF; rw [hF]
  have e3 : s8FutF O = 0 := by unfold s8FutF; cases e : O.life <;> simp_all
  have e4 : s8FutWF O = 0 := by unfold s8FutWF; cases e : O.life <;> simp_all
  rw [e1, e3] at a; rw [e2, e4] at b
  omega

theorem s8_fut_congr (s s' : sim.state.St) (hl : s'.objs.val.length = s.objs.val.length)
    (h : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      ((s'.objs.val[j]'h').life = .Future ↔ (s.objs.val[j]'h).life = .Future) ∧
      (s'.objs.val[j]'h').nested.val.length = (s.objs.val[j]'h).nested.val.length) :
    simFut s' = simFut s ∧ simFutW s' = simFutW s := by
  refine ⟨sim_sum_map_congr _ _ _ _ hl (fun j h1 h2 => ?_), sim_sum_map_congr _ _ _ _ hl (fun j h1 h2 => ?_)⟩
  · obtain ⟨e1, -⟩ := h j h1 h2
    cases a : (s'.objs.val[j]'h2).life <;> cases b : (s.objs.val[j]'h1).life <;> simp_all
  · obtain ⟨e1, e2⟩ := h j h1 h2
    cases a : (s'.objs.val[j]'h2).life <;> cases b : (s.objs.val[j]'h1).life <;> simp_all

theorem s8_fut_le (s : sim.state.St) : simFut s ≤ s.objs.val.length := by
  unfold simFut
  have : ∀ l : List sim.state.OState, (l.map (fun o => match o.life with | .Future => 1 | _ => 0)).sum ≤ l.length := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; split <;> omega
  exact this _

/-- the maximal number of unjudged slots -/
def s8Umax (c : sim.state.Ctx) : Nat := (c.pb.objects.val.map (fun o => 1 + o.nested.val.length)).sum

theorem s8_unj_le (c : sim.state.Ctx) (s : sim.state.St) (hinv : SimInv c s) : simUnj s ≤ s8Umax c := by
  unfold simUnj s8Umax
  have key : ∀ (l : List sim.state.OState) (L : List sim.playable.TopObj), l.length = L.length →
      (∀ j (h : j < l.length) (h' : j < L.length), (l[j]'h).nested.val.length = (L[j]'h').nested.val.length) →
      (l.map simUnjO).sum ≤ (L.map (fun o => 1 + o.nested.val.length)).sum := by
    intro l; induction l with
    | nil => intro L _ _; simp
    | cons a t ih =>
      intro L hl hn
      cases L with
      | nil => simp at hl
      | cons A T =>
        simp only [List.map_cons, List.sum_cons]
        have h0 := hn 0 (by simp) (by simp); simp at h0
        have : simUnjO a ≤ 1 + A.nested.val.length := by
          unfold simUnjO; rw [← h0]
          have := List.length_filter_le (fun x => x.isNone) a.nested.val
          split <;> omega
        have := ih T (by simpa using hl) (fun j h h' => by
          have := hn (j+1) (by simp; omega) (by simp; omega); simpa using this)
        omega
  exact key _ _ hinv.objs_len (fun j h h' => hinv.nested_len j h h')

/-- `SimARInv` transfer to a state with the same judgement-side fields -/
theorem s8_ar_xfer (h64 : System.Platform.numBits = 64) (tn fo P b0 n c s) (hI : SimARInv tn fo P b0 n c s 0 0 0)
    (s' : sim.state.St) (b0' : Nat) (hinv' : SimInv c s') (hU : simUnj s' = simUnj s)
    (htf : s3b_TfInv P (b0' + simUnj s' * (n + n + 4)) s') (hik : simIK c s')
    (h1 : s'.score = s.score) (h2 : s'.health = s.health) (h3 : s'.score_rp = s.score_rp)
    (h4 : s'.health_rp = s.health_rp) (h5 : s'.out = s.out) (h6 : s'.as_target = s.as_target)
    (h7 : s'.as_recent = s.as_recent) (h8 : s'.as_seen = s.as_seen) (h9 : s'.speed = s.speed)
    (hND : ((s'.dict_slots.val.filterMap id).map (·.val)).Nodup)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32) :
    SimARInv tn fo P b0' n c s' 0 0 0 := by
  obtain ⟨hinv, htf0, hik0, hem, hsp, hcnt, hseen, henum⟩ := hI
  refine ⟨hinv', by simpa using htf, hik, ?_, by rw [h9]; exact hsp, by rw [h6, h7, h8]; exact hcnt,
    by rw [h8, hU]; exact hseen, s8_enum h64 tn fo c s' hinv' hND hos hns⟩
  rw [hU]; exact sim_emitBud_congr c s s' _ h1 h2 h3 h4 h5 hem

theorem s8_instOk_obj {c : sim.state.Ctx} {s s' : sim.state.St} {x : Nat} (h : simInstOk c s x)
    (hx' : x < s'.objs.val.length) (he : ∀ hx : x < s.objs.val.length, s'.objs.val[x]'hx' = s.objs.val[x]'hx)
    (hl : s.insts.val.length ≤ s'.insts.val.length) : simInstOk c s' x := by
  obtain ⟨hx, a, b, d, e⟩ := h
  have := he hx
  refine ⟨hx', ?_, ?_, ?_, ?_⟩ <;> rw [this]
  · omega
  · omega
  · intro j hj; have := d j hj; omega
  · exact e


theorem s8_unj_set_eq (s : sim.state.St) (j : Usize) (hj : j.val < s.objs.val.length) (O : sim.state.OState)
    (hr : O.result = (s.objs.val[j.val]'hj).result) (hn : O.nested = (s.objs.val[j.val]'hj).nested) (s' : sim.state.St)
    (hs' : s'.objs = s.objs.set j O) : simUnj s' = simUnj s := by
  have a := sim_sum_map_set simUnjO s.objs.val j.val hj O
  have e : simUnjO O = simUnjO (s.objs.val[j.val]'hj) := by unfold simUnjO; rw [hr, hn]
  unfold simUnj; rw [hs', vec_set_val']; omega

/-- Future -> Past without becoming alive (first scan / later scan, object `j`) -/
theorem s8LC_past (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n CS : Nat) (c : sim.state.Ctx)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (s : sim.state.St) (hL : s8LC tn fo P b n CS c s) (j : Usize) (hj : j.val < s.objs.val.length)
    (hF : (s.objs.val[j.val]'hj).life = .Future) (nf : Usize) (hfirst : s.first_lifetime_update = false)
    (hfut : simFutOK { s with objs := s.objs.set j { (s.objs.val[j.val]'hj) with life := .Past }, next_future := nf }) :
    s8LC tn fo P b n CS c { s with objs := s.objs.set j { (s.objs.val[j.val]'hj) with life := .Past }, next_future := nf } := by
  set O : sim.state.OState := { (s.objs.val[j.val]'hj) with life := .Past } with hO
  set s' : sim.state.St := { s with objs := s.objs.set j O, next_future := nf } with hs'
  have hl' : s'.objs.val.length = s.objs.val.length := s8_set_len _ _ _
  have hg : ∀ x (h' : x < s'.objs.val.length) (h : x < s.objs.val.length), j.val ≠ x → s'.objs.val[x]'h' = s.objs.val[x]'h := by
    intro x h' h hne; show (s.objs.set j O).val[x]'h' = _; rw [s8_set_get _ _ _ _ h' h, if_neg hne]
  have hgj : ∀ h' : j.val < s'.objs.val.length, s'.objs.val[j.val]'h' = O := by
    intro h'; show (s.objs.set j O).val[j.val]'h' = _; rw [s8_set_get _ _ _ _ h' hj, if_pos rfl]
  have hne : ∀ x (h : x < s.objs.val.length), (s.objs.val[x]'h).life ≠ .Future → j.val ≠ x := by
    intro x h hx e; subst e; exact hx hF
  have hFS := s8_fut_set s.objs.val j.val hj O hF (by rw [hO]; simp)
  have hF1 : simFut s' + 1 = simFut s := by
    rw [s8_simFut_eq, s8_simFut_eq]; show ((s.objs.set j O).val.map s8FutF).sum + 1 = _; rw [vec_set_val']; exact hFS.1
  have hF2 : simFutW s' + ((s.objs.val[j.val]'hj).nested.val.length + 2) = simFutW s := by
    rw [s8_simFutW_eq, s8_simFutW_eq]; show ((s.objs.set j O).val.map s8FutWF).sum + _ = _; rw [vec_set_val']; exact hFS.2
  have hU : simUnj s' = simUnj s := s8_unj_set_eq s j hj O rfl rfl s' rfl
  have hinv0 := sim_inv_objs_set hL.ar.inv O hj rfl
  have hinv' : SimInv c s' := ⟨hinv0.objs_len, hinv0.nested_len, hinv0.nested_small, hinv0.dict_in, hinv0.dict_small⟩
  refine ⟨?ar, ?lp, hL.pl, hL.pool, hL.dnd, ?dal, ?ald, hL.frl, hL.frn, hL.nfr, by rw [hl']; exact hL.dlen,
    fun x hx => by rw [hl']; exact hL.actl x hx, hL.actnd, ?actnf, ?aal, ?cc, ?ins, ?cs, ?tk, ?tkv, ?spt,
    fun h => by simp [s', hfirst] at h, fun _ => hfut⟩
  case ar =>
    refine s8_ar_xfer h64 tn fo P _ n c s hL.ar s' _ hinv' hU ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl hL.dnd hos hns
    · have := hL.ar.tf
      have h2 := Nat.mul_le_mul_right (4 * n + 8) (show simFut s' ≤ simFut s by omega)
      exact sim_tf_mono E this (by simp only [Nat.add_zero]; rw [hU]; omega)
    · intro x hx
      obtain ⟨hx0, hal⟩ := hL.dal x hx
      exact s8_instOk_obj (hL.ar.ik x hx) (by rw [hl']; exact hx0) (fun h => hg _ _ h (hne _ h (by rw [hal]; simp))) le_rfl
  case lp =>
    refine ⟨hL.lp.1, fun x hx => ?_⟩
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj]; exact hL.lp.2 _ hj
    · rw [hg x hx hx0 e]; exact hL.lp.2 _ hx0
  case dal =>
    intro x hx
    obtain ⟨hx0, hal⟩ := hL.dal x hx
    exact ⟨by rw [hl']; exact hx0, by rw [hg _ _ hx0 (hne _ hx0 (by rw [hal]; simp))]; exact hal⟩
  case ald =>
    intro x hx hal
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj] at hal; simp [hO] at hal
    · rw [hg x hx hx0 e] at hal; exact hL.ald x hx0 hal
  case actnf =>
    intro x hx h
    have hx0 : x.val < s.objs.val.length := hL.actl x hx
    rw [hg _ h hx0 (hne _ hx0 (hL.actnf x hx hx0))]; exact hL.actnf x hx hx0
  case aal =>
    intro x hx hal
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj] at hal; simp [hO] at hal
    · rw [hg x hx hx0 e] at hal; exact hL.aal x hx0 hal
  case cc => have := hL.cc; show s.child_counter.val + simFut s' ≤ s'.objs.val.length; rw [hl']; omega
  case ins => have := hL.ins; show s.insts.val.length + simFutW s' < _; omega
  case cs =>
    intro x hx
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj]; exact hL.cs _ hj
    · rw [hg x hx hx0 e]; exact hL.cs _ hx0
  case tk =>
    intro x hx
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj]; exact hL.tk _ hj
    · rw [hg x hx hx0 e]; exact hL.tk _ hx0
  case tkv =>
    intro x hx
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj]; exact hL.tkv _ hj
    · rw [hg x hx hx0 e]; exact hL.tkv _ hx0
  case spt =>
    intro x hx hxc hal
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : j.val = x
    · subst e; rw [hgj] at hal; simp [hO] at hal
    · rw [hg x hx hx0 e] at hal ⊢; exact hL.spt x hx0 hxc hal


theorem s8_fm_set (i : Usize) : ∀ (l : List (Option Usize)) (x : Nat) (hx : x < l.length), l[x]'hx = none →
    ((l.set x (some i)).filterMap id).Perm (i :: l.filterMap id) := by
  intro l; induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx hn
    cases x with
    | zero => simp at hn; subst hn; simp
    | succ x =>
      simp only [List.set_cons_succ]
      have := ih x (by simpa using hx) (by simpa using hn)
      cases a with
      | none => simpa using this
      | some y =>
        simp only [List.filterMap_cons, id]
        exact (this.cons y).trans (List.Perm.swap i y _)

theorem s8_fm_len : ∀ (l : List (Option Usize)), (∀ a ∈ l, a ≠ none) → (l.filterMap id).length = l.length := by
  intro l; induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    cases a with
    | none => exact absurd rfl (h none (by simp))
    | some y =>
      show (y :: t.filterMap id).length = (some y :: t).length
      simp only [List.length_cons]; rw [ih (fun b hb => h b (by simp [hb]))]

theorem s8_mem_fm (l : List (Option Usize)) (x : Usize) : some x ∈ l ↔ x ∈ l.filterMap id := by
  simp [List.mem_filterMap]

/-- consequences of became_alive's dictionary / free-list step -/
theorem s8_ds_facts (s : sim.state.St) (i : Usize) (v1 : alloc.vec.Vec (Option Usize)) (FL : alloc.vec.Vec Usize)
    (hDS : s8DS s i v1 FL)
    (frl : ∀ x ∈ s.free_list.val, ∃ h : x.val < s.dict_slots.val.length, s.dict_slots.val[x.val]'h = none)
    (frn : s.free_list.val.Nodup)
    (nfr : ∀ x (h : x < s.dict_slots.val.length), s.dict_slots.val[x]'h = none → ∃ y ∈ s.free_list.val, y.val = x) :
    (v1.val.filterMap id).Perm (i :: s.dict_slots.val.filterMap id) ∧ FL.val.Nodup ∧
    (∀ y ∈ FL.val, ∃ h : y.val < v1.val.length, v1.val[y.val]'h = none) ∧
    (∀ y (h : y < v1.val.length), v1.val[y]'h = none → ∃ z ∈ FL.val, z.val = y) ∧
    (v1.val.length = s.dict_slots.val.length ∨
      (v1.val.length = s.dict_slots.val.length + 1 ∧ ∀ a ∈ s.dict_slots.val, a ≠ none)) := by
  obtain ⟨hnil, hcons⟩ := hDS
  rcases hfl : s.free_list.val.reverse with _ | ⟨x0, Lr⟩
  · have hf : s.free_list.val = [] := by simpa using hfl
    obtain ⟨hv, hF⟩ := hnil hf
    have hall : ∀ a ∈ s.dict_slots.val, a ≠ none := by
      intro a ha e; subst e
      obtain ⟨y, hy, hyv⟩ := List.getElem_of_mem ha
      obtain ⟨z, hz, -⟩ := nfr y hy hyv
      rw [hf] at hz; simp at hz
    refine ⟨?_, by rw [hF]; simp, by rw [hF]; simp, ?_, Or.inr ⟨by rw [hv]; simp, hall⟩⟩
    · rw [hv]; simpa using List.perm_append_singleton i (s.dict_slots.val.filterMap id)
    · intro y hy hn
      exfalso
      have hn2 : (s.dict_slots.val ++ [some i])[y]? = some none := by rw [← hv, List.getElem?_eq_getElem hy, hn]
      have hy2 : y < s.dict_slots.val.length + 1 := by have := hy; rw [hv] at this; simpa using this
      by_cases hyl : y < s.dict_slots.val.length
      · rw [List.getElem?_append_left hyl, List.getElem?_eq_getElem hyl] at hn2
        simp only [Option.some.injEq] at hn2
        exact hall _ (List.getElem_mem hyl) hn2
      · rw [List.getElem?_append_right (by omega)] at hn2
        have : y - s.dict_slots.val.length = 0 := by omega
        rw [this] at hn2; simp at hn2
  · have hf : s.free_list.val = Lr.reverse ++ [x0] := by
      have := congrArg List.reverse hfl; simpa using this
    obtain ⟨hx, hv, hF⟩ := hcons _ _ hf
    have hx0 := frl x0 (by rw [hf]; simp)
    obtain ⟨hx0', hxn⟩ := hx0
    have hnd := frn; rw [hf] at hnd
    have hnx : x0 ∉ Lr.reverse := by
      intro h; have := List.nodup_append.1 hnd; exact this.2.2 x0 h x0 (by simp) rfl
    have hvv : v1.val = s.dict_slots.val.set x0.val (some i) := by rw [hv, vec_set_val']
    refine ⟨by rw [hvv]; exact s8_fm_set i _ _ hx hxn, by rw [hF]; exact (List.nodup_append.1 hnd).1, ?_, ?_,
      Or.inl (by rw [hvv]; simp)⟩
    · intro y hy
      rw [hF] at hy
      obtain ⟨hy0, hyn⟩ := frl y (by rw [hf]; simp [hy])
      have hne : x0.val ≠ y.val := by
        intro e; apply hnx; have : x0 = y := UScalar.eq_of_val_eq e
        rw [this]; exact hy
      refine ⟨by rw [hvv]; simpa using hy0, ?_⟩
      simp only [hvv]; rw [List.getElem_set_ne hne]; exact hyn
    · intro y hy hn
      have hyl : y < s.dict_slots.val.length := by rw [hvv] at hy; simpa using hy
      by_cases e : x0.val = y
      · subst e; simp [hvv] at hn
      · simp only [hvv] at hn; rw [List.getElem_set_ne e] at hn
        obtain ⟨z, hz, hzv⟩ := nfr y hyl hn
        rw [hf] at hz
        rcases List.mem_append.1 hz with hz | hz
        · rw [hF]; exact ⟨z, hz, hzv⟩
        · simp at hz; subst hz; exact absurd hzv e


theorem s8_getElem_congr {α} (l : List α) (a b : Nat) (ha : a < l.length) (hb : b < l.length) (e : a = b) :
    l[a]'ha = l[b]'hb := by subst e; rfl

/-- every spinner-tick reference belongs to a spinner (context property) -/
def s8TKCtx (c : sim.state.Ctx) : Prop :=
  ∀ r, simRefOk c r → ((simHobj c r).kind = .SpinnerTick ∨ (simHobj c r).kind = .SpinnerBonusTick) →
    ∀ j (hj : j < c.pb.objects.val.length), r.top.val = j → (c.pb.objects.val[j]'hj).h.kind = .Spinner

/-- Future -> Alive via `became_alive` (object `i`), from its frame -/
theorem s8LC_alive (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b n CS : Nat) (c : sim.state.Ctx)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (hC : SimARCtx c) (hTK : s8TKCtx c)
    (s : sim.state.St) (hL : s8LC tn fo P b n CS c s) (i : Usize) (hi : i.val < c.pb.objects.val.length)
    (ho : i.val < s.objs.val.length) (hF : (s.objs.val[i.val]'ho).life = .Future)
    (hfirst : s.first_lifetime_update = false)
    (s' : sim.state.St) (hinv' : SimInv c s')
    (htf' : s3b_TfInv P (b + (simFut s - 1) * (4 * n + 8) + simUnj s * (n + n + 4)) s')
    (k : Usize) (v1 : alloc.vec.Vec (Option Usize)) (FL v2 : alloc.vec.Vec Usize) (cid : U64)
    (hDS : s8DS s i v1 FL) (hv2 : v2.val = s.active.val ++ [i]) (hcid : cid.val = s.child_counter.val + 1)
    (T TL : Nat) (hTs : (c.pb.objects.val[i.val]'hi).h.kind = .Spinner →
      T = (c.pb.objects.val[i.val]'hi).nested.val.length ∧ TL = (c.pb.objects.val[i.val]'hi).nested.val.length)
    (hR : s8R i (s8K (s.objs.val[i.val]'ho) cid k) (c.pb.objects.val[i.val]'hi).nested.val.length
      ((c.pb.objects.val[i.val]'hi).nested.val.length + 2) T TL
      { s with active := v2, dict_slots := v1, free_list := FL, child_counter := cid } s')
    (hfut : s'.first_lifetime_update = false → simFutOK s') :
    s8LC tn fo P b n CS c s' := by
  obtain ⟨⟨ins, pl, th, O, hs'⟩, hkey, hdv, htkl, htkv, hil, hiu, hpl, hP, hin, hT, hTL⟩ := hR
  have hso : s'.objs = s.objs.set i O := by rw [hs']
  subst hs'
  have hN : (s.objs.val[i.val]'ho).nested.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length :=
    hL.ar.inv.nested_len _ ho hi
  have hl' : (s.objs.set i O).val.length = s.objs.val.length := s8_set_len _ _ _
  have ho' : i.val < (s.objs.set i O).val.length := by rw [hl']; exact ho
  have hgi : (s.objs.set i O).val[i.val]'ho' = O := by rw [s8_set_get _ _ _ _ ho' ho, if_pos rfl]
  have hg : ∀ x (h' : x < (s.objs.set i O).val.length) (h : x < s.objs.val.length), i.val ≠ x →
      (s.objs.set i O).val[x]'h' = s.objs.val[x]'h := by
    intro x h' h hne; rw [s8_set_get _ _ _ _ h' h, if_neg hne]
  have hne : ∀ x (h : x < s.objs.val.length), (s.objs.val[x]'h).life ≠ .Future → i.val ≠ x := by
    intro x h hx e; subst e; exact hx hF
  have hk := hkey ho'; rw [hgi] at hk
  simp only [s8BAKey, s8K, Prod.mk.injEq] at hk
  obtain ⟨kl, kc, kcs, klp, kr, kn, kls, ki⟩ := hk
  have hdv' := hdv ho'; rw [hgi] at hdv'
  have hin' := hin ho'; rw [hgi] at hin'
  have hT' := hT ho'; rw [hgi] at hT'
  have hTL' := hTL ho'; rw [hgi] at hTL'
  have htkl' := htkl (fun h => by have := hL.tk _ h; rw [hN] at this; exact this) ho'; rw [hgi] at htkl'
  have htkv' := htkv (fun h x hx => hL.tkv _ h x hx) ho'; rw [hgi] at htkv'
  change s.insts.val.length ≤ ins.val.length at hil
  change ins.val.length ≤ s.insts.val.length + _ at hiu
  have hFS := s8_fut_set s.objs.val i.val ho O hF (by rw [kl]; simp)
  have hF1 : ∀ S : sim.state.St, S.objs = s.objs.set i O → simFut S + 1 = simFut s := by
    intro S hS; rw [s8_simFut_eq, s8_simFut_eq, hS, vec_set_val']; exact hFS.1
  have hF2 : ∀ S : sim.state.St, S.objs = s.objs.set i O → simFutW S + ((s.objs.val[i.val]'ho).nested.val.length + 2) = simFutW s := by
    intro S hS; rw [s8_simFutW_eq, s8_simFutW_eq, hS, vec_set_val']; exact hFS.2
  have hU : ∀ S : sim.state.St, S.objs = s.objs.set i O → simUnj S = simUnj s := fun S hS => s8_unj_set_eq s i ho O kr kn S hS
  have hni : some i ∉ s.dict_slots.val := by
    intro h; obtain ⟨hx, hal⟩ := hL.dal i h; rw [hal] at hF; cases hF
  have hnia : i ∉ s.active.val := by
    intro h; exact hL.actnf i h ho hF
  obtain ⟨hperm, hFLnd, hFLfree, hnfr', hlen'⟩ := s8_ds_facts s i v1 FL hDS hL.frl hL.frn hL.nfr
  have hmem : ∀ x, some x ∈ v1.val ↔ x = i ∨ some x ∈ s.dict_slots.val := by
    intro x; rw [s8_mem_fm, hperm.mem_iff, s8_mem_fm]; simp
  have hND' : ((v1.val.filterMap id).map (·.val)).Nodup := by
    refine (hperm.map _).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, hL.dnd⟩
    obtain ⟨x, hx, hxv⟩ := List.mem_map.1 h
    have : x = i := UScalar.eq_of_val_eq hxv
    subst this; exact hni ((s8_mem_fm _ _).2 hx)
  refine ⟨?ar, ?lp, by show 6 ≤ pl.val.length; rw [hpl]; exact hL.pl, hP, hND', ?dal, ?ald, hFLfree, hFLnd, hnfr',
    ?dlen, ?actl, ?actnd, ?actnf, ?aal, ?cc, ?ins, ?cs, ?tk, ?tkv, ?spt,
    fun h => by simp [hfirst] at h, hfut⟩
  case ar =>
    refine s8_ar_xfer h64 tn fo P _ n c s hL.ar _ _ hinv' (hU _ hso) ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl hND' hos hns
    · refine sim_tf_mono E htf' ?_
      rw [hU _ hso, Nat.eq_sub_of_add_eq (hF1 _ hso)]
    · intro x hx
      rcases (hmem x).1 hx with e | hx
      · rw [e]
        refine ⟨ho', ?_, ?_, ?_, ?_⟩ <;> rw [hgi]
        · exact hin'
        · exact hdv'
        · intro j hj; exact htkv' _ (List.getElem_mem hj)
        · intro r hr hrt hk
          have hsp := hTK r hr hk i.val hi hrt
          obtain ⟨hT0, -⟩ := hTs hsp
          rw [hT', hT0]
          obtain ⟨htop, hn⟩ := hr
          have e2 := s8_getElem_congr c.pb.objects.val _ _ htop hi hrt
          rw [e2] at hn; exact hn (hC.tkn r ⟨htop, fun h => by rw [e2]; exact hn h⟩ hk)
      · obtain ⟨hx0, hal⟩ := hL.dal x hx
        exact s8_instOk_obj (hL.ar.ik x hx) (by rw [hl']; exact hx0)
          (fun h => hg _ _ h (hne _ h (by rw [hal]; simp))) hil
  case lp =>
    refine ⟨hL.lp.1, fun x hx => ?_⟩
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : i.val = x
    · subst e; show ((s.objs.set i O).val[i.val]'hx).last_pressed.len.val ≤ 3; rw [hgi, klp]; simp [replay.frames.ACTLIST_EMPTY]
    · show ((s.objs.set i O).val[x]'hx).last_pressed.len.val ≤ 3; rw [hg x hx hx0 e]; exact hL.lp.2 _ hx0
  case dal =>
    intro x hx
    rcases (hmem x).1 hx with e | hx
    · subst e; exact ⟨ho', by show ((s.objs.set x O).val[x.val]'ho').life = _; rw [hgi, kl]⟩
    · obtain ⟨hx0, hal⟩ := hL.dal x hx
      exact ⟨by rw [hl']; exact hx0, by
        show ((s.objs.set i O).val[x.val]'(by rw [hl']; exact hx0)).life = _
        rw [hg _ _ hx0 (hne _ hx0 (by rw [hal]; simp))]; exact hal⟩
  case ald =>
    intro x hx hal
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    by_cases e : i.val = x
    · exact ⟨i, (hmem i).2 (Or.inl rfl), e⟩
    · change ((s.objs.set i O).val[x]'hx).life = _ at hal
      rw [hg x hx hx0 e] at hal
      obtain ⟨y, hy, hyv⟩ := hL.ald x hx0 hal
      exact ⟨y, (hmem y).2 (Or.inr hy), hyv⟩
  case dlen =>
    show v1.val.length ≤ (s.objs.set i O).val.length
    rw [hl']
    rcases hlen' with e | ⟨e, hall⟩
    · rw [e]; exact hL.dlen
    · rw [e]
      have h1 := s8_fm_len _ hall
      have h2 := s8_nodup_lt' ((s.dict_slots.val.filterMap id).map (·.val)) hL.dnd s.objs.val.length i.val ho
        (by intro h; obtain ⟨x, hx, hxv⟩ := List.mem_map.1 h
            have : x = i := UScalar.eq_of_val_eq hxv
            subst this; exact hni ((s8_mem_fm _ _).2 hx))
        (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
            exact (hL.dal y ((s8_mem_fm _ _).2 hy)).1)
      simp only [List.length_map] at h2; omega
  case actl =>
    intro x hx
    show x.val < (s.objs.set i O).val.length; rw [hl']
    change x ∈ v2.val at hx; rw [hv2] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.actl x hx
    · simp at hx; subst hx; exact ho
  case actnd =>
    show v2.val.Nodup; rw [hv2]
    exact List.nodup_append.2 ⟨hL.actnd, List.nodup_singleton i, by
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hnia ha⟩
  case actnf =>
    intro x hx h
    change x ∈ v2.val at hx; rw [hv2] at hx
    show ((s.objs.set i O).val[x.val]'h).life ≠ _
    rcases List.mem_append.1 hx with hx | hx
    · have hx0 := hL.actl x hx
      rw [hg _ h hx0 (hne _ hx0 (hL.actnf x hx hx0))]; exact hL.actnf x hx hx0
    · simp at hx; subst hx; rw [hgi, kl]; simp
  case aal =>
    intro x hx hal
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    show ∃ y ∈ v2.val, y.val = x
    rw [hv2]
    by_cases e : i.val = x
    · exact ⟨i, by simp, e⟩
    · change ((s.objs.set i O).val[x]'hx).life = _ at hal
      rw [hg x hx hx0 e] at hal
      obtain ⟨y, hy, hyv⟩ := hL.aal x hx0 hal
      exact ⟨y, List.mem_append_left _ hy, hyv⟩
  case cc =>
    have := hL.cc; have := hF1 _ hso
    show cid.val + _ ≤ (s.objs.set i O).val.length; rw [hl', hcid]; omega
  case ins =>
    have := hL.ins; have := hF2 _ hso
    show ins.val.length + _ < _; rw [← hN] at hiu; omega
  case cs =>
    intro x hx
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    show ((s.objs.set i O).val[x]'hx).completed_spins.val ≤ CS
    by_cases e : i.val = x
    · subst e; rw [hgi, kcs]; simp
    · rw [hg x hx hx0 e]; exact hL.cs _ hx0
  case tk =>
    intro x hx
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    show ((s.objs.set i O).val[x]'hx).tick_insts.val.length ≤ ((s.objs.set i O).val[x]'hx).nested.val.length
    by_cases e : i.val = x
    · subst e; rw [hgi, kn, hN]; exact htkl'
    · rw [hg x hx hx0 e]; exact hL.tk _ hx0
  case tkv =>
    intro x hx
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    show ∀ y ∈ ((s.objs.set i O).val[x]'hx).tick_insts.val, y.val < ins.val.length
    by_cases e : i.val = x
    · subst e; rw [hgi]; exact htkv'
    · rw [hg x hx hx0 e]; intro y hy; have := hL.tkv _ hx0 y hy; omega
  case spt =>
    intro x hx hxc hal hsp
    have hx0 : x < s.objs.val.length := by rw [← hl']; exact hx
    change ((s.objs.set i O).val[x]'hx).life = _ at hal
    show ((s.objs.set i O).val[x]'hx).tick_live.val.length = _ ∧ ((s.objs.set i O).val[x]'hx).tick_insts.val.length = _
    by_cases e : i.val = x
    · subst e; rw [hgi]; obtain ⟨a, b⟩ := hTs hsp; exact ⟨by rw [hTL', b], by rw [hT', a]⟩
    · rw [hg x hx hx0 e] at hal ⊢; exact hL.spt x hx0 hxc hal hsp


theorem s8_getElem_eq {α} (l l' : List α) (e : l' = l) (k : Nat) (hk : k < l'.length) (hk' : k < l.length) :
    l'[k]'hk = l[k]'hk' := by subst e; rfl

theorem s8_dfr_j {i : Usize} {s s' : sim.state.St} (hD : s8DFr i s s') (j : Nat) (h : j < s.objs.val.length)
    (h' : j < s'.objs.val.length) (hj : j ≠ i.val) :
    (s'.objs.val[j]'h').life = (s.objs.val[j]'h).life ∧ (s'.objs.val[j]'h').tick_insts = (s.objs.val[j]'h).tick_insts ∧
    (s'.objs.val[j]'h').tick_live = (s.objs.val[j]'h).tick_live ∧
    (s'.objs.val[j]'h').completed_spins = (s.objs.val[j]'h).completed_spins := by
  have e := hD.ow j h h' hj
  simp only [simKeepJ, Prod.mk.injEq] at e
  obtain ⟨a1, -, -, -, -, -, -, -, a9, a10, -, -, -, -, -, -, -, a18, -, -⟩ := e
  exact ⟨a1, a9, a10, a18⟩

/-- Alive -> Past via `became_dead` (object `i`), from its frame -/
theorem s8LC_dead (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (b n CS : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (hL : s8LC tn fo P b n CS c s) (i : Usize) (s' : sim.state.St)
    (hI' : SimARInv tn fo P (b + simFut s * (4 * n + 8)) n c s' 0 0 0) (hLP' : simLP s')
    (hP' : simPoolOk s') (hD : s8DFr i s s') : s8LC tn fo P b n CS c s' := by
  obtain ⟨kt, kf, knf, kfo, kac, kcc, kpr, kpl, kil⟩ := hD.keep
  obtain ⟨slot, hsl, hsv, hds', hfl'⟩ := hD.dict
  have hl := hD.len
  have hinv := hL.ar.inv
  have hinv' := hI'.inv
  obtain ⟨hio, hal⟩ := hL.dal i (by rw [← hsv]; exact List.getElem_mem hsl)
  have hio' : i.val < s'.objs.val.length := by rw [hl]; exact hio
  have hiP := (hD.oi hio hio').1
  have hg := fun j h h' hj => s8_dfr_j hD j h h' hj
  have hne' : ∀ j (h' : j < s'.objs.val.length), (s'.objs.val[j]'h').life ≠ .Past → j ≠ i.val := by
    intro j h hx e; subst e; exact hx hiP
  have hN : ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length),
      (s'.objs.val[j]'h').nested.val.length = (s.objs.val[j]'h).nested.val.length := by
    intro j h h'
    rw [hinv'.nested_len j h' (by rw [← hinv.objs_len]; exact h), hinv.nested_len j h]
  have hFC : simFut s' = simFut s ∧ simFutW s' = simFutW s := by
    refine s8_fut_congr s s' hl (fun j h h' => ⟨?_, hN j h h'⟩)
    by_cases e : j = i.val
    · subst e; rw [hiP, hal]; simp
    · rw [(hg j h h' e).1]
  have hdv : s'.dict_slots.val = s.dict_slots.val.set slot.val none := by rw [hds', vec_set_val']
  have hdl : s'.dict_slots.val.length = s.dict_slots.val.length := by rw [hdv]; simp
  have hperm : (s.dict_slots.val.filterMap id).Perm (i :: s'.dict_slots.val.filterMap id) := by
    have h1 := s8_fm_set i (s.dict_slots.val.set slot.val none) slot.val (by simpa using hsl) (by simp)
    have e : (s.dict_slots.val.set slot.val none).set slot.val (some i) = s.dict_slots.val := by
      rw [List.set_set, ← hsv, List.set_getElem_self]
    rw [e, ← hdv] at h1; exact h1
  have hND2 := (hperm.map (·.val)).nodup_iff.1 hL.dnd
  simp only [List.map_cons, List.nodup_cons] at hND2
  obtain ⟨hiN, hND'⟩ := hND2
  have hmem : ∀ x, some x ∈ s.dict_slots.val ↔ x = i ∨ some x ∈ s'.dict_slots.val := by
    intro x; rw [s8_mem_fm, hperm.mem_iff, s8_mem_fm]; simp
  have hxi : ∀ x, some x ∈ s'.dict_slots.val → x.val ≠ i.val := by
    intro x hx e
    have : x = i := UScalar.eq_of_val_eq e
    subst this; exact hiN (List.mem_map.2 ⟨x, (s8_mem_fm _ _).1 hx, rfl⟩)
  refine ⟨by rw [hFC.1]; exact hI', hLP', by rw [kpl]; exact hL.pl, hP', hND', ?dal, ?ald, ?frl, ?frn, ?nfr,
    ?dlen, ?actl, ?actnd, ?actnf, ?aal, ?cc, ?ins, ?cs, ?tk, ?tkv, ?spt, ?ftr, ?fut⟩
  case dal =>
    intro x hx
    obtain ⟨h0, ha⟩ := hL.dal x ((hmem x).2 (Or.inr hx))
    exact ⟨by rw [hl]; exact h0, by rw [(hg _ h0 _ (hxi x hx)).1]; exact ha⟩
  case ald =>
    intro j h hA
    have h0 : j < s.objs.val.length := by rw [← hl]; exact h
    have hj := hne' j h (by rw [hA]; simp)
    rw [(hg j h0 h hj).1] at hA
    obtain ⟨x, hx, hxv⟩ := hL.ald j h0 hA
    rcases (hmem x).1 hx with e | hx'
    · subst e; exact absurd hxv.symm hj
    · exact ⟨x, hx', hxv⟩
  case frl =>
    intro x hx
    rw [hfl'] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨h0, hn⟩ := hL.frl x hx
      have hne : slot.val ≠ x.val := by
        intro e; rw [s8_getElem_congr _ _ _ hsl h0 e] at hsv; rw [hsv] at hn; cases hn
      refine ⟨by rw [hdl]; exact h0, ?_⟩
      simp only [hdv]; rw [List.getElem_set_ne hne]; exact hn
    · simp at hx; subst hx; exact ⟨by rw [hdl]; exact hsl, by simp [hdv]⟩
  case frn =>
    rw [hfl']
    refine List.nodup_append.2 ⟨hL.frn, List.nodup_singleton _, ?_⟩
    intro a ha b hb e
    simp at hb; subst hb; subst e
    obtain ⟨h0, hn⟩ := hL.frl a ha
    rw [hsv] at hn; cases hn
  case nfr =>
    intro x h hn
    have h0 : x < s.dict_slots.val.length := by rw [← hdl]; exact h
    by_cases e : slot.val = x
    · exact ⟨slot, by rw [hfl']; simp, e⟩
    · simp only [hdv] at hn; rw [List.getElem_set_ne e] at hn
      obtain ⟨y, hy, hyv⟩ := hL.nfr x h0 hn
      exact ⟨y, by rw [hfl']; exact List.mem_append_left _ hy, hyv⟩
  case dlen => rw [hdl, hl]; exact hL.dlen
  case actl => intro x hx; rw [kac] at hx; rw [hl]; exact hL.actl x hx
  case actnd => rw [kac]; exact hL.actnd
  case actnf =>
    intro x hx h
    rw [kac] at hx
    have h0 := hL.actl x hx
    by_cases e : x.val = i.val
    · have : (s'.objs.val[x.val]'h).life = .Past := by rw [s8_getElem_congr _ _ _ h hio' e]; exact hiP
      rw [this]; simp
    · rw [(hg _ h0 h e).1]; exact hL.actnf x hx h0
  case aal =>
    intro j h hA
    have h0 : j < s.objs.val.length := by rw [← hl]; exact h
    have hj := hne' j h (by rw [hA]; simp)
    rw [(hg j h0 h hj).1] at hA
    obtain ⟨x, hx, hxv⟩ := hL.aal j h0 hA
    exact ⟨x, by rw [kac]; exact hx, hxv⟩
  case cc => rw [kcc, hFC.1, hl]; exact hL.cc
  case ins => rw [kil, hFC.2]; exact hL.ins
  case cs =>
    intro j h
    have h0 : j < s.objs.val.length := by rw [← hl]; exact h
    by_cases e : j = i.val
    · subst e; rw [(hD.oi h0 h).2.2.2.1]; exact hL.cs _ h0
    · rw [(hg j h0 h e).2.2.2]; exact hL.cs j h0
  case tk =>
    intro j h
    have h0 : j < s.objs.val.length := by rw [← hl]; exact h
    rw [hN j h0 h]
    by_cases e : j = i.val
    · subst e; rw [(hD.oi h0 h).2.2.1]; exact hL.tk _ h0
    · rw [(hg j h0 h e).2.1]; exact hL.tk j h0
  case tkv =>
    intro j h x hx
    have h0 : j < s.objs.val.length := by rw [← hl]; exact h
    rw [kil]
    by_cases e : j = i.val
    · subst e; rw [(hD.oi h0 h).2.2.1] at hx; exact hL.tkv _ h0 x hx
    · rw [(hg j h0 h e).2.1] at hx; exact hL.tkv j h0 x hx
  case spt =>
    intro j h hj hA hsp
    have h0 : j < s.objs.val.length := by rw [← hl]; exact h
    have hje := hne' j h (by rw [hA]; simp)
    obtain ⟨a1, a9, a10, -⟩ := hg j h0 h hje
    rw [a1] at hA; rw [a9, a10]; exact hL.spt j h0 hj hA hsp
  case ftr =>
    intro hf j h
    rw [kf] at hf
    have := hL.ftr hf i.val hio
    rw [hal] at this; cases this
  case fut =>
    intro hf
    rw [kf] at hf
    obtain ⟨f1, f2, f3⟩ := hL.fut hf
    refine ⟨fun x hx => ?_, fun k hk hnf h => ?_, by rw [kfo, knf]; exact f3⟩
    · rw [kfo] at hx; rw [hl]; exact f1 x hx
    · have hk0 : k < s.future_order.val.length := by rw [← kfo]; exact hk
      rw [knf] at hnf
      have key : ∀ x : Usize, x = s.future_order.val[k]'hk0 → ∀ hx : x.val < s'.objs.val.length,
          (s'.objs.val[x.val]'hx).life = .Future := by
        intro x ex hx
        subst ex
        have hx0 : (s.future_order.val[k]'hk0).val < s.objs.val.length := by rw [← hl]; exact hx
        have hF := f2 k hk0 hnf hx0
        have hne : (s.future_order.val[k]'hk0).val ≠ i.val := by
          intro e; rw [s8_getElem_congr s.objs.val _ _ hx0 hio e, hal] at hF; cases hF
        rw [(hg _ hx0 hx hne).1]; exact hF
      exact key _ (s8_getElem_eq _ _ (by rw [kfo]) k hk hk0) h


/-! ## transport lemmas for the lifetime loops -/

def s8Z (s : sim.state.St) : sim.state.St := { s with future_order := alloc.vec.Vec.new Usize, next_future := 0#usize }

theorem s8R_fo {i K N M T TL sB s'} (h : s8R i K N M T TL sB s') (F : alloc.vec.Vec Usize) (m : Usize) :
    s8R i K N M T TL { sB with future_order := F, next_future := m } { s' with future_order := F, next_future := m } := by
  obtain ⟨⟨ins, pl, th, O, hs⟩, hk, hdv, htl, htv, hil, hiu, hpl, hP, hin, hT, hTL⟩ := h
  subst hs
  exact ⟨⟨ins, pl, th, O, rfl⟩, hk, hdv, htl, htv, hil, hiu, hpl, hP, hin, hT, hTL⟩

theorem s8_st_eta (s : sim.state.St) (F : alloc.vec.Vec Usize) (m : Usize) (h1 : s.future_order = F)
    (h2 : s.next_future = m) : ({ s with future_order := F, next_future := m } : sim.state.St) = s := by
  subst h1 h2; rfl

theorem s8_futOK_nil (s : sim.state.St) (h : s.future_order.val = []) : simFutOK s := by
  refine ⟨fun x hx => ?_, fun k hk => ?_, ?_⟩
  · rw [h] at hx; cases hx
  · exfalso; rw [h] at hk; simp at hk
  · rw [h]; simp

theorem s8_vnew_val : (alloc.vec.Vec.new Usize).val = [] := by simp [alloc.vec.Vec.new]

theorem s8LC_fo (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (b n CS : Nat) (c : sim.state.Ctx)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (s : sim.state.St) (hL : s8LC tn fo P b n CS c s) (F : alloc.vec.Vec Usize) (m : Usize)
    (hfut : s.first_lifetime_update = false → simFutOK { s with future_order := F, next_future := m }) :
    s8LC tn fo P b n CS c { s with future_order := F, next_future := m } :=
  { hL with
    ar := s8_ar_xfer h64 tn fo P _ n c s hL.ar _ _ (let h := hL.ar.inv; ⟨h.1, h.2, h.3, h.4, h.5⟩) rfl hL.ar.tf hL.ar.ik
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hL.dnd hos hns
    fut := hfut }

theorem s8LC_first (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (b n CS : Nat) (c : sim.state.Ctx)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (s : sim.state.St) (hL : s8LC tn fo P b n CS c s) :
    s8LC tn fo P b n CS c (s8Z { s with first_lifetime_update := false }) :=
  { hL with
    ar := s8_ar_xfer h64 tn fo P _ n c s hL.ar _ _ (let h := hL.ar.inv; ⟨h.1, h.2, h.3, h.4, h.5⟩) rfl hL.ar.tf hL.ar.ik
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hL.dnd hos hns
    ftr := fun h => by simp [s8Z] at h
    fut := fun _ => s8_futOK_nil _ s8_vnew_val }

theorem s8_futOK_set (s : sim.state.St) (j : Usize) (O : sim.state.OState) (hok : simFutOK s)
    (hnot : ∀ k (hk : k < s.future_order.val.length), s.next_future.val ≤ k → (s.future_order.val[k]'hk).val ≠ j.val)
    (s' : sim.state.St) (hso : s'.objs = s.objs.set j O) (hfo : s'.future_order = s.future_order)
    (hnf : s'.next_future = s.next_future) : simFutOK s' := by
  obtain ⟨f1, f2, f3⟩ := hok
  have hl : s'.objs.val.length = s.objs.val.length := by rw [hso]; exact s8_set_len _ _ _
  refine ⟨fun x hx => ?_, fun k hk hk2 h => ?_, by rw [hfo, hnf]; exact f3⟩
  · rw [hfo] at hx; rw [hl]; exact f1 x hx
  · have hk0 : k < s.future_order.val.length := by rw [← hfo]; exact hk
    rw [hnf] at hk2
    have key : ∀ x : Usize, x = s.future_order.val[k]'hk0 → ∀ hx : x.val < s'.objs.val.length,
        (s'.objs.val[x.val]'hx).life = .Future := by
      intro x ex hx
      have hne := hnot k hk0 hk2
      subst ex
      have hx0 : (s.future_order.val[k]'hk0).val < s.objs.val.length := by rw [← hl]; exact hx
      have e1 := s8_getElem_eq (s.objs.set j O).val s'.objs.val (by rw [hso]) _ hx (by rw [s8_set_len]; exact hx0)
      rw [e1, s8_set_get _ _ _ _ _ hx0, if_neg (Ne.symm hne)]
      exact f2 k hk0 hk2 hx0
    exact key _ (s8_getElem_eq _ _ (by rw [hfo]) k hk hk0) h

theorem s8_futOK_succ (s : sim.state.St) (hok : simFutOK s) (h : s.next_future.val < s.future_order.val.length)
    (i3 : Usize) (hi3 : i3.val = s.next_future.val + 1) :
    simFutOK { s with next_future := i3 } ∧
    ∀ k (hk : k < s.future_order.val.length), i3.val ≤ k →
      (s.future_order.val[k]'hk).val ≠ (s.future_order.val[s.next_future.val]'h).val := by
  obtain ⟨f1, f2, f3⟩ := hok
  have hd : s.future_order.val.drop s.next_future.val =
      (s.future_order.val[s.next_future.val]'h) :: s.future_order.val.drop i3.val := by
    rw [hi3]; exact List.drop_eq_getElem_cons h
  rw [hd] at f3
  have f3' := List.nodup_cons.1 f3
  refine ⟨⟨f1, fun k hk hk2 hx => f2 k hk (by have : i3.val ≤ k := hk2; omega) hx, f3'.2⟩, fun k hk hk2 e => ?_⟩
  apply f3'.1
  have hm : s.future_order.val[k]'hk ∈ s.future_order.val.drop i3.val := by
    refine List.mem_iff_getElem.2 ⟨k - i3.val, by simp; omega, ?_⟩
    simp only [List.getElem_drop]
    exact s8_getElem_congr _ _ _ _ _ (by omega)
  have e' : s.future_order.val[k]'hk = s.future_order.val[s.next_future.val]'h := UScalar.eq_of_val_eq e
  rw [← e']; exact hm

theorem s8_U64max : U64.max = 2 ^ 64 - 1 := by first | scalar_tac | simp [U64.max] | (unfold U64.max; rfl)

/-- `became_alive` on a Future object preserves the core lifetime invariant (stated on the state with its future
order replaced by `F`/`m`, so it serves both the first scan and the later scans) -/
theorem s8_ba_LC (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P) (b n CS : Nat) (c : sim.state.Ctx)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (hC : SimARCtx c) (hTK : s8TKCtx c) (hCS : simCSH P n tn fo c)
    (hBud : b + c.pb.objects.val.length * (4 * n + 8) + s8Umax c * (n + n + 4) + 1 < Usize.max)
    (s : sim.state.St) (F : alloc.vec.Vec Usize) (m : Usize)
    (hL : s8LC tn fo P b n CS c { s with future_order := F, next_future := m })
    (hfirst : s.first_lifetime_update = false) (i : Usize) (ho : i.val < s.objs.val.length)
    (hF : (s.objs.val[i.val]'ho).life = .Future)
    (hnot : ∀ k (hk : k < F.val.length), m.val ≤ k → (F.val[k]'hk).val ≠ i.val) :
    ∃ res s', sim.step.became_alive c s i = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → s8LC tn fo P b n CS c { s' with future_order := F, next_future := m } ∧
        s'.first_lifetime_update = s.first_lifetime_update ∧ s'.future_order = s.future_order ∧
        s'.next_future = s.next_future ∧ s8LuKeep s' = s8LuKeep s ∧ s'.objs.val.length = s.objs.val.length ∧
        ∀ j (h : j < s.objs.val.length) (h' : j < s'.objs.val.length), j ≠ i.val → s'.objs.val[j]'h' = s.objs.val[j]'h) := by
  have hinv : SimInv c s := let h := hL.ar.inv; ⟨h.1, h.2, h.3, h.4, h.5⟩
  have hi : i.val < c.pb.objects.val.length := by rw [← hinv.objs_len]; exact ho
  have hlen := hinv.objs_len
  have hUm := usize_max_64 h64
  have hdl : s.dict_slots.val.length ≤ s.objs.val.length := hL.dlen
  have hfree : ∀ x ∈ s.free_list.val, x.val < s.dict_slots.val.length := fun x hx => (hL.frl x hx).1
  have hact : s.active.val.length ≤ s.objs.val.length := by
    have hnd : (s.active.val.map (·.val)).Nodup := List.Nodup.map (fun a b h => UScalar.eq_of_val_eq h) hL.actnd
    have := s8_nodup_lt _ hnd s.objs.val.length
      (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hL.actl y hy)
    rw [List.length_map] at this; exact this
  have hcc0 : s.child_counter.val + simFut s ≤ s.objs.val.length := hL.cc
  have hU64 := s8_U64max
  have hcc : s.child_counter.val + 1 ≤ U64.max := by omega
  have hFS := s8_fut_set s.objs.val i.val ho { (s.objs.val[i.val]'ho) with life := .Past } hF (by simp)
  have hW : (s.objs.val[i.val]'ho).nested.val.length + 2 ≤ simFutW s := by rw [s8_simFutW_eq]; omega
  have hF1 : 1 ≤ simFut s := by rw [s8_simFut_eq]; omega
  have hins : s.insts.val.length + simFutW s < Usize.max := hL.ins
  have hN : (s.objs.val[i.val]'ho).nested.val.length = (c.pb.objects.val[i.val]'hi).nested.val.length :=
    hinv.nested_len _ ho hi
  have hcap : s.insts.val.length + 2 + (c.pb.objects.val[i.val]'hi).nested.val.length < Usize.max := by omega
  have hUnj : simUnj s ≤ s8Umax c := s8_unj_le c s hinv
  have hFl : simFut s ≤ s.objs.val.length := s8_fut_le s
  obtain ⟨u, hu⟩ : ∃ u, simFut s = u + 1 := ⟨simFut s - 1, by omega⟩
  have hm1 : (u + 1) * (4 * n + 8) ≤ c.pb.objects.val.length * (4 * n + 8) := Nat.mul_le_mul_right _ (by omega)
  have hm2 : simUnj s * (n + n + 4) ≤ s8Umax c * (n + n + 4) := Nat.mul_le_mul_right _ hUnj
  have hm3 : (u + 1) * (4 * n + 8) = u * (4 * n + 8) + (4 * n + 8) := by ring
  have htf : s3b_TfInv P (b + simFut s * (4 * n + 8) + (simUnj s + 0) * (n + n + 4)) s := hL.ar.tf
  have hTf : s3b_TfInv P (b + u * (4 * n + 8) + simUnj s * (n + n + 4) + n + n + 4 + (n + n + 4)) s := by
    refine sim_tf_mono E htf ?_
    rw [hu, hm3]; simp only [Nat.add_zero]; omega
  have hB : b + u * (4 * n + 8) + simUnj s * (n + n + 4) + n + n + 4 + (n + n + 4) + 1 < Usize.max := by omega
  obtain ⟨res, s', e1, r1, r2⟩ := s8_became_alive_fr tn fo c s i hi hinv hfree (by omega) (by omega) hcc hL.pl hcap
    hL.pool hC E X (b + u * (4 * n + 8) + simUnj s * (n + n + 4)) n hCS hTf hB
  refine ⟨res, s', e1, r1, fun hr => ?_⟩
  obtain ⟨hinv', htf', k, v1, FL, v2, cid, hDS, hv2, hcid, hR⟩ := r2 hr
  obtain ⟨T, TL, hTs, hR⟩ := hR ho
  have hR' := s8R_fo hR F m
  obtain ⟨⟨ins, pl, th, O, hs'⟩, -⟩ := hR
  have hso : s'.objs = s.objs.set i O := by rw [hs']
  have hl' : s'.objs.val.length = s.objs.val.length := by rw [hso]; exact s8_set_len _ _ _
  have hfut : ({ s' with future_order := F, next_future := m } : sim.state.St).first_lifetime_update = false →
      simFutOK { s' with future_order := F, next_future := m } := fun _ =>
    s8_futOK_set { s with future_order := F, next_future := m } i O (hL.fut hfirst) hnot _ hso rfl rfl
  have htf2 : s3b_TfInv P (b + (simFut s - 1) * (4 * n + 8) + simUnj s * (n + n + 4))
      { s' with future_order := F, next_future := m } := by
    have e : simFut s - 1 = u := by omega
    rw [e]; exact htf'
  have hLC := s8LC_alive h64 tn fo E b n CS c hos hns hC hTK { s with future_order := F, next_future := m } hL i hi ho hF
    hfirst { s' with future_order := F, next_future := m } ⟨hinv'.1, hinv'.2, hinv'.3, hinv'.4, hinv'.5⟩ htf2 k v1 FL v2 cid hDS hv2 hcid T TL hTs hR' hfut
  refine ⟨hLC, by rw [hs'], by rw [hs'], by rw [hs'], by rw [hs']; rfl, hl', fun j h h' hj => ?_⟩
  have e2 := s8_getElem_eq (s.objs.set i O).val s'.objs.val (by rw [hso]) j h' (by rw [s8_set_len]; exact h)
  rw [e2, s8_set_get _ _ _ _ _ h, if_neg (Ne.symm hj)]

/-- leaving the lifetime phase: the active-list filter restores `aact` -/
theorem s8LC_filt (h64 : System.Platform.numBits = 64) (tn : Nat → String) (fo : alloc.vec.Vec Usize)
    {P : Nat → sim.transforms.TObj → Prop} (b n CS : Nat) (c : sim.state.Ctx)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (s : sim.state.St) (hL : s8LC tn fo P b n CS c s) (KF : alloc.vec.Vec Usize)
    (hKF : KF.val = s.active.val.filter (s8Alive s)) : simLifeInv tn fo P b n CS c { s with active := KF } := by
  have hsub : ∀ x ∈ KF.val, x ∈ s.active.val ∧ s8Alive s x = true := by
    intro x hx; rw [hKF] at hx; exact List.mem_filter.1 hx
  refine ⟨{ hL with
    ar := s8_ar_xfer h64 tn fo P _ n c s hL.ar _ _ (let h := hL.ar.inv; ⟨h.1, h.2, h.3, h.4, h.5⟩) rfl hL.ar.tf hL.ar.ik
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hL.dnd hos hns
    actl := fun x hx => hL.actl x (hsub x hx).1
    actnd := by show KF.val.Nodup; rw [hKF]; exact hL.actnd.filter _
    actnf := fun x hx => hL.actnf x (hsub x hx).1
    aal := ?_ }, ?_⟩
  · intro j h hA
    obtain ⟨x, hx, hxv⟩ := hL.aal j h hA
    refine ⟨x, ?_, hxv⟩
    show x ∈ KF.val
    rw [hKF]; refine List.mem_filter.2 ⟨hx, ?_⟩
    subst hxv
    change (s.objs.val[x.val]'h).life = .Alive at hA
    simp only [s8Alive, List.getElem?_eq_getElem h, hA, lifeS, s8_lbe2]
  · intro x hx h
    have ha := (hsub x hx).2
    simp only [s8Alive, List.getElem?_eq_getElem h] at ha
    show (s.objs.val[x.val]'h).life = .Alive
    revert ha
    cases (s.objs.val[x.val]'h).life <;> simp [lifeS, s8_lbe1, s8_lbe3]

/-! ## the loop families -/

def s8AF (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b n CS : Nat)
    (c : sim.state.Ctx) (s0 : sim.state.St) (i : Nat) (S : sim.state.St) (F : List Usize) : Prop :=
  s8LC tn fo P b n CS c (s8Z S) ∧ S.first_lifetime_update = false ∧ s8LuKeep S = s8LuKeep s0 ∧
  (∀ j (h : j < S.objs.val.length), i ≤ j → (S.objs.val[j]'h).life = .Future) ∧
  (∀ x ∈ F, ∃ h : x.val < S.objs.val.length, x.val < i ∧ (S.objs.val[x.val]'h).life = .Future) ∧
  (F.map (·.val)).Nodup

def s8BF (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b n CS : Nat)
    (c : sim.state.Ctx) (s0 : sim.state.St) (S : sim.state.St) : Prop :=
  s8LC tn fo P b n CS c S ∧ S.first_lifetime_update = false ∧ s8LuKeep S = s8LuKeep s0

def s8DF (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop) (b n CS : Nat)
    (c : sim.state.Ctx) (s0 : sim.state.St) (snap : alloc.vec.Vec Usize) (_k : Nat) (S : sim.state.St) : Prop :=
  s8LC tn fo P b n CS c S ∧ S.first_lifetime_update = false ∧ s8LuKeep S = s8LuKeep s0 ∧
  ∀ x ∈ snap.val, x.val < S.objs.val.length

theorem s8Umax_eq (c : sim.state.Ctx) :
    s8Umax c = (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum := by
  unfold s8Umax; congr 1; apply List.map_congr_left; intro o _; omega


-- CONDITIONAL: context premises (hC/hCS/hTK/hp/htl: ev_ctxWF-level facts), the budget bound hBud and the spin bound hCSb (from RunBudgetS, simcore3)
theorem sim.step.lifetime_update_refines (h64 : System.Platform.numBits = 64) (tn : Nat → String)
    (fo : alloc.vec.Vec Usize) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (X : simTfX P)
    (b n CS : Nat) (c : sim.state.Ctx) (hC : SimARCtx c) (hCS : simCSH P n tn fo c) (hTK : s8TKCtx c)
    (hos : c.pb.objects.val.length < 2 ^ 32) (hns : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32)
    (hp : ∀ i, i < c.pb.objects.val.length → s3aPathOk c i)
    (htl : ∀ i (hi : i < c.pb.objects.val.length), (c.pb.objects.val[i]'hi).h.kind = .Slider →
      ∃ hti : i < c.tail_idx.val.length, (c.tail_idx.val[i]'hti).val < (c.pb.objects.val[i]'hi).nested.val.length)
    (hBud : b + c.pb.objects.val.length * (4 * n + 8) + s8Umax c * (n + n + 4) + 1 < Usize.max)
    (hCSb : CS * 360 < 2 ^ 63)
    (s : sim.state.St) (hL : simLifeInv tn fo P b n CS c s) :
    ∃ res s', sim.step.lifetime_update c s = ok (res, s') ∧
      simRelM tn s' res (OsuModel.Sim.Sim.lifetimeUpdate (simCtxS tn fo c) (simStS tn s)) ∧
      (res = .Ok () → simLifeInv tn fo P b n CS c s' ∧ s8LuKeep s' = s8LuKeep s ∧
        s'.first_lifetime_update = false) := by
  have hUm := usize_max_64 h64
  have hU64 := s8_U64max
  have hcl : c.pb.objects.val.length < Usize.max := by omega
  have hlen' : ∀ i S F, s8AF tn fo P b n CS c s i S F → S.objs.val.length = c.pb.objects.val.length :=
    fun i S F h => h.1.ar.inv.objs_len
  have hF' : ∀ (i : Usize) S F (ho : i.val < S.objs.val.length), s8AF tn fo P b n CS c s i.val S F →
      s.t < (S.objs.val[i.val]'ho).lifetime_start → s8AF tn fo P b n CS c s (i.val + 1) S (F ++ [i]) := by
    intro i S F ho h _
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h1, h2, h3, fun j hj hij => h4 j hj (by omega), fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨a, b', d⟩ := h5 x hx; exact ⟨a, by omega, d⟩
      · simp at hx; subst hx; exact ⟨ho, by omega, h4 _ ho (le_refl _)⟩
    · rw [List.map_append]
      refine List.nodup_append.2 ⟨h6, List.nodup_singleton _, ?_⟩
      intro a ha b' hb e
      simp at hb; subst hb; subst e
      obtain ⟨x, hx, hxv⟩ := List.mem_map.1 ha
      obtain ⟨_, hlt, _⟩ := h5 x hx; omega
  have hPa' : ∀ (i : Usize) S F (ho : i.val < S.objs.val.length), s8AF tn fo P b n CS c s i.val S F →
      ¬ s.t < (S.objs.val[i.val]'ho).lifetime_start → (S.objs.val[i.val]'ho).lifetime_end ≤ s.t →
      s8AF tn fo P b n CS c s (i.val + 1) { S with objs := S.objs.set i { (S.objs.val[i.val]'ho) with life := .Past } } F := by
    intro i S F ho h _ _
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    set O : sim.state.OState := { (S.objs.val[i.val]'ho) with life := .Past } with hO
    have hg : ∀ x (h' : x < (S.objs.set i O).val.length) (h : x < S.objs.val.length), i.val ≠ x →
        (S.objs.set i O).val[x]'h' = S.objs.val[x]'h := fun x h' h hne => by rw [s8_set_get _ _ _ _ h' h, if_neg hne]
    refine ⟨?_, h2, h3, fun j hj hij => ?_, fun x hx => ?_, h6⟩
    · exact s8LC_past h64 tn fo E b n CS c hos hns (s8Z S) h1 i ho (h4 _ ho (le_refl _)) 0#usize h2
        (s8_futOK_nil _ s8_vnew_val)
    · have hj' : j < (S.objs.set i O).val.length := hj
      have hj0 : j < S.objs.val.length := by rw [s8_set_len] at hj'; exact hj'
      show ((S.objs.set i O).val[j]'hj').life = .Future
      rw [hg j hj' hj0 (by omega)]; exact h4 j hj0 (by omega)
    · obtain ⟨hx0, hlt, hfx⟩ := h5 x hx
      have hx1 : x.val < (S.objs.set i O).val.length := by rw [s8_set_len]; exact hx0
      refine ⟨hx1, by omega, ?_⟩
      show ((S.objs.set i O).val[x.val]'hx1).life = _
      rw [hg _ _ hx0 (by omega)]; exact hfx
  have hAa' : ∀ (i : Usize) S F (ho : i.val < S.objs.val.length), s8AF tn fo P b n CS c s i.val S F →
      ¬ s.t < (S.objs.val[i.val]'ho).lifetime_start → ¬ (S.objs.val[i.val]'ho).lifetime_end ≤ s.t →
      ∃ res s'', sim.step.became_alive c S i = ok (res, s'') ∧
        simRelM tn s'' res (OsuModel.Sim.Sim.becameAlive i.val (simCtxS tn fo c) (simStS tn S)) ∧
        (res = .Ok () → s8AF tn fo P b n CS c s (i.val + 1) s'' F) := by
    intro i S F ho h _ _
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    obtain ⟨res, s'', e1, r1, r2⟩ := s8_ba_LC h64 tn fo E X b n CS c hos hns hC hTK hCS hBud S
      (alloc.vec.Vec.new Usize) 0#usize h1 h2 i ho (h4 _ ho (le_refl _))
      (fun k hk => by rw [s8_vnew_val] at hk; simp at hk)
    refine ⟨res, s'', e1, r1, fun hr => ?_⟩
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := r2 hr
    refine ⟨g1, by rw [g2]; exact h2, by rw [g5]; exact h3, fun j hj hij => ?_, fun x hx => ?_, h6⟩
    · have hj0 : j < S.objs.val.length := by rw [← g6]; exact hj
      rw [g7 j hj0 hj (by omega)]; exact h4 j hj0 (by omega)
    · obtain ⟨hx0, hlt, hfx⟩ := h5 x hx
      have hx1 : x.val < s''.objs.val.length := by rw [g6]; exact hx0
      exact ⟨hx1, by omega, by rw [g7 _ hx0 hx1 (by omega)]; exact hfx⟩
  have hA0' : s.first_lifetime_update = true → s8AF tn fo P b n CS c s 0 { s with first_lifetime_update := false } [] := by
    intro hf
    exact ⟨s8LC_first h64 tn fo b n CS c hos hns s hL.1, rfl, rfl, fun j hj _ => hL.ftr hf j hj, by simp, by simp⟩
  have hfo' : ∀ S, s8BF tn fo P b n CS c s S → ∀ x ∈ S.future_order.val, x.val < S.objs.val.length :=
    fun S h => (h.1.fut h.2.1).1
  have hPb' : ∀ S (h : S.next_future.val < S.future_order.val.length)
      (ho : (S.future_order.val[S.next_future.val]'h).val < S.objs.val.length), s8BF tn fo P b n CS c s S →
      ¬ s.t < (S.objs.val[(S.future_order.val[S.next_future.val]'h).val]'ho).lifetime_start →
      (S.objs.val[(S.future_order.val[S.next_future.val]'h).val]'ho).lifetime_end ≤ s.t →
      ∀ i3 : Usize, i3.val = S.next_future.val + 1 →
      s8BF tn fo P b n CS c s (s8SP S (S.future_order.val[S.next_future.val]'h)
        (S.objs.val[(S.future_order.val[S.next_future.val]'h).val]'ho) i3) := by
    intro S h ho hB _ _ i3 hi3
    obtain ⟨h1, h2, h3⟩ := hB
    have hok := h1.fut h2
    obtain ⟨hok3, hnot⟩ := s8_futOK_succ S hok h i3 hi3
    have hFx := hok.2.1 _ h (le_refl _) ho
    refine ⟨?_, h2, h3⟩
    unfold s8SP
    exact s8LC_past h64 tn fo E b n CS c hos hns S h1 _ ho hFx i3 h2
      (s8_futOK_set { S with next_future := i3 } _ _ hok3 hnot _ rfl rfl rfl)
  have hAb' : ∀ S (h : S.next_future.val < S.future_order.val.length)
      (ho : (S.future_order.val[S.next_future.val]'h).val < S.objs.val.length), s8BF tn fo P b n CS c s S →
      ¬ s.t < (S.objs.val[(S.future_order.val[S.next_future.val]'h).val]'ho).lifetime_start →
      ¬ (S.objs.val[(S.future_order.val[S.next_future.val]'h).val]'ho).lifetime_end ≤ s.t →
      ∀ i3 : Usize, i3.val = S.next_future.val + 1 →
      ∃ res s'', sim.step.became_alive c { S with next_future := i3 } (S.future_order.val[S.next_future.val]'h) =
          ok (res, s'') ∧
        simRelM tn s'' res (OsuModel.Sim.Sim.becameAlive (S.future_order.val[S.next_future.val]'h).val
          (simCtxS tn fo c) (simStS tn { S with next_future := i3 })) ∧
        (res = .Ok () → s8BF tn fo P b n CS c s s'') := by
    intro S h ho hB _ _ i3 hi3
    obtain ⟨h1, h2, h3⟩ := hB
    have hok := h1.fut h2
    obtain ⟨hok3, hnot⟩ := s8_futOK_succ S hok h i3 hi3
    have hFx := hok.2.1 _ h (le_refl _) ho
    have hZ := s8LC_fo h64 tn fo b n CS c hos hns S h1 S.future_order i3 (fun _ => hok3)
    obtain ⟨res, s'', e1, r1, r2⟩ := s8_ba_LC h64 tn fo E X b n CS c hos hns hC hTK hCS hBud
      { S with next_future := i3 } S.future_order i3 hZ h2 _ ho hFx hnot
    refine ⟨res, s'', e1, r1, fun hr => ?_⟩
    obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := r2 hr
    have e : ({ s'' with future_order := S.future_order, next_future := i3 } : sim.state.St) = s'' :=
      s8_st_eta s'' _ _ g3 g4
    rw [e] at g1
    exact ⟨g1, by rw [g2]; exact h2, by rw [g5]; exact h3⟩
  have hB0' : s.first_lifetime_update = false → s8BF tn fo P b n CS c s s := fun hf => ⟨hL.1, hf, rfl⟩
  have hb' : ∀ snap k S, s8DF tn fo P b n CS c s snap k S → ∀ hk : k < snap.val.length,
      (snap.val[k]'hk).val < S.objs.val.length := fun snap k S h hk => h.2.2.2 _ (List.getElem_mem hk)
  have hd' : ∀ snap k S (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < S.objs.val.length),
      s8DF tn fo P b n CS c s snap k S →
      ((S.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ s.t ∨ s.t < (S.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      ∃ res s'', sim.step.became_dead c S (snap.val[k]'hk) = ok (res, s'') ∧
        simRelM tn s'' res (OsuModel.Sim.Sim.becameDead (snap.val[k]'hk).val (simCtxS tn fo c) (simStS tn S)) ∧
        (res = .Ok () → s8DF tn fo P b n CS c s snap (k + 1) s'') := by
    intro snap k S hk ho hD _
    obtain ⟨h1, h2, h3, h4⟩ := hD
    have hlS := h1.ar.inv.objs_len
    have hi : (snap.val[k]'hk).val < c.pb.objects.val.length := by rw [← hlS]; exact ho
    have hfl : S.free_list.val.length < Usize.max := by
      have hnd : (S.free_list.val.map (·.val)).Nodup := List.Nodup.map (fun a b h => UScalar.eq_of_val_eq h) h1.frn
      have := s8_nodup_lt _ hnd S.dict_slots.val.length
        (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact (h1.frl y hy).1)
      rw [List.length_map] at this
      have := h1.dlen
      omega
    obtain ⟨res, s'', e1, r1, r2⟩ := sim.step.became_dead_refines h64 tn fo E (b + simFut S * (4 * n + 8)) n c hC hCS
      (by omega) hos hns S _ h1.ar hi (hp _ hi) h1.lp (htl _ hi)
      (fun h => lt_of_le_of_lt (Nat.mul_le_mul_right _ (h1.cs _ h)) hCSb)
      (fun h => by have := h1.tk _ h; rw [h1.ar.inv.nested_len _ h hi] at this; exact this)
      h1.dnd hfl h1.pl h1.pool
    refine ⟨res, s'', e1, r1, fun hr => ?_⟩
    obtain ⟨g1, g2, g3, g4⟩ := r2 hr
    exact ⟨s8LC_dead tn fo b n CS c S h1 _ s'' g1 g2 g3 g4, by rw [g4.keep.2.1]; exact h2, by rw [g4.lk]; exact h3,
      fun x hx => by rw [g4.len]; exact h4 x hx⟩
  have hs' : ∀ snap k S (hk : k < snap.val.length) (ho : (snap.val[k]'hk).val < S.objs.val.length),
      s8DF tn fo P b n CS c s snap k S →
      ¬ ((S.objs.val[(snap.val[k]'hk).val]'ho).lifetime_end ≤ s.t ∨ s.t < (S.objs.val[(snap.val[k]'hk).val]'ho).lifetime_start) →
      s8DF tn fo P b n CS c s snap (k + 1) S := fun snap k S hk ho h _ => h
  have he' : ∀ snap S, s8DF tn fo P b n CS c s snap snap.val.length S → ∀ x ∈ S.active.val, x.val < S.objs.val.length :=
    fun snap S h => h.1.actl
  have hAD' : ∀ sE FUT sorted, s8AF tn fo P b n CS c s c.pb.objects.val.length sE FUT.val →
      sim.step.sort_by_lifetime_start sE (alloc.vec.Vec.deref FUT) = ok sorted →
      s8DF tn fo P b n CS c s sE.active 0 { sE with next_future := 0#usize, future_order := sorted } := by
    intro sE FUT sorted hA hsort
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
    have hdv : (alloc.vec.Vec.deref FUT).val = FUT.val := by simp [alloc.vec.Vec.deref, Slice.from_val]
    have hlE : sE.objs.val.length = c.pb.objects.val.length := h1.ar.inv.objs_len
    obtain ⟨out, hout, hv⟩ := s5_sort_model sE (alloc.vec.Vec.deref FUT) (by rw [hdv]; intro e he; exact (h5 e he).1) (by
      rw [hdv]
      have := s8_nodup_lt _ h6 sE.objs.val.length
        (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact (h5 y hy).1)
      rw [List.length_map] at this; omega)
    rw [hsort] at hout
    simp only [ok.injEq] at hout
    subst hout
    have hperm : (sorted.val.map (·.val)).Perm (FUT.val.map (·.val)) := by
      rw [hv, hdv]; exact s8_sortL_perm _ _
    have hmem : ∀ x ∈ sorted.val, x ∈ FUT.val := by
      intro x hx
      have : x.val ∈ FUT.val.map (·.val) := hperm.mem_iff.1 (List.mem_map_of_mem hx)
      obtain ⟨y, hy, hyv⟩ := List.mem_map.1 this
      rw [← UScalar.eq_of_val_eq hyv]; exact hy
    have hnd : sorted.val.Nodup := List.Nodup.of_map (·.val) (hperm.nodup_iff.2 h6)
    have hfut : simFutOK { s8Z sE with future_order := sorted, next_future := 0#usize } := by
      refine ⟨fun x hx => (h5 x (hmem x hx)).1, fun k hk _ hx => ?_, by simp; exact hnd⟩
      obtain ⟨h0, -, hf⟩ := h5 _ (hmem _ (List.getElem_mem hk))
      exact hf
    have hLC := s8LC_fo h64 tn fo b n CS c hos hns (s8Z sE) h1 sorted 0#usize (fun _ => hfut)
    exact ⟨hLC, h2, h3, fun x hx => h1.actl x hx⟩
  have hBD' : ∀ S, s8BF tn fo P b n CS c s S → s8DF tn fo P b n CS c s S.active 0 S :=
    fun S h => ⟨h.1, h.2.1, h.2.2, fun x hx => h.1.actl x hx⟩
  obtain ⟨res, s', e, r, hok⟩ := s8_lu_gen tn fo c s hcl (s8AF tn fo P b n CS c s) hlen' hF' hPa' hAa' hA0'
    (s8BF tn fo P b n CS c s) hfo' hPb' hAb' hB0' (s8DF tn fo P b n CS c s) hb' hd' hs' he' hAD' hBD'
  refine ⟨res, s', e, r, fun hr => ?_⟩
  obtain ⟨snap, sE, KF, ⟨h1, h2, h3, -⟩, hs'', hKF⟩ := hok hr
  subst hs''
  exact ⟨s8LC_filt h64 tn fo b n CS c hos hns sE h1 KF hKF, h3, h2⟩

end OsuProofs
