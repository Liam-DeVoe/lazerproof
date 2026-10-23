/-
Sim3b (transform-mod state hooks + mod update hooks), part 1: small `sim::step` leaves.
`pool_get`/`pool_return` (DrawablePool), `with_abs_begin`/`with_abs_end` (the two halves of `Sim.withAbs`),
`v_xy`, `hundreds`, `clamp_net`, `ref_seen`, `prec_end_of`.
Statement shape (sim core interface): `∃ r s', f c s args = ok (r, s') ∧ Spec.F (abs args) (simCtxS tn fo c) (simStS tn s)
= .ok (abs r, simStS tn s')`; `Result<_, SimErr>` results are related by `s3b_rrel` (Ok ↦ ok, Err ↦ error).
-/
import OsuProofs.Sim.Hit
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

/-- Rust `Result<α, SimErr>` (with the final Rust state) vs a spec `SimM` evaluation: `Ok v` ↦ `.ok (f v, S)`,
`Err _` ↦ some `.error`. -/
def s3b_rrel {α β : Type} (f : α → β) (S : OsuModel.Sim.St) :
    core.result.Result α sim.err.SimErr → Except String (β × OsuModel.Sim.St) → Prop
  | .Ok v, e => e = .ok (f v, S)
  | .Err _, e => ∃ m, e = .error m

/-- `SimInv` only reads `objs` and `dict_slots`. -/
theorem s3b_inv_of {c : sim.state.Ctx} {s s' : sim.state.St} (h : SimInv c s) (ho : s'.objs = s.objs)
    (hd : s'.dict_slots = s.dict_slots) : SimInv c s' := by
  obtain ⟨a, b, d, e, f⟩ := h
  exact ⟨by rw [ho]; exact a, by rw [ho]; exact b, d, by rw [hd]; exact e, by rw [hd]; exact f⟩

/-! ## small pure leaves -/
theorem sim.step.v_xy_refines (x y : F32) :
    ∃ v, sim.step.v_xy x y = ok v ∧ (⟨x, y⟩ : OsuModel.Sim.Vec2) = abs v :=
  ⟨⟨x, y⟩, rfl, rfl⟩

/-- `hundreds n` = the spec's `(n / 100).toNat` for a positive count (`Int.div` rounds toward zero = `/` here). -/
theorem sim.step.hundreds_refines (n : I64) :
    ∃ q, sim.step.hundreds n = ok q ∧ q.val = (n.val / 100).toNat := by
  unfold sim.step.hundreds
  by_cases h : n ≤ 0#i64
  · have h0 : n.val ≤ 0 := by scalar_tac
    refine ⟨0#u64, by simp [h], ?_⟩
    have : n.val / 100 ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg h0 (by decide)
    simp; omega
  · have h0 : 0 < n.val := by scalar_tac
    obtain ⟨d, hd, hdv⟩ : ∃ d, n / 100#i64 = ok d ∧ d.val = Int.tdiv n.val 100 := by
      obtain ⟨d, hd, hdv⟩ := IScalar.div_spec (x := n) (y := 100#i64) (by simp) (by simp)
      exact ⟨d, hd, by simpa using hdv⟩
    refine ⟨IScalar.hcast .U64 d, by simp [h, hd], ?_⟩
    have ht : Int.tdiv n.val 100 = n.val / 100 := Int.tdiv_eq_ediv_of_nonneg (by omega)
    have hpos : 0 ≤ d.val := by rw [hdv, ht]; omega
    rw [IScalar.hcast_val_eq]
    simp only [UScalarTy.U64_numBits_eq]
    have hb : d.val < 2 ^ 64 := by have := d.hmax; simp [IScalar.max] at this; omega
    rw [Int.emod_eq_of_lt hpos (by omega), hdv, ht]

theorem sim.step.clamp_net_refines (x lo hi : F64) :
    ∃ r, sim.step.clamp_net x lo hi = ok r ∧ ∀ C S,
      s3b_rrel id S r (OsuModel.Sim.Sim.liftNet (F64.clamp x lo hi) C S) := by
  unfold sim.step.clamp_net
  rw [net.mathops.f64_clamp_refines]
  cases hc : F64.clamp x lo hi with
  | ok v => exact ⟨.Ok v, by simp [exceptI, sim.err.lift_net], fun C S => by simp [s3b_rrel, OsuModel.Sim.Sim.liftNet, hc]⟩
  | error e => exact ⟨.Err (.Net (exnI e)), by simp [exceptI, sim.err.lift_net],
      fun C S => by simp [s3b_rrel, OsuModel.Sim.Sim.liftNet, hc]⟩

theorem s3b_foldl_contains {X : Type} (f : X → Nat × Int) (y : Nat × Int) (l : List X) :
    l.foldl (fun b x => b || decide (f x = y)) false = (l.map f).contains y := by
  suffices ∀ b, l.foldl (fun b x => b || decide (f x = y)) b = (b || (l.map f).contains y) by simpa using this false
  induction l with
  | nil => intro b; simp
  | cons x t ih =>
    intro b; simp only [List.foldl_cons, ih, List.map_cons, List.contains_cons]
    have e : (y == f x) = decide (f x = y) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact eq_comm
    rw [e, Bool.or_assoc]

/-- `ref_seen seen r` = `seen.contains r` (on the abstract references). -/
theorem sim.step.ref_seen_refines (seen : Slice sim.step.Ref) (r : sim.step.Ref) :
    sim.step.ref_seen seen r = ok ((seen.val.map (fun x => (abs x : Nat × Int))).contains (abs r)) := by
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => sim.step.ref_seen_loop.body seen r x.1 x.2) (·.1)
    seen.val.length (by have := seen.property; omega)
    (fun _ => True) (fun x => x.2)
    (fun k b => b || decide ((abs (seen.val[k]!) : Nat × Int) = abs r)) (fun y b => y = b)
    (by
      rintro ⟨i, b⟩ _ hk j1 hj1 hj1v
      simp only at hk hj1 hj1v ⊢
      have hkv : i.val < seen.val.length := hk
      refine ⟨(j1, b || decide ((abs (seen.val[i.val]'hkv) : Nat × Int) = abs r)), ?_, rfl, ?_, trivial⟩
      · simp only [sim.step.ref_seen_loop.body, slice_lt_len_iff, hkv, if_true, slice_index_ok _ _ hkv, bind_ok, hj1]
        by_cases h1 : (seen.val[i.val]'hkv).top = r.top <;> by_cases h2 : (seen.val[i.val]'hkv).nested = r.nested <;>
          simp_all [abs, UScalar.eq_equiv, IScalar.eq_equiv]
      · simp [getElem!_def, hkv])
    (by
      rintro ⟨i, b⟩ _ hge
      have : ¬ i < Slice.len seen := by rw [slice_lt_len_iff]; simp at hge; omega
      exact ⟨b, by simp only [sim.step.ref_seen_loop.body, this, ite_false], rfl⟩)
    (0#usize, false) trivial (by simp)
  unfold sim.step.ref_seen sim.step.ref_seen_loop
  rw [hl, hv]
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero]
  rw [← foldl_iterR seen.val (fun b x => b || decide ((abs x : Nat × Int) = abs r)) false]
  rw [s3b_foldl_contains]

/-! ## `prec_end_of` -/
instance s3b_inhPrecEnd : Inhabited sim.state.PrecEnd := ⟨⟨none, alloc.vec.Vec.new _⟩⟩

/-- `prev?` of `adaptiveSpeedOnResult` as a total function on in-range references. -/
def s3b_precEnd (c : sim.state.Ctx) (r : sim.step.Ref) : Option F64 :=
  if r.nested.val < 0 then (c.prec_end.val[r.top.val]!).top else (c.prec_end.val[r.top.val]!).nested.val[r.nested.val.toNat]!

def s3b_precOk (c : sim.state.Ctx) (r : sim.step.Ref) : Prop :=
  ∃ h : r.top.val < c.prec_end.val.length,
    0 ≤ r.nested.val → r.nested.val.toNat < (c.prec_end.val[r.top.val]'h).nested.val.length

theorem sim.step.prec_end_of_refines (c : sim.state.Ctx) (r : sim.step.Ref) (hr : s3b_precOk c r) :
    sim.step.prec_end_of c r = ok (s3b_precEnd c r) := by
  obtain ⟨ht, hn⟩ := hr
  unfold sim.step.prec_end_of s3b_precEnd
  simp only [vec_index_eq _ _ ht, bind_ok]
  by_cases hneg : r.nested < 0#i64
  · have h0 : r.nested.val < 0 := by scalar_tac
    simp [hneg, h0, getElem!_def, ht]
  · have h0 : 0 ≤ r.nested.val := by scalar_tac
    have hl := hn h0
    have hc := sim_i64_cast_usize r.nested h0 (by have := (c.prec_end.val[r.top.val]'ht).nested.property; omega)
    have hl' : (IScalar.hcast .Usize r.nested).val < (c.prec_end.val[r.top.val]'ht).nested.val.length := by omega
    have : ¬ r.nested.val < 0 := by omega
    simp only [hneg, lift, bind_ok, vec_index_eq _ _ hl', if_false, this, ite_false, Bool.false_eq_true, decide_false]
    simp [getElem!_def, ht, hc, hl]

/-! ## Pools (`DrawablePool.Get` / `Return`) -/
/-- the value of `inst_new` (`{} : Inst`) -/
def s3b_instNew : sim.state.Inst :=
  { tf := { pos := ⟨0, 0⟩, scale := ⟨1, 1⟩, rot := 0, alpha := 0, trackers := alloc.vec.Vec.new _, last_update := 0,
            delay := 0 }
    loaded := false, bound_pos := ⟨0, 0⟩, bound_stack := 0#i64, bound_scale := 0, size := ⟨0, 0⟩, origin := ⟨0, 0⟩
    rel_anchor := ⟨0, 0⟩, body_size := ⟨0, 0⟩, body_offset := ⟨0, 0⟩, body_radius := 0, refresh_pending := false
    body_tf := { pos := ⟨0, 0⟩, scale := ⟨1, 1⟩, rot := 0, alpha := 1, trackers := alloc.vec.Vec.new _,
                 last_update := 0, delay := 0 }
    body_loaded := false, drawable_tracking := false, armed := .Idle, ball_pos := ⟨0, 0⟩ }

theorem s3b_inst_new : sim.state.inst_new = ok s3b_instNew := by
  simp [sim.state.inst_new, sim.transforms.tobj_new, sim.transforms.F32_1, sim.transforms.F32_0,
    sim.transforms.F64_0, s3b_instNew]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide +kernel

theorem s3b_instNew_abs : (abs s3b_instNew : OsuModel.Sim.Inst) = {} := by
  simp [abs, s3b_instNew, armedS] <;> rfl

theorem s3b_len_sub_one {α} (v : alloc.vec.Vec α) (h : 0 < v.val.length) :
    ∃ k : Usize, alloc.vec.Vec.len v - 1#usize = ok k ∧ k.val = v.val.length - 1 := by
  obtain ⟨z, hz, hzv, _⟩ := eq_ok_of_spec (UScalar.sub_spec (x := alloc.vec.Vec.len v) (y := 1#usize) (by simp; omega))
  exact ⟨z, hz, by simpa using hzv⟩

theorem s3b_push_last {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    ∃ v' k, alloc.vec.Vec.push v x = ok v' ∧ alloc.vec.Vec.len v' - 1#usize = ok k ∧ v'.val = v.val ++ [x] ∧
      k.val = v.val.length := by
  obtain ⟨k, hk, hkv⟩ := s3b_len_sub_one (vpush v x h) (by simp)
  exact ⟨_, k, vec_push_ok v x h, hk, by simp, by simpa using hkv⟩

/-- the abstract pool (LIFO: Rust top = last element ↦ spec head) -/
def s3b_poolS (l : alloc.vec.Vec (Option Usize)) : List (Option Nat) := (l.val.map (·.map (·.val))).reverse

theorem s3b_stS_pools (tn) (s : sim.state.St) : (simStS tn s).pools = (s.pools.val.map s3b_poolS).toArray := rfl
theorem s3b_stS_insts (tn) (s : sim.state.St) : (simStS tn s).insts = (s.insts.val.map abs).toArray := rfl

/-- spec `poolGet` on an arbitrary state (in range) -/
theorem s3b_poolGet_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (pk : Nat) (h : pk < S.pools.size) :
    OsuModel.Sim.Sim.poolGet pk C S = match S.pools[pk] with
      | some k :: rest => .ok (k, { S with pools := S.pools.set pk rest })
      | none :: rest => .ok (S.insts.size, { S with pools := S.pools.set pk rest, insts := S.insts.push {} })
      | [] => .ok (S.insts.size, { S with insts := S.insts.push {} }) := by
  unfold OsuModel.Sim.Sim.poolGet
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind, OsuModel.Sim.Sim.getA, dif_pos h, simM_pure,
    OsuModel.Sim.Sim.setA]
  rcases hL : S.pools[pk] with _ | ⟨_ | k, rest⟩ <;> rfl

theorem s3b_stS_upd (tn) (s : sim.state.St) (ins : alloc.vec.Vec sim.state.Inst)
    (pl : alloc.vec.Vec (alloc.vec.Vec (Option Usize))) :
    simStS tn { s with insts := ins, pools := pl } =
      { simStS tn s with insts := (ins.val.map abs).toArray, pools := (pl.val.map s3b_poolS).toArray } := rfl

theorem s3b_pools_set (s : sim.state.St) (pk : Usize) (hpk : pk.val < s.pools.val.length)
    (P : alloc.vec.Vec (Option Usize)) :
    ((s.pools.set pk P).val.map s3b_poolS).toArray =
      (s.pools.val.map s3b_poolS).toArray.set pk.val (s3b_poolS P) (by simp [hpk]) := by
  simp [alloc.vec.Vec.set, List.map_set]

theorem sim.step.pool_get_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (pk : Usize)
    (hpk : pk.val < s.pools.val.length) (hcap : s.insts.val.length < Usize.max) :
    ∃ k s', sim.step.pool_get s pk = ok (k, s') ∧
      OsuModel.Sim.Sim.poolGet pk.val (simCtxS tn fo c) (simStS tn s) = .ok (k.val, simStS tn s') ∧
      (∃ ins' pl', s' = { s with insts := ins', pools := pl' }) ∧
      s'.pools.val.length = s.pools.val.length ∧
      (s'.insts.val = s.insts.val ∨ (s'.insts.val = s.insts.val ++ [s3b_instNew] ∧ k.val = s.insts.val.length)) ∧
      ((∀ j, some j ∈ (s.pools.val[pk.val]'hpk).val → j.val < s.insts.val.length) → k.val < s'.insts.val.length) := by
  have hpk' : pk.val < (simStS tn s).pools.size := by simp [s3b_stS_pools, hpk]
  rw [s3b_poolGet_spec _ _ _ hpk']
  have hPv : (simStS tn s).pools[pk.val]'hpk' = s3b_poolS (s.pools.val[pk.val]'hpk) := by simp [s3b_stS_pools]
  rw [hPv]
  unfold sim.step.pool_get
  rw [vec_index_mut_eq _ _ hpk]
  simp only [bind_ok, alloc.vec.Vec.pop]
  have hP0 : s.pools.set pk (s.pools.val[pk.val]'hpk) = s.pools := by
    apply alloc.vec.Vec.ext; simp [alloc.vec.Vec.set]
  have hset := s3b_pools_set s pk hpk
  generalize hP : s.pools.val[pk.val]'hpk = P at hP0
  obtain ⟨v', k, hv', hk, hv'v, hkv⟩ := s3b_push_last s.insts s3b_instNew hcap
  have hins : ((v'.val.map abs).toArray : Array OsuModel.Sim.Inst) = (simStS tn s).insts.push {} := by
    simp [s3b_stS_insts, hv'v, s3b_instNew_abs]
  have hsz : (simStS tn s).insts.size = s.insts.val.length := by simp [s3b_stS_insts]
  rcases List.eq_nil_or_concat P.val with h | ⟨L, x, h⟩
  · have hS : s3b_poolS P = [] := by simp [s3b_poolS, h]
    have hP1 : alloc.vec.Vec.from P.val.dropLast (by have := P.property; simp; omega) = P := by
      apply alloc.vec.Vec.ext; simp [alloc.vec.Vec.from, h]; rfl
    refine ⟨k, { s with insts := v' }, ?_, ?_, ⟨_, _, rfl⟩, rfl, Or.inr ⟨hv'v, hkv⟩, fun _ => by rw [hv'v, hkv]; simp⟩
    · have hP2 : ∀ pf, s.pools.set pk (alloc.vec.Vec.from [] pf) = s.pools := by
        intro pf; rw [← hP0]; congr 1; apply alloc.vec.Vec.ext; simp [alloc.vec.Vec.from, h]; rfl
      simp [h, s3b_inst_new, hv', hk, hP2]
    · simp only [hS]
      have e := s3b_stS_upd tn s v' s.pools
      simp only [] at e
      rw [e, hins, hkv, hsz]; rfl
  · have hl : P.val.getLast? = some x := by simp [h]
    have hdl : P.val.dropLast = L := by simp [h]
    have hLb : L.length ≤ Usize.max := by have := P.property; simp [h] at this; omega
    have hP1 : alloc.vec.Vec.from P.val.dropLast (by have := P.property; simp; omega) =
        (alloc.vec.Vec.from L hLb : alloc.vec.Vec (Option Usize)) := by
      apply alloc.vec.Vec.ext; simp [alloc.vec.Vec.from, hdl]
    have hS : s3b_poolS P = x.map (·.val) :: s3b_poolS (alloc.vec.Vec.from L hLb) := by
      simp [s3b_poolS, h, alloc.vec.Vec.from_val]
    rcases x with _ | j
    · refine ⟨k, { s with insts := v', pools := s.pools.set pk (alloc.vec.Vec.from L hLb) }, ?_, ?_, ⟨_, _, rfl⟩,
        by simp [alloc.vec.Vec.set], Or.inr ⟨hv'v, hkv⟩, fun _ => by rw [hv'v, hkv]; simp⟩
      · simp [hl, s3b_inst_new, hv', hk, hP1]
      · simp only [hS, Option.map_none]
        have e := s3b_stS_upd tn s v' (s.pools.set pk (alloc.vec.Vec.from L hLb))
        simp only [] at e
        rw [e, hins, hset, hkv, hsz]; rfl
    · refine ⟨j, { s with pools := s.pools.set pk (alloc.vec.Vec.from L hLb) }, ?_, ?_, ⟨_, _, rfl⟩,
        by simp [alloc.vec.Vec.set], Or.inl rfl, fun hj => hj j (by simp [h])⟩
      · simp [hl, hP1]
      · simp only [hS, Option.map_some]
        have e := s3b_stS_upd tn s s.insts (s.pools.set pk (alloc.vec.Vec.from L hLb))
        simp only [] at e
        rw [e, hset]; rfl

theorem s3b_arr_index {α : Type} {n : Usize} (v : Std.Array α n) (i : Usize) (h : i.val < v.val.length) :
    Std.Array.index_usize v i = ok (v.val[i.val]'h) := by
  obtain ⟨x, hx, hx'⟩ := eq_ok_of_spec (Std.Array.index_usize_spec v i h)
  rw [hx, hx']

theorem s3b_pool_max (pk : Usize) (h : pk.val < 6) :
    ∃ m : Usize, Std.Array.index_usize sim.state.POOL_MAX pk = ok m ∧ pk.val < OsuModel.Sim.poolMax.size ∧
      ∀ h', m.val = OsuModel.Sim.poolMax[pk.val]'h' := by
  have hl : sim.state.POOL_MAX.val = [100#usize, 100#usize, 100#usize, 20#usize, 200#usize, 200#usize] := by
    unfold sim.state.POOL_MAX; rfl
  have h' : pk.val < sim.state.POOL_MAX.val.length := by rw [hl]; simpa using h
  refine ⟨_, s3b_arr_index _ _ h', by simp [OsuModel.Sim.poolMax]; omega, fun _ => ?_⟩
  simp only [hl]
  have : pk.val = 0 ∨ pk.val = 1 ∨ pk.val = 2 ∨ pk.val = 3 ∨ pk.val = 4 ∨ pk.val = 5 := by omega
  rcases this with e | e | e | e | e | e <;> simp [e, OsuModel.Sim.poolMax]

/-- spec `poolReturn` on an arbitrary state (in range) -/
theorem s3b_poolReturn_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (pk k : Nat) (h : pk < S.pools.size)
    (hm : pk < OsuModel.Sim.poolMax.size) :
    OsuModel.Sim.Sim.poolReturn pk k C S =
      if OsuModel.Sim.poolMax[pk] ≤ (S.pools[pk]).length then .ok ((), S)
      else .ok ((), { S with pools := S.pools.set pk (some k :: S.pools[pk]) }) := by
  unfold OsuModel.Sim.Sim.poolReturn
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind, OsuModel.Sim.Sim.getA, dif_pos h, dif_pos hm,
    simM_pure, OsuModel.Sim.Sim.setA, ge_iff_le]
  split <;> rfl

theorem sim.step.pool_return_refines (tn fo) (c : sim.state.Ctx) (s : sim.state.St) (pk k : Usize)
    (hpk : pk.val < s.pools.val.length) (h6 : pk.val < 6) :
    ∃ s', sim.step.pool_return s pk k = ok s' ∧
      OsuModel.Sim.Sim.poolReturn pk.val k.val (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn s') ∧
      (∃ pl', s' = { s with pools := pl' }) ∧ s'.pools.val.length = s.pools.val.length := by
  have hpk' : pk.val < (simStS tn s).pools.size := by simp [s3b_stS_pools, hpk]
  obtain ⟨m, hm, hms, hmv⟩ := s3b_pool_max pk h6
  rw [s3b_poolReturn_spec _ _ _ _ hpk' hms]
  have hPv : (simStS tn s).pools[pk.val]'hpk' = s3b_poolS (s.pools.val[pk.val]'hpk) := by simp [s3b_stS_pools]
  rw [hPv, ← hmv hms]
  have hlen : (s3b_poolS (s.pools.val[pk.val]'hpk)).length = (s.pools.val[pk.val]'hpk).val.length := by
    simp [s3b_poolS]
  rw [hlen]
  unfold sim.step.pool_return
  simp only [vec_index_eq _ _ hpk, bind_ok, hm, vec_index_mut_eq _ _ hpk]
  by_cases hc : (s.pools.val[pk.val]'hpk).val.length < m.val
  · have hlt : alloc.vec.Vec.len (s.pools.val[pk.val]'hpk) < m := by
      show (alloc.vec.Vec.len _).val < m.val; simpa using hc
    have hm200 : m.val ≤ 200 := by
      rw [hmv hms]; have : pk.val = 0 ∨ pk.val = 1 ∨ pk.val = 2 ∨ pk.val = 3 ∨ pk.val = 4 ∨ pk.val = 5 := by omega
      rcases this with e | e | e | e | e | e <;> simp [e, OsuModel.Sim.poolMax]
    have hcap : (s.pools.val[pk.val]'hpk).val.length < Usize.max := by
      have : (200 : Nat) < Usize.max := by scalar_tac
      omega
    have hle : ¬ m.val ≤ (s.pools.val[pk.val]'hpk).val.length := by omega
    refine ⟨{ s with pools := s.pools.set pk (vpush _ (some k) hcap) }, ?_, ?_, ⟨_, rfl⟩, by simp [alloc.vec.Vec.set]⟩
    · simp [hlt, vec_push_ok _ _ hcap]
    · rw [if_neg hle]
      have e := s3b_stS_upd tn s s.insts (s.pools.set pk (vpush _ (some k) hcap))
      simp only [] at e
      rw [e, s3b_pools_set s pk hpk]
      have : s3b_poolS (vpush _ (some k) hcap) = some k.val :: s3b_poolS (s.pools.val[pk.val]'hpk) := by
        simp [s3b_poolS]
      rw [this]; rfl
  · have hlt : ¬ alloc.vec.Vec.len (s.pools.val[pk.val]'hpk) < m := by
      intro h; apply hc; have : (alloc.vec.Vec.len _).val < m.val := h; simpa using this
    have hle : m.val ≤ (s.pools.val[pk.val]'hpk).val.length := by omega
    refine ⟨s, by simp [hlt], by rw [if_pos hle], ⟨s.pools, rfl⟩, rfl⟩

/-! ## `withAbs` halves -/
/-- `with_abs_begin`: saves the delay and sets it to `t - now` (`absSeq`). -/
theorem sim.step.with_abs_begin_eq (s : sim.state.St) (k : Usize) (now t : F64) (hk : k.val < s.insts.val.length) :
    sim.step.with_abs_begin s k now t = ok ((s.insts.val[k.val]'hk).tf.delay,
      { s with insts := s.insts.set k ({ s.insts.val[k.val]'hk with tf := { (s.insts.val[k.val]'hk).tf with delay := t - now } }) }) := by
  simp [sim.step.with_abs_begin, vec_index_eq _ _ hk, vec_index_mut_eq _ _ hk, sim.transforms.abs_seq,
    float.F64.sub]

/-- `with_abs_end`: restores the delay. -/
theorem sim.step.with_abs_end_eq (s : sim.state.St) (k : Usize) (saved : F64) (hk : k.val < s.insts.val.length) :
    sim.step.with_abs_end s k saved = ok
      { s with insts := s.insts.set k ({ s.insts.val[k.val]'hk with tf := { (s.insts.val[k.val]'hk).tf with delay := saved } }) } := by
  simp [sim.step.with_abs_end, vec_index_mut_eq _ _ hk]

theorem s3b_arr_modify {α} (a : _root_.Array α) (k : Nat) (h : k < a.size) (f : α → α) :
    a.modify k f = a.set k (f a[k]) := by
  apply Array.ext
  · simp
  · intro i h1 h2; simp only [Array.getElem_modify, Array.getElem_set]; by_cases e : k = i <;> simp [e]

/-- spec `withAbs` on an in-range instance -/
theorem s3b_withAbs_spec (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) (k : Nat) (now t : F64)
    (f : OsuModel.Sim.TObj → OsuModel.Sim.TObj) (hk : k < S.insts.size) :
    OsuModel.Sim.Sim.withAbs k now t f C S = .ok ((), { S with insts := (S.insts.set k
      { S.insts[k] with tf := { f (OsuModel.Sim.absSeq S.insts[k].tf now t) with delay := S.insts[k].tf.delay } }) }) := by
  unfold OsuModel.Sim.Sim.withAbs OsuModel.Sim.Sim.modifyInst
  simp only [simM_bind, OsuModel.Sim.Sim.st, simM_get, Except.bind, OsuModel.Sim.Sim.checkIdx, if_pos hk, simM_pure,
    simM_modify]
  rw [s3b_arr_modify _ _ hk]

end OsuProofs
