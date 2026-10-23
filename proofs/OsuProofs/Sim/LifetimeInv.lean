import OsuProofs.Sim.Lifetime
/-
  sim8: `simLifeInv`, the lifetime-chain part of the step invariant (STATE "[sim8 -> simcore3]").
  `s8LC` is the core kept by every lifetime function (also in the middle of the newly-dead scan, where `active`
  may still hold just-killed objects); `simLifeInv` adds `active ⊆ alive`, restored by the active filter.
  Budget: `SimARInv` carries `b + simFut s * (4n+8)`: every Future object still owes one `became_alive`
  (two `update_state_from_result` calls, 2·(n+n+4)); the caller chooses `b` per step.
-/
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- number of objects not yet alive -/
def simFut (s : sim.state.St) : Nat :=
  (s.objs.val.map (fun o => match o.life with | .Future => 1 | _ => 0)).sum

/-- instance slots still owed to Future objects (`became_alive` takes at most nested + 2) -/
def simFutW (s : sim.state.St) : Nat :=
  (s.objs.val.map (fun o => match o.life with | .Future => o.nested.val.length + 2 | _ => 0)).sum

/-- the future order from `next_future` on lists exactly the pending (Future) objects, without duplicates -/
def simFutOK (s : sim.state.St) : Prop :=
  (∀ x ∈ s.future_order.val, x.val < s.objs.val.length) ∧
  (∀ k (hk : k < s.future_order.val.length), s.next_future.val ≤ k →
    ∀ h : (s.future_order.val[k]'hk).val < s.objs.val.length,
      (s.objs.val[(s.future_order.val[k]'hk).val]'h).life = .Future) ∧
  (s.future_order.val.drop s.next_future.val).Nodup

/-- core lifetime invariant (holds throughout the lifetime phase) -/
structure s8LC (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop)
    (b n CS : Nat) (c : sim.state.Ctx) (s : sim.state.St) : Prop where
  ar : SimARInv tn fo P (b + simFut s * (4 * n + 8)) n c s 0 0 0
  lp : simLP s
  pl : 6 ≤ s.pools.val.length
  pool : simPoolOk s
  dnd : ((s.dict_slots.val.filterMap id).map (·.val)).Nodup
  dal : ∀ x, some x ∈ s.dict_slots.val → ∃ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).life = .Alive
  ald : ∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).life = .Alive → ∃ x, some x ∈ s.dict_slots.val ∧ x.val = j
  frl : ∀ x ∈ s.free_list.val, ∃ h : x.val < s.dict_slots.val.length, s.dict_slots.val[x.val]'h = none
  frn : s.free_list.val.Nodup
  nfr : ∀ x (h : x < s.dict_slots.val.length), s.dict_slots.val[x]'h = none → ∃ y ∈ s.free_list.val, y.val = x
  dlen : s.dict_slots.val.length ≤ s.objs.val.length
  actl : ∀ x ∈ s.active.val, x.val < s.objs.val.length
  actnd : s.active.val.Nodup
  actnf : ∀ x ∈ s.active.val, ∀ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).life ≠ .Future
  aal : ∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).life = .Alive → ∃ x ∈ s.active.val, x.val = j
  cc : s.child_counter.val + simFut s ≤ s.objs.val.length
  ins : s.insts.val.length + simFutW s < Usize.max
  cs : ∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).completed_spins.val ≤ CS
  tk : ∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).tick_insts.val.length ≤ (s.objs.val[j]'h).nested.val.length
  tkv : ∀ j (h : j < s.objs.val.length), ∀ x ∈ (s.objs.val[j]'h).tick_insts.val, x.val < s.insts.val.length
  spt : ∀ j (h : j < s.objs.val.length) (hj : j < c.pb.objects.val.length), (s.objs.val[j]'h).life = .Alive →
    (c.pb.objects.val[j]'hj).h.kind = .Spinner →
    (s.objs.val[j]'h).tick_live.val.length = (c.pb.objects.val[j]'hj).nested.val.length ∧
    (s.objs.val[j]'h).tick_insts.val.length = (c.pb.objects.val[j]'hj).nested.val.length
  ftr : s.first_lifetime_update = true → ∀ j (h : j < s.objs.val.length), (s.objs.val[j]'h).life = .Future
  fut : s.first_lifetime_update = false → simFutOK s

/-- the lifetime part of the step invariant: the core plus `active` = alive objects (both directions) -/
structure simLifeInv (tn : Nat → String) (fo : alloc.vec.Vec Usize) (P : Nat → sim.transforms.TObj → Prop)
    (b n CS : Nat) (c : sim.state.Ctx) (s : sim.state.St) : Prop extends s8LC tn fo P b n CS c s where
  aact : ∀ x ∈ s.active.val, ∀ h : x.val < s.objs.val.length, (s.objs.val[x.val]'h).life = .Alive

end OsuProofs
