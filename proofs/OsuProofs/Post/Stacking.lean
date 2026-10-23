/-
`beatmap::processor` stacking (Rust) refines `OsuModel.Beatmap.OsuBeatmapProcessor.applyStacking*`.
Loops via `loop_fold_gen'` + `loop_step`; ∃-form callee refinements are turned into equations with
`Classical.choose` (`*_R` result functions) so that `simp` can evaluate Rust loop bodies.
-/
import OsuProofs.Post.Processor
import OsuProofs.Beatmap.Objects
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

theorem ssh_full (h : beatmap.objects.OsuHitObject) (val : I32) :
    ∃ v, beatmap.objects.set_stack_height h val = ok { h with stack_height := val, nested := v } ∧
      OsuHitObject.setStackHeight (abs h) (abs val) = abs ({ h with stack_height := val, nested := v } : beatmap.objects.OsuHitObject) := by
  let g := fun (no : beatmap.objects.NestedObject) => { no with stack_height := val }
  obtain ⟨v, hl, hv⟩ := loop_fold_gen' (fun x => beatmap.objects.set_stack_height_loop.body val x.1 x.2) (·.2)
    h.nested.val.length (by have := h.nested.property; omega)
    (fun x => x.1.val.length = h.nested.val.length) (fun x => x.1.val)
    (fun k L => L.modify k g) (fun y L => y.val = L)
    (by loop_step [beatmap.objects.set_stack_height_loop.body, vec_index_mut_usize_ok, vec_set_val', list_modify_set, g])
    (by loop_end [beatmap.objects.set_stack_height_loop.body])
    (h.nested, 0#usize) rfl (by simp)
  simp only at hl hv
  refine ⟨v, ?_, ?_⟩
  · unfold beatmap.objects.set_stack_height
    rw [show beatmap.objects.set_stack_height_loop h.nested val 0#usize = ok v by
      unfold beatmap.objects.set_stack_height_loop; exact hl]
    simp only [bind_ok]
  · rw [show (0#usize : Usize).val = 0 from rfl, iterR_modify_map] at hv
    simp [OsuHitObject.setStackHeight, abs, hv, g, Function.comp_def]

/-- the Rust result of `set_stack_height` (only the nested vector is not given in closed form) -/
noncomputable def sshR (h : beatmap.objects.OsuHitObject) (v : I32) : beatmap.objects.OsuHitObject :=
  { h with stack_height := v, nested := (ssh_full h v).choose }
theorem ssh_ok (h : beatmap.objects.OsuHitObject) (v : I32) :
    beatmap.objects.set_stack_height h v = ok (sshR h v) :=
  (ssh_full h v).choose_spec.1
@[simp] theorem ssh_abs (h : beatmap.objects.OsuHitObject) (v : I32) :
    (abs (sshR h v) : OsuHitObject) = (abs h : OsuHitObject).setStackHeight (abs v) :=
  (ssh_full h v).choose_spec.2.symm
@[simp] theorem sshR_kind (h : beatmap.objects.OsuHitObject) (v : I32) : (sshR h v).kind = h.kind := rfl
@[simp] theorem sshR_start (h : beatmap.objects.OsuHitObject) (v : I32) : (sshR h v).start_time = h.start_time := rfl
@[simp] theorem sshR_pos (h : beatmap.objects.OsuHitObject) (v : I32) : (sshR h v).position = h.position := rfl
@[simp] theorem sshR_sh (h : beatmap.objects.OsuHitObject) (v : I32) : (sshR h v).stack_height = v := rfl

theorem near_eq (a b : net.osutk.Vector2) :
    beatmap.processor.near a b = ok (OsuBeatmapProcessor.near (abs a) (abs b)) := by
  obtain ⟨r, h1, h2⟩ := beatmap.processor.near_refines a b
  rw [h1, h2]; rfl

theorem i32S_wsub (a b : I32) : i32S (core.num.I32.wrapping_sub a b) = i32S a - i32S b := rfl

/-- every slider path satisfies the `end_position` side condition -/
def hosOk (l : List beatmap.objects.OsuHitObject) : Prop :=
  ∀ h ∈ l, ∀ s, h.kind = .Slider s → obPathOk s.path

theorem hosOk_set (l : List beatmap.objects.OsuHitObject) (k : Nat) (x : beatmap.objects.OsuHitObject)
    (hl : hosOk l) (hx : ∀ s, x.kind = .Slider s → obPathOk s.path) : hosOk (l.set k x) := by
  intro h hm s hs
  rcases List.mem_or_eq_of_mem_set hm with hm | rfl
  · exact hl h hm s hs
  · exact hx s hs

/-- `for j in [k+1 : i+1]`: shift the stack height of the objects ending near `nEnd` (stack_circle, slider case). -/
def scInnerG (nEnd : Vec2) (off : Int32) (k : Nat) (L : List OsuHitObject) : List OsuHitObject :=
  if OsuBeatmapProcessor.near nEnd L[k]!.position then L.set k (L[k]!.setStackHeight (L[k]!.stackHeight - off)) else L

theorem sc_inner (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (i : Usize) (nEnd : net.osutk.Vector2)
    (off : I32) (j : Usize) (hi : i.val < hos.val.length) (hj : j.val ≤ i.val + 1) (hok : hosOk hos.val) :
    ∃ r, beatmap.processor.stack_circle_loop0_loop0 hos i nEnd off j = ok r ∧ r.val.length = hos.val.length ∧
      hosOk r.val ∧
      r.val.map (abs : _ → OsuHitObject) =
        iterR (fun k s => .yield (scInnerG (abs nEnd) (abs off) k s)) j.val (i.val + 1 - j.val) (hos.val.map abs) := by
  have hmax : i.val + 1 ≤ Usize.max := by have := hos.property; omega
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => beatmap.processor.stack_circle_loop0_loop0.body i nEnd off x.1 x.2)
    (·.2) (i.val + 1) hmax
    (fun x => x.1.val.length = hos.val.length ∧ hosOk x.1.val) (fun x => x.1.val.map (abs : _ → OsuHitObject))
    (fun k L => scInnerG (abs nEnd) (abs off) k L)
    (fun y L => y.val.length = hos.val.length ∧ hosOk y.val ∧ y.val.map abs = L)
    (by
      intro t hI hlt j1 hj1 hj1v
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i hmax
      have hlt' : t.2.val < t.1.val.length := by omega
      have hc : t.2 < i1 := by show t.2.val < i1.val; omega
      have hc' : t.2.val < i1.val := by omega
      have hget : (t.1.val.map (abs : _ → OsuHitObject))[t.2.val]! = abs (t.1.val[t.2.val]'hlt') := by
        rw [getElem!_pos _ _ (by simpa using hlt')]; simp
      unfold scInnerG; rw [hget]
      by_cases hn : OsuBeatmapProcessor.near (abs nEnd) (abs (t.1.val[t.2.val]'hlt') : OsuHitObject).position = true
      · refine ⟨(alloc.vec.Vec.set t.1 t.2 (sshR (t.1.val[t.2.val]'hlt')
            (core.num.I32.wrapping_sub (t.1.val[t.2.val]'hlt').stack_height off)), j1), ?_, rfl, ?_, ?_⟩
        · simp [beatmap.processor.stack_circle_loop0_loop0.body, hi1, hc, hc', vec_index_usize_ok _ _ hlt',
            near_eq, vec_index_mut_usize_ok _ _ hlt', ssh_ok, hj1, lift]
          simp only [abs] at hn ⊢; simp [hn]
        · simp only [hn, if_true, vec_set_val', List.map_set, ssh_abs]
          congr 2
        · refine ⟨by simp [vec_set_val', hI.1], ?_⟩
          rw [vec_set_val']
          refine hosOk_set _ _ _ hI.2 ?_
          intro s hs; exact hI.2 _ (List.getElem_mem _) s hs
      · refine ⟨(t.1, j1), ?_, rfl, ?_, hI⟩
        · simp [beatmap.processor.stack_circle_loop0_loop0.body, hi1, hc, hc', vec_index_usize_ok _ _ hlt',
            near_eq, hj1]
          simp only [abs] at hn ⊢; simp [hn]
        · simp [hn])
    (by
      intro t hI hge
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i hmax
      have hc : ¬ t.2 < i1 := by show ¬ t.2.val < i1.val; omega
      have hc' : ¬ t.2.val < i1.val := by omega
      exact ⟨t.1, by simp [beatmap.processor.stack_circle_loop0_loop0.body, hi1, hc, hc'], hI.1, hI.2, rfl⟩)
    (hos, j) ⟨rfl, hok⟩ hj
  exact ⟨y, by unfold beatmap.processor.stack_circle_loop0_loop0; exact hl, hy.1, hy.2.1, hy.2.2⟩

/-! ## `stack_slider` (the `objectI.isSlider` branch of `applyStacking`) -/

/-- spec body of the slider loop (state: hos, objectI, objectIIdx, nn), copied from `applyStacking` -/
def slF (thrD : F64) (_x : Nat) (s : Array OsuHitObject × OsuHitObject × Nat × Int) :
    Id (ForInStep (Array OsuHitObject × OsuHitObject × Nat × Int)) :=
  if s.2.2.2 - 1 < ((0 : Nat) : Int) then pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2 - 1))
  else if s.1[(s.2.2.2 - 1).toNat]!.isSpinner = true then pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2 - 1))
  else if thrD < s.1[s.2.2.1]!.startTime - s.1[(s.2.2.2 - 1).toNat]!.startTime then
    pure (ForInStep.done (s.1, s.1[s.2.2.1]!, s.2.2.1, s.2.2.2 - 1))
  else if OsuBeatmapProcessor.near s.1[(s.2.2.2 - 1).toNat]!.endPosition s.1[s.2.2.1]!.position = true then
    pure (ForInStep.yield
      (s.1.set! (s.2.2.2 - 1).toNat (s.1[(s.2.2.2 - 1).toNat]!.setStackHeight (s.1[s.2.2.1]!.stackHeight + 1)),
       (s.1.set! (s.2.2.2 - 1).toNat (s.1[(s.2.2.2 - 1).toNat]!.setStackHeight (s.1[s.2.2.1]!.stackHeight + 1)))[(s.2.2.2 - 1).toNat]!,
       (s.2.2.2 - 1).toNat, s.2.2.2 - 1))
  else pure (ForInStep.yield (s.1, s.1[s.2.2.1]!, s.2.2.1, s.2.2.2 - 1))

/-- Rust/spec relation for the slider loop (`go` = not yet broken). -/
def slR (N : Nat) (t : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × I64 × Bool × Usize)
    (s : Array OsuHitObject × OsuHitObject × Nat × Int) : Prop :=
  t.2.2.2.1 = true ∧ t.1.val.length = N ∧ t.1.val.map abs = s.1.toList ∧ t.2.1.val = s.2.2.1 ∧
    t.2.2.1.val = s.2.2.2 ∧ t.2.1.val < N ∧ 0 ≤ t.2.2.1.val ∧ t.2.2.1.val ≤ N ∧ hosOk t.1.val ∧ N < 2^62

theorem arr_get_abs (v : alloc.vec.Vec beatmap.objects.OsuHitObject) (A : Array OsuHitObject)
    (hA : v.val.map abs = A.toList) (k : Nat) (hk : k < v.val.length) : A[k]! = abs (v.val[k]'hk) := by
  rw [getElem!_pos A k (by rw [← Array.length_toList, ← hA]; simpa using hk)]
  have : A.toList[k]'(by rw [← hA]; simpa using hk) = abs (v.val[k]'hk) := by simp [← hA]
  simpa using this

theorem ss_step (start : Usize) (hs0 : start.val = 0) (n : Usize) (thr : F32) (N : Nat) (hn : n.val = N)
    (h64 : System.Platform.numBits = 64) (hNmax : N + 2 ≤ Usize.max)
    (t : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × I64 × Bool × Usize)
    (s : Array OsuHitObject × OsuHitObject × Nat × Int) (hR : slR N t s) (hlt : t.2.2.2.2.val < N + 1) :
    (∀ s', slF (F32.toF64 thr) t.2.2.2.2.val s = .yield s' → ∃ t', beatmap.processor.stack_slider_loop.body start n thr
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 = ok (.cont t') ∧ t'.2.2.2.2.val = t.2.2.2.2.val + 1 ∧ slR N t' s') ∧
    (∀ s', slF (F32.toF64 thr) t.2.2.2.2.val s = .done s' → ∃ y,
      (beatmap.processor.stack_slider_loop.body start n thr t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 = ok (.done y) ∨
        ∃ t', beatmap.processor.stack_slider_loop.body start n thr t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 = ok (.cont t') ∧
          beatmap.processor.stack_slider_loop.body start n thr t'.1 t'.2.1 t'.2.2.1 t'.2.2.2.1 t'.2.2.2.2 = ok (.done y)) ∧
      y.val.map abs = s'.1.toList ∧ hosOk y.val ∧ y.val.length = N) := by
  obtain ⟨hv, oi, nn, go, fuel⟩ := t
  obtain ⟨A, ob, oN, nI⟩ := s
  obtain ⟨hgo, hlen, hA, hoi, hnn, hoiN, hnn0, hnnN, hok, hN⟩ := hR
  simp only at hgo hlen hA hoi hnn hoiN hnn0 hnnN hok hlt ⊢
  subst hgo hoi hnn
  obtain ⟨n1, hn1, hn1v⟩ := usize_add_one n (by have := hv.property; omega)
  obtain ⟨fuel1, hf1, hf1v⟩ := usize_add_one fuel (by omega)
  have hfl : fuel < n1 := by show fuel.val < n1.val; omega
  have hfl' : fuel.val < n1.val := by omega
  have hb0 : ((start.val : Int)).bmod 18446744073709551616 = 0 := by simp [hs0]
  obtain ⟨nn1, hnn1, hnn1v⟩ := i64_sub_one nn (by omega) (by omega)
  have hst : (UScalar.hcast .I64 start).val = 0 := by rw [UScalar.hcast_val_eq]; simp [hs0]
  have hbody0 : ∀ t' : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × I64 × Bool × Usize,
      beatmap.processor.stack_slider_loop.body start n thr t'.1 t'.2.1 t'.2.2.1 false t'.2.2.2.2 =
      ok (.done t'.1) := by intro t'; simp [beatmap.processor.stack_slider_loop.body]
  by_cases hneg : nn.val - 1 < 0
  · -- break: `nn < startIndex`
    have hlt0 : nn1 < UScalar.hcast .I64 start := by show nn1.val < (UScalar.hcast .I64 start).val; omega
    have hsp : slF (F32.toF64 thr) fuel.val (A, ob, oi.val, nn.val) = .done (A, ob, oi.val, nn.val - 1) := by
      simp [slF, hneg]; rfl
    rw [hsp]
    refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
    injection h with h; subst h
    refine ⟨hv, Or.inr ⟨(hv, oi, nn1, false, fuel1), ?_, hbody0 _⟩, hA, hok, hlen⟩
    simp [beatmap.processor.stack_slider_loop.body, hn1, hfl, hfl', hf1, hnn1, lift, hlt0, hb0,
      show nn1.val < 0 by omega]
  · have hge : ¬ nn1 < UScalar.hcast .I64 start := by show ¬ nn1.val < (UScalar.hcast .I64 start).val; omega
    have hge' : ¬ nn1.val < 0 := by omega
    have hkv : (IScalar.hcast .Usize nn1).val = (nn.val - 1).toNat := by
      rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
    have hk : (IScalar.hcast .Usize nn1).val < hv.val.length := by omega
    generalize hkk : IScalar.hcast .Usize nn1 = k at hkv hk
    have hrk : (beatmap.processor.stack_slider_loop.body start n thr hv oi nn true fuel) =
        beatmap.processor.stack_slider_loop.body start n thr hv oi nn true fuel := rfl
    have hoil : oi.val < hv.val.length := by omega
    have hAk : A[(nn.val - 1).toNat]! = abs (hv.val[k.val]'hk) := by
      rw [arr_get_abs hv A hA _ (by omega)]; simp only [hkv]
    have hAo : A[oi.val]! = abs (hv.val[oi.val]'hoil) := arr_get_abs hv A hA _ hoil
    have hR' : ∀ hv' : alloc.vec.Vec beatmap.objects.OsuHitObject, ∀ oi' : Usize, ∀ A' : Array OsuHitObject,
        hv'.val.length = N → hv'.val.map abs = A'.toList → oi'.val < N → hosOk hv'.val →
        ∀ ob', slR N (hv', oi', nn1, true, fuel1) (A', ob', oi'.val, nn.val - 1) := by
      intro hv' oi' A' h1 h2 h3 h4 ob'
      exact ⟨rfl, h1, h2, rfl, hnn1v, h3, by show 0 ≤ nn1.val; omega, by show nn1.val ≤ (N : Int); omega, h4, hN⟩
    simp only [slF, show ¬ (nn.val - 1 < ((0 : Nat) : Int)) by omega, if_false, hAk, hAo]
    by_cases hsp : (abs (hv.val[k.val]'hk) : OsuHitObject).isSpinner = true
    · simp only [hsp, if_true]
      refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
      injection h with h; subst h
      refine ⟨(hv, oi, nn1, true, fuel1), ?_, by simp [hf1v], hR' hv oi A hlen hA hoiN hok _⟩
      simp [beatmap.processor.stack_slider_loop.body, hn1, hfl, hfl', hf1, hnn1, lift, hge, hge', hb0, hkk,
        vec_index_usize_ok _ _ hk, is_spinner_ok, hsp]
    · simp only [hsp, if_false, Bool.false_eq_true]
      have hsp' : beatmap.objects.is_spinner (hv.val[k.val]'hk) = ok false := by
        rw [is_spinner_ok]; simpa using hsp
      by_cases hth : F32.toF64 thr < (abs (hv.val[oi.val]'hoil) : OsuHitObject).startTime -
          (abs (hv.val[k.val]'hk) : OsuHitObject).startTime
      · simp only [hth, if_true]
        refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
        injection h with h; subst h
        refine ⟨hv, Or.inr ⟨(hv, oi, nn1, false, fuel1), ?_, hbody0 _⟩, hA, hok, hlen⟩
        have hth' : F32.toF64 thr < (hv.val[oi.val]'hoil).start_time - (hv.val[k.val]'hk).start_time := hth
        simp [beatmap.processor.stack_slider_loop.body, hn1, hfl, hfl', hf1, hnn1, lift, hge, hge', hb0, hkk,
          vec_index_usize_ok _ _ hk, vec_index_usize_ok _ _ hoil, hsp', float.F32.to_f64, float.F64.sub, float.F64.lt, hth']
      · simp only [hth, if_false]
        have hth' : ¬ F32.toF64 thr < (hv.val[oi.val]'hoil).start_time - (hv.val[k.val]'hk).start_time := hth
        have hep := beatmap.objects.end_position_refines (hv.val[k.val]'hk)
          (hok _ (List.getElem_mem _)) h64
        have hnear : beatmap.processor.near (bv2I (OsuHitObject.endPosition (abs (hv.val[k.val]'hk))))
            (hv.val[oi.val]'hoil).position =
            ok (OsuBeatmapProcessor.near (abs (hv.val[k.val]'hk) : OsuHitObject).endPosition
              (abs (hv.val[oi.val]'hoil) : OsuHitObject).position) := by
          rw [near_eq]; rfl
        by_cases hnr : OsuBeatmapProcessor.near (abs (hv.val[k.val]'hk) : OsuHitObject).endPosition
            (abs (hv.val[oi.val]'hoil) : OsuHitObject).position = true
        · simp only [hnr, if_true]
          refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
          injection h with h; subst h
          let x := sshR (hv.val[k.val]'hk) (core.num.I32.wrapping_add (hv.val[oi.val]'hoil).stack_height 1#i32)
          have hxa : (abs x : OsuHitObject) = (abs (hv.val[k.val]'hk) : OsuHitObject).setStackHeight
              ((abs (hv.val[oi.val]'hoil) : OsuHitObject).stackHeight + 1) := by
            simp only [x, ssh_abs]; congr 1
          have hmap : (alloc.vec.Vec.set hv k x).val.map (abs : _ → OsuHitObject) =
              (A.set! (nn.val - 1).toNat ((abs (hv.val[k.val]'hk) : OsuHitObject).setStackHeight
                ((abs (hv.val[oi.val]'hoil) : OsuHitObject).stackHeight + 1))).toList := by
            rw [vec_set_val', List.map_set, hA, hxa, ← hkv]; simp
          refine ⟨(alloc.vec.Vec.set hv k x, k, nn1, true, fuel1), ?_, by simp [hf1v], ?_⟩
          · simp [beatmap.processor.stack_slider_loop.body, hn1, hfl, hfl', hf1, hnn1, lift, hge, hge', hb0, hkk,
              vec_index_usize_ok _ _ hk, vec_index_usize_ok _ _ hoil, hsp', float.F32.to_f64, float.F64.sub,
              float.F64.lt, hth', hep, hnear, hnr, vec_index_mut_usize_ok _ _ hk, ssh_ok, x]
          · have := hR' (alloc.vec.Vec.set hv k x) k _ (by simp [vec_set_val', hlen]) hmap (by omega)
              (by
                rw [vec_set_val']
                refine hosOk_set _ _ _ hok ?_
                intro s hs
                have hx : x.kind = (hv.val[k.val]'hk).kind := rfl
                rw [hx] at hs; exact hok _ (List.getElem_mem _) s hs)
              ((A.set! (nn.val - 1).toNat ((abs (hv.val[k.val]'hk) : OsuHitObject).setStackHeight
                ((abs (hv.val[oi.val]'hoil) : OsuHitObject).stackHeight + 1)))[(nn.val - 1).toNat]!)
            simpa only [hkv] using this
        · simp only [hnr, if_false, Bool.false_eq_true]
          refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
          injection h with h; subst h
          refine ⟨(hv, oi, nn1, true, fuel1), ?_, by simp [hf1v], hR' hv oi A hlen hA hoiN hok _⟩
          simp [beatmap.processor.stack_slider_loop.body, hn1, hfl, hfl', hf1, hnn1, lift, hge, hge', hb0, hkk,
            vec_index_usize_ok _ _ hk, vec_index_usize_ok _ _ hoil, hsp', float.F32.to_f64, float.F64.sub,
            float.F64.lt, hth', hep, hnear, hnr]


theorem ss_loop (start : Usize) (hs0 : start.val = 0) (n : Usize) (thr : F32) (N : Nat) (hn : n.val = N)
    (h64 : System.Platform.numBits = 64) (hNmax : N + 2 ≤ Usize.max)
    (t : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × I64 × Bool × Usize)
    (s : Array OsuHitObject × OsuHitObject × Nat × Int) (hR : slR N t s) (hle : t.2.2.2.2.val ≤ N + 1) :
    ∃ y, beatmap.processor.stack_slider_loop t.1 start n thr t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 = ok y ∧
      y.val.map abs = (iterR (slF (F32.toF64 thr)) t.2.2.2.2.val (N + 1 - t.2.2.2.2.val) s).1.toList ∧ hosOk y.val ∧
      y.val.length = N := by
  have := loop_iterR (fun (x : alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × I64 × Bool × Usize) =>
      beatmap.processor.stack_slider_loop.body start n thr x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (slF (F32.toF64 thr)) (N + 1) (fun x => x.2.2.2.2.val) (slR N) (fun y s => y.val.map abs = s.1.toList ∧ hosOk y.val ∧ y.val.length = N)
    (fun t s hR hlt => ss_step start hs0 n thr N hn h64 hNmax t s hR hlt)
    (by
      intro t s hR hge
      obtain ⟨hgo, hlen, hA, -, -, -, -, -, hok, -⟩ := hR
      obtain ⟨n1, hn1, hn1v⟩ := usize_add_one n (by omega)
      have hc : ¬ t.2.2.2.2 < n1 := by show ¬ t.2.2.2.2.val < n1.val; omega
      have hc' : ¬ t.2.2.2.2.val < n1.val := by omega
      exact ⟨t.1, by simp [beatmap.processor.stack_slider_loop.body, hgo, hn1, hc, hc'], hA, hok, hlen⟩)
    t s hR hle
  obtain ⟨y, hl, hq⟩ := this
  exact ⟨y, by unfold beatmap.processor.stack_slider_loop; exact hl, hq⟩

theorem beatmap.processor.stack_slider_refines (sl : F32) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (i start : Usize) (hs0 : start.val = 0) (hi : i.val < hos.val.length) (hN : hos.val.length < 2^62)
    (hok : hosOk hos.val) (h64 : System.Platform.numBits = 64) (hmax : hos.val.length + 2 ≤ Usize.max) :
    ∃ y, beatmap.processor.stack_slider sl hos i start = ok y ∧
      y.val.map abs = (forIn (m := Id) [:hos.val.length + 1]
        ((hos.val.map abs).toArray, (hos.val.map abs).toArray[i.val]!, i.val, (i.val : Int))
        (slF (F32.toF64 (OsuBeatmapProcessor.stackThreshold sl (hos.val.map abs).toArray[i.val]!)))).1.toList ∧
      hosOk y.val ∧ y.val.length = hos.val.length := by
  let A : Array OsuHitObject := (hos.val.map abs).toArray
  have hA : hos.val.map abs = A.toList := by simp [A]
  have hAi : A[i.val]! = abs (hos.val[i.val]'hi) := arr_get_abs hos A hA _ hi
  obtain ⟨thr, hthr, hthrv⟩ := beatmap.processor.stack_threshold_refines sl (hos.val[i.val]'hi)
  have hthrv' : OsuBeatmapProcessor.stackThreshold sl A[i.val]! = thr := by rw [hAi]; simpa [abs] using hthrv
  have hnn : (UScalar.hcast .I64 i).val = (i.val : Int) := by
    rw [UScalar.hcast_val_eq]; simp; simp only [Int.bmod]; split <;> omega
  obtain ⟨y, hl, hy, hyok, hyl⟩ := ss_loop start hs0 (alloc.vec.Vec.len hos) thr hos.val.length (by simp) h64 hmax
    (hos, i, UScalar.hcast .I64 i, true, 0#usize) (A, A[i.val]!, i.val, (i.val : Int))
    ⟨rfl, rfl, hA, rfl, hnn, hi, by show (0 : Int) ≤ (UScalar.hcast .I64 i).val; rw [hnn]; omega,
      by show (UScalar.hcast .I64 i).val ≤ (hos.val.length : Int); rw [hnn]; omega, hok, hN⟩ (by simp)
  refine ⟨y, ?_, ?_⟩
  · simp only [beatmap.processor.stack_slider, vec_index_eq hos i hi, hthr, bind_ok, lift]
    exact hl
  · exact ⟨by rw [hy, forIn_range_iterR, hthrv']; simp [A], hyok, hyl⟩

/-! ## `stack_circle` (the `objectI.isCircle` branch of `applyStacking`) -/
open ControlFlow in
section


theorem arr_set!_toList {α} (a : Array α) (i : Nat) (x : α) : (a.set! i x).toList = a.toList.set i x := by
  simp [Array.set!]

theorem arr_set!_get_self {α} [Inhabited α] (a : Array α) (i : Nat) (x : α) (h : i < a.size) : (a.set! i x)[i]! = x := by
  rw [getElem!_pos _ _ (by simpa using h)]; simp [Array.set!]

theorem arr_set!_get_ne {α} [Inhabited α] (a : Array α) (i j : Nat) (x : α) (h : i ≠ j) : (a.set! i x)[j]! = a[j]! := by
  simp [Array.set!, getElem!_def, Array.getElem?_setIfInBounds, h]

theorem arr_set!_size {α} (a : Array α) (i : Nat) (x : α) : (a.set! i x).size = a.size := by simp [Array.set!]


/-- spec body of the circle loop (state: hos, extendedStartIndex, objectI, objectIIdx, nn), copied from
`applyStacking` (`thr` = stackThreshold of the outer object `i`) -/
def scF (thr : F32) (i : Nat) (_x : Nat) (s : Array OsuHitObject × Nat × OsuHitObject × Nat × Int) :
    Id (ForInStep (Array OsuHitObject × Nat × OsuHitObject × Nat × Int)) :=
  if s.2.2.2.2 - 1 < 0 then
    pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2 - 1))
  else
    if s.1[(s.2.2.2.2 - 1).toNat]!.isSpinner = true then
      pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2 - 1))
    else
      if
          thr <
            F32.ofInt32
              (s.2.2.1.startTime.toInt32 -
                s.1[(s.2.2.2.2 - 1).toNat]!.endTime.toInt32) then
        pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2 - 1))
      else
        if (s.2.2.2.2 - 1).toNat < s.2.1 then
          if
              ((s.1.set! (s.2.2.2.2 - 1).toNat
                        (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                          0))[(s.2.2.2.2 - 1).toNat]!.isSlider &&
                  OsuBeatmapProcessor.near
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                          (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                            0))[(s.2.2.2.2 - 1).toNat]!.endPosition
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                          (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                            0))[s.2.2.2.1]!.position) =
                true then
            do
            let r ←
              forIn [(s.2.2.2.2 - 1).toNat + 1:i + 1]
                  (s.1.set! (s.2.2.2.2 - 1).toNat
                    (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0))
                  fun j s2 =>
                  if
                      OsuBeatmapProcessor.near
                          (s.1.set! (s.2.2.2.2 - 1).toNat
                                (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                  0))[(s.2.2.2.2 - 1).toNat]!.endPosition
                          s2[j]!.position =
                        true then
                    pure
                      (ForInStep.yield
                        (s2.set! j
                          (s2[j]!.setStackHeight
                            (s2[j]!.stackHeight -
                              ((s.1.set! (s.2.2.2.2 - 1).toNat
                                        (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                          0))[s.2.2.2.1]!.stackHeight -
                                  (s.1.set! (s.2.2.2.2 - 1).toNat
                                        (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                          0))[(s.2.2.2.2 - 1).toNat]!.stackHeight +
                                1)))))
                  else pure (ForInStep.yield s2)
            pure
                (ForInStep.done
                  (r, (s.2.2.2.2 - 1).toNat,
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                        (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0))[s.2.2.2.1]!,
                    s.2.2.2.1, s.2.2.2.2 - 1))
          else
            if
                OsuBeatmapProcessor.near
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                          (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                            0))[(s.2.2.2.2 - 1).toNat]!.position
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                          (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                            0))[s.2.2.2.1]!.position =
                  true then
              pure
                (ForInStep.yield
                  ((s.1.set! (s.2.2.2.2 - 1).toNat
                          (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0)).set!
                      (s.2.2.2.2 - 1).toNat
                      ((s.1.set! (s.2.2.2.2 - 1).toNat
                              (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                0))[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                        ((s.1.set! (s.2.2.2.2 - 1).toNat
                                (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                  0))[s.2.2.2.1]!.stackHeight +
                          1)),
                    (s.2.2.2.2 - 1).toNat,
                    ((s.1.set! (s.2.2.2.2 - 1).toNat
                            (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0)).set!
                        (s.2.2.2.2 - 1).toNat
                        ((s.1.set! (s.2.2.2.2 - 1).toNat
                                (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                  0))[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                          ((s.1.set! (s.2.2.2.2 - 1).toNat
                                  (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                                    0))[s.2.2.2.1]!.stackHeight +
                            1)))[(s.2.2.2.2 - 1).toNat]!,
                    (s.2.2.2.2 - 1).toNat, s.2.2.2.2 - 1))
            else
              pure
                (ForInStep.yield
                  (s.1.set! (s.2.2.2.2 - 1).toNat
                      (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0),
                    (s.2.2.2.2 - 1).toNat,
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                        (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0))[s.2.2.2.1]!,
                    s.2.2.2.1, s.2.2.2.2 - 1))
        else
          if
              (s.1[(s.2.2.2.2 - 1).toNat]!.isSlider &&
                  OsuBeatmapProcessor.near s.1[(s.2.2.2.2 - 1).toNat]!.endPosition
                    s.1[s.2.2.2.1]!.position) =
                true then
            do
            let r ←
              forIn [(s.2.2.2.2 - 1).toNat + 1:i + 1] s.1 fun j s2 =>
                  if
                      OsuBeatmapProcessor.near s.1[(s.2.2.2.2 - 1).toNat]!.endPosition
                          s2[j]!.position =
                        true then
                    pure
                      (ForInStep.yield
                        (s2.set! j
                          (s2[j]!.setStackHeight
                            (s2[j]!.stackHeight -
                              (s.1[s.2.2.2.1]!.stackHeight -
                                  s.1[(s.2.2.2.2 - 1).toNat]!.stackHeight +
                                1)))))
                  else pure (ForInStep.yield s2)
            pure
                (ForInStep.done
                  (r, s.2.1, s.1[s.2.2.2.1]!, s.2.2.2.1, s.2.2.2.2 - 1))
          else
            if
                OsuBeatmapProcessor.near s.1[(s.2.2.2.2 - 1).toNat]!.position
                    s.1[s.2.2.2.1]!.position =
                  true then
              pure
                (ForInStep.yield
                  (s.1.set! (s.2.2.2.2 - 1).toNat
                      (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                        (s.1[s.2.2.2.1]!.stackHeight + 1)),
                    s.2.1,
                    (s.1.set! (s.2.2.2.2 - 1).toNat
                        (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight
                          (s.1[s.2.2.2.1]!.stackHeight + 1)))[(s.2.2.2.2 - 1).toNat]!,
                    (s.2.2.2.2 - 1).toNat, s.2.2.2.2 - 1))
            else
              pure
                (ForInStep.yield
                  (s.1, s.2.1, s.1[s.2.2.2.1]!, s.2.2.2.1, s.2.2.2.2 - 1))

/-- the Rust circle-loop body after the `k < extended_start_index` branch (copied from Generated/Funs) -/
def scRestR (i : Usize) (k object_i_idx : Usize) (nn1 : I64) (go : Bool) (fuel1 : Usize)
    (hos1 : alloc.vec.Vec beatmap.objects.OsuHitObject) (extended_start_index1 : Usize) :
    Result (ControlFlow ((alloc.vec.Vec beatmap.objects.OsuHitObject) × Usize × Usize × I64 × Bool × Usize)
      (Usize × (alloc.vec.Vec beatmap.objects.OsuHitObject))) := do
  let oho2 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      beatmap.objects.OsuHitObject) hos1 k
  let n_end ← beatmap.objects.end_position oho2
  let oho3 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      beatmap.objects.OsuHitObject) hos1 object_i_idx
  let b2 ← beatmap.objects.is_slider oho2
  if b2
  then
    let b3 ← beatmap.processor.near n_end oho3.position
    if b3
    then
      let i5 ←
        lift (core.num.I32.wrapping_sub oho3.stack_height
          oho2.stack_height)
      let offset ← lift (core.num.I32.wrapping_add i5 1#i32)
      let j ← k + 1#usize
      let hos2 ←
        beatmap.processor.stack_circle_loop0_loop0 hos1 i n_end
          offset j
      ok (cont (hos2, extended_start_index1, object_i_idx, nn1,
        false, fuel1))
    else
      let b4 ← beatmap.processor.near oho2.position oho3.position
      if b4
      then
        let sh ←
          lift (core.num.I32.wrapping_add oho3.stack_height 1#i32)
        let (oho4, index_mut_back) ←
          alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice
            beatmap.objects.OsuHitObject) hos1 k
        let oho5 ← beatmap.objects.set_stack_height oho4 sh
        let hos2 := index_mut_back oho5
        ok (cont (hos2, extended_start_index1, k, nn1, go, fuel1))
      else
        ok (cont (hos1, extended_start_index1, object_i_idx, nn1, go,
          fuel1))
  else
    let b3 ← beatmap.processor.near oho2.position oho3.position
    if b3
    then
      let sh ←
        lift (core.num.I32.wrapping_add oho3.stack_height 1#i32)
      let (oho4, index_mut_back) ←
        alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice
          beatmap.objects.OsuHitObject) hos1 k
      let oho5 ← beatmap.objects.set_stack_height oho4 sh
      let hos2 := index_mut_back oho5
      ok (cont (hos2, extended_start_index1, k, nn1, go, fuel1))
    else
      ok (cont (hos1, extended_start_index1, object_i_idx, nn1, go,
        fuel1))

/-- spec circle-loop body after the `k < extendedStartIndex` branch (as `scF`, with the current
array `AB` and start index `extB`) -/
def scRestS (thr : F32) (i : Nat) (AB : Array OsuHitObject) (extB : Nat) (oi : Nat) (nnI : Int) :
    Id (ForInStep (Array OsuHitObject × Nat × OsuHitObject × Nat × Int)) :=
  if
      (AB[(nnI - 1).toNat]!.isSlider &&
          OsuBeatmapProcessor.near AB[(nnI - 1).toNat]!.endPosition
            AB[oi]!.position) =
        true then
    do
    let r ←
      forIn [(nnI - 1).toNat + 1:i + 1] AB fun j s2 =>
          if
              OsuBeatmapProcessor.near AB[(nnI - 1).toNat]!.endPosition
                  s2[j]!.position =
                true then
            pure
              (ForInStep.yield
                (s2.set! j
                  (s2[j]!.setStackHeight
                    (s2[j]!.stackHeight -
                      (AB[oi]!.stackHeight -
                          AB[(nnI - 1).toNat]!.stackHeight +
                        1)))))
          else pure (ForInStep.yield s2)
    pure
        (ForInStep.done
          (r, extB, AB[oi]!, oi, nnI - 1))
  else
    if
        OsuBeatmapProcessor.near AB[(nnI - 1).toNat]!.position
            AB[oi]!.position =
          true then
      pure
        (ForInStep.yield
          (AB.set! (nnI - 1).toNat
              (AB[(nnI - 1).toNat]!.setStackHeight
                (AB[oi]!.stackHeight + 1)),
            extB,
            (AB.set! (nnI - 1).toNat
                (AB[(nnI - 1).toNat]!.setStackHeight
                  (AB[oi]!.stackHeight + 1)))[(nnI - 1).toNat]!,
            (nnI - 1).toNat, nnI - 1))
    else
      pure
        (ForInStep.yield
          (AB, extB, AB[oi]!, oi, nnI - 1))


abbrev CT := alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × Usize × I64 × Bool × Usize
abbrev CS := Array OsuHitObject × Nat × OsuHitObject × Nat × Int

def scR (N i : Nat) (t : CT) (s : CS) : Prop :=
  t.2.2.2.2.1 = true ∧ t.1.val.length = N ∧ t.1.val.map abs = s.1.toList ∧ t.2.1.val = s.2.1 ∧
    t.2.2.1.val = s.2.2.2.1 ∧ t.2.2.2.1.val = s.2.2.2.2 ∧ s.2.2.1 = s.1[s.2.2.2.1]! ∧ t.2.2.1.val ≤ i ∧ i < N ∧
    0 ≤ t.2.2.2.1.val ∧ t.2.2.2.1.val ≤ t.2.2.1.val ∧ hosOk t.1.val ∧ N < 2^62 ∧ t.2.1.val ≤ N

def scBody (iU n : Usize) (thr : F32) (t : CT) :=
  beatmap.processor.stack_circle_loop0.body iU n thr t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2

theorem circ_time (a b : F64) :
    F32.ofInt ((IScalar.cast .I64 (core.num.I32.wrapping_sub (⟨(F64.toInt32 a).toBitVec⟩ : I32)
      (⟨(F64.toInt32 b).toBitVec⟩ : I32))).val) = F32.ofInt32 (F64.toInt32 a - F64.toInt32 b) := by
  have h1 : (IScalar.cast .I64 (core.num.I32.wrapping_sub (⟨(F64.toInt32 a).toBitVec⟩ : I32)
      (⟨(F64.toInt32 b).toBitVec⟩ : I32))).val = (core.num.I32.wrapping_sub (⟨(F64.toInt32 a).toBitVec⟩ : I32)
      (⟨(F64.toInt32 b).toBitVec⟩ : I32)).val := by
    rw [IScalar.cast_val_eq]; simp only [Int.bmod]
    have := (core.num.I32.wrapping_sub (⟨(F64.toInt32 a).toBitVec⟩ : I32) (⟨(F64.toInt32 b).toBitVec⟩ : I32)).hmin
    have := (core.num.I32.wrapping_sub (⟨(F64.toInt32 a).toBitVec⟩ : I32) (⟨(F64.toInt32 b).toBitVec⟩ : I32)).hmax
    simp at *; split <;> omega
  rw [h1, ← i32S_toInt]; rfl



def scInnerA (E : Vec2) (off : Int32) (j : Nat) (s2 : Array OsuHitObject) : Array OsuHitObject :=
  if OsuBeatmapProcessor.near E s2[j]!.position = true then s2.set! j (s2[j]!.setStackHeight (s2[j]!.stackHeight - off)) else s2

theorem scInnerA_toList (E : Vec2) (off : Int32) (j : Nat) (s2 : Array OsuHitObject) :
    (scInnerA E off j s2).toList = scInnerG E off j s2.toList := by
  unfold scInnerA scInnerG
  simp only [Array.getElem!_eq_toList_getElem!]
  split <;> simp [arr_set!_toList, *]

theorem sc_inner_spec (E : Vec2) (off : Int32) (lo hi : Nat) (AB : Array OsuHitObject) :
    (forIn (m := Id) [lo:hi] AB (fun j s2 => if OsuBeatmapProcessor.near E s2[j]!.position = true then
        pure (ForInStep.yield (s2.set! j (s2[j]!.setStackHeight (s2[j]!.stackHeight - off))))
      else pure (ForInStep.yield s2))).toList =
      iterR (fun k s => .yield (scInnerG E off k s)) lo (hi - lo) AB.toList := by
  rw [forIn_range_iterR]
  rw [show (fun (j : Nat) (s2 : Array OsuHitObject) => (if OsuBeatmapProcessor.near E s2[j]!.position = true then
        pure (ForInStep.yield (s2.set! j (s2[j]!.setStackHeight (s2[j]!.stackHeight - off))))
      else pure (ForInStep.yield s2) : Id _)) = fun j s2 => .yield (scInnerA E off j s2) by
    funext j s2; unfold scInnerA; split <;> rfl]
  exact iterR_hom Array.toList (scInnerA E off) (fun k L => scInnerG E off k L) (scInnerA_toList E off) _ _ _



theorem scF_rest (thr : F32) (i x : Nat) (s : CS) (h1 : ¬ s.2.2.2.2 - 1 < 0)
    (h2 : ¬ s.1[(s.2.2.2.2 - 1).toNat]!.isSpinner = true)
    (h3 : ¬ thr < F32.ofInt32 (s.2.2.1.startTime.toInt32 - s.1[(s.2.2.2.2 - 1).toNat]!.endTime.toInt32)) :
    scF thr i x s = if (s.2.2.2.2 - 1).toNat < s.2.1 then
        scRestS thr i (s.1.set! (s.2.2.2.2 - 1).toNat (s.1[(s.2.2.2.2 - 1).toNat]!.setStackHeight 0))
          (s.2.2.2.2 - 1).toNat s.2.2.2.1 s.2.2.2.2
      else scRestS thr i s.1 s.2.1 s.2.2.2.1 s.2.2.2.2 := by
  simp only [scF, h1, h2, h3, if_false, Bool.false_eq_true]
  split <;> rfl



theorem sc_rest (thr : F32) (iU : Usize) (N : Nat) (h64 : System.Platform.numBits = 64)
    (hosB : alloc.vec.Vec beatmap.objects.OsuHitObject) (AB : Array OsuHitObject) (extB k oi : Usize) (nn1 : I64)
    (nnI : Int) (fuel1 : Usize)
    (hB : hosB.val.map abs = AB.toList) (hlenB : hosB.val.length = N) (hokB : hosOk hosB.val) (hextB : extB.val ≤ N)
    (hkI : (nnI - 1).toNat = k.val) (hnn1 : nn1.val = nnI - 1) (hnn0 : 0 ≤ nnI - 1) (hko : k.val < oi.val)
    (hoi : oi.val ≤ iU.val) (hiN : iU.val < N) (hN : N < 2^62) :
    (∀ s', scRestS thr iU.val AB extB.val oi.val nnI = .yield s' → ∃ t',
        scRestR iU k oi nn1 true fuel1 hosB extB = ok (.cont t') ∧ t'.2.2.2.2.2 = fuel1 ∧ scR N iU.val t' s') ∧
    (∀ s', scRestS thr iU.val AB extB.val oi.val nnI = .done s' → ∃ y : Usize × alloc.vec.Vec beatmap.objects.OsuHitObject,
      scRestR iU k oi nn1 true fuel1 hosB extB = ok (.cont (y.2, y.1, oi, nn1, false, fuel1)) ∧
      y.1.val = s'.2.1 ∧ y.2.val.map abs = s'.1.toList ∧ hosOk y.2.val ∧ y.1.val ≤ N ∧ y.2.val.length = N) := by
  have hk : k.val < hosB.val.length := by omega
  have hoil : oi.val < hosB.val.length := by omega
  have hAk : AB[(nnI - 1).toNat]! = abs (hosB.val[k.val]'hk) := by rw [hkI]; exact arr_get_abs hosB AB hB _ hk
  have hAo : AB[oi.val]! = abs (hosB.val[oi.val]'hoil) := arr_get_abs hosB AB hB _ hoil
  have hep := beatmap.objects.end_position_refines (hosB.val[k.val]'hk) (hokB _ (List.getElem_mem _)) h64
  have hsl := beatmap.objects.is_slider_refines (hosB.val[k.val]'hk)
  have hR' : ∀ (hv' : alloc.vec.Vec beatmap.objects.OsuHitObject) (oi' : Usize) (A' : Array OsuHitObject),
      hv'.val.length = N → hv'.val.map abs = A'.toList → oi'.val ≤ iU.val → (nnI - 1) ≤ oi'.val →
      hosOk hv'.val →
      scR N iU.val (hv', extB, oi', nn1, true, fuel1) (A', extB.val, A'[oi'.val]!, oi'.val, nnI - 1) := by
    intro hv' oi' A' h1 h2 h3 h4 h5
    exact ⟨rfl, h1, h2, rfl, rfl, hnn1, rfl, h3, hiN, by show (0 : Int) ≤ nn1.val; omega,
      by show nn1.val ≤ (oi'.val : Int); omega, h5, hN, hextB⟩
  -- the near-position update (both in the slider-not-near and the non-slider case)
  have hupd : ∀ s', (if OsuBeatmapProcessor.near AB[(nnI - 1).toNat]!.position AB[oi.val]!.position = true then
        pure (ForInStep.yield (AB.set! (nnI - 1).toNat (AB[(nnI - 1).toNat]!.setStackHeight (AB[oi.val]!.stackHeight + 1)),
          extB.val, (AB.set! (nnI - 1).toNat (AB[(nnI - 1).toNat]!.setStackHeight (AB[oi.val]!.stackHeight + 1)))[(nnI - 1).toNat]!,
          (nnI - 1).toNat, nnI - 1))
      else pure (ForInStep.yield (AB, extB.val, AB[oi.val]!, oi.val, nnI - 1)) : Id (ForInStep CS)) = .yield s' →
      ∃ t', ((do
        let b4 ← beatmap.processor.near (hosB.val[k.val]'hk).position (hosB.val[oi.val]'hoil).position
        if b4 = true then do
          let (oho4, index_mut_back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
            beatmap.objects.OsuHitObject) hosB k
          let oho5 ← beatmap.objects.set_stack_height oho4 (core.num.I32.wrapping_add (hosB.val[oi.val]'hoil).stack_height 1#i32)
          ok (ControlFlow.cont (index_mut_back oho5, extB, k, nn1, true, fuel1))
        else ok (ControlFlow.cont (hosB, extB, oi, nn1, true, fuel1))) :
          Result (ControlFlow CT (Usize × alloc.vec.Vec beatmap.objects.OsuHitObject))) = ok (.cont t') ∧
        t'.2.2.2.2.2 = fuel1 ∧ scR N iU.val t' s' := by
    intro s' h
    rw [hAk, hAo] at h
    have hn := near_eq (hosB.val[k.val]'hk).position (hosB.val[oi.val]'hoil).position
    by_cases hnr : OsuBeatmapProcessor.near (abs (hosB.val[k.val]'hk) : OsuHitObject).position
        (abs (hosB.val[oi.val]'hoil) : OsuHitObject).position = true
    · rw [if_pos hnr] at h; injection h with h; subst h
      let x := sshR (hosB.val[k.val]'hk) (core.num.I32.wrapping_add (hosB.val[oi.val]'hoil).stack_height 1#i32)
      have hxa : (abs x : OsuHitObject) = (abs (hosB.val[k.val]'hk) : OsuHitObject).setStackHeight
          ((abs (hosB.val[oi.val]'hoil) : OsuHitObject).stackHeight + 1) := by simp only [x, ssh_abs]; congr 1
      have hmap : (alloc.vec.Vec.set hosB k x).val.map (abs : _ → OsuHitObject) =
          (AB.set! (nnI - 1).toNat ((abs (hosB.val[k.val]'hk) : OsuHitObject).setStackHeight
            ((abs (hosB.val[oi.val]'hoil) : OsuHitObject).stackHeight + 1))).toList := by
        rw [vec_set_val', List.map_set, hB, hxa, hkI, arr_set!_toList]
      refine ⟨(alloc.vec.Vec.set hosB k x, extB, k, nn1, true, fuel1), ?_, rfl, ?_⟩
      · have hn' : beatmap.processor.near (hosB.val[k.val]'hk).position (hosB.val[oi.val]'hoil).position = ok true := by
          rw [hn]; simpa [abs] using hnr
        simp only [hn', bind_ok, if_true, vec_index_mut_eq _ _ hk]
        simp [ssh_ok, x]
      · have := hR' (alloc.vec.Vec.set hosB k x) k _ (by simp [vec_set_val', hlenB]) hmap (by omega) (by omega)
          (by
            rw [vec_set_val']
            refine hosOk_set _ _ _ hokB ?_
            intro s hs
            have hx : x.kind = (hosB.val[k.val]'hk).kind := rfl
            rw [hx] at hs; exact hokB _ (List.getElem_mem _) s hs)
        simpa only [hkI] using this
    · rw [if_neg hnr] at h; injection h with h; subst h
      refine ⟨(hosB, extB, oi, nn1, true, fuel1), ?_, rfl, ?_⟩
      · have hn' : beatmap.processor.near (hosB.val[k.val]'hk).position (hosB.val[oi.val]'hoil).position = ok false := by
          rw [hn]; simpa [abs] using hnr
        simp only [hn', bind_ok, Bool.false_eq_true, if_false]
      · rw [← hAo]; exact hR' hosB oi AB hlenB hB hoi (by omega) hokB
  have hnE := near_eq (bv2I (OsuHitObject.endPosition (abs (hosB.val[k.val]'hk)))) (hosB.val[oi.val]'hoil).position
  unfold scRestS scRestR
  simp only [hAk, hAo, vec_index_eq _ _ hk, vec_index_eq _ _ hoil, bind_ok, hep, hsl]
  by_cases hs : (abs (hosB.val[k.val]'hk) : OsuHitObject).isSlider = true
  · by_cases hnr : OsuBeatmapProcessor.near (abs (hosB.val[k.val]'hk) : OsuHitObject).endPosition
        (abs (hosB.val[oi.val]'hoil) : OsuHitObject).position = true
    · have hnE' : beatmap.processor.near (bv2I (OsuHitObject.endPosition (abs (hosB.val[k.val]'hk))))
          (hosB.val[oi.val]'hoil).position = ok true := by rw [hnE]; simpa [abs] using hnr
      simp only [hs, hnr, Bool.and_self, if_true, hnE', bind_ok]
      obtain ⟨j1, hj1, hj1v⟩ := usize_add_one k (by have := hosB.property; omega)
      obtain ⟨r, hr, hrl, hrok, hrv⟩ := sc_inner hosB iU (bv2I (OsuHitObject.endPosition (abs (hosB.val[k.val]'hk))))
        (core.num.I32.wrapping_add (core.num.I32.wrapping_sub (hosB.val[oi.val]'hoil).stack_height
          (hosB.val[k.val]'hk).stack_height) 1#i32) j1 (by omega) (by omega) hokB
      refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
      injection h with h; subst h
      refine ⟨(extB, r), ?_, rfl, ?_, hrok, hextB, by simp only; omega⟩
      · simp only [hj1, bind_ok, lift, hr]
      · simp only
        rw [hrv, hB, hj1v, sc_inner_spec, hkI]
        congr 2
    · have hnE' : beatmap.processor.near (bv2I (OsuHitObject.endPosition (abs (hosB.val[k.val]'hk))))
          (hosB.val[oi.val]'hoil).position = ok false := by rw [hnE]; simpa [abs] using hnr
      simp only [hs, hnr, Bool.and_false, Bool.true_and, Bool.false_eq_true, if_true, if_false, hnE', bind_ok, lift]
      exact ⟨fun s' h => hupd s' (by rw [hAk, hAo]; exact h), fun s' h => by split at h <;> simp at h⟩
  · simp only [hs, Bool.false_and, Bool.false_eq_true, if_false, lift, bind_ok]
    exact ⟨fun s' h => hupd s' (by rw [hAk, hAo]; exact h), fun s' h => by split at h <;> simp at h⟩



theorem sc_step (iU n : Usize) (thr : F32) (N : Nat) (hn : n.val = N) (h64 : System.Platform.numBits = 64)
    (hNmax : N + 2 ≤ Usize.max) (t : CT) (s : CS) (hR : scR N iU.val t s) (hlt : t.2.2.2.2.2.val < N + 1) :
    (∀ s', scF thr iU.val t.2.2.2.2.2.val s = .yield s' → ∃ t', scBody iU n thr t = ok (.cont t') ∧
        t'.2.2.2.2.2.val = t.2.2.2.2.2.val + 1 ∧ scR N iU.val t' s') ∧
    (∀ s', scF thr iU.val t.2.2.2.2.2.val s = .done s' → ∃ y,
      (scBody iU n thr t = ok (.done y) ∨ ∃ t', scBody iU n thr t = ok (.cont t') ∧ scBody iU n thr t' = ok (.done y)) ∧
      y.1.val = s'.2.1 ∧ y.2.val.map abs = s'.1.toList ∧ hosOk y.2.val ∧ y.1.val ≤ N ∧ y.2.val.length = N) := by
  obtain ⟨hv, ext, oi, nn, go, fuel⟩ := t
  obtain ⟨A, eN, ob, oN, nI⟩ := s
  obtain ⟨hgo, hlen, hA, hext, hoi, hnn, hob, hoii, hiN, hnn0, hnno, hok, hN, hextN⟩ := hR
  simp only at hgo hlen hA hext hoi hnn hob hoii hiN hnn0 hnno hok hextN hlt ⊢
  subst hgo hext hoi hnn hob
  obtain ⟨n1, hn1, hn1v⟩ := usize_add_one n (by have := hv.property; omega)
  obtain ⟨fuel1, hf1, hf1v⟩ := usize_add_one fuel (by omega)
  have hfl : fuel < n1 := by show fuel.val < n1.val; omega
  have hfl' : fuel.val < n1.val := by omega
  obtain ⟨nn1, hnn1, hnn1v⟩ := i64_sub_one nn (by omega) (by omega)
  have hbody0 : ∀ t' : CT, t'.2.2.2.2.1 = false → scBody iU n thr t' = ok (.done (t'.2.1, t'.1)) := by
    intro t' h; simp [scBody, beatmap.processor.stack_circle_loop0.body, h]
  have hoil : oi.val < hv.val.length := by omega
  have hAo : A[oi.val]! = abs (hv.val[oi.val]'hoil) := arr_get_abs hv A hA _ hoil
  by_cases hneg : nn.val - 1 < 0
  · have hlt0 : nn1 < 0#i64 := by show nn1.val < (0#i64 : I64).val; simp; omega
    have hsp : scF thr iU.val fuel.val (A, ext.val, A[oi.val]!, oi.val, nn.val) =
        .done (A, ext.val, A[oi.val]!, oi.val, nn.val - 1) := by
      simp [scF, hneg]; rfl
    rw [hsp]
    refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
    injection h with h; subst h
    refine ⟨(ext, hv), Or.inr ⟨(hv, ext, oi, nn1, false, fuel1), ?_, hbody0 _ rfl⟩, rfl, hA, hok, hextN, hlen⟩
    simp [scBody, beatmap.processor.stack_circle_loop0.body, hn1, hfl, hfl', hf1, hnn1, lift, hlt0,
      show nn1.val < 0 by omega]
  · have hge0 : ¬ nn1 < 0#i64 := by show ¬ nn1.val < (0#i64 : I64).val; simp; omega
    have hge' : ¬ nn1.val < 0 := by omega
    have hkv : (IScalar.hcast .Usize nn1).val = (nn.val - 1).toNat := by
      rw [IScalar.hcast_val_eq]; simp only [UScalarTy.Usize_numBits_eq, h64]; omega
    have hk : (IScalar.hcast .Usize nn1).val < hv.val.length := by omega
    generalize hkk : IScalar.hcast .Usize nn1 = k at hkv hk
    have hko : k.val ≠ oi.val := by omega
    have hAk : A[(nn.val - 1).toNat]! = abs (hv.val[k.val]'hk) := by
      rw [arr_get_abs hv A hA _ (by omega)]; simp only [hkv]
    have hR' : ∀ (hv' : alloc.vec.Vec beatmap.objects.OsuHitObject) (ext' oi' : Usize) (A' : Array OsuHitObject),
        hv'.val.length = N → hv'.val.map abs = A'.toList → oi'.val ≤ iU.val → (nn.val - 1) ≤ oi'.val →
        hosOk hv'.val → ext'.val ≤ N →
        scR N iU.val (hv', ext', oi', nn1, true, fuel1) (A', ext'.val, A'[oi'.val]!, oi'.val, nn.val - 1) := by
      intro hv' ext' oi' A' h1 h2 h3 h4 h5 h6
      exact ⟨rfl, h1, h2, rfl, rfl, hnn1v, rfl, h3, hiN, by show (0 : Int) ≤ nn1.val; omega,
        by show nn1.val ≤ (oi'.val : Int); omega, h5, hN, h6⟩
    have hsp' := is_spinner_ok (hv.val[k.val]'hk)
    by_cases hsp : (abs (hv.val[k.val]'hk) : OsuHitObject).isSpinner = true
    · simp only [scF, show ¬ (nn.val - 1 < 0) by omega, if_false, hAk]
      simp only [hsp, if_true]
      refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
      injection h with h; subst h
      refine ⟨(hv, ext, oi, nn1, true, fuel1), ?_, by simp [hf1v], ?_⟩
      · simp [scBody, beatmap.processor.stack_circle_loop0.body, hn1, hfl, hfl', hf1, hnn1, lift, hge0, hge', hkk,
          vec_index_usize_ok _ _ hk, hsp', hsp]
      · exact hR' hv ext oi A hlen hA hoii (by omega) hok hextN
    · have hsp0 := hsp
      rw [Bool.not_eq_true] at hsp; rw [hsp] at hsp'
      have het := beatmap.objects.end_time_refines (hv.val[k.val]'hk)
      by_cases hth : thr < F32.ofInt32 (F64.toInt32 (abs (hv.val[oi.val]'hoil) : OsuHitObject).startTime -
          F64.toInt32 (abs (hv.val[k.val]'hk) : OsuHitObject).endTime)
      · simp only [scF, show ¬ (nn.val - 1 < 0) by omega, if_false, hAk, hsp, Bool.false_eq_true]
        rw [← hAo] at hth
        simp only [hth, if_true]
        refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
        injection h with h; subst h
        refine ⟨(ext, hv), Or.inr ⟨(hv, ext, oi, nn1, false, fuel1), ?_, hbody0 _ rfl⟩, rfl, hA, hok, hextN, hlen⟩
        rw [hAo] at hth
        have hth' : thr < F32.ofInt ((IScalar.cast .I64 (core.num.I32.wrapping_sub
            (⟨(F64.toInt32 (hv.val[oi.val]'hoil).start_time).toBitVec⟩ : I32)
            (⟨(F64.toInt32 (OsuHitObject.endTime (abs (hv.val[k.val]'hk)))).toBitVec⟩ : I32))).val) := by
          rw [circ_time]; exact hth
        simp only [scBody, beatmap.processor.stack_circle_loop0.body, if_true, hn1, hfl, bind_ok, hf1, hnn1, hge0,
          if_false, lift, hkk, vec_index_eq _ _ hk, vec_index_eq _ _ hoil, hsp', het, float.F64.to_i32_sat,
          float.F32.from_i64, float.F32.lt, hth', decide_true, Bool.false_eq_true]
      · have hth0 : ¬ thr < F32.ofInt32 (F64.toInt32 A[oi.val]!.startTime - F64.toInt32 A[(nn.val - 1).toNat]!.endTime) := by
          rw [hAo, hAk]; exact hth
        rw [scF_rest thr iU.val fuel.val (A, ext.val, A[oi.val]!, oi.val, nn.val) (by simp only; omega)
          (by simp only; rw [hAk]; exact hsp0) hth0]
        simp only
        have hth' : ¬ thr < F32.ofInt ((IScalar.cast .I64 (core.num.I32.wrapping_sub
            (⟨(F64.toInt32 (hv.val[oi.val]'hoil).start_time).toBitVec⟩ : I32)
            (⟨(F64.toInt32 (OsuHitObject.endTime (abs (hv.val[k.val]'hk)))).toBitVec⟩ : I32))).val) := by
          rw [circ_time]; exact hth
        have hkoi : k.val < oi.val := by omega
        by_cases hke : k.val < ext.val
        · have hke' : (nn.val - 1).toNat < ext.val := by omega
          have hkeR : k < ext := hke
          rw [if_pos hke']
          let x0 := sshR (hv.val[k.val]'hk) 0#i32
          let A' := A.set! (nn.val - 1).toNat (A[(nn.val - 1).toNat]!.setStackHeight 0)
          have hmap : (alloc.vec.Vec.set hv k x0).val.map (abs : _ → OsuHitObject) = A'.toList := by
            rw [vec_set_val', List.map_set, hA, arr_set!_toList, hkv]; simp only [x0, ssh_abs, hAk, A']; rfl
          have hb := sc_rest thr iU N h64 (alloc.vec.Vec.set hv k x0) A' k k oi nn1 nn.val fuel1 hmap
            (by simp [vec_set_val', hlen])
            (by
              rw [vec_set_val']
              refine hosOk_set _ _ _ hok ?_
              intro s hs
              have hx : x0.kind = (hv.val[k.val]'hk).kind := rfl
              rw [hx] at hs; exact hok _ (List.getElem_mem _) s hs) (by omega) hkv.symm hnn1v (by omega) hkoi hoii hiN hN
          have hR : scBody iU n thr (hv, ext, oi, nn, true, fuel) =
              scRestR iU k oi nn1 true fuel1 (alloc.vec.Vec.set hv k x0) k := by
            simp only [scBody, beatmap.processor.stack_circle_loop0.body, if_true, hn1, hfl, bind_ok, hf1, hnn1, hge0,
              if_false, lift, hkk, vec_index_eq _ _ hk, vec_index_eq _ _ hoil, hsp', het, float.F64.to_i32_sat,
              float.F32.from_i64, float.F32.lt, hth', decide_false, Bool.false_eq_true, hkeR, vec_index_mut_eq _ _ hk]
            simp [ssh_ok, scRestR, lift, x0]
          rw [hR]
          refine ⟨fun s' h => ?_, fun s' h => ?_⟩
          · obtain ⟨t', h1, h2, h3⟩ := hb.1 s' (by rw [hkv]; exact h)
            exact ⟨t', h1, by rw [h2, hf1v], h3⟩
          · obtain ⟨y, h1, h2, h3, h4, h5, h6⟩ := hb.2 s' (by rw [hkv]; exact h)
            exact ⟨y, Or.inr ⟨_, h1, hbody0 _ rfl⟩, h2, h3, h4, h5, h6⟩
        · have hke' : ¬ (nn.val - 1).toNat < ext.val := by omega
          have hkeR : ¬ k < ext := hke
          rw [if_neg hke']
          have hb := sc_rest thr iU N h64 hv A ext k oi nn1 nn.val fuel1 hA hlen hok hextN hkv.symm hnn1v (by omega)
            hkoi hoii hiN hN
          have hR : scBody iU n thr (hv, ext, oi, nn, true, fuel) = scRestR iU k oi nn1 true fuel1 hv ext := by
            simp only [scBody, beatmap.processor.stack_circle_loop0.body, if_true, hn1, hfl, bind_ok, hf1, hnn1, hge0,
              if_false, lift, hkk, vec_index_eq _ _ hk, vec_index_eq _ _ hoil, hsp', het, float.F64.to_i32_sat,
              float.F32.from_i64, float.F32.lt, hth', decide_false, Bool.false_eq_true, hkeR]
            simp [scRestR, lift]
          rw [hR]
          refine ⟨fun s' h => ?_, fun s' h => ?_⟩
          · obtain ⟨t', h1, h2, h3⟩ := hb.1 s' h
            exact ⟨t', h1, by rw [h2, hf1v], h3⟩
          · obtain ⟨y, h1, h2, h3, h4, h5, h6⟩ := hb.2 s' h
            exact ⟨y, Or.inr ⟨_, h1, hbody0 _ rfl⟩, h2, h3, h4, h5, h6⟩



theorem sc_loop (iU n : Usize) (thr : F32) (N : Nat) (hn : n.val = N) (h64 : System.Platform.numBits = 64)
    (hNmax : N + 2 ≤ Usize.max) (t : CT) (s : CS) (hR : scR N iU.val t s) (hle : t.2.2.2.2.2.val ≤ N + 1) :
    ∃ y, beatmap.processor.stack_circle_loop0 t.1 iU n t.2.1 t.2.2.1 thr t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 = ok y ∧
      y.1.val = (iterR (scF thr iU.val) t.2.2.2.2.2.val (N + 1 - t.2.2.2.2.2.val) s).2.1 ∧
      y.2.val.map abs = (iterR (scF thr iU.val) t.2.2.2.2.2.val (N + 1 - t.2.2.2.2.2.val) s).1.toList ∧
      hosOk y.2.val ∧ y.1.val ≤ N ∧ y.2.val.length = N := by
  have := loop_iterR (scBody iU n thr) (scF thr iU.val) (N + 1) (fun x => x.2.2.2.2.2.val) (scR N iU.val)
    (fun y s => y.1.val = s.2.1 ∧ y.2.val.map abs = s.1.toList ∧ hosOk y.2.val ∧ y.1.val ≤ N ∧ y.2.val.length = N)
    (fun t s hR hlt => by
      obtain ⟨h1, h2⟩ := sc_step iU n thr N hn h64 hNmax t s hR hlt
      exact ⟨h1, fun s' h => by
        obtain ⟨y, hy, hy1, hy2, hy3, hy4, hy5⟩ := h2 s' h; exact ⟨y, hy, hy1, hy2, hy3, hy4, hy5⟩⟩)
    (by
      intro t s hR hge
      obtain ⟨hgo, hlen, hA, hext, -, -, -, -, -, -, -, hok, -, hextN⟩ := hR
      obtain ⟨n1, hn1, hn1v⟩ := usize_add_one n (by omega)
      have hc : ¬ t.2.2.2.2.2 < n1 := by show ¬ t.2.2.2.2.2.val < n1.val; omega
      have hc' : ¬ t.2.2.2.2.2.val < n1.val := by omega
      exact ⟨(t.2.1, t.1), by simp [scBody, beatmap.processor.stack_circle_loop0.body, hgo, hn1, hc, hc'], hext, hA, hok,
        hextN, hlen⟩)
    t s hR hle
  obtain ⟨y, hl, hq⟩ := this
  exact ⟨y, by unfold beatmap.processor.stack_circle_loop0; exact hl, hq⟩

theorem beatmap.processor.stack_circle_refines (sl : F32) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (i ext0 : Usize) (hi : i.val < hos.val.length) (hext : ext0.val ≤ hos.val.length) (hN : hos.val.length < 2^62)
    (hok : hosOk hos.val) (h64 : System.Platform.numBits = 64) (hmax : hos.val.length + 2 ≤ Usize.max) :
    ∃ y, beatmap.processor.stack_circle sl hos i ext0 = ok y ∧
      let r := forIn (m := Id) [:hos.val.length + 1]
        ((hos.val.map abs).toArray, ext0.val, (hos.val.map abs).toArray[i.val]!, i.val, (i.val : Int))
        (scF (OsuBeatmapProcessor.stackThreshold sl (hos.val.map abs).toArray[i.val]!) i.val)
      y.1.val = r.2.1 ∧ y.2.val.map abs = r.1.toList ∧ hosOk y.2.val ∧ y.1.val ≤ hos.val.length ∧
        y.2.val.length = hos.val.length := by
  let A : Array OsuHitObject := (hos.val.map abs).toArray
  have hA : hos.val.map abs = A.toList := by simp [A]
  have hAi : A[i.val]! = abs (hos.val[i.val]'hi) := arr_get_abs hos A hA _ hi
  obtain ⟨thr, hthr, hthrv⟩ := beatmap.processor.stack_threshold_refines sl (hos.val[i.val]'hi)
  have hthrv' : OsuBeatmapProcessor.stackThreshold sl A[i.val]! = thr := by rw [hAi]; simpa [abs] using hthrv
  have hnn : (UScalar.hcast .I64 i).val = (i.val : Int) := by
    rw [UScalar.hcast_val_eq]; simp; simp only [Int.bmod]; split <;> omega
  obtain ⟨y, hl, hy1, hy2, hy3, hy4, hy5⟩ := sc_loop i (alloc.vec.Vec.len hos) thr hos.val.length (by simp) h64 hmax
    (hos, ext0, i, UScalar.hcast .I64 i, true, 0#usize) (A, ext0.val, A[i.val]!, i.val, (i.val : Int))
    ⟨rfl, rfl, hA, rfl, rfl, hnn, rfl, le_refl _, hi, by show (0 : Int) ≤ (UScalar.hcast .I64 i).val; rw [hnn]; omega,
      by show (UScalar.hcast .I64 i).val ≤ (i.val : Int); rw [hnn], hok, hN, hext⟩ (by simp)
  refine ⟨y, ?_, ?_⟩
  · simp only [beatmap.processor.stack_circle, vec_index_eq hos i hi, hthr, bind_ok, lift]
    exact hl
  · simp only
    rw [forIn_range_iterR, hthrv']
    exact ⟨by simpa [A] using hy1, by simpa [A] using hy2, hy3, hy4, hy5⟩


end

/-! ## `apply_stacking` (outer reverse pass) -/

/-- the outer spec loop body of `applyStacking` (state: hos, extendedStartIndex, i) -/
def asF (sl : F32) (N : Nat) (_x : Nat) (s : Array OsuHitObject × Nat × Nat) :
    Id (ForInStep (Array OsuHitObject × Nat × Nat)) :=
  if s.2.2 ≤ 0 then pure (ForInStep.done (s.1, s.2.1, s.2.2))
  else if (s.1[s.2.2]!.stackHeight != 0 || s.1[s.2.2]!.isSpinner) = true then
    pure (ForInStep.yield (s.1, s.2.1, s.2.2 - 1))
  else if s.1[s.2.2]!.isCircle = true then do
    let r ← forIn [:N + 1] (s.1, s.2.1, s.1[s.2.2]!, s.2.2, (s.2.2 : Int))
      (scF (OsuBeatmapProcessor.stackThreshold sl s.1[s.2.2]!) s.2.2)
    pure (ForInStep.yield (r.1, r.2.1, s.2.2 - 1))
  else if s.1[s.2.2]!.isSlider = true then do
    let r ← forIn [:N + 1] (s.1, s.1[s.2.2]!, s.2.2, (s.2.2 : Int))
      (slF (F32.toF64 (OsuBeatmapProcessor.stackThreshold sl s.1[s.2.2]!)))
    pure (ForInStep.yield (r.1, s.2.1, s.2.2 - 1))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2 - 1))

theorem applyStacking_eq (sl : F32) (hos : Array OsuHitObject) :
    OsuBeatmapProcessor.applyStacking sl hos = (forIn (m := Id) [:hos.size] (hos, 0, hos.size - 1) (asF sl hos.size)).1 := by
  rfl


abbrev AT := alloc.vec.Vec beatmap.objects.OsuHitObject × Usize × Usize × Usize
abbrev AS := Array OsuHitObject × Nat × Nat

def asR (N : Nat) (t : AT) (s : AS) : Prop :=
  t.1.val.map abs = s.1.toList ∧ t.2.1.val = s.2.1 ∧ t.2.2.1.val = s.2.2 ∧ t.1.val.length = N ∧ hosOk t.1.val ∧
    t.2.1.val ≤ N ∧ t.2.2.1.val < N ∧ N < 2^62 ∧ N + 2 ≤ Usize.max

def asBody (sl : F32) (n : Usize) (t : AT) :=
  beatmap.processor.apply_stacking_loop.body sl n t.1 t.2.1 t.2.2.1 t.2.2.2

theorem i32_bne_zero (x : I32) : ((i32S x) != 0) = (x != 0#i32) := by
  have : (i32S x = 0) ↔ (x = 0#i32) := by
    rw [show (0 : Int32) = i32S 0#i32 from rfl, abs_i32S_inj]
  by_cases h : x = 0#i32
  · simp [h, bne, show i32S 0#i32 = 0 from rfl]
  · have h' : ¬ i32S x = 0 := fun e => h (this.mp e)
    simp [bne, h, h']

theorem as_step (sl : F32) (n : Usize) (N : Nat) (hn : n.val = N) (h64 : System.Platform.numBits = 64)
    (t : AT) (s : AS) (hR : asR N t s) (hlt : t.2.2.2.val < N) :
    (∀ s', asF sl N t.2.2.2.val s = .yield s' → ∃ t', asBody sl n t = ok (.cont t') ∧
        t'.2.2.2.val = t.2.2.2.val + 1 ∧ asR N t' s') ∧
    (∀ s', asF sl N t.2.2.2.val s = .done s' → ∃ y, (asBody sl n t = ok (.done y) ∨
        ∃ t', asBody sl n t = ok (.cont t') ∧ asBody sl n t' = ok (.done y)) ∧
      y.val.map abs = s'.1.toList ∧ hosOk y.val) := by
  obtain ⟨hv, ext, i, fuel⟩ := t
  obtain ⟨A, eN, iN⟩ := s
  obtain ⟨hA, hext, hi, hlen, hok, hextN, hiN, hN, hmax⟩ := hR
  simp only at hA hext hi hlen hok hextN hiN hlt ⊢
  subst hext hi
  have hfl : fuel < n := by show fuel.val < n.val; omega
  have hfl' : fuel.val < n.val := by omega
  by_cases hi0 : i.val ≤ 0
  · have hsp : asF sl N fuel.val (A, ext.val, i.val) = .done (A, ext.val, i.val) := by simp [asF, hi0]; rfl
    rw [hsp]
    refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
    injection h with h; subst h
    have hc : ¬ i > 0#usize := by show ¬ (0#usize : Usize).val < i.val; simp; omega
    exact ⟨hv, Or.inl (by simp [asBody, beatmap.processor.apply_stacking_loop.body, hfl, hfl', hc]), hA, hok⟩
  · have hc : i > 0#usize := by show (0#usize : Usize).val < i.val; simp; omega
    obtain ⟨fuel1, hf1, hf1v⟩ := usize_add_one fuel (by omega)
    obtain ⟨i1, hi1, hi1v⟩ := usize_sub_one i (by omega)
    have hil : i.val < hv.val.length := by omega
    have hAi : A[i.val]! = abs (hv.val[i.val]'hil) := arr_get_abs hv A hA _ hil
    have hR' : ∀ (hv' : alloc.vec.Vec beatmap.objects.OsuHitObject) (ext' : Usize) (A' : Array OsuHitObject),
        hv'.val.map abs = A'.toList → hv'.val.length = N → hosOk hv'.val → ext'.val ≤ N →
        asR N (hv', ext', i1, fuel1) (A', ext'.val, i.val - 1) := by
      intro hv' ext' A' h1 h2 h3 h4
      exact ⟨h1, rfl, by simp only; omega, h2, h3, h4, by simp only; omega, hN, hmax⟩
    have hsh := i32_bne_zero (hv.val[i.val]'hil).stack_height
    have hsp' := is_spinner_ok (hv.val[i.val]'hil)
    have hci := beatmap.objects.is_circle_refines (hv.val[i.val]'hil)
    have hsl := beatmap.objects.is_slider_refines (hv.val[i.val]'hil)
    simp only [asF, hi0, if_false, hAi]
    have hbase : ∀ (hv1 : alloc.vec.Vec beatmap.objects.OsuHitObject) (ext1 : Usize),
        asBody sl n (hv, ext, i, fuel) = ok (.cont (hv1, ext1, i1, fuel1)) →
        ∃ t', asBody sl n (hv, ext, i, fuel) = ok (.cont t') ∧ t'.2.2.2.val = fuel.val + 1 ∧ t' = (hv1, ext1, i1, fuel1) :=
      fun hv1 ext1 h => ⟨_, h, by simp [hf1v], rfl⟩
    have hAeq : (hv.val.map (abs : _ → OsuHitObject)).toArray = A := by
      apply Array.ext' ; simp [hA]
    have hsh' : ((abs (hv.val[i.val]'hil) : OsuHitObject).stackHeight != 0) =
        ((hv.val[i.val]'hil).stack_height != 0#i32) := hsh
    by_cases hskip : ((abs (hv.val[i.val]'hil) : OsuHitObject).stackHeight != 0 ||
        (abs (hv.val[i.val]'hil) : OsuHitObject).isSpinner) = true
    · simp only [hskip, if_true]
      refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
      injection h with h; subst h
      refine ⟨(hv, ext, i1, fuel1), ?_, by simp [hf1v], hR' hv ext A hA hlen hok hextN⟩
      by_cases hb : ((hv.val[i.val]'hil).stack_height != 0#i32) = true
      · have hbv : ¬ (hv.val[i.val]'hil).stack_height.val = 0 := by
          intro h0; apply (bne_iff_ne.mp hb); exact IScalar.eq_of_val_eq (by simpa using h0)
        simp [asBody, beatmap.processor.apply_stacking_loop.body, hfl, hfl', hc, hf1, hi1, vec_index_eq _ _ hil, hbv]
      · have hspin : (abs (hv.val[i.val]'hil) : OsuHitObject).isSpinner = true := by
          rw [hsh'] at hskip; simpa [hb] using hskip
        have hbv : (hv.val[i.val]'hil).stack_height.val = 0 := by simpa using hb
        simp [asBody, beatmap.processor.apply_stacking_loop.body, hfl, hfl', hc, hf1, hi1, vec_index_eq _ _ hil, hbv,
          hsp', hspin]
    · simp only [hskip, if_false, Bool.false_eq_true]
      rw [hsh'] at hskip
      have hx0 : (hv.val[i.val]'hil).stack_height = 0#i32 := by
        by_contra hne; apply hskip; simp [bne_iff_ne.mpr hne]
      have hspin : (abs (hv.val[i.val]'hil) : OsuHitObject).isSpinner = false := by
        cases h : (abs (hv.val[i.val]'hil) : OsuHitObject).isSpinner
        · rfl
        · exfalso; apply hskip; simp [h]
      have hbv : (hv.val[i.val]'hil).stack_height.val = 0 := by rw [hx0]; rfl
      by_cases hcir : (abs (hv.val[i.val]'hil) : OsuHitObject).isCircle = true
      · simp only [hcir, if_true]
        obtain ⟨⟨ye, yh⟩, hy, hy1, hy2, hyok, hy4, hy5⟩ := beatmap.processor.stack_circle_refines sl hv i ext hil
          (by omega) (by omega) hok h64 (by omega)
        rw [hAeq, hlen, hAi] at hy1 hy2
        rw [hlen] at hy4 hy5
        refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
        injection h with h; subst h
        refine ⟨(yh, ye, i1, fuel1), ?_, by simp [hf1v], ?_⟩
        · simp [asBody, beatmap.processor.apply_stacking_loop.body, hfl, hfl', hc, hf1, hi1, vec_index_eq _ _ hil, hbv,
            hsp', hspin, hci, hcir, hy]
        · exact ⟨hy2, hy1, by simp only; omega, hy5, hyok, hy4, by simp only; omega, hN, hmax⟩
      · simp only [hcir, if_false, Bool.false_eq_true]
        rw [Bool.not_eq_true] at hcir
        by_cases hsli : (abs (hv.val[i.val]'hil) : OsuHitObject).isSlider = true
        · simp only [hsli, if_true]
          obtain ⟨y, hy, hy1, hyok, hyl⟩ := beatmap.processor.stack_slider_refines sl hv i 0#usize rfl hil (by omega)
            hok h64 (by omega)
          rw [hAeq, hlen, hAi] at hy1
          rw [hlen] at hyl
          refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
          injection h with h; subst h
          refine ⟨(y, ext, i1, fuel1), ?_, by simp [hf1v], ?_⟩
          · simp [asBody, beatmap.processor.apply_stacking_loop.body, hfl, hfl', hc, hf1, hi1, vec_index_eq _ _ hil,
              hbv, hsp', hspin, hci, hcir, hsl, hsli, hy]
          · exact ⟨hy1, rfl, by simp only; omega, hyl, hyok, hextN, by simp only; omega, hN, hmax⟩
        · simp only [hsli, if_false, Bool.false_eq_true]
          rw [Bool.not_eq_true] at hsli
          refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
          injection h with h; subst h
          refine ⟨(hv, ext, i1, fuel1), ?_, by simp [hf1v], hR' hv ext A hA hlen hok hextN⟩
          simp [asBody, beatmap.processor.apply_stacking_loop.body, hfl, hfl', hc, hf1, hi1, vec_index_eq _ _ hil,
            hbv, hsp', hspin, hci, hcir, hsl, hsli]


theorem beatmap.processor.apply_stacking_refines (sl : F32) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (h0 : 0 < hos.val.length) (hN : hos.val.length < 2^62) (hok : hosOk hos.val) (h64 : System.Platform.numBits = 64) :
    ∃ y, beatmap.processor.apply_stacking sl hos = ok y ∧
      OsuBeatmapProcessor.applyStacking sl (abs hos) = abs y := by
  have hmax : hos.val.length + 2 ≤ Usize.max := by rw [usize_max_64 h64]; omega
  let N := hos.val.length
  let A : Array OsuHitObject := (hos.val.map abs).toArray
  have hA : hos.val.map abs = A.toList := by simp [A]
  obtain ⟨e, he, hev⟩ := usize_sub_one (alloc.vec.Vec.len hos) (by simp; omega)
  have := loop_iterR (asBody sl (alloc.vec.Vec.len hos)) (asF sl N) N (fun x => x.2.2.2.val) (asR N)
    (fun y s => y.val.map abs = s.1.toList ∧ hosOk y.val)
    (fun t s hR hlt => as_step sl (alloc.vec.Vec.len hos) N (by simp [N]) h64 t s hR hlt)
    (by
      intro t s hR hge
      obtain ⟨hA', -, -, -, hok', -⟩ := hR
      have hc : ¬ t.2.2.2 < alloc.vec.Vec.len hos := by show ¬ t.2.2.2.val < (alloc.vec.Vec.len hos).val; simp; omega
      exact ⟨t.1, by simp [asBody, beatmap.processor.apply_stacking_loop.body, hc], hA', hok'⟩)
    (hos, 0#usize, e, 0#usize) (A, 0, N - 1)
    ⟨hA, rfl, by simp [hev, N], rfl, hok, by simp, by simp [hev]; omega, hN, hmax⟩ (by simp)
  obtain ⟨y, hl, hq, -⟩ := this
  refine ⟨y, ?_, ?_⟩
  · simp only [beatmap.processor.apply_stacking, he, bind_ok]
    unfold beatmap.processor.apply_stacking_loop; exact hl
  · rw [applyStacking_eq, forIn_range_iterR]
    have hsz : (abs hos : Array OsuHitObject).size = N := by simp [abs, N]
    have hab : (abs hos : Array OsuHitObject) = A := rfl
    rw [hsz, hab]
    apply Array.ext'
    rw [show (abs y : Array OsuHitObject).toList = y.val.map abs by simp [abs]]
    simpa using hq.symm

@[step] theorem beatmap.processor.apply_stacking_step (sl : F32) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (h0 : 0 < hos.val.length) (hN : hos.val.length < 2^62) (hok : hosOk hos.val) (h64 : System.Platform.numBits = 64) :
    beatmap.processor.apply_stacking sl hos ⦃ r => OsuBeatmapProcessor.applyStacking sl (abs hos) = abs r ⦄ :=
  spec_of_ex (beatmap.processor.apply_stacking_refines sl hos h0 hN hok h64)

/-! ## `apply_stacking_old` (format version < 6) -/

/-- `position2` of `applyStackingOld` -/
def pos2 (h : OsuHitObject) : Vec2 := match h.kind with
  | .slider s => h.position + s.path.positionAt 1
  | _ => h.position

/-- inner spec loop body of `applyStackingOld` (state: hos, startTime, sliderStack) -/
def soF (sl : F32) (i : Nat) (j : Nat) (s : Array OsuHitObject × F64 × Int32) :
    Id (ForInStep (Array OsuHitObject × F64 × Int32)) :=
  if s.2.1 < s.1[j]!.startTime - (OsuBeatmapProcessor.stackThreshold sl s.1[i]!).toF64 then
    pure (ForInStep.done (s.1, s.2.1, s.2.2))
  else if OsuBeatmapProcessor.near s.1[j]!.position s.1[i]!.position = true then
    pure (ForInStep.yield (s.1.set! i (s.1[i]!.setStackHeight (s.1[i]!.stackHeight + 1)),
      (s.1.set! i (s.1[i]!.setStackHeight (s.1[i]!.stackHeight + 1)))[j]!.startTime, s.2.2))
  else if OsuBeatmapProcessor.near s.1[j]!.position (pos2 s.1[i]!) = true then
    pure (ForInStep.yield (s.1.set! j (s.1[j]!.setStackHeight (s.1[j]!.stackHeight - (s.2.2 + 1))),
      (s.1.set! j (s.1[j]!.setStackHeight (s.1[j]!.stackHeight - (s.2.2 + 1))))[j]!.startTime, s.2.2 + 1))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

/-- outer spec loop body of `applyStackingOld` -/
def soG (sl : F32) (N : Nat) (i : Nat) (hos : Array OsuHitObject) : Id (ForInStep (Array OsuHitObject)) :=
  if (hos[i]!.stackHeight != 0 && !hos[i]!.isSlider) = true then pure (ForInStep.yield hos)
  else do
    let r ← forIn [i + 1:N] (hos, hos[i]!.endTime, (0 : Int32)) (soF sl i)
    pure (ForInStep.yield r.1)

theorem applyStackingOld_eq (sl : F32) (hos : Array OsuHitObject) :
    OsuBeatmapProcessor.applyStackingOld sl hos = forIn (m := Id) [:hos.size] hos (soG sl hos.size) := by
  rfl

theorem pos2_nonslider (h : beatmap.objects.OsuHitObject) (hk : ∀ sd, h.kind ≠ .Slider sd) :
    pos2 (abs h) = bv2S h.position := by
  unfold pos2
  cases hh : h.kind with
  | Circle => simp [abs, hh]
  | Spinner sp => simp [abs, hh]
  | Slider sd => exact absurd hh (hk sd)

theorem pos2_slider (h : beatmap.objects.OsuHitObject) (sd : beatmap.objects.SliderData) (hk : h.kind = .Slider sd) :
    pos2 (abs h) = Vec2.add (bv2S h.position) (SliderPath.positionAt (spS sd.path) 1) := by
  unfold pos2
  have : (abs h : OsuHitObject).kind = .slider (abs sd) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
  rw [this]
  show (abs h : OsuHitObject).position + (abs sd : SliderData).path.positionAt 1 = _
  rw [show (abs sd : SliderData).path = abs sd.path from rfl, ob_abs_sliderPath]; rfl

abbrev OT := alloc.vec.Vec beatmap.objects.OsuHitObject × F64 × I32 × Usize × Bool
abbrev OS := Array OsuHitObject × F64 × Int32

def soR (N i : Nat) (t : OT) (s : OS) : Prop :=
  t.2.2.2.2 = true ∧ t.1.val.map abs = s.1.toList ∧ t.2.1 = s.2.1 ∧ i32S t.2.2.1 = s.2.2 ∧ t.1.val.length = N ∧
    hosOk t.1.val ∧ i < t.2.2.2.1.val ∧ N < 2^62

def soBody (sl : F32) (n i : Usize) (t : OT) :=
  beatmap.processor.apply_stacking_old_loop0_loop0.body sl n i t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

theorem proc_F64_ONE : beatmap.processor.F64_ONE = ok (1 : F64) := by
  simp [beatmap.processor.F64_ONE, float.F64.from_bits] <;> decide

theorem pos2_ok (h : beatmap.objects.OsuHitObject) (hp : ∀ s, h.kind = .Slider s → obPathOk s.path)
    (h64 : System.Platform.numBits = 64) :
    (match h.kind with
      | beatmap.objects.ObjectKind.Circle => ok h.position
      | beatmap.objects.ObjectKind.Slider s => do
        let f2 ← beatmap.processor.F64_ONE
        let v ← beatmap.slider_path.position_at s.path f2
        beatmap.vector2.add h.position v
      | beatmap.objects.ObjectKind.Spinner _ => ok h.position) = ok (bv2I (pos2 (abs h))) := by
  unfold pos2
  cases hk : h.kind with
  | Circle => simp [abs, hk]
  | Spinner sp => simp [abs, hk]
  | Slider sd =>
    obtain ⟨h1, h2⟩ := hp sd hk
    simp only [proc_F64_ONE, bind_ok, beatmap.slider_path.position_at_refines sd.path 1 h1 h2 h64,
      beatmap.vector2.add_refines, bv2S_I]
    have : (abs h : OsuHitObject).kind = .slider (abs sd) := by show (abs h.kind : ObjectKind) = _; rw [hk]; rfl
    rw [this]
    show ok (bv2I (Vec2.add (bv2S h.position) (SliderPath.positionAt (spS sd.path) 1))) =
      ok (bv2I ((abs h : OsuHitObject).position + (abs sd : SliderData).path.positionAt 1))
    rw [show (abs sd : SliderData).path = abs sd.path from rfl, ob_abs_sliderPath]; rfl

theorem so_step (sl : F32) (n i : Usize) (N : Nat) (hn : n.val = N) (h64 : System.Platform.numBits = 64)
    (t : OT) (s : OS) (hR : soR N i.val t s) (hlt : t.2.2.2.1.val < N) :
    (∀ s', soF sl i.val t.2.2.2.1.val s = .yield s' → ∃ t', soBody sl n i t = ok (.cont t') ∧
        t'.2.2.2.1.val = t.2.2.2.1.val + 1 ∧ soR N i.val t' s') ∧
    (∀ s', soF sl i.val t.2.2.2.1.val s = .done s' → ∃ y, (soBody sl n i t = ok (.done y) ∨
        ∃ t', soBody sl n i t = ok (.cont t') ∧ soBody sl n i t' = ok (.done y)) ∧
      y.val.map abs = s'.1.toList ∧ hosOk y.val ∧ y.val.length = N) := by
  obtain ⟨hv, st, ss, j, go⟩ := t
  obtain ⟨A, sT, sS⟩ := s
  obtain ⟨hgo, hA, hst, hss, hlen, hok, hij, hN⟩ := hR
  simp only at hgo hA hst hss hlen hok hij hlt ⊢
  subst hgo hst hss
  have hjn : j < n := by show j.val < n.val; omega
  have hjn' : j.val < n.val := by omega
  have hil : i.val < hv.val.length := by omega
  have hjl : j.val < hv.val.length := by omega
  have hji : j.val ≠ i.val := by omega
  have hAi : A[i.val]! = abs (hv.val[i.val]'hil) := arr_get_abs hv A hA _ hil
  have hAj : A[j.val]! = abs (hv.val[j.val]'hjl) := arr_get_abs hv A hA _ hjl
  obtain ⟨thr, hthr, hthrv⟩ := beatmap.processor.stack_threshold_refines sl (hv.val[i.val]'hil)
  have hthrv' : OsuBeatmapProcessor.stackThreshold sl (abs (hv.val[i.val]'hil)) = thr := by simpa [abs] using hthrv
  obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := hv.property; omega)
  have hbody0 : ∀ t' : OT, t'.2.2.2.2 = false → soBody sl n i t' = ok (.done t'.1) := by
    intro t' h; simp [soBody, beatmap.processor.apply_stacking_old_loop0_loop0.body, h]
  have hR' : ∀ (hv' : alloc.vec.Vec beatmap.objects.OsuHitObject) (A' : Array OsuHitObject) (st' : F64) (ss' : I32),
      hv'.val.map abs = A'.toList → hv'.val.length = N → hosOk hv'.val →
      soR N i.val (hv', st', ss', j1, true) (A', st', i32S ss') := by
    intro hv' A' st' ss' h1 h2 h3
    exact ⟨rfl, h1, rfl, rfl, h2, h3, by simp only; omega, hN⟩
  unfold soF
  rw [hAi, hAj, hthrv']
  by_cases hbr : st < (abs (hv.val[j.val]'hjl) : OsuHitObject).startTime - F32.toF64 thr
  · rw [if_pos hbr]
    refine ⟨fun s' h => by simp at h, fun s' h => ?_⟩
    injection h with h; subst h
    refine ⟨hv, Or.inr ⟨(hv, st, ss, j, false), ?_, hbody0 _ rfl⟩, hA, hok, hlen⟩
    have hbr' : st < (hv.val[j.val]'hjl).start_time - F32.toF64 thr := hbr
    simp [soBody, beatmap.processor.apply_stacking_old_loop0_loop0.body, hjn, hjn', vec_index_eq _ _ hil,
      vec_index_eq _ _ hjl, hthr, float.F32.to_f64, float.F64.sub, float.F64.lt, hbr']
  · rw [if_neg hbr]
    have hbr' : ¬ st < (hv.val[j.val]'hjl).start_time - F32.toF64 thr := hbr
    have hp2 := pos2_ok (hv.val[i.val]'hil) (hok _ (List.getElem_mem _)) h64
    have hn1 := near_eq (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position
    have hn2 := near_eq (hv.val[j.val]'hjl).position (bv2I (pos2 (abs (hv.val[i.val]'hil))))
    have hrust : ∀ (r : Result (alloc.vec.Vec beatmap.objects.OsuHitObject × F64 × I32)) (q : alloc.vec.Vec beatmap.objects.OsuHitObject × F64 × I32),
        r = ok q → True := fun _ _ _ => trivial
    by_cases hb1 : OsuBeatmapProcessor.near (abs (hv.val[j.val]'hjl) : OsuHitObject).position
        (abs (hv.val[i.val]'hil) : OsuHitObject).position = true
    · rw [if_pos hb1]
      refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
      injection h with h; subst h
      let x := sshR (hv.val[i.val]'hil) (core.num.I32.wrapping_add (hv.val[i.val]'hil).stack_height 1#i32)
      have hxa : (abs x : OsuHitObject) = (abs (hv.val[i.val]'hil) : OsuHitObject).setStackHeight
          ((abs (hv.val[i.val]'hil) : OsuHitObject).stackHeight + 1) := by simp only [x, ssh_abs]; congr 1
      have hmap : (alloc.vec.Vec.set hv i x).val.map (abs : _ → OsuHitObject) =
          (A.set! i.val ((abs (hv.val[i.val]'hil) : OsuHitObject).setStackHeight
            ((abs (hv.val[i.val]'hil) : OsuHitObject).stackHeight + 1))).toList := by
        rw [vec_set_val', List.map_set, hA, hxa, arr_set!_toList]
      have hjget : (alloc.vec.Vec.set hv i x).val[j.val]'(by simp [vec_set_val']; omega) = hv.val[j.val]'hjl := by
        simp only [vec_set_val']; rw [List.getElem_set_ne (by omega)]
      refine ⟨(alloc.vec.Vec.set hv i x, (hv.val[j.val]'hjl).start_time, ss, j1, true), ?_, by simp [hj1v], ?_⟩
      · have hb1' : beatmap.processor.near (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position = ok true := by
          rw [hn1]; simpa [abs] using hb1
        simp [soBody, beatmap.processor.apply_stacking_old_loop0_loop0.body, hjn, hjn', vec_index_eq _ _ hil,
          vec_index_eq _ _ hjl, hthr, float.F32.to_f64, float.F64.sub, float.F64.lt, hbr', hp2, hb1', lift,
          vec_index_mut_eq _ _ hil, ssh_ok, hj1, x]
        have hix : alloc.vec.Vec.index_usize (alloc.vec.Vec.set hv i x) j = ok (hv.val[j.val]'hjl) := by
          rw [vec_index_usize_ok _ _ (by simp [vec_set_val']; omega), hjget]
        simp only [x] at hix
        split
        · simp [hix]
        · rename_i sd heq
          obtain ⟨h1, h2⟩ := hok _ (List.getElem_mem _) sd heq
          simp [beatmap.slider_path.position_at_refines sd.path 1 h1 h2 h64, beatmap.vector2.add_refines, hix]
        · simp [hix]
      · have := hR' (alloc.vec.Vec.set hv i x) _ (hv.val[j.val]'hjl).start_time ss hmap (by simp [vec_set_val', hlen])
          (by
            rw [vec_set_val']
            refine hosOk_set _ _ _ hok ?_
            intro s hs
            have hx : x.kind = (hv.val[i.val]'hil).kind := rfl
            rw [hx] at hs; exact hok _ (List.getElem_mem _) s hs)
        rw [arr_set!_get_ne _ _ _ _ hji.symm, hAj] at *
        exact this
    · rw [if_neg hb1]
      have hb1' : beatmap.processor.near (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position = ok false := by
        rw [hn1]; simpa [abs] using hb1
      by_cases hb2 : OsuBeatmapProcessor.near (abs (hv.val[j.val]'hjl) : OsuHitObject).position
          (pos2 (abs (hv.val[i.val]'hil))) = true
      · rw [if_pos hb2]
        refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
        injection h with h; subst h
        let x := sshR (hv.val[j.val]'hjl) (core.num.I32.wrapping_sub (hv.val[j.val]'hjl).stack_height
          (core.num.I32.wrapping_add ss 1#i32))
        have hxa : (abs x : OsuHitObject) = (abs (hv.val[j.val]'hjl) : OsuHitObject).setStackHeight
            ((abs (hv.val[j.val]'hjl) : OsuHitObject).stackHeight - (i32S ss + 1)) := by
          simp only [x, ssh_abs]; congr 1
        have hmap : (alloc.vec.Vec.set hv j x).val.map (abs : _ → OsuHitObject) =
            (A.set! j.val ((abs (hv.val[j.val]'hjl) : OsuHitObject).setStackHeight
              ((abs (hv.val[j.val]'hjl) : OsuHitObject).stackHeight - (i32S ss + 1)))).toList := by
          rw [vec_set_val', List.map_set, hA, hxa, arr_set!_toList]
        have hix : alloc.vec.Vec.index_usize (alloc.vec.Vec.set hv j x) j = ok x := by
          rw [vec_index_usize_ok _ _ (by simp [vec_set_val']; omega)]; simp [vec_set_val']
        simp only [x] at hix
        refine ⟨(alloc.vec.Vec.set hv j x, (hv.val[j.val]'hjl).start_time, core.num.I32.wrapping_add ss 1#i32, j1, true),
          ?_, by simp [hj1v], ?_⟩
        · simp [soBody, beatmap.processor.apply_stacking_old_loop0_loop0.body, hjn, hjn', vec_index_eq _ _ hil,
            vec_index_eq _ _ hjl, hthr, float.F32.to_f64, float.F64.sub, float.F64.lt, hbr', hb1', lift,
            vec_index_mut_eq _ _ hjl, ssh_ok, hj1, x]
          split
          · rename_i heq
            rw [pos2_nonslider _ (by intro sd h'; rw [heq] at h'; cases h')] at hb2
            have : beatmap.processor.near (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position = ok true := by
              rw [hn1]; simpa [abs] using hb2
            simp [this, hix]
          · rename_i sd heq
            obtain ⟨h1, h2⟩ := hok _ (List.getElem_mem _) sd heq
            rw [pos2_slider _ sd heq] at hb2
            have : beatmap.processor.near (hv.val[j.val]'hjl).position
                (bv2I (Vec2.add (bv2S (hv.val[i.val]'hil).position) (SliderPath.positionAt (spS sd.path) 1))) = ok true := by
              rw [near_eq]; simpa [abs] using hb2
            simp [beatmap.slider_path.position_at_refines sd.path 1 h1 h2 h64, beatmap.vector2.add_refines, this, hix]
          · rename_i heq
            rw [pos2_nonslider _ (by intro sd h'; rw [heq] at h'; cases h')] at hb2
            have : beatmap.processor.near (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position = ok true := by
              rw [hn1]; simpa [abs] using hb2
            simp [this, hix]
        · have := hR' (alloc.vec.Vec.set hv j x) _ (hv.val[j.val]'hjl).start_time (core.num.I32.wrapping_add ss 1#i32) hmap
            (by simp [vec_set_val', hlen])
            (by
              rw [vec_set_val']
              refine hosOk_set _ _ _ hok ?_
              intro s hs
              have hx : x.kind = (hv.val[j.val]'hjl).kind := rfl
              rw [hx] at hs; exact hok _ (List.getElem_mem _) s hs)
          rw [arr_set!_get_self _ _ _ (by rw [← Array.length_toList, ← hA]; simpa using hjl)]
          rw [show i32S ss + 1 = i32S (core.num.I32.wrapping_add ss 1#i32) from rfl]
          exact this
      · rw [if_neg hb2]
        refine ⟨fun s' h => ?_, fun s' h => by simp at h⟩
        injection h with h; subst h
        refine ⟨(hv, st, ss, j1, true), ?_, by simp [hj1v], hR' hv A st ss hA hlen hok⟩
        simp [soBody, beatmap.processor.apply_stacking_old_loop0_loop0.body, hjn, hjn', vec_index_eq _ _ hil,
          vec_index_eq _ _ hjl, hthr, float.F32.to_f64, float.F64.sub, float.F64.lt, hbr', hb1', lift, hj1]
        split
        · rename_i heq
          rw [pos2_nonslider _ (by intro sd h'; rw [heq] at h'; cases h')] at hb2
          have : beatmap.processor.near (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position = ok false := by
            rw [hn1]; simpa [abs] using hb2
          simp [this]
        · rename_i sd heq
          obtain ⟨h1, h2⟩ := hok _ (List.getElem_mem _) sd heq
          rw [pos2_slider _ sd heq] at hb2
          have : beatmap.processor.near (hv.val[j.val]'hjl).position
              (bv2I (Vec2.add (bv2S (hv.val[i.val]'hil).position) (SliderPath.positionAt (spS sd.path) 1))) = ok false := by
            rw [near_eq]; simpa [abs] using hb2
          simp [beatmap.slider_path.position_at_refines sd.path 1 h1 h2 h64, beatmap.vector2.add_refines, this]
        · rename_i heq
          rw [pos2_nonslider _ (by intro sd h'; rw [heq] at h'; cases h')] at hb2
          have : beatmap.processor.near (hv.val[j.val]'hjl).position (hv.val[i.val]'hil).position = ok false := by
            rw [hn1]; simpa [abs] using hb2
          simp [this]

theorem so_loop (sl : F32) (n i : Usize) (N : Nat) (hn : n.val = N) (h64 : System.Platform.numBits = 64)
    (t : OT) (s : OS) (hR : soR N i.val t s) (hle : t.2.2.2.1.val ≤ N) :
    ∃ y, loop (soBody sl n i) t = ok y ∧
      y.val.map abs = (iterR (soF sl i.val) t.2.2.2.1.val (N - t.2.2.2.1.val) s).1.toList ∧ hosOk y.val ∧
      y.val.length = N := by
  have := loop_iterR (soBody sl n i) (soF sl i.val) N (fun x => x.2.2.2.1.val) (soR N i.val)
    (fun y s => y.val.map abs = s.1.toList ∧ hosOk y.val ∧ y.val.length = N)
    (fun t s hR hlt => so_step sl n i N hn h64 t s hR hlt)
    (by
      intro t s hR hge
      obtain ⟨hgo, hA, -, -, hlen, hok, -⟩ := hR
      have hc : ¬ t.2.2.2.1 < n := by show ¬ t.2.2.2.1.val < n.val; omega
      exact ⟨t.1, by simp [soBody, beatmap.processor.apply_stacking_old_loop0_loop0.body, hgo, hc], hA, hok, hlen⟩)
    t s hR hle
  exact this

theorem so_body_eq : beatmap.processor.apply_stacking_old_loop0_loop1.body =
    beatmap.processor.apply_stacking_old_loop0_loop0.body := by
  funext sl n i hos st ss j go; rfl

def soGA (sl : F32) (N : Nat) (i : Nat) (hos : Array OsuHitObject) : Array OsuHitObject :=
  if (hos[i]!.stackHeight != 0 && !hos[i]!.isSlider) = true then hos
  else (forIn (m := Id) [i + 1:N] (hos, hos[i]!.endTime, (0 : Int32)) (soF sl i)).1

theorem soG_eq (sl : F32) (N i : Nat) (hos : Array OsuHitObject) : soG sl N i hos = .yield (soGA sl N i hos) := by
  unfold soG soGA; split <;> rfl

theorem beatmap.processor.apply_stacking_old_refines (sl : F32) (hos : alloc.vec.Vec beatmap.objects.OsuHitObject)
    (hN : hos.val.length < 2^62) (hok : hosOk hos.val) (h64 : System.Platform.numBits = 64) :
    ∃ y, beatmap.processor.apply_stacking_old sl hos = ok y ∧
      OsuBeatmapProcessor.applyStackingOld sl (abs hos) = abs y ∧ hosOk y.val ∧ y.val.length = hos.val.length := by
  have hmax : hos.val.length ≤ Usize.max := by rw [usize_max_64 h64]; omega
  let N := hos.val.length
  let n := alloc.vec.Vec.len hos
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => beatmap.processor.apply_stacking_old_loop0.body sl n x.1 x.2) (·.2) N
    hmax (fun x => x.1.val.length = N ∧ hosOk x.1.val) (fun x => (x.1.val.map (abs : _ → OsuHitObject)).toArray)
    (fun k A => soGA sl N k A) (fun y A => (y.val.map abs).toArray = A ∧ hosOk y.val ∧ y.val.length = N)
    (by
      intro t hI hlt j1 hj1 hj1v
      obtain ⟨hlen, hokt⟩ := hI
      have hil : t.2.val < t.1.val.length := by omega
      have hc : t.2 < n := by show t.2.val < n.val; simp [n, N] at hlt ⊢; omega
      have hA : t.1.val.map abs = ((t.1.val.map (abs : _ → OsuHitObject)).toArray).toList := by simp
      have hAi : ((t.1.val.map (abs : _ → OsuHitObject)).toArray)[t.2.val]! = abs (t.1.val[t.2.val]'hil) :=
        arr_get_abs t.1 _ hA _ hil
      have het := beatmap.objects.end_time_refines (t.1.val[t.2.val]'hil)
      have hsl := beatmap.objects.is_slider_refines (t.1.val[t.2.val]'hil)
      have hsh : ((abs (t.1.val[t.2.val]'hil) : OsuHitObject).stackHeight != 0) =
          ((t.1.val[t.2.val]'hil).stack_height != 0#i32) := i32_bne_zero (t.1.val[t.2.val]'hil).stack_height
      -- the inner loop (both Rust copies)
      obtain ⟨r, hr, hrv, hrok, hrl⟩ := so_loop sl n t.2 N (by simp [n, N]) h64
        (t.1, OsuHitObject.endTime (abs (t.1.val[t.2.val]'hil)), 0#i32, j1, true)
        ((t.1.val.map (abs : _ → OsuHitObject)).toArray, OsuHitObject.endTime (abs (t.1.val[t.2.val]'hil)), 0)
        ⟨rfl, hA, rfl, rfl, hlen, hokt, by simp [hj1v], hN⟩ (by simp [hj1v]; omega)
      have hr0 : beatmap.processor.apply_stacking_old_loop0_loop0 sl t.1 n t.2
          (OsuHitObject.endTime (abs (t.1.val[t.2.val]'hil))) 0#i32 j1 true = ok r := by
        unfold beatmap.processor.apply_stacking_old_loop0_loop0; exact hr
      have hr1 : beatmap.processor.apply_stacking_old_loop0_loop1 sl t.1 n t.2
          (OsuHitObject.endTime (abs (t.1.val[t.2.val]'hil))) 0#i32 j1 true = ok r := by
        unfold beatmap.processor.apply_stacking_old_loop0_loop1; rw [so_body_eq]; exact hr
      have hspec : (forIn (m := Id) [t.2.val + 1:N] ((t.1.val.map (abs : _ → OsuHitObject)).toArray,
          OsuHitObject.endTime (abs (t.1.val[t.2.val]'hil)), (0 : Int32)) (soF sl t.2.val)).1 =
          (r.val.map (abs : _ → OsuHitObject)).toArray := by
        have hrv' := hrv; simp only [hj1v] at hrv'
        rw [forIn_range_iterR]; apply Array.ext'; simp [hrv']
      unfold soGA
      rw [hAi]
      by_cases hskip : ((abs (t.1.val[t.2.val]'hil) : OsuHitObject).stackHeight != 0 &&
          !(abs (t.1.val[t.2.val]'hil) : OsuHitObject).isSlider) = true
      · rw [if_pos hskip]
        refine ⟨(t.1, j1), ?_, rfl, rfl, hlen, hokt⟩
        rw [hsh] at hskip
        have hb : ((t.1.val[t.2.val]'hil).stack_height != 0#i32) = true := (Bool.and_eq_true _ _ ▸ hskip).1
        have hns : (abs (t.1.val[t.2.val]'hil) : OsuHitObject).isSlider = false := by
          have := (Bool.and_eq_true _ _ ▸ hskip).2; simpa using this
        have hbv : ¬ (t.1.val[t.2.val]'hil).stack_height.val = 0 := by
          intro h0; apply (bne_iff_ne.mp hb); exact IScalar.eq_of_val_eq (by simpa using h0)
        simp [beatmap.processor.apply_stacking_old_loop0.body, hc, vec_index_eq _ _ hil, hbv, hsl, hns, hj1]
      · rw [if_neg hskip, hspec]
        refine ⟨(r, j1), ?_, rfl, rfl, hrl, hrok⟩
        by_cases hb : ((t.1.val[t.2.val]'hil).stack_height != 0#i32) = true
        · have hss : (abs (t.1.val[t.2.val]'hil) : OsuHitObject).isSlider = true := by
            rw [hsh, hb] at hskip; simpa using hskip
          have hbv : ¬ (t.1.val[t.2.val]'hil).stack_height.val = 0 := by
            intro h0; apply (bne_iff_ne.mp hb); exact IScalar.eq_of_val_eq (by simpa using h0)
          simp [beatmap.processor.apply_stacking_old_loop0.body, hc, vec_index_eq _ _ hil, hbv, hsl, hss, het, hj1, hr0]
        · have hbv : (t.1.val[t.2.val]'hil).stack_height.val = 0 := by simpa using hb
          simp [beatmap.processor.apply_stacking_old_loop0.body, hc, vec_index_eq _ _ hil, hbv, het, hj1, hr1])
    (by
      intro t hI hge
      have hc : ¬ t.2 < n := by show ¬ t.2.val < n.val; simp [n, N] at hge ⊢; omega
      exact ⟨t.1, by simp [beatmap.processor.apply_stacking_old_loop0.body, hc], rfl, hI.2, hI.1⟩)
    (hos, 0#usize) ⟨rfl, hok⟩ (by simp)
  refine ⟨y, ?_, ?_, hy.2.1, hy.2.2⟩
  · unfold beatmap.processor.apply_stacking_old beatmap.processor.apply_stacking_old_loop0; exact hl
  · rw [applyStackingOld_eq, forIn_range_iterR]
    rw [show soG sl (abs hos : Array OsuHitObject).size =
      fun i h => .yield (soGA sl (abs hos : Array OsuHitObject).size i h) from funext fun i => funext fun h => soG_eq _ _ _ _]
    have hsz : (abs hos : Array OsuHitObject).size = N := by simp [abs, N]
    rw [hsz]
    have h1 := hy.1
    simp only at h1
    rw [show (abs hos : Array OsuHitObject) = (hos.val.map abs).toArray from rfl]
    rw [show (0#usize : Usize).val = 0 from rfl] at h1
    rw [← h1]; rfl

theorem asa_loop (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (hok : hosOk hos.val) :
    ∃ y, beatmap.processor.apply_stacking_all_loop hos 0#usize = ok y ∧
      y.val = hos.val.map (fun h => sshR h 0#i32) ∧ hosOk y.val := by
  let g := fun h => sshR h 0#i32
  obtain ⟨y, hl, hy⟩ := loop_fold_gen' (fun x => beatmap.processor.apply_stacking_all_loop.body x.1 x.2) (·.2)
    hos.val.length (by have := hos.property; omega)
    (fun x => x.1.val.length = hos.val.length ∧ hosOk x.1.val) (fun x => x.1.val)
    (fun k L => L.modify k g) (fun y L => y.val = L ∧ hosOk y.val)
    (by
      intro t hI hlt j1 hj1 hj1v
      have hlt' : t.2.val < t.1.val.length := by omega
      refine ⟨(alloc.vec.Vec.set t.1 t.2 (g (t.1.val[t.2.val]'hlt')), j1), ?_, rfl, ?_, ?_⟩
      · simp [beatmap.processor.apply_stacking_all_loop.body, vec_lt_len_iff, hlt', vec_index_mut_eq _ _ hlt', ssh_ok, hj1, g]
      · simp only [vec_set_val']; rw [list_modify_set _ _ hlt']
      · refine ⟨by simp [vec_set_val', hI.1], ?_⟩
        rw [vec_set_val']; refine hosOk_set _ _ _ hI.2 ?_
        intro s hs; exact hI.2 _ (List.getElem_mem _) s hs)
    (by
      intro t hI hge
      have hc : ¬ t.2 < alloc.vec.Vec.len t.1 := by rw [vec_lt_len_iff]; omega
      exact ⟨t.1, by simp [beatmap.processor.apply_stacking_all_loop.body, hc], rfl, hI.2⟩)
    (hos, 0#usize) ⟨rfl, hok⟩ (by simp)
  refine ⟨y, by unfold beatmap.processor.apply_stacking_all_loop; exact hl, ?_, hy.2⟩
  have := hy.1; simp only at this
  rw [this, show (0#usize : Usize).val = 0 from rfl, iterR_modify_map]

theorem beatmap.processor.apply_stacking_all_refines (fv : I32) (sl : F32)
    (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (hN : hos.val.length < 2^62) (hok : hosOk hos.val)
    (h64 : System.Platform.numBits = 64) :
    ∃ y, beatmap.processor.apply_stacking_all fv sl hos = ok y ∧
      OsuBeatmapProcessor.applyStackingAll (abs fv) sl (abs hos) = abs y := by
  unfold beatmap.processor.apply_stacking_all OsuBeatmapProcessor.applyStackingAll
  by_cases h0 : hos.val.length = 0
  · have : alloc.vec.Vec.len hos = 0#usize := by apply UScalar.eq_of_val_eq; simpa using h0
    refine ⟨hos, by simp [this], ?_⟩
    have hs : (abs hos : Array OsuHitObject).size = 0 := by simp [abs, h0]
    simp [hs]
  · have hne : alloc.vec.Vec.len hos ≠ 0#usize := by
      intro h; apply h0; have := congrArg UScalar.val h; simpa using this
    obtain ⟨y1, hy1, hy1v, hy1ok⟩ := asa_loop hos hok
    have hs : ¬ ((abs hos : Array OsuHitObject).size == 0) = true := by simp [abs, h0]
    have hmap : (abs y1 : Array OsuHitObject) = (abs hos : Array OsuHitObject).map (·.setStackHeight 0) := by
      apply Array.ext'
      rw [show (abs y1 : Array OsuHitObject).toList = y1.val.map abs from by simp [abs],
        show (abs hos : Array OsuHitObject) = (hos.val.map abs).toArray from rfl, hy1v]
      simp only [List.map_map, Array.toList_map, List.toList_toArray]
      apply List.map_congr_left; intro h _; simp only [Function.comp_apply, ssh_abs]; rfl
    have hlen1 : y1.val.length = hos.val.length := by simp [hy1v]
    simp only [hne, if_false, hy1, bind_ok, hs]
    rw [← hmap]
    by_cases hf : fv ≥ 6#i32
    · have hf' : (abs fv : Int32) ≥ 6 := by
        show i32S fv ≥ 6; rw [show (6 : Int32) = i32S 6#i32 from rfl, ge_iff_le, abs_i32S_le_iff]; exact hf
      obtain ⟨y, hy, hyv⟩ := beatmap.processor.apply_stacking_refines sl y1 (by omega) (by omega) hy1ok h64
      exact ⟨y, by simp [hf, hy], by simp [hf', hyv]⟩
    · have hf' : ¬ (abs fv : Int32) ≥ 6 := by
        show ¬ i32S fv ≥ 6; rw [show (6 : Int32) = i32S 6#i32 from rfl, ge_iff_le, abs_i32S_le_iff]; exact hf
      obtain ⟨y, hy, hyv, -⟩ := beatmap.processor.apply_stacking_old_refines sl y1 (by omega) hy1ok h64
      exact ⟨y, by simp [hf, hy], by simp [hf', hyv]⟩

@[step] theorem beatmap.processor.apply_stacking_all_step (fv : I32) (sl : F32)
    (hos : alloc.vec.Vec beatmap.objects.OsuHitObject) (hN : hos.val.length < 2^62) (hok : hosOk hos.val)
    (h64 : System.Platform.numBits = 64) :
    beatmap.processor.apply_stacking_all fv sl hos ⦃ r =>
      OsuBeatmapProcessor.applyStackingAll (abs fv) sl (abs hos) = abs r ⦄ :=
  spec_of_ex (beatmap.processor.apply_stacking_all_refines fv sl hos hN hok h64)

end OsuProofs
