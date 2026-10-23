/-
`beatmap::slider_event_generator` (Rust) refines `OsuModel.Beatmap.SliderEventGenerator` (generateTicks,
generate). Descriptors map field-wise (`sedS`); the decode monad result by `hRel` (HitObjectParser.lean).
-/
import OsuProofs.Beatmap.SliderPath
import OsuProofs.Beatmap.ModSettings2
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

def setS : beatmap.slider_event_generator.SliderEventType → SliderEventType
  | .Tick => .tick | .LegacyLastTick => .legacyLastTick | .Head => .head | .Repeat => .repeat | .Tail => .tail
def sedS (e : beatmap.slider_event_generator.SliderEventDescriptor) : SliderEventDescriptor :=
  { type := setS e.etype, time := e.time, spanIndex := i32S e.span_index, spanStartTime := e.span_start_time,
    pathProgress := e.path_progress }
def sedsS (l : List beatmap.slider_event_generator.SliderEventDescriptor) : Array SliderEventDescriptor :=
  (l.map sedS).toArray

/-- Spec body of `generateTicks` (definitionally the spec's `for` body). -/
def seTickBody (si : Int32) (sst sd : F64) (rev : Bool) (len td mde : F64)
    (b : Array SliderEventDescriptor × F64) : ForInStep (Array SliderEventDescriptor × F64) :=
  if (!decide (b.2 ≤ len)) = true then .done b
  else if len - mde ≤ b.2 then .done b
  else .yield (b.1.push { type := .tick, time := sst + (if rev = true then 1 - b.2 / len else b.2 / len) * sd, spanIndex := si, spanStartTime := sst, pathProgress := b.2 / len }, b.2 + td)

theorem beatmap.slider_event_generator.generate_ticks_refines (si : I32) (sst sd : F64) (rev : Bool) (len td mde : F64) :
    ∃ v, beatmap.slider_event_generator.generate_ticks si sst sd rev len td mde = ok v ∧
      sedsS v.val = SliderEventGenerator.generateTicks (i32S si) sst sd rev len td mde ∧ v.val.length ≤ 10000000 := by
  unfold beatmap.slider_event_generator.generate_ticks SliderEventGenerator.generateTicks
  simp only [Id.run_bind, forIn_range_idx, id_run_eq]
  generalize hS : iterIdx _ 0 _ _ = S
  have hS' : iterIdx (fun _ b => seTickBody (i32S si) sst sd rev len td mde b) 0 (10000000 - 0) (#[], td) = S := hS
  unfold beatmap.slider_event_generator.generate_ticks_loop
  refine Exists.imp (fun y H => ⟨H.1, ?hv, H.2.2⟩) (loop_iterIdx' _ _ 10000000
    (fun (x : alloc.vec.Vec beatmap.slider_event_generator.SliderEventDescriptor × F64 × U64 × Bool) k
      (b : Array SliderEventDescriptor × F64) =>
      x.2.2.1.val = k ∧ x.2.2.2 = true ∧ sedsS x.1.val = b.1 ∧ x.2.1 = b.2 ∧ x.1.val.length = k ∧ k ≤ 10000000)
    (fun (y : alloc.vec.Vec beatmap.slider_event_generator.SliderEventDescriptor) (c : Array SliderEventDescriptor × F64) =>
      sedsS y.val = c.1 ∧ y.val.length ≤ 10000000)
    ?hstep ?hend (alloc.vec.Vec.new _, td, 0#u64, true) 0 (#[], td) ⟨by simp, rfl, by simp [sedsS], rfl, by simp, by omega⟩ hS')
  case hv => obtain ⟨_, h1, _⟩ := H; rw [h1, ← hS]; rfl
  case hend =>
    rintro ⟨o, d, fu, g⟩ k b ⟨h1, h2, h3, h4, h5, h6⟩ hk
    dsimp only at h1 h2 h3 h4 h5 h6
    subst h2
    have hf : ¬ fu < 10000000#u64 := by show ¬ fu.val < (10000000#u64).val; simp; omega
    exact ⟨o, by simp [beatmap.slider_event_generator.generate_ticks_loop.body, hf], h3, by omega⟩
  case hstep =>
    rintro ⟨o, d, fu, g⟩ k ⟨b1, b2⟩ ⟨h1, h2, h3, h4, h5, h6⟩ hk
    dsimp only at h1 h2 h3 h4 h5 h6
    subst h2 h3 h4
    have hf : fu < 10000000#u64 := by show fu.val < (10000000#u64).val; simp; omega
    unfold seTickBody
    by_cases hle : d ≤ len
    · by_cases hm : len - mde ≤ d
      · right
        refine ⟨(sedsS o.val, d), by simp [hle, hm], o, ?_, rfl, by omega⟩
        rw [loop_unfold]
        simp only [beatmap.slider_event_generator.generate_ticks_loop.body, ite_true, hf, float.F64.le, hle, hm,
          decide_true, bind_ok, float.F64.sub]
        rw [loop_unfold]
        simp [beatmap.slider_event_generator.generate_ticks_loop.body]
      · left
        let e : beatmap.slider_event_generator.SliderEventDescriptor :=
          { etype := .Tick, time := sst + (if rev = true then 1 - d / len else d / len) * sd, span_index := si,
            span_start_time := sst, path_progress := d / len }
        obtain ⟨o1, ho1, ho1v⟩ := push_eq o e (by have := usize_ge_32; omega)
        obtain ⟨fu1, hfu1, hfu1v⟩ := eq_ok_of_spec (U64.add_spec (x := fu) (y := 1#u64) (by simp [U64.max_eq]; omega))
        refine ⟨_, by simp only [hle, hm, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]; rfl,
          (o1, d + td, fu1, true), ?_, ?_⟩
        · have he : (if rev = true then (do let f1 ← beatmap.slider_event_generator.D1; ok (f1 - d / len))
              else ok (d / len) : Result F64) = ok (if rev = true then 1 - d / len else d / len) := by
            cases rev <;> simp [bmc_beatmap_slider_event_generator_D1, float.F64.sub]
          simp only [beatmap.slider_event_generator.generate_ticks_loop.body, ite_true, hf, float.F64.le, hle, hm,
            decide_true, decide_false, bind_ok, float.F64.sub, float.F64.div, Bool.false_eq_true, ite_false,
            float.F64.mul, float.F64.add, hfu1]
          rw [he, bind_ok, show (beatmap.slider_event_generator.SliderEventDescriptor.mk .Tick
            (sst + (if rev = true then 1 - d / len else d / len) * sd) si sst (d / len)) = e from rfl, ho1]
          simp
        · refine ⟨by simp [hfu1v, h1], rfl, ?_, rfl, by rw [ho1v]; simp; omega, by omega⟩
          dsimp only; rw [ho1v]; simp [sedsS, sedS, setS, e]
    · right
      refine ⟨(sedsS o.val, d), by simp [hle], o, ?_, rfl, by omega⟩
      rw [loop_unfold]
      simp only [beatmap.slider_event_generator.generate_ticks_loop.body, ite_true, hf, float.F64.le, hle,
        decide_false, bind_ok, Bool.false_eq_true, ite_false]
      rw [loop_unfold]
      simp [beatmap.slider_event_generator.generate_ticks_loop.body]

abbrev SED := beatmap.slider_event_generator.SliderEventDescriptor

theorem se_rev_loop (ticks : alloc.vec.Vec SED) :
    ∀ (out : alloc.vec.Vec SED) (k : Usize), k.val ≤ ticks.val.length →
      out.val.length + k.val ≤ Usize.max →
    ∃ o', beatmap.slider_event_generator.generate_loop0_loop0 out ticks k = ok o' ∧
      o'.val = out.val ++ (ticks.val.take k.val).reverse := by
  intro out k hk hb
  unfold beatmap.slider_event_generator.generate_loop0_loop0
  have H := loop_ok (fun (x : alloc.vec.Vec SED × Usize) =>
      beatmap.slider_event_generator.generate_loop0_loop0.body ticks x.1 x.2) (fun x => x.2.val)
    (fun x => x.2.val ≤ k.val ∧ x.1.val ++ (ticks.val.take x.2.val).reverse = out.val ++ (ticks.val.take k.val).reverse ∧
      x.1.val.length + x.2.val = out.val.length + k.val)
    (fun (v : alloc.vec.Vec SED) => v.val = out.val ++ (ticks.val.take k.val).reverse) (by
      rintro ⟨o, j⟩ ⟨h1, h2, h3⟩
      dsimp only at h1 h2 h3 ⊢
      by_cases hc : 0 < j.val
      · right
        have hc' : j > 0#usize := by show (0#usize).val < j.val; simpa using hc
        obtain ⟨j1, hj1, hj1v⟩ := usize_sub_one j hc
        have ej : j1.val < ticks.val.length := by omega
        obtain ⟨o1, ho1, ho1v⟩ := push_eq o (ticks.val[j1.val]'ej) (by omega)
        refine ⟨(o1, j1), by simp [beatmap.slider_event_generator.generate_loop0_loop0.body, hc', hj1,
          vec_index_usize_eq ticks j1 ej, ho1], ⟨by dsimp only; omega, ?_, by dsimp only; rw [ho1v]; simp; omega⟩,
          by dsimp only; omega⟩
        dsimp only; rw [ho1v, ← h2]
        have e : j.val = j1.val + 1 := by omega
        have ht : List.take (j1.val + 1) ticks.val = List.take j1.val ticks.val ++ [ticks.val[j1.val]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem ej]; simp
        rw [e, ht, List.reverse_append]; simp
      · left
        have hc' : ¬ j > 0#usize := by show ¬ (0#usize).val < j.val; simpa using hc
        refine ⟨o, by simp [beatmap.slider_event_generator.generate_loop0_loop0.body, hc'], ?_⟩
        rw [← h2]; have : j.val = 0 := by omega
        simp [this])
    (out, k) ⟨le_refl _, rfl, rfl⟩
  exact H

theorem se_fwd_loop (ticks : alloc.vec.Vec SED) :
    ∀ (out : alloc.vec.Vec SED), out.val.length + ticks.val.length ≤ Usize.max →
    ∃ o', beatmap.slider_event_generator.generate_loop0_loop1 out ticks 0#usize = ok o' ∧
      o'.val = out.val ++ ticks.val := by
  intro out hb
  unfold beatmap.slider_event_generator.generate_loop0_loop1
  have H := loop_ok (fun (x : alloc.vec.Vec SED × Usize) =>
      beatmap.slider_event_generator.generate_loop0_loop1.body ticks x.1 x.2) (fun x => ticks.val.length - x.2.val)
    (fun x => x.2.val ≤ ticks.val.length ∧ x.1.val = out.val ++ ticks.val.take x.2.val)
    (fun (v : alloc.vec.Vec SED) => v.val = out.val ++ ticks.val) (by
      rintro ⟨o, j⟩ ⟨h1, h2⟩
      dsimp only at h1 h2 ⊢
      by_cases hc : j.val < ticks.val.length
      · right
        have hc' : j < alloc.vec.Vec.len ticks := by show j.val < (alloc.vec.Vec.len ticks).val; simpa using hc
        obtain ⟨j1, hj1, hj1v⟩ := usize_add_one j (by have := alloc.vec.Vec.property ticks; omega)
        obtain ⟨o1, ho1, ho1v⟩ := push_eq o (ticks.val[j.val]'hc) (by rw [h2]; simp; omega)
        refine ⟨(o1, j1), by simp [beatmap.slider_event_generator.generate_loop0_loop1.body, hc', hj1,
          vec_index_usize_eq ticks j hc, ho1], ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only; rw [ho1v, h2, hj1v, List.take_add_one, List.getElem?_eq_getElem hc]; simp
      · left
        have hc' : ¬ j < alloc.vec.Vec.len ticks := by show ¬ j.val < (alloc.vec.Vec.len ticks).val; simpa using hc
        refine ⟨o, by simp [beatmap.slider_event_generator.generate_loop0_loop1.body, hc'], ?_⟩
        rw [h2]; have : j.val = ticks.val.length := by omega
        simp [this])
    (out, 0#usize) ⟨by simp, by simp⟩
  exact H

theorem se_forIn_ex_pure {ε β : Type} (f : Nat → β → Except ε (ForInStep β)) (g : Nat → β → Id (ForInStep β))
    (hf : ∀ i s, f i s = .ok (g i s)) : ∀ (n s : Nat) (b : β),
    forIn (m := Except ε) (List.range' s n) b f = .ok (iterIdx g s n b) := by
  intro n
  induction n with
  | zero => intro s b; rfl
  | succ n ih =>
    intro s b
    rw [List.range'_succ, List.forIn_cons, hf, iterIdx_succ]
    cases (g s b : ForInStep β) with
    | done c => rfl
    | yield c => exact ih (s + 1) c

theorem se_forIn_range_ex {ε β : Type} (f : Nat → β → Except ε (ForInStep β)) (g : Nat → β → Id (ForInStep β))
    (hf : ∀ i s, f i s = .ok (g i s)) (n : Nat) (b : β) :
    forIn (m := Except ε) [:n] b f = .ok (iterIdx g 0 n b) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact se_forIn_ex_pure f g hf n 0 b

/-- The repeat descriptor of span `span`. -/
def seRep (st sd : F64) (span : Int32) : SliderEventDescriptor :=
  { type := .repeat, time := (st + F64.ofInt32 span * sd) + sd, spanIndex := span,
    spanStartTime := st + F64.ofInt32 span * sd, pathProgress := F64.ofInt32 ((span + 1) % 2) }

/-- Spec span ticks (in event order). -/
def seTicks (st sd : F64) (length td mde : F64) (span : Int32) : Array SliderEventDescriptor :=
  if (span % 2 == 1) = true then
    (SliderEventGenerator.generateTicks span (st + F64.ofInt32 span * sd) sd (span % 2 == 1) length td mde).reverse
  else SliderEventGenerator.generateTicks span (st + F64.ofInt32 span * sd) sd (span % 2 == 1) length td mde

/-- Spec body of the span loop of `generate` (definitionally the spec's `for` body). -/
def seGenBody (st sd : F64) (sc : Int32) (length td mde : F64) (spanN : Nat) (out : Array SliderEventDescriptor) :
    ForInStep (Array SliderEventDescriptor) :=
  if (!td == 0) = true then
    if Int32.ofNat spanN < sc - 1 then .yield ((out ++ seTicks st sd length td mde (Int32.ofNat spanN)).push (seRep st sd (Int32.ofNat spanN)))
    else .yield (out ++ seTicks st sd length td mde (Int32.ofNat spanN))
  else
    if Int32.ofNat spanN < sc - 1 then .yield (out.push (seRep st sd (Int32.ofNat spanN)))
    else .yield out

theorem se_cast_i64 (x : I32) : (IScalar.cast .I64 x).val = x.val := by
  rw [IScalar.cast_val_eq]; have := x.hBounds; simp at this ⊢

theorem se_i32_rem2 (x : I32) : ∃ z, x % 2#i32 = ok z ∧ i32S z = i32S x % 2 := by
  obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (IScalar.rem_spec x (y := 2#i32) (by simp))
  refine ⟨z, hz, ?_⟩
  apply Int32.toInt_inj.mp
  rw [Int32.toInt_mod, i32S_toInt, i32S_toInt, hzv]; rfl

theorem se_wrapping_add1 (x : I32) : i32S (core.num.I32.wrapping_add x 1#i32) = i32S x + 1 := rfl

theorem se_rep_block (st sd : F64) (span : I32) (out : alloc.vec.Vec SED) (hb : out.val.length < Usize.max) :
    ∃ o, (do
      let i3 ← lift (IScalar.cast .I64 span)
      let f3 ← float.F64.from_i64 i3
      let f4 ← float.F64.mul f3 sd
      let f5 ← float.F64.add st f4
      let f6 ← float.F64.add (st + F64.ofInt span.val * sd) sd
      let i4 ← lift (core.num.I32.wrapping_add span 1#i32)
      let i5 ← i4 % 2#i32
      let i6 ← lift (IScalar.cast .I64 i5)
      let f7 ← float.F64.from_i64 i6
      alloc.vec.Vec.push out
        ({ etype := .Repeat, time := f6, span_index := span, span_start_time := f5, path_progress := f7 } : SED)) = ok o ∧
      sedsS o.val = (sedsS out.val).push (seRep st sd (i32S span)) ∧ o.val.length = out.val.length + 1 := by
  obtain ⟨z, hz, hzv⟩ := se_i32_rem2 (core.num.I32.wrapping_add span 1#i32)
  let e : SED := { etype := .Repeat, time := (st + F64.ofInt span.val * sd) + sd, span_index := span, span_start_time := st + F64.ofInt span.val * sd, path_progress := F64.ofInt z.val }
  obtain ⟨o, ho, hov⟩ := push_eq out e hb
  refine ⟨o, ?_, ?_, by rw [hov]; simp⟩
  · simp only [lift, bind_ok, float.F64.from_i64, se_cast_i64, float.F64.mul, float.F64.add, hz]
    exact ho
  · rw [hov]
    simp only [sedsS, List.map_append, List.map_cons, List.map_nil, List.toArray_appendList]
    rw [← List.push_toArray]; congr 1
    simp only [sedS, seRep, e, setS, F64.ofInt32, i32S_toInt]
    rw [← i32S_toInt z, hzv, se_wrapping_add1]

theorem se_i32S_ofNat (x : I32) (k : Nat) (h : x.val = k) : i32S x = Int32.ofNat k := by
  apply Int32.toInt_inj.mp
  rw [i32S_toInt, h]
  have := x.hBounds; simp at this
  rw [Int32.toInt_ofNat_of_lt (by omega)]

theorem se_tail (st sd : F64) (sc span : I32) (k : Nat) (hsp : i32S span = Int32.ofNat k)
    (span1 : I32) (hs1 : span + 1#i32 = ok span1) (o1 : alloc.vec.Vec SED) (hb : o1.val.length < Usize.max) :
    ∃ o2, (do
      let i2 ← lift (core.num.I32.wrapping_sub sc 1#i32)
      let out2 ← if span < i2 then (do
          let i3 ← lift (IScalar.cast .I64 span)
          let f3 ← float.F64.from_i64 i3
          let f4 ← float.F64.mul f3 sd
          let f5 ← float.F64.add st f4
          let f6 ← float.F64.add (st + F64.ofInt span.val * sd) sd
          let i4 ← lift (core.num.I32.wrapping_add span 1#i32)
          let i5 ← i4 % 2#i32
          let i6 ← lift (IScalar.cast .I64 i5)
          let f7 ← float.F64.from_i64 i6
          alloc.vec.Vec.push o1
            ({ etype := .Repeat, time := f6, span_index := span, span_start_time := f5, path_progress := f7 } : SED))
        else ok o1
      let span1' ← span + 1#i32
      (ok (ControlFlow.cont (out2, span1')) : Result (ControlFlow (alloc.vec.Vec SED × I32) (alloc.vec.Vec SED)))) = ok (.cont (o2, span1)) ∧
      sedsS o2.val = (if Int32.ofNat k < i32S sc - 1 then (sedsS o1.val).push (seRep st sd (Int32.ofNat k)) else sedsS o1.val) ∧
      o2.val.length ≤ o1.val.length + 1 := by
  have hc : (span < core.num.I32.wrapping_sub sc 1#i32) ↔ Int32.ofNat k < i32S sc - 1 := by
    rw [← hsp, ← i32S_wsub1, i32S_lt]; rfl
  by_cases h : Int32.ofNat k < i32S sc - 1
  · obtain ⟨o2, ho2, ho2v, ho2l⟩ := se_rep_block st sd span o1 hb
    refine ⟨o2, ?_, by rw [if_pos h, ho2v, hsp], by omega⟩
    rw [ho2]
    simp only [lift, bind_ok, if_pos (hc.mpr h), hs1]
  · refine ⟨o1, ?_, by rw [if_neg h], by omega⟩
    simp only [lift, bind_ok, if_neg (fun e => h (hc.mp e)), hs1]

theorem se_outer (st sd : F64) (sc : I32) (length td mde : F64) (n : I32) (hn0 : 0 ≤ n.val) (hn : n.val ≤ sc.val ∨ n.val = 0)
    (h64 : System.Platform.numBits = 64) :
    ∀ (out : alloc.vec.Vec SED), out.val.length ≤ 1 →
    ∃ o, beatmap.slider_event_generator.generate_loop0 0 st sd sc length td mde out n 0#i32 = ok o ∧
      sedsS o.val = iterIdx (fun i s => seGenBody st sd (i32S sc) length td mde i s) 0 (n.val.toNat - 0) (sedsS out.val) ∧
      o.val.length ≤ 1 + n.val.toNat * 10000001 := by
  intro out hout
  have hmax := usize_max64 h64
  have hnb := n.hBounds
  simp at hnb
  unfold beatmap.slider_event_generator.generate_loop0
  refine loop_iterIdx' _ _ n.val.toNat
    (fun (x : alloc.vec.Vec SED × I32) k (b : Array SliderEventDescriptor) =>
      x.2.val = k ∧ sedsS x.1.val = b ∧ x.1.val.length ≤ 1 + k * 10000001 ∧ k ≤ n.val.toNat)
    (fun (y : alloc.vec.Vec SED) (c : Array SliderEventDescriptor) =>
      sedsS y.val = c ∧ y.val.length ≤ 1 + n.val.toNat * 10000001)
    ?_ ?_ (out, 0#i32) 0 _ ⟨by simp, rfl, by omega, by omega⟩ rfl
  · rintro ⟨o, span⟩ k b ⟨h1, h2, h3, h4⟩ hk
    dsimp only at h1 h2 h3 h4
    subst h2
    left
    have hlt : span < n := by show span.val < n.val; omega
    have hsp : i32S span = Int32.ofNat k := se_i32S_ofNat span k h1
    obtain ⟨span1, hs1, hs1v⟩ := i32_add_one span (by omega) (by omega)
    obtain ⟨i1, hi1, hi1v⟩ := se_i32_rem2 span
    have hrev : decide (i1 = 1#i32) = (Int32.ofNat k % 2 == 1) := by
      have : (i1 = 1#i32) ↔ (i32S span % 2 = 1) := by
        rw [← hi1v]; constructor
        · intro h; rw [h]; rfl
        · intro h; apply IScalar.eq_of_val_eq; rw [← i32S_toInt, h]; rfl
      rw [← hsp]; by_cases h : i32S span % 2 = 1 <;> simp [this, h]
    have hof : F64.ofInt32 (Int32.ofNat k) = F64.ofInt span.val := by rw [← hsp]; simp [F64.ofInt32, i32S_toInt]
    have hlen : o.val.length < Usize.max := by rw [hmax]; omega
    simp only [beatmap.slider_event_generator.generate_loop0.body, hlt, if_true, lift, bind_ok, float.F64.from_i64,
      se_cast_i64, float.F64.mul, float.F64.add, hi1, float.F64.eq]
    unfold seGenBody
    by_cases hz : (td == 0) = true
    · rw [if_pos hz]
      have hz' : ¬ ((!td == 0) = true) := by simp [hz]
      rw [if_neg hz']
      obtain ⟨o2, ho2, ho2v, ho2l⟩ := se_tail st sd sc span k hsp span1 hs1 o hlen
      simp only [lift, bind_ok, float.F64.from_i64, se_cast_i64, float.F64.mul, float.F64.add] at ho2
      refine ⟨sedsS o2.val, ?_, (o2, span1), ?_, ?_⟩
      · rw [ho2v]; split <;> rfl
      · exact ho2
      · exact ⟨by simp [hs1v, h1], rfl, by dsimp only; omega, by omega⟩
    · rw [if_neg hz]
      have hz' : ((!td == 0) = true) := by simpa using hz
      rw [if_pos hz']
      obtain ⟨tk, htk, htkv, htkl⟩ := beatmap.slider_event_generator.generate_ticks_refines span
        (st + F64.ofInt span.val * sd) sd (decide (i1 = 1#i32)) length td mde
      rw [hrev, hsp] at htkv
      rw [htk, bind_ok]
      have hst : seTicks st sd length td mde (Int32.ofNat k) =
          (if (Int32.ofNat k % 2 == 1) = true then (sedsS tk.val).reverse else sedsS tk.val) := by
        unfold seTicks; rw [hof, htkv]
      rw [hst]
      have htl : tk.val.length ≤ 10000000 := htkl
      have hsl : (sedsS tk.val).size = tk.val.length := by simp [sedsS]
      by_cases hr : i1 = 1#i32
      · have hb : (Int32.ofNat k % 2 == 1) = true := by rw [← hrev, decide_eq_true_eq]; exact hr
        rw [if_pos hb, if_pos hr]
        obtain ⟨o1, ho1, ho1v⟩ := se_rev_loop tk o (alloc.vec.Vec.len tk) (by simp) (by simp; rw [hmax]; omega)
        rw [ho1, bind_ok]
        have hlen1 : o1.val.length < Usize.max := by rw [ho1v, hmax]; simp; omega
        obtain ⟨o2, ho2, ho2v, ho2l⟩ := se_tail st sd sc span k hsp span1 hs1 o1 hlen1
        simp only [lift, bind_ok, float.F64.from_i64, se_cast_i64, float.F64.mul, float.F64.add] at ho2
        have e1 : sedsS o1.val = sedsS o.val ++ (sedsS tk.val).reverse := by
          rw [ho1v]; simp [sedsS, List.map_reverse]
        refine ⟨sedsS o2.val, ?_, (o2, span1), ho2, ?_⟩
        · rw [ho2v, e1]; split <;> rename_i h <;> simp [h]
        · refine ⟨by simp [hs1v, h1], rfl, ?_, by omega⟩
          dsimp only; rw [ho1v] at ho2l; simp at ho2l; omega
      · have hb : (Int32.ofNat k % 2 == 1) = false := by rw [← hrev, decide_eq_false_iff_not]; exact hr
        rw [if_neg (show ¬ ((Int32.ofNat k % 2 == 1) = true) by simp [hb]), if_neg hr]
        obtain ⟨o1, ho1, ho1v⟩ := se_fwd_loop tk o (by rw [hmax]; omega)
        rw [ho1, bind_ok]
        have hlen1 : o1.val.length < Usize.max := by rw [ho1v, hmax]; simp; omega
        obtain ⟨o2, ho2, ho2v, ho2l⟩ := se_tail st sd sc span k hsp span1 hs1 o1 hlen1
        simp only [lift, bind_ok, float.F64.from_i64, se_cast_i64, float.F64.mul, float.F64.add] at ho2
        have e1 : sedsS o1.val = sedsS o.val ++ sedsS tk.val := by
          rw [ho1v]; simp [sedsS]
        refine ⟨sedsS o2.val, ?_, (o2, span1), ho2, ?_⟩
        · rw [ho2v, e1]; split <;> rename_i h <;> simp [h]
        · refine ⟨by simp [hs1v, h1], rfl, ?_, by omega⟩
          dsimp only; rw [ho1v] at ho2l; simp at ho2l; omega
  · rintro ⟨o, span⟩ k b ⟨h1, h2, h3, h4⟩ hk
    dsimp only at h1 h2 h3 h4
    have hlt : ¬ span < n := by show ¬ span.val < n.val; omega
    have hk' : k = n.val.toNat := by omega
    subst hk'
    exact ⟨o, by simp [beatmap.slider_event_generator.generate_loop0.body, hlt], h2, h3⟩

theorem se_push_bind {α β : Type} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max)
    (k : alloc.vec.Vec α → Result β) :
    (do let w ← alloc.vec.Vec.push v x; k w) = k (alloc.vec.Vec.from (v.val ++ [x]) (by simp; omega)) := by
  obtain ⟨w, hw, hwv⟩ := push_eq v x h
  rw [hw, bind_ok]; congr 1
  apply alloc.vec.Vec.ext; rw [hwv]; simp

theorem beatmap.slider_event_generator.generate_refines (st sd vel td0 total : F64) (sc : I32)
    (h64 : System.Platform.numBits = 64) :
    ∃ r, beatmap.slider_event_generator.generate st sd vel td0 total sc = ok r ∧
      hRel (fun v => sedsS v.val) r (SliderEventGenerator.generate st sd vel td0 total (i32S sc)) := by
  unfold beatmap.slider_event_generator.generate SliderEventGenerator.generate
  simp only [bmc_beatmap_slider_event_generator_MAX_LENGTH, bind_ok, max_refines, min_refines,
    bmc_beatmap_slider_event_generator_D0, net.mathops.f64_clamp_refines]
  obtain ⟨r1, hr1, hr1v⟩ := lift_net_exceptI beatmap.errors.W_MATH_CLAMP_TICKDISTANCE_0_LENGTH id id (fun _ => rfl)
    (F64.clamp td0 0 (F64.min 100000 total)) "Math.Clamp(tickDistance, 0, length)"
  rw [hr1, bind_ok]
  cases hc : F64.clamp td0 0 (F64.min 100000 total) with
  | error e =>
    rw [hc] at hr1v
    cases r1 with
    | Ok v => simp [hRel, liftNet] at hr1v
    | Err e' => exact ⟨_, rfl, by simp [hRel, liftNet]⟩
  | ok td =>
    rw [hc] at hr1v
    cases r1 with
    | Err e' => simp [hRel, liftNet] at hr1v
    | Ok v =>
      simp only [hRel, liftNet, id] at hr1v
      subst hr1v
      simp only [liftNet, except_bind_ok]
      generalize hS : forIn (m := Except String) (ρ := Std.Legacy.Range) ([:(i32S sc).toNatClampNeg]) _ _ = S
      have hS' : S = .ok (iterIdx (fun i s => seGenBody st sd (i32S sc) (F64.min 100000 total) v (vel * 10) i s) 0
          (i32S sc).toNatClampNeg #[{ type := .head, time := st, spanIndex := 0, spanStartTime := st, pathProgress := 0 }]) := by
        rw [← hS]; apply se_forIn_range_ex; intro i s
        unfold seGenBody seTicks seRep
        split <;> split <;> rfl
      rw [hS']
      have hmax := usize_max64 h64
      obtain ⟨hd, hhd, hhdv⟩ := push_eq (alloc.vec.Vec.new SED)
        ({ etype := .Head, time := st, span_index := 0#i32, span_start_time := st, path_progress := 0 } : SED)
        (by simp; omega)
      obtain ⟨nn, hn, hnn0, hnn1, hnn2⟩ : ∃ nn : I32, (if sc < 0#i32 then ok 0#i32 else ok sc : Result I32) = ok nn ∧
          0 ≤ nn.val ∧ (nn.val ≤ sc.val ∨ nn.val = 0) ∧ nn.val.toNat = (i32S sc).toNatClampNeg := by
        by_cases h : sc.val < 0
        · have h' : sc < 0#i32 := by show sc.val < (0#i32).val; simpa using h
          refine ⟨0#i32, by simp [h'], by simp, Or.inr (by simp), ?_⟩
          simp [Int32.toNatClampNeg, i32S_toInt]; omega
        · have h' : ¬ sc < 0#i32 := by show ¬ sc.val < (0#i32).val; simpa using h
          refine ⟨sc, by simp [h'], by omega, Or.inl (le_refl _), ?_⟩
          simp [Int32.toNatClampNeg, i32S_toInt]
      obtain ⟨o1, ho1, ho1v, ho1l⟩ := se_outer st sd sc (F64.min 100000 total) v (vel * 10)
        nn hnn0 hnn1 h64 hd (by rw [hhdv]; simp)
      simp only [bmc_beatmap_slider_event_generator_D10, float.F64.mul, hhd, hn, ho1, bind_ok]
      rw [hnn2] at ho1v ho1l
      have hsd : sedsS hd.val = #[{ type := .head, time := st, spanIndex := 0, spanStartTime := st, pathProgress := 0 }] := by
        rw [hhdv]; simp [sedsS, sedS, setS]; rfl
      rw [hsd] at ho1v
      obtain ⟨i2, hi2, hi2v⟩ := se_i32_rem2 sc
      have hof : ∀ y : I32, F64.ofInt32 (i32S y) = F64.ofInt y.val := fun y => by simp [F64.ofInt32, i32S_toInt]
      simp only [lift, bind_ok, float.F64.from_i64, se_cast_i64, bmc_beatmap_slider_event_generator_D2,
        bmc_beatmap_slider_event_generator_TAIL_LENIENCY, float.F64.div, float.F64.add, float.F64.sub, max_refines, hi2]
      rw [except_bind_ok]
      have ht : SliderEventGenerator.TAIL_LENIENCY = -36 := rfl
      rw [ht, ← i32S_wsub1, hof, hof, ← hi2v]
      have hlen : o1.val.length + 2 < Usize.max := by
        rw [hmax]; have := hnn0; have : nn.val.toNat ≤ 2^31 := by have := nn.hBounds; simp at this; omega
        omega
      by_cases h0 : i2 = 0#i32
      · have hb : (i32S i2 == 0) = true := by rw [h0]; rfl
        rw [if_pos h0, if_pos hb]
        rw [bmc_beatmap_slider_event_generator_D1, bind_ok, bind_ok]
        rw [se_push_bind _ _ (by omega)]
        rw [se_push_bind _ _ (by simp; omega)]
        refine ⟨_, rfl, ?_⟩
        simp only [hRel, except_pure]
        simp only [Nat.sub_zero] at ho1v; rw [← ho1v]
        simp [sedsS, sedS, setS, hof]
      · have hb : ¬ (i32S i2 == 0) = true := by
          intro e; apply h0; apply IScalar.eq_of_val_eq; rw [← i32S_toInt]; simp at e; rw [e]; rfl
        rw [if_neg h0, if_neg hb, bind_ok]
        rw [se_push_bind _ _ (by omega)]
        rw [se_push_bind _ _ (by simp; omega)]
        refine ⟨_, rfl, ?_⟩
        simp only [hRel, except_pure]
        simp only [Nat.sub_zero] at ho1v; rw [← ho1v]
        simp [sedsS, sedS, setS, hof]

end OsuProofs
