/-
Sim3c part 1: the `OsuModWiggle` handler of `customState`: `wiggle_one` (one `wig` sample pair) and `wiggle_state`
(the two segment-generation loops over `net.random`, then the `withAbs … transformTo position` loop) refine the
spec's `.wiggle` block (`s3c_wigSpec`, a verbatim copy of the block of `Sim.customState`, defeq to it).

Budget: one call adds `n1 + n2 ≤ s3c_W` transforms (`n1 = preempt/100 ≤ 2^31/100`, `n2 = (d/100).toInt32 < 2^31`).
-/
import OsuProofs.Sim3.SC_WA
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

/-! ## spec side -/

/-- the spec's `dur?` of the `.wiggle` block (verbatim) -/
def s3c_durS (o : OsuModel.Sim.TopObj) (p : OsuModel.Sim.Sim.Part) : Option F64 :=
  if p == .top then
      (match o.h.kind with
       | .slider => o.slider.map (·.duration)
       | .spinner => o.spinner.map (·.duration)
       | _ => none)
    else none

/-- the Rust `dur` of `wiggle_state` -/
def s3c_durR (o : sim.playable.TopObj) (p : sim.step.Part) : Option F64 :=
  match p with
  | .Top => (match o.h.kind with
    | .Slider => o.slider.map (·.duration)
    | .Spinner => o.spinner.map (·.duration)
    | _ => none)
  | _ => none

theorem s3c_durS_eq (tn) (o : sim.playable.TopObj) (p : sim.step.Part) :
    s3c_durS (topS tn o) (abs p) = s3c_durR o p := by
  cases p <;> cases hK : o.h.kind <;> cases o.slider <;> cases o.spinner <;>
    simp [s3c_durS, s3c_durR, topS, hobjS, kindS, hK, abs, partS] <;> rfl

/-- the spec's `.wiggle` handler block of `Sim.customState` (Step.lean, `OsuModWiggle.cs:42-81`), verbatim:
`o` = the top object, `p` the part, `h` its hit object, `k` its instance, `now` the clock -/
def s3c_wigSpec (o : OsuModel.Sim.TopObj) (p : OsuModel.Sim.Sim.Part) (h : OsuModel.Sim.HObj) (k : Nat)
    (now strength : F64) : OsuModel.Sim.SimM (ForInStep PUnit) := do
  let origin := (← OsuModel.Sim.Sim.instOf k).tf.pos
  let mut rng := NetRandom.create (F64.toInt32 h.start)
  let mut segs : Array (F64 × OsuModel.Sim.Vec2) := #[]
  let wig (rng : NetRandom.State) : OsuModel.Sim.Vec2 × NetRandom.State :=
    let (a, rng) := NetRandom.sample rng
    let (b, rng) := NetRandom.sample rng
    let ang : F32 := F64.toF32 (a * 2 * Framework.EasingConst.pi)
    let dist : F32 := F64.toF32 (b * strength * 7)
    (⟨F64.toF32 (F32.toF64 dist * F64.cos (F32.toF64 ang) + F32.toF64 origin.x),
      F64.toF32 (F32.toF64 dist * F64.sin (F32.toF64 ang) + F32.toF64 origin.y)⟩, rng)
  let n1 : Int := (F64.toInt32 h.preempt).toInt / 100
  for q in [0:n1.toNat] do
    let (v, rng') := wig rng
    rng := rng'
    segs := segs.push (h.start - h.preempt + F64.ofInt (q * 100), v)
  let dur? : Option F64 := s3c_durS o p
  if let some d := dur? then
    let n2 := (F64.toInt32 (d / 100)).toInt
    for q in [0:n2.toNat] do
      let (v, rng') := wig rng
      rng := rng'
      segs := segs.push (h.start + F64.ofInt (q * 100), v)
  for (t0, v) in segs do
    OsuModel.Sim.Sim.withAbs k now t0 fun tf => (OsuModel.Sim.transformTo tf now .position v 100).1
  return .yield PUnit.unit

/-- the vector of one `wig` -/
def s3c_wv (strength : F64) (o : OsuModel.Sim.Vec2) (r : NetRandom.State) : OsuModel.Sim.Vec2 :=
  ⟨(((NetRandom.sample (NetRandom.sample r).2).1 * strength * 7).toF32.toF64 *
      ((NetRandom.sample r).1 * 2 * Framework.EasingConst.pi).toF32.toF64.cos + o.x.toF64).toF32,
   (((NetRandom.sample (NetRandom.sample r).2).1 * strength * 7).toF32.toF64 *
      ((NetRandom.sample r).1 * 2 * Framework.EasingConst.pi).toF32.toF64.sin + o.y.toF64).toF32⟩

/-- the generator after one `wig` -/
def s3c_wr (r : NetRandom.State) : NetRandom.State := (NetRandom.sample (NetRandom.sample r).2).2

/-- one iteration of a segment-generation loop -/
def s3c_gstep (base strength : F64) (o : OsuModel.Sim.Vec2) (q : Nat)
    (s : NetRandom.State × Array (F64 × OsuModel.Sim.Vec2)) : NetRandom.State × Array (F64 × OsuModel.Sim.Vec2) :=
  (s3c_wr s.1, s.2.push (base + F64.ofInt ((q : Int) * 100), s3c_wv strength o s.1))

/-- per-call transform budget of a `Wiggle` handler -/
def s3c_W : Nat := 2 ^ 31 + 2 ^ 25

/-! ## `wiggle_one` -/
theorem sim.step.wiggle_one_refines (rng : net.random.State) (strength : F64) (origin : sim.basic.Vec2)
    (hs : stOk rng) :
    ∃ v r2, sim.step.wiggle_one rng strength origin = ok (v, r2) ∧ stOk r2 ∧ stS r2 = s3c_wr (stS rng) ∧
      (abs v : OsuModel.Sim.Vec2) = s3c_wv strength (abs origin) (stS rng) := by
  obtain ⟨a, r1, h1, o1, e1⟩ := net.random.sample_refines rng hs
  obtain ⟨b, r2, h2, o2, e2⟩ := net.random.sample_refines r1 o1
  have e1a : (NetRandom.sample (stS rng)).1 = a := by rw [← e1]
  have e1b : (NetRandom.sample (stS rng)).2 = stS r1 := by rw [← e1]
  have e2a : (NetRandom.sample (stS r1)).1 = b := by rw [← e2]
  have e2b : (NetRandom.sample (stS r1)).2 = stS r2 := by rw [← e2]
  refine ⟨⟨(s3c_wv strength (abs origin) (stS rng)).x, (s3c_wv strength (abs origin) (stS rng)).y⟩, r2, ?_, o2, ?_, rfl⟩
  · simp only [sim.step.wiggle_one, h1, h2, bind_ok, fb64_4611686018427387904, fb64_4619567317775286272, fw_PI,
      float.F64.mul, float.F64.to_f32, float.F32.to_f64, float.F64.cos, float.F64.sin, float.F64.add, uncurry_apply_pair,
      s3c_wv, e1a, e1b, e2a]
    rfl
  · simp only [s3c_wr, e1b, e2b]

/-! ## spec loops with pure bodies -/
theorem s3c_forIn_range_pure {σ : Type} (n : Nat) (init : σ) (F : Nat → σ → OsuModel.Sim.SimM (ForInStep σ))
    (g : Nat → σ → σ) (hF : ∀ q s, F q s = pure (.yield (g q s))) (C : OsuModel.Sim.Ctx) (S : OsuModel.Sim.St) :
    forIn [:n] init F C S = .ok ((List.range' 0 n).foldl (fun s q => g q s) init, S) := by
  have hFe : F = fun q s => pure (.yield (g q s)) := funext fun q => funext fun s => hF q s
  subst hFe
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [List.forIn_pure_yield_eq_foldl]
  rfl

/-! ## Rust segment-generation loops -/
theorem s3c_u64_mul (x y : U64) (h : x.val * y.val ≤ U64.max) : ∃ z, x * y = ok z ∧ z.val = x.val * y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.mul_spec (x := x) (y := y) h)
  exact ⟨z, hz, by simpa using hv⟩
theorem s3c_u64_add (x y : U64) (h : x.val + y.val ≤ U64.max) : ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (U64.add_spec (x := x) (y := y) h)
  exact ⟨z, hz, by simpa using hv⟩

/-- Rust `(rng, seg_t, seg_v)` vs the spec `(rng, segs)` -/
def s3cR (rng : net.random.State) (t : alloc.vec.Vec F64) (v : alloc.vec.Vec sim.basic.Vec2)
    (S : NetRandom.State × Array (F64 × OsuModel.Sim.Vec2)) : Prop :=
  stOk rng ∧ stS rng = S.1 ∧ t.val.length = v.val.length ∧ S.2.toList = t.val.zip (v.val.map abs)

theorem s3cR_push (rng r2 : net.random.State) (t : alloc.vec.Vec F64) (v : alloc.vec.Vec sim.basic.Vec2)
    (S : NetRandom.State × Array (F64 × OsuModel.Sim.Vec2)) (base strength : F64) (o : OsuModel.Sim.Vec2) (q : Nat)
    (x : F64) (vv : sim.basic.Vec2) (h1 : t.val.length < Usize.max) (h2 : v.val.length < Usize.max)
    (hR : s3cR rng t v S) (o2 : stOk r2) (er : stS r2 = s3c_wr (stS rng)) (ev : (abs vv : OsuModel.Sim.Vec2) = s3c_wv strength o (stS rng))
    (hx : x = base + F64.ofInt ((q : Int) * 100)) :
    s3cR r2 (vpush t x h1) (vpush v vv h2) (s3c_gstep base strength o q S) := by
  obtain ⟨_, e1, e2, e3⟩ := hR
  refine ⟨o2, by rw [er, e1]; rfl, by simp [e2], ?_⟩
  simp only [s3c_gstep, Array.toList_push, e3, vpush_val, List.map_append, List.map_cons, List.map_nil]
  rw [List.zip_append (by simp [e2])]
  simp [hx, ev, e1]

theorem s3c_loop0 (f f1 strength : F64) (origin : sim.basic.Vec2) (n1 : U64) (hn : n1.val ≤ 2 ^ 32) :
    ∀ m (q : U64) rng (t : alloc.vec.Vec F64) (v : alloc.vec.Vec sim.basic.Vec2) S, n1.val - q.val = m →
      q.val ≤ n1.val → t.val.length + m < 2 ^ 32 - 1 → s3cR rng t v S →
      ∃ rng' t' v', sim.step.wiggle_state_loop0 f f1 strength origin rng t v n1 q = ok (rng', t', v') ∧
        s3cR rng' t' v' ((List.range' q.val m).foldl (fun s q => s3c_gstep (f - f1) strength (abs origin) q s) S) ∧
        t'.val.length = t.val.length + m := by
  intro m
  induction m with
  | zero =>
    intro q rng t v S hm hq hl hR
    refine ⟨rng, t, v, ?_, by simpa using hR, by simp⟩
    have : ¬ q < n1 := by show ¬ q.val < n1.val; omega
    unfold sim.step.wiggle_state_loop0; rw [loop_unfold]
    simp [sim.step.wiggle_state_loop0.body, this]
  | succ m ih =>
    intro q rng t v S hm hq hl hR
    have hlt : q < n1 := by show q.val < n1.val; omega
    obtain ⟨vv, r2, hw, o2, er, ev⟩ := sim.step.wiggle_one_refines rng strength origin hR.1
    obtain ⟨m100, hm100, hm100v⟩ := s3c_u64_mul q 100#u64 (by simp [U64.max_eq]; omega)
    obtain ⟨q1, hq1, hq1v⟩ := s3c_u64_add q 1#u64 (by simp [U64.max_eq]; omega)
    have hp1 : t.val.length < Usize.max := by have := usize_ge_32; omega
    have hp2 : v.val.length < Usize.max := by rw [← hR.2.2.1]; exact hp1
    obtain ⟨rng', t', v', hl', hR', hlen'⟩ := ih q1 r2 (vpush t _ hp1) (vpush v vv hp2)
      (s3c_gstep (f - f1) strength (abs origin) q.val S) (by simp at hq1v; omega) (by simp at hq1v; omega)
      (by simp; omega) (s3cR_push rng r2 t v S _ strength _ q.val _ vv hp1 hp2 hR o2 er ev rfl)
    have hx : F64.ofInt ((m100.val : Nat) : Int) = F64.ofInt ((q.val : Int) * 100) := by
      rw [hm100v]; simp
    have hstep : sim.step.wiggle_state_loop0 f f1 strength origin rng t v n1 q =
        sim.step.wiggle_state_loop0 f f1 strength origin r2 (vpush t (f - f1 + F64.ofInt ((q.val : Int) * 100)) hp1) (vpush v vv hp2) n1 q1 := by
      unfold sim.step.wiggle_state_loop0; rw [loop_unfold]
      simp only [sim.step.wiggle_state_loop0.body, if_pos hlt, hw, bind_ok, float.F64.sub, hm100, float.F64.from_u64,
        float.F64.add, hx, vec_push_ok _ _ hp1, vec_push_ok _ _ hp2, hq1, uncurry_apply_pair]
    refine ⟨rng', t', v', ?_, ?_, by rw [hlen']; simp; omega⟩
    · rw [hstep]; exact hl'
    · simp only [List.range'_succ, List.foldl_cons]
      simp at hq1v; rw [hq1v] at hR'; exact hR'

theorem s3c_loop2 (f strength : F64) (origin : sim.basic.Vec2) (n2 : U64) (hn : n2.val ≤ 2 ^ 32) :
    ∀ m (q : U64) rng (t : alloc.vec.Vec F64) (v : alloc.vec.Vec sim.basic.Vec2) S, n2.val - q.val = m →
      q.val ≤ n2.val → t.val.length + m < 2 ^ 32 - 1 → s3cR rng t v S →
      ∃ rng' t' v', sim.step.wiggle_state_loop2 f strength origin rng t v n2 q = ok (t', v') ∧
        s3cR rng' t' v' ((List.range' q.val m).foldl (fun s q => s3c_gstep f strength (abs origin) q s) S) ∧
        t'.val.length = t.val.length + m := by
  intro m
  induction m with
  | zero =>
    intro q rng t v S hm hq hl hR
    refine ⟨rng, t, v, ?_, by simpa using hR, by simp⟩
    have : ¬ q < n2 := by show ¬ q.val < n2.val; omega
    unfold sim.step.wiggle_state_loop2; rw [loop_unfold]
    simp [sim.step.wiggle_state_loop2.body, this]
  | succ m ih =>
    intro q rng t v S hm hq hl hR
    have hlt : q < n2 := by show q.val < n2.val; omega
    obtain ⟨vv, r2, hw, o2, er, ev⟩ := sim.step.wiggle_one_refines rng strength origin hR.1
    obtain ⟨m100, hm100, hm100v⟩ := s3c_u64_mul q 100#u64 (by simp [U64.max_eq]; omega)
    obtain ⟨q1, hq1, hq1v⟩ := s3c_u64_add q 1#u64 (by simp [U64.max_eq]; omega)
    have hp1 : t.val.length < Usize.max := by have := usize_ge_32; omega
    have hp2 : v.val.length < Usize.max := by rw [← hR.2.2.1]; exact hp1
    obtain ⟨rng', t', v', hl', hR', hlen'⟩ := ih q1 r2 (vpush t _ hp1) (vpush v vv hp2)
      (s3c_gstep f strength (abs origin) q.val S) (by simp at hq1v; omega) (by simp at hq1v; omega)
      (by simp; omega) (s3cR_push rng r2 t v S _ strength _ q.val _ vv hp1 hp2 hR o2 er ev rfl)
    have hx : F64.ofInt ((m100.val : Nat) : Int) = F64.ofInt ((q.val : Int) * 100) := by
      rw [hm100v]; simp
    have hstep : sim.step.wiggle_state_loop2 f strength origin rng t v n2 q =
        sim.step.wiggle_state_loop2 f strength origin r2 (vpush t (f + F64.ofInt ((q.val : Int) * 100)) hp1) (vpush v vv hp2) n2 q1 := by
      unfold sim.step.wiggle_state_loop2; rw [loop_unfold]
      simp only [sim.step.wiggle_state_loop2.body, if_pos hlt, hw, bind_ok, hm100, float.F64.from_u64,
        float.F64.add, hx, vec_push_ok _ _ hp1, vec_push_ok _ _ hp2, hq1, uncurry_apply_pair]
    refine ⟨rng', t', v', ?_, ?_, by rw [hlen']; simp; omega⟩
    · rw [hstep]; exact hl'
    · simp only [List.range'_succ, List.foldl_cons]
      simp at hq1v; rw [hq1v] at hR'; exact hR'

/-! ## the `withAbs … transformTo position v 100` loop -/
theorem s3c_csPost_trans {P : Nat → sim.transforms.TObj → Prop} {b b' : Nat} {c : sim.state.Ctx}
    {s0 s1 s2 : sim.state.St} (h1 : s3b_csPost P b c s0 s1) (h2 : s3b_csPost P b' c s1 s2) : s3b_csPost P b' c s0 s2 :=
  ⟨h2.1, h2.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1, s3c_ito_trans h1.2.2.2.2 h2.2.2.2.2⟩

theorem sim.step.wiggle_state_loop1_eq (s : sim.state.St) (k : Usize) (now : F64) (t : alloc.vec.Vec F64)
    (v : alloc.vec.Vec sim.basic.Vec2) (z : Usize) :
    sim.step.wiggle_state_loop1 s k now t v z = sim.step.wiggle_state_loop3 100 s k now t v z := by
  unfold sim.step.wiggle_state_loop1 sim.step.wiggle_state_loop3
  congr 1
  funext x
  rcases x with ⟨s1, z1⟩
  simp only [sim.step.wiggle_state_loop1.body, sim.step.wiggle_state_loop3.body, fb64_4636737291354636288, bind_ok]

/-- one segment: 1 transform -/
theorem s3c_seg (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (s : sim.state.St) (k : Usize) (hk : k.val < s.insts.val.length) (now t0 : F64) (vv : sim.basic.Vec2)
    (hinv : SimInv c s) (hP : s3b_TfInv P (b + 1) s) :
    ∃ sq tf1, sim.transforms.transform_to { (s.insts.val[k.val]'hk).tf with delay := t0 - now } now
        sim.transforms.Member.Position vv 100 net.framework.Easing.None none = ok (sq, tf1) ∧
      OsuModel.Sim.Sim.withAbs k.val now t0 (fun tf => (OsuModel.Sim.transformTo tf now .position (abs vv) 100).1)
        (simCtxS tn fo c) (simStS tn s) = .ok ((), simStS tn (s3b_waSt s k hk tf1)) ∧
      s3b_csPost P b c s (s3b_waSt s k hk tf1) := by
  have hT0 : P (b + 1) { (s.insts.val[k.val]'hk).tf with delay := t0 - now } :=
    E.delay _ _ _ (hP _ (List.getElem_mem hk)).1
  dsimp only at hT0
  obtain ⟨sq', tf1, h3, e3, p3⟩ := E.tto b _ now .Position vv 100 .None none hT0
  refine ⟨sq', tf1, h3, ?_⟩
  refine s3b_wa tn fo E b (b + 1) (by omega) c s k hk now t0 _ tf1 hinv hP ?_ p3
  exact congrArg Prod.fst e3

theorem s3c_loop3 (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat) (c : sim.state.Ctx)
    (k : Usize) (now : F64) (t : alloc.vec.Vec F64) (v : alloc.vec.Vec sim.basic.Vec2)
    (hlen : t.val.length = v.val.length)
    (G : (F64 × OsuModel.Sim.Vec2) → PUnit → OsuModel.Sim.SimM (ForInStep PUnit))
    (hG : ∀ x u, G x u = (OsuModel.Sim.Sim.withAbs k.val now x.1
      (fun tf => (OsuModel.Sim.transformTo tf now .position x.2 100).1) >>= fun _ => pure (ForInStep.yield PUnit.unit)))
    (s0 : sim.state.St) (hk : k.val < s0.insts.val.length) :
    ∀ m (z : Usize) s1, t.val.length - z.val = m → z.val ≤ t.val.length → s3b_csPost P (b + m) c s0 s1 →
      ∃ s', sim.step.wiggle_state_loop3 100 s1 k now t v z = ok s' ∧
        forIn ((t.val.zip (v.val.map (fun x => (abs x : OsuModel.Sim.Vec2)))).drop z.val) PUnit.unit G (simCtxS tn fo c) (simStS tn s1) =
          .ok (PUnit.unit, simStS tn s') ∧ s3b_csPost P b c s0 s' := by
  intro m
  induction m with
  | zero =>
    intro z s1 hm hz hI
    have hnl : ¬ z < alloc.vec.Vec.len t := by rw [vec_lt_len_iff]; omega
    refine ⟨s1, ?_, ?_, by simpa using hI⟩
    · unfold sim.step.wiggle_state_loop3; rw [loop_unfold]
      simp [sim.step.wiggle_state_loop3.body, hnl]
    · rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl
  | succ m ih =>
    intro z s1 hm hz hI
    have hzl : z.val < t.val.length := by omega
    have hzv : z.val < v.val.length := by omega
    have hlt : z < alloc.vec.Vec.len t := by rw [vec_lt_len_iff]; exact hzl
    have hk1 : k.val < s1.insts.val.length := by rw [hI.2.2.1]; exact hk
    obtain ⟨z1, hz1, hz1v⟩ := usize_add_one z (by have := t.property; omega)
    obtain ⟨sq, tf1, h3, e2, q2⟩ := s3c_seg tn fo E (b + m) c s1 k hk1 now (t.val[z.val]'hzl) (v.val[z.val]'hzv) hI.1
      (by rw [show b + m + 1 = b + (m + 1) by omega]; exact hI.2.1)
    obtain ⟨s', h', e', q'⟩ := ih z1 (s3b_waSt s1 k hk1 tf1) (by omega) (by omega) (s3c_csPost_trans hI q2)
    have hstep : sim.step.wiggle_state_loop3 100 s1 k now t v z =
        sim.step.wiggle_state_loop3 100 (s3b_waSt s1 k hk1 tf1) k now t v z1 := by
      unfold sim.step.wiggle_state_loop3; rw [loop_unfold]
      simp only [sim.step.wiggle_state_loop3.body, if_pos hlt, vec_index_eq _ _ hzl, vec_index_eq _ _ hzv, bind_ok,
        sim.step.with_abs_begin_eq _ _ _ _ hk1, s3b_index_mut_set _ _ _ hk1, h3, uncurry_apply_pair]
      rw [s3b_waR_end s1 k hk1 _ tf1]
      simp only [bind_ok, hz1]
    refine ⟨s', by rw [hstep]; exact h', ?_, q'⟩
    have hzz : z.val < (t.val.zip (v.val.map (fun x => (abs x : OsuModel.Sim.Vec2)))).length := by simp; omega
    rw [List.drop_eq_getElem_cons hzz, List.forIn_cons, hG]
    simp only [List.getElem_zip, List.getElem_map]
    rw [s3b_bind_ok' _ _ _ _ _ _ (s3b_cs_yield _ _ _ _ e2)]
    rw [hz1v] at e'
    exact e'


/-! ## `wiggle_state` -/
theorem s3c_i32_cast_i64 (x : I32) : (IScalar.cast .I64 x).val = x.val := by
  simp [IScalar.cast_val_eq]; try scalar_tac

theorem s3c_hundreds (x : I32) : ∃ n, sim.step.hundreds (IScalar.cast .I64 x) = ok n ∧ n.val = (x.val / 100).toNat := by
  have hc := s3c_i32_cast_i64 x
  have hb1 := x.hmin; have hb2 := x.hmax
  unfold sim.step.hundreds
  split
  · rename_i hle
    have : (IScalar.cast .I64 x).val ≤ 0 := by simpa using hle
    refine ⟨_, rfl, ?_⟩
    simp; omega
  · rename_i hlt
    have : ¬ (IScalar.cast .I64 x).val ≤ 0 := by simpa using hlt
    obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (I64.div_spec (x := IScalar.cast .I64 x) (y := 100#i64) (by simp) (by simp))
    refine ⟨_, by rw [hq, bind_ok], ?_⟩
    simp at hqv
    have hx : x.val < 2 ^ 31 := by simpa using hb2
    have hx0 : 0 < x.val := by omega
    rw [IScalar.hcast_val_eq, hqv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    rw [Int.emod_eq_of_lt (by omega) (by simp; omega)]

theorem s3c_n2 (x : I32) : ∃ n, (if IScalar.cast .I64 x ≤ 0#i64 then ok 0#u64 else ok (IScalar.hcast .U64 (IScalar.cast .I64 x))) =
    (ok n : Result U64) ∧ n.val = x.val.toNat := by
  have hc := s3c_i32_cast_i64 x
  have hb1 := x.hmin; have hb2 := x.hmax
  split
  · rename_i hle
    have : (IScalar.cast .I64 x).val ≤ 0 := by simpa using hle
    exact ⟨_, rfl, by simp; omega⟩
  · rename_i hlt
    have : ¬ (IScalar.cast .I64 x).val ≤ 0 := by simpa using hlt
    refine ⟨_, rfl, ?_⟩
    have hx : x.val < 2 ^ 31 := by simpa using hb2
    rw [IScalar.hcast_val_eq, hc, Int.emod_eq_of_lt (by omega) (by simp; omega)]

set_option maxHeartbeats 1600000 in
theorem sim.step.wiggle_state_refines (tn fo) {P : Nat → sim.transforms.TObj → Prop} (E : s3b_TfEng P) (b : Nat)
    (c : sim.state.Ctx) (s : sim.state.St) (i : Usize) (p : sim.step.Part) (k : Usize) (h : sim.playable.HObj)
    (strength now : F64) (hinv : SimInv c s) (hP : s3b_TfInv P (b + s3c_W) s) (hk : k.val < s.insts.val.length)
    (hi : i.val < c.pb.objects.val.length) :
    ∃ s', sim.step.wiggle_state c s i p k h strength now = ok s' ∧
      s3c_wigSpec (topS tn (c.pb.objects.val[i.val]'hi)) (abs p) (hobjS tn h) k.val now strength
        (simCtxS tn fo c) (simStS tn s) = .ok (.yield PUnit.unit, simStS tn s') ∧ s3b_csPost P b c s s' := by
  have hI : OsuModel.Sim.Sim.instOf k.val (simCtxS tn fo c) (simStS tn s) =
      .ok (abs (s.insts.val[k.val]'hk), simStS tn s) := by
    have hk' : k.val < (simStS tn s).insts.size := by simpa [s3b_stS_insts] using hk
    simp only [OsuModel.Sim.Sim.instOf, simM_bind, OsuModel.Sim.Sim.st, simM_get, s3b_ebok, OsuModel.Sim.Sim.getA,
      dif_pos hk', simM_pure]
    simp [s3b_stS_insts]
  obtain ⟨rng0, hc, oc, ec⟩ := net.random.create_refines (⟨(F64.toInt32 h.start).toBitVec⟩ : I32)
  obtain ⟨n1, hn1, hn1v⟩ := s3c_hundreds (⟨(F64.toInt32 h.preempt).toBitVec⟩ : I32)
  have hX1 := (⟨(F64.toInt32 h.preempt).toBitVec⟩ : I32).hmax
  have hX1' := (⟨(F64.toInt32 h.preempt).toBitVec⟩ : I32).hmin
  simp only [i32mk_val] at hn1v hX1 hX1'
  have hn1b : n1.val ≤ 21474836 := by
    rw [hn1v]; have : (F64.toInt32 h.preempt).toInt < 2 ^ 31 := by simpa using hX1
    omega
  have hR0 : s3cR rng0 (alloc.vec.Vec.new F64) (alloc.vec.Vec.new sim.basic.Vec2)
      (NetRandom.create (hobjS tn h).start.toInt32, #[]) :=
    ⟨oc, by rw [ec]; rfl, rfl, rfl⟩
  obtain ⟨rng1, t1, v1, hl0, hR1, hlen1⟩ := s3c_loop0 h.start h.preempt strength ((s.insts.val[k.val]'hk).tf.pos) n1 (by omega) n1.val 0#u64 rng0
    _ _ _ (by simp) (by simp) (by simp; omega) hR0
  have ht1 : t1.val.length = n1.val := by simpa using hlen1
  have hR1' : s3cR rng1 t1 v1 (List.foldl (fun s_1 q => s3c_gstep ((hobjS tn h).start - (hobjS tn h).preempt) strength
      (abs (s.insts.val[k.val]'hk).tf.pos) q s_1) (NetRandom.create (hobjS tn h).start.toInt32, #[]) (List.range' 0 n1.val)) := hR1
  have hn1s : n1.val = ((hobjS tn h).preempt.toInt32.toInt / 100).toNat := hn1v
  have hW : 21474836 + (2 ^ 31 - 1) ≤ s3c_W := by unfold s3c_W; omega
  unfold s3c_wigSpec
  rw [simM_bind, hI, s3b_ebok]
  dsimp only
  rw [simM_bind, s3c_forIn_range_pure _ _ _ (s3c_gstep ((hobjS tn h).start - (hobjS tn h).preempt) strength (abs (s.insts.val[k.val]'hk).tf.pos))
    ?hF, s3b_ebok]
  case hF => intro q s; rfl
  dsimp only
  rw [s3c_durS_eq, ← hn1s]
  rcases hd : s3c_durR (c.pb.objects.val[i.val]'hi) p with _ | d
  · -- no duration loop
    obtain ⟨s', h', e', q'⟩ := s3c_loop3 tn fo E b c k now t1 v1 hR1.2.2.1
      (fun x _ => OsuModel.Sim.Sim.withAbs k.val now x.1 (fun tf => (OsuModel.Sim.transformTo tf now .position x.2 100).1)
        >>= fun _ => pure (ForInStep.yield PUnit.unit)) (fun _ _ => rfl) s hk t1.val.length 0#usize s (by simp) (by simp)
      (s3b_csPost_refl E (b' := b + s3c_W) (by omega) c s hinv hP)
    refine ⟨s', ?_, ?_, q'⟩
    · unfold sim.step.wiggle_state
      simp only [vec_index_eq _ _ hi, vec_index_eq _ _ hk, bind_ok, float.F64.to_i32_sat, lift, hc, hn1, hl0,
        uncurry_apply_pair, part_eq_ok]
      revert hd
      cases p <;> cases hK : (c.pb.objects.val[i.val]'hi).h.kind <;> cases hsl : (c.pb.objects.val[i.val]'hi).slider <;>
        cases hsp : (c.pb.objects.val[i.val]'hi).spinner <;>
        simp [s3c_durR, hK, hsl, hsp, sim.step.Part.read_discriminant] <;>
        (rw [sim.step.wiggle_state_loop1_eq]; exact h')
    · dsimp only
      rw [← Array.forIn_toList, hR1'.2.2.2]
      refine (s3b_bind_ok' _ _ _ _ PUnit.unit _ ?_).trans rfl
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at e'
      exact e'
  · -- the duration loop
    obtain ⟨N2, hN2, hN2v⟩ := s3c_n2 (⟨(F64.toInt32 (d / 100)).toBitVec⟩ : I32)
    have hX2 := (⟨(F64.toInt32 (d / 100)).toBitVec⟩ : I32).hmax
    have hN2' : (if (F64.toInt32 (d / 100)).toInt ≤ 0 then 0#u64 else IScalar.hcast UScalarTy.U64
        (IScalar.cast IScalarTy.I64 (⟨(F64.toInt32 (d / 100)).toBitVec⟩ : I32))) = N2 := by
      simpa using hN2
    simp only [i32mk_val] at hN2v hX2
    have hN2b : N2.val ≤ 2 ^ 31 - 1 := by
      rw [hN2v]; have : (F64.toInt32 (d / 100)).toInt < 2 ^ 31 := by simpa using hX2
      omega
    have hN2s : N2.val = (F64.toInt32 (d / 100)).toInt.toNat := hN2v
    obtain ⟨rng2, t2, v2, hl2, hR2, hlen2⟩ := s3c_loop2 h.start strength ((s.insts.val[k.val]'hk).tf.pos) N2 (by omega) N2.val 0#u64 rng1 t1 v1
      _ (by simp) (by simp) (by omega) hR1'
    have ht2 : t2.val.length = n1.val + N2.val := by simpa [ht1] using hlen2
    have hR2' : s3cR rng2 t2 v2 (List.foldl (fun s_1 q => s3c_gstep (hobjS tn h).start strength
        (abs (s.insts.val[k.val]'hk).tf.pos) q s_1) (List.foldl (fun s_1 q => s3c_gstep ((hobjS tn h).start - (hobjS tn h).preempt) strength
          (abs (s.insts.val[k.val]'hk).tf.pos) q s_1) (NetRandom.create (hobjS tn h).start.toInt32, #[]) (List.range' 0 n1.val)) (List.range' 0 N2.val)) := hR2
    obtain ⟨s', h', e', q'⟩ := s3c_loop3 tn fo E b c k now t2 v2 hR2.2.2.1
      (fun x _ => OsuModel.Sim.Sim.withAbs k.val now x.1 (fun tf => (OsuModel.Sim.transformTo tf now .position x.2 100).1)
        >>= fun _ => pure (ForInStep.yield PUnit.unit)) (fun _ _ => rfl) s hk t2.val.length 0#usize s (by simp) (by simp)
      (s3b_csPost_refl E (b' := b + s3c_W) (by omega) c s hinv hP)
    refine ⟨s', ?_, ?_, q'⟩
    · unfold sim.step.wiggle_state
      simp only [vec_index_eq _ _ hi, vec_index_eq _ _ hk, bind_ok, float.F64.to_i32_sat, lift, hc, hn1, hl0,
        uncurry_apply_pair, part_eq_ok]
      revert hd
      cases p <;> cases hK : (c.pb.objects.val[i.val]'hi).h.kind <;> cases hsl : (c.pb.objects.val[i.val]'hi).slider <;>
        cases hsp : (c.pb.objects.val[i.val]'hi).spinner <;>
        simp [s3c_durR, hK, hsl, hsp, sim.step.Part.read_discriminant] <;>
        (try intro hdd) <;> (try subst hdd) <;>
        first | (simp only [fb64_4636737291354636288, float.F64.div, bind_ok, hN2, hl2, uncurry_apply_pair]; exact h') | (simp only [hN2', hl2, bind_ok, uncurry_apply_pair]; exact h')
    · dsimp only
      rw [simM_bind, s3c_forIn_range_pure _ _ _ (s3c_gstep (hobjS tn h).start strength (abs (s.insts.val[k.val]'hk).tf.pos)) ?hF2, s3b_ebok]
      case hF2 => intro q s; rfl
      dsimp only
      rw [← hN2s, Prod.mk.eta, ← Array.forIn_toList, hR2'.2.2.2]
      refine (s3b_bind_ok' _ _ _ _ PUnit.unit _ ?_).trans rfl
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at e'
      exact e'

end OsuProofs
