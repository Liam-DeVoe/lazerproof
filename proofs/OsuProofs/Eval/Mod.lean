/-
`eval/mod.rs` glue (the stages of `eval::evaluate`) refines the staged spec `ev_specEval` (E2EBase.lean):
decode_beatmap, decode_osr, without_unseeded (+ unseeded_random), find_unseeded, gameplay_playable, same_settings/
same_mod/same_mods, decode_time_check, decode_frames, step_times_of, initial_speeds, true_gameplay_rate, sched_ctx,
resolve_mods (without_classic, replace_or_append, apply_overrides, is_autoplay/has_autoplay).
Callees of other slices enter through `EvalAssumptions` (or are proved: `beatmap.decoder.decode_refines`).
-/
import OsuProofs.Eval.Osr
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

/-- "keep or drop the i-th element" loops (`Vec::push` of a clone when `keep`). -/
theorem ev_filter_loop {X : Type} (body : alloc.vec.Vec X × Usize → Result (ControlFlow (alloc.vec.Vec X × Usize) (alloc.vec.Vec X)))
    (l : List X) (keep : X → Bool)
    (hstep : ∀ out i (h : i.val < l.length), out.val.length < Usize.max →
      ∃ out' i', body (out, i) = ok (.cont (out', i')) ∧
        out'.val = (if keep (l[i.val]'h) then out.val ++ [l[i.val]'h] else out.val) ∧ i'.val = i.val + 1)
    (hend : ∀ out i, l.length ≤ i.val → body (out, i) = ok (.done out)) :
    ∀ out i, i.val ≤ l.length → out.val.length + (l.length - i.val) ≤ Usize.max →
      ∃ r, loop body (out, i) = ok r ∧ r.val = out.val ++ (l.drop i.val).filter keep := by
  intro out i
  induction hk : l.length - i.val using Nat.strong_induction_on generalizing out i with
  | _ k ih =>
    intro hle hmax
    by_cases hlt : i.val < l.length
    · obtain ⟨out', i', hb, hout, hi⟩ := hstep out i hlt (by omega)
      have hl' : out'.val.length ≤ out.val.length + 1 := by rw [hout]; split <;> simp
      obtain ⟨r, hl, hr⟩ := ih (l.length - i'.val) (by omega) out' i' rfl (by omega) (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
      rw [hr, hout, hi, List.drop_eq_getElem_cons hlt, List.filter_cons]
      split <;> simp_all
    · refine ⟨out, by rw [loop_unfold, hend out i (by omega)]; simp only [bind_ok], ?_⟩
      rw [List.drop_eq_nil_of_le (by omega)]; simp

end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_i32S_eq0 (x : I32) : (i32S x = 0) ↔ x = 0#i32 := by
  rw [← ev_i32S_zero]; exact abs_i32S_inj x 0#i32

theorem eval.decode_beatmap_refines (bm osr : Slice U8) (hb : InputBounds bm osr) :
    ∃ r, eval.decode_beatmap bm = ok r ∧ ev_rjRel dec_dbS r (evS_beatmap (bytesS bm)) := by
  obtain ⟨N, hN, hpath, hsize⟩ := hb.decLines
  obtain ⟨r, hr, hrel⟩ := beatmap.decoder.decode_refines bm hb.bmLen hb.h64 N hN hpath hsize
  unfold eval.decode_beatmap evS_beatmap
  rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Ok d =>
    cases hD : OsuModel.Beatmap.LegacyBeatmapDecoder.decode (bytesS bm) with
    | error _ => intro h; exact h.elim
    | ok D =>
      intro h; simp only [hRel] at h; subst h
      by_cases h0 : d.ruleset_id = 0#i32
      · refine ⟨.Ok d, by simp [h0], ?_⟩
        simp [OsuModel.Eval.liftE, (ev_i32S_eq0 _).mpr h0, dec_dbS, ev_rjRel, pure, Except.pure]
      · refine ⟨.Err ⟨.BeatmapDecode, .OtherRuleset d.ruleset_id⟩, by simp [h0, eval.reject], ?_⟩
        have : ¬ i32S d.ruleset_id = 0 := fun hh => h0 ((ev_i32S_eq0 _).mp hh)
        simp [OsuModel.Eval.liftE, dec_dbS, this, ev_rjRel, OsuModel.Eval.reject, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, ev_stageS]
  | Err e =>
    cases hD : OsuModel.Beatmap.LegacyBeatmapDecoder.decode (bytesS bm) with
    | ok _ => intro h; exact h.elim
    | error _ =>
      intro _
      refine ⟨.Err ⟨.BeatmapDecode, .Decode e⟩, by simp [eval.reject], ?_⟩
      simp [OsuModel.Eval.liftE, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_vstr_beq (a : alloc.vec.Vec U32) (l : List Char) :
    (vstrS a == String.ofList l) = decide (a.val.map chOf = l) := by
  by_cases h : a.val.map chOf = l
  · simp [vstrS, h]
  · have : ¬ vstrS a = String.ofList l := fun hh => h (String.ofList_inj.mp hh)
    simp [this, h]

theorem ev_str_eq_vec (a : alloc.vec.Vec U32) (ha : VValid a) (lit : Slice U8) :
    beatmap.dotnet.str_eq (alloc.vec.Vec.deref a) lit = ok (decide (a.val.map chOf = litS lit)) := by
  rw [beatmap.dotnet.str_eq_refines _ (by intro u hu; exact ha u (by simpa using hu))]
  simp [strS]

theorem eval.unseeded_random_refines (m : beatmap.mod_settings.ModConfig) (hm : ev_mcOk m) :
    eval.unseeded_random m = ok (OsuModel.Eval.unseededRandom (mcS m)) := by
  obtain ⟨hv, -, hk⟩ := hm
  obtain ⟨o, ho, hov⟩ := beatmap.mod_settings.get_opt_int_refines m hk beatmap.names.K_SEED
  have hseed : keyName beatmap.names.K_SEED.val = "seed" := by simp [beatmap.names.K_SEED, keyName, keyNames]
  rw [hseed] at hov
  have hiso : (mcS m).getOptInt "seed" = none ↔ o = none := by rw [← hov]; simp
  unfold eval.unseeded_random OsuModel.Eval.unseededRandom
  simp only [lift, bind_ok, ev_str_eq_vec _ hv, ho]
  have l1 : litS (Array.to_slice (Array.make 2#usize [82#u8, 68#u8])) = ['R', 'D'] := by decide
  have l2 : litS (Array.to_slice (Array.make 2#usize [84#u8, 80#u8])) = ['T', 'P'] := by decide
  have eRD : "RD" = String.ofList ['R', 'D'] := rfl
  have eTP : "TP" = String.ofList ['T', 'P'] := rfl
  rw [show (mcS m).known = m.known from rfl, show (mcS m).acronym = vstrS m.acronym from rfl]
  generalize (mcS m).getOptInt "seed" = g at hov hiso
  rw [eRD, eTP, ev_vstr_beq, ev_vstr_beq, l1, l2]
  cases hk : m.known <;> simp [hk]
  by_cases h1 : m.acronym.val.map chOf = ['R', 'D'] <;> by_cases h2 : m.acronym.val.map chOf = ['T', 'P'] <;>
    simp [h1, h2, core.option.Option.is_none, Option.isNone] <;> cases o <;> (subst hov; simp_all)
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.without_unseeded_refines (ms : Slice beatmap.mod_settings.ModConfig) (hms : ∀ m ∈ ms.val, ev_mcOk m) :
    ∃ r, eval.without_unseeded ms = ok r ∧ r.val = ms.val.filter (fun m => !OsuModel.Eval.unseededRandom (mcS m)) := by
  have hmax := ms.property
  unfold eval.without_unseeded eval.without_unseeded_loop
  obtain ⟨r, hr, hv⟩ := ev_filter_loop (fun x => eval.without_unseeded_loop.body ms x.1 x.2) ms.val
    (fun m => !OsuModel.Eval.unseededRandom (mcS m))
    (by
      intro out i hi hlen
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      have hu := eval.unseeded_random_refines _ (hms _ (List.getElem_mem hi))
      by_cases hk : OsuModel.Eval.unseededRandom (mcS (ms.val[i.val]'hi)) = true
      · refine ⟨out, i1, by simp [eval.without_unseeded_loop.body, (slice_lt_len_iff i ms).mpr hi, slice_index_ok ms i hi,
          hu, hk, hi1], by simp [hk], hv1⟩
      · refine ⟨vpush out (ms.val[i.val]'hi) hlen, i1, by simp [eval.without_unseeded_loop.body, (slice_lt_len_iff i ms).mpr hi,
          slice_index_ok ms i hi, hu, hk, hi1, ev_mc_clone, vec_push_ok out _ hlen], by simp [hk], hv1⟩)
    (by intro out i hi; simp [eval.without_unseeded_loop.body, (show ¬ i < Slice.len ms by scalar_tac)])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)
  exact ⟨r, hr, by simpa using hv⟩


theorem ev_filter_mcS (l : List beatmap.mod_settings.ModConfig) (p : OsuModel.Beatmap.ModConfig → Bool) :
    (l.filter (fun m => p (mcS m))).map mcS = (l.map mcS).filter p := by
  induction l with
  | nil => rfl
  | cons x t ih => by_cases h : p (mcS x) <;> simp [List.filter_cons, h, ih]
end OsuProofs

namespace OsuProofs
open OsuImpl

instance ev_inhMC : Inhabited beatmap.mod_settings.ModConfig :=
  ⟨{ acronym := alloc.vec.Vec.new _, known := false, settings := alloc.vec.Vec.new _ }⟩

/-- the index found by `find_unseeded` -/
def ev_unsIdx (l : List beatmap.mod_settings.ModConfig) : Option Nat :=
  l.findIdx? (fun m => OsuModel.Eval.unseededRandom (mcS m))

theorem eval.find_unseeded_refines (ms : Slice beatmap.mod_settings.ModConfig) (hms : ∀ m ∈ ms.val, ev_mcOk m) :
    ∃ r, eval.find_unseeded ms = ok r ∧ r.map (·.val) = ev_unsIdx ms.val := by
  have hmax := ms.property
  unfold eval.find_unseeded eval.find_unseeded_loop
  let U : Nat → Bool := fun j => OsuModel.Eval.unseededRandom (mcS (ms.val.getD j default))
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Option Usize × Usize) => eval.find_unseeded_loop.body ms x.1 x.2)
    (fun x => ms.val.length + 1 - x.2.val + (if x.1.isSome then 0 else 1))
    (fun x => x.2.val ≤ ms.val.length ∧
      (x.1 = none → ∀ j < x.2.val, U j = false) ∧
      (∀ j, x.1 = some j → j.val < x.2.val ∧ U j.val = true ∧ ∀ j' < j.val, U j' = false))
    (fun y => y.map (·.val) = ev_unsIdx ms.val)
    (by
      rintro ⟨r, i⟩ ⟨hi, hn, hs⟩
      dsimp only at hi hn hs ⊢
      have hgd : ∀ j (h : j < ms.val.length), U j = OsuModel.Eval.unseededRandom (mcS (ms.val[j]'h)) := by
        intro j h; simp [U, List.getElem?_eq_getElem h]
      cases r with
      | some j =>
        left
        refine ⟨some j, by simp [eval.find_unseeded_loop.body], ?_⟩
        obtain ⟨hj, hU, hb⟩ := hs j rfl
        simp only [Option.map_some, ev_unsIdx]
        symm; rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨by omega, by rw [← hgd _ (by omega)]; exact hU, fun k hk => ?_⟩
        rw [← hgd _ (by omega), hb k hk]; simp
      | none =>
        by_cases hlt : i.val < ms.val.length
        · right
          obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
          have hu := eval.unseeded_random_refines _ (hms _ (List.getElem_mem hlt))
          by_cases hk : OsuModel.Eval.unseededRandom (mcS (ms.val[i.val]'hlt)) = true
          · refine ⟨(some i, i1), by simp [eval.find_unseeded_loop.body, (slice_lt_len_iff i ms).mpr hlt,
              slice_index_ok ms i hlt, hu, hk, hi1], ⟨by dsimp only; omega, by simp, ?_⟩, by simp; omega⟩
            intro j hj; simp at hj; subst hj
            exact ⟨by dsimp only; omega, by rw [hgd _ hlt]; exact hk, hn rfl⟩
          · refine ⟨(none, i1), by simp [eval.find_unseeded_loop.body, (slice_lt_len_iff i ms).mpr hlt,
              slice_index_ok ms i hlt, hu, hk, hi1], ⟨by dsimp only; omega, ?_, by simp⟩, by simp; omega⟩
            intro _ j hj
            dsimp only at hj
            by_cases hji : j < i.val
            · exact hn rfl j hji
            · have : j = i.val := by omega
              subst this; rw [hgd _ hlt]; simpa using hk
        · left
          refine ⟨none, by simp [eval.find_unseeded_loop.body, (show ¬ i < Slice.len ms by scalar_tac)], ?_⟩
          simp only [Option.map_none, ev_unsIdx]
          symm; rw [List.findIdx?_eq_none_iff]
          intro x hx
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
          rw [← hgd _ hj]; exact hn rfl j (by omega))
    (none, 0#usize) ⟨by simp, by simp, by simp⟩
  exact ⟨y, hy, hq⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_unsIdx_none (l : List beatmap.mod_settings.ModConfig) :
    ev_unsIdx l = none ↔ (l.map mcS).find? OsuModel.Eval.unseededRandom = none := by
  simp [ev_unsIdx, List.findIdx?_eq_none_iff, List.find?_eq_none]

theorem eval.gameplay_playable_refines (A : EvalAssumptions) (d : beatmap.types.DecodedBeatmap)
    (mods : Slice beatmap.mod_settings.ModConfig) (hm : ∀ m ∈ mods.val, ev_mcOk m) (hpb : ev_pbOk d mods) :
    ∃ r, eval.gameplay_playable d mods = ok r ∧ ev_rjRel abs r (evS_gameplay (dec_dbS d) (mods.val.map mcS)) := by
  obtain ⟨o, ho, hov⟩ := eval.find_unseeded_refines mods hm
  unfold eval.gameplay_playable evS_gameplay
  rw [ho]; simp only [bind_ok]
  cases o with
  | some i =>
    have hne : (mods.val.map mcS).find? OsuModel.Eval.unseededRandom ≠ none := by
      intro h; rw [← ev_unsIdx_none, ← hov] at h; simp at h
    obtain ⟨m, hm'⟩ := Option.ne_none_iff_exists'.mp hne
    have hi : i.val < mods.val.length := by
      simp [ev_unsIdx] at hov; exact (List.findIdx?_eq_some_iff_getElem.mp hov.symm).1
    refine ⟨.Err ⟨.Playable, .Unseeded (mods.val[i.val]'hi).acronym⟩, ?_, ?_⟩
    · simp [slice_index_ok mods i hi, clone_vec_u32, eval.reject]
    · rw [hm']; simp [ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]
  | none =>
    have hn : (mods.val.map mcS).find? OsuModel.Eval.unseededRandom = none := by
      rw [← ev_unsIdx_none, ← hov]; simp
    rw [hn]; simp only
    obtain ⟨r, hr, hrel⟩ := A.playable d mods hm hpb
    unfold eval.playable_of; rw [hr]; simp only [bind_ok]
    revert hrel
    cases r with
    | Ok pb =>
      cases OsuModel.Eval.playableOf (dec_dbS d) (mods.val.map mcS) with
      | ok PB => intro h; exact ⟨.Ok pb, rfl, by simp [ev_eRel] at h; simp [OsuModel.Eval.liftE, ev_rjRel, h, pure, Except.pure]⟩
      | error _ => intro h; exact h.elim
    | Err e =>
      cases OsuModel.Eval.playableOf (dec_dbS d) (mods.val.map mcS) with
      | ok _ => intro h; exact h.elim
      | error _ => intro _; exact ⟨.Err ⟨.Playable, .Decode e⟩, by simp [eval.reject],
          by simp [OsuModel.Eval.liftE, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_all_loop (body : Bool × Usize → Result (ControlFlow (Bool × Usize) Bool)) (n : Nat) (P : Nat → Bool)
    (hn : n ≤ Usize.max)
    (hstep : ∀ r i, i.val < n → ∃ i' : Usize, body (r, i) = ok (.cont (r && P i.val, i')) ∧ i'.val = i.val + 1)
    (hend : ∀ r i, n ≤ i.val → body (r, i) = ok (.done r)) :
    ∀ r (i : Usize), i.val ≤ n → loop body (r, i) = ok (r && decide (∀ j, i.val ≤ j → j < n → P j = true)) := by
  intro r i
  induction hk : n - i.val using Nat.strong_induction_on generalizing r i with
  | _ k ih =>
    intro hle
    by_cases hlt : i.val < n
    · obtain ⟨i', hb, hi⟩ := hstep r i hlt
      rw [loop_unfold, hb]; simp only [bind_ok]
      rw [ih (n - i'.val) (by omega) _ i' rfl (by omega)]
      congr 1
      cases r <;> simp only [Bool.false_and, Bool.true_and]
      by_cases hp : P i.val = true
      · simp only [hp, Bool.true_and]
        congr 1; apply propext; constructor
        · intro h j hj hjn; by_cases e : j = i.val; · subst e; exact hp
          exact h j (by omega) hjn
        · intro h j hj hjn; exact h j (by omega) hjn
      · simp only [Bool.not_eq_true] at hp; simp only [hp, Bool.false_and]
        symm; simp only [decide_eq_false_iff_not, not_forall]
        exact ⟨i.val, le_refl _, hlt, by simp [hp]⟩
    · rw [loop_unfold, hend r i (by omega)]; simp only [bind_ok]
      congr 1; cases r <;> simp; intro j hj hjn; omega
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_map_chOf_inj (a b : List U32) (ha : ∀ u ∈ a, u.val.isValidChar) (hb : ∀ u ∈ b, u.val.isValidChar) :
    a.map chOf = b.map chOf ↔ a = b := by
  constructor
  · intro h
    induction a generalizing b with
    | nil => cases b <;> simp_all
    | cons x t ih =>
      cases b with
      | nil => simp at h
      | cons y u =>
        simp only [List.map_cons, List.cons.injEq] at h
        have hx := chOf_toNat x (ha x (by simp)); have hy := chOf_toNat y (hb y (by simp))
        have : x = y := UScalar.eq_of_val_eq (by rw [← hx, ← hy, h.1])
        subst this
        rw [ih u (fun v hv => ha v (by simp [hv])) (fun v hv => hb v (by simp [hv])) h.2]
  · intro h; rw [h]

theorem ev_vstr_beq_vec (a b : alloc.vec.Vec U32) (ha : VValid a) (hb : VValid b) :
    (vstrS a == vstrS b) = decide (a.val = b.val) := by
  have := ev_map_chOf_inj a.val b.val ha hb
  by_cases h : a.val = b.val
  · simp [vstrS, h]
  · have h2 : ¬ vstrS a = vstrS b := fun hh => h (this.mp (String.ofList_inj.mp hh))
    simp [h, h2]

theorem ev_key_beq (k1 k2 : U32) (h1 : k1.val < 44) (h2 : k2.val < 44) :
    (keyName k1.val == keyName k2.val) = decide (k1 = k2) := by
  have := keyName_inj k1.val k2.val h1 h2
  by_cases h : k1 = k2
  · subst h; simp
  · have : ¬ keyName k1.val = keyName k2.val := fun hh => h (UScalar.eq_of_val_eq (this.mp hh))
    simp [h, this]

theorem eval.same_settings_refines (x y : beatmap.mod_settings.ModConfig) (hx : KeysOk x.settings.val)
    (hy : KeysOk y.settings.val) :
    eval.same_settings x y = ok ((mcS x).settings.size == (mcS y).settings.size &&
      ((mcS x).settings.zip (mcS y).settings).all fun (p, q) => p.1 == q.1 && p.2 == q.2) := by
  unfold eval.same_settings
  have hxm := x.settings.property
  by_cases hl : x.settings.val.length = y.settings.val.length
  · have hne : ¬ (alloc.vec.Vec.len x.settings != alloc.vec.Vec.len y.settings) = true := by
      simp [hl]
    rw [if_neg hne]
    unfold eval.same_settings_loop
    rw [ev_all_loop (fun x_1 => eval.same_settings_loop.body x.settings y.settings x_1.1 x_1.2) x.settings.val.length
      (fun j => decide ((x.settings.val.getD j default).1 = (y.settings.val.getD j default).1) &&
        (svS (x.settings.val.getD j default).2 == svS (y.settings.val.getD j default).2)) hxm
      (by
        intro r i hi
        obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
        refine ⟨i1, ?_, hv1⟩
        have hix : i.val < x.settings.val.length := hi
        have hiy : i.val < y.settings.val.length := by omega
        have g1 : x.settings.val.getD i.val default = x.settings.val[i.val]'hix := by
          simp [List.getElem?_eq_getElem hix]
        have g2 : y.settings.val.getD i.val default = y.settings.val[i.val]'hiy := by
          simp [List.getElem?_eq_getElem hiy]
        rw [g1, g2]
        generalize hpx : x.settings.val[i.val]'hix = px
        generalize hpy : y.settings.val[i.val]'hiy = py
        have e1 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) x.settings i = ok px := by
          rw [vec_index_eq _ _ hix, hpx]
        have e2 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) y.settings i = ok py := by
          rw [vec_index_eq _ _ hiy, hpy]
        obtain ⟨k1, v1⟩ := px; obtain ⟨k2, v2⟩ := py
        unfold eval.same_settings_loop.body
        by_cases hk : k1 = k2
        · subst hk
          by_cases hb : (svS v1 == svS v2) = true
          · simp [(vec_lt_len_iff i x.settings).mpr hix, e1, e2, hi1, beatmap.mod_settings.setting_value_beq_refines, hb]
          · simp only [Bool.not_eq_true] at hb
            simp [(vec_lt_len_iff i x.settings).mpr hix, e1, e2, hi1, beatmap.mod_settings.setting_value_beq_refines, hb]
        · simp [(vec_lt_len_iff i x.settings).mpr hix, e1, e2, hi1, hk])
      (by intro r i hi; simp [eval.same_settings_loop.body, (show ¬ i < alloc.vec.Vec.len x.settings by scalar_tac)])
      true 0#usize (by simp)]
    congr 1
    simp only [mcS, valsS, List.size_toArray, List.length_map, hl, beq_self_eq_true, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Array.all_iff_forall, List.zip_toArray]
    constructor
    · intro h i hi _
      simp only [List.size_toArray, List.length_zip, List.length_map] at hi
      have hix : i < x.settings.val.length := by omega
      have hiy : i < y.settings.val.length := by omega
      have := h i (by simp) hiy
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hiy,
        Option.getD_some] at this
      simp only [List.getElem_toArray, List.getElem_zip, List.getElem_map]
      rw [ev_key_beq _ _ (hx _ (List.getElem_mem hix)) (hy _ (List.getElem_mem hiy))]
      exact this
    · intro h j _ hj
      have hix : j < x.settings.val.length := by omega
      have := h j (by simp; omega) ⟨by omega, by simp; omega⟩
      simp only [List.getElem_toArray, List.getElem_zip, List.getElem_map] at this
      rw [ev_key_beq _ _ (hx _ (List.getElem_mem hix)) (hy _ (List.getElem_mem hj))] at this
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hj,
        Option.getD_some]
      exact this
  · have hne : (alloc.vec.Vec.len x.settings != alloc.vec.Vec.len y.settings) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; exact hl (by simpa using congrArg (fun u : Usize => u.val) h)
    rw [if_pos hne]
    simp [mcS, valsS, hl]
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- the pair test of `sameMods` -/
def ev_sameModS (x y : OsuModel.Beatmap.ModConfig) : Bool :=
  x.acronym == y.acronym && x.known == y.known && x.settings.size == y.settings.size &&
    (x.settings.zip y.settings).all fun (p, q) => p.1 == q.1 && p.2 == q.2

theorem eval.same_mod_refines (x y : beatmap.mod_settings.ModConfig) (hx : ev_mcOk x) (hy : ev_mcOk y) :
    eval.same_mod x y = ok (ev_sameModS (mcS x) (mcS y)) := by
  unfold eval.same_mod ev_sameModS
  dsimp only
  rw [beatmap.dotnet.str_eq2_refines]
  simp only [bind_ok, ms_deref_val]
  have hb := ev_vstr_beq_vec x.acronym y.acronym hx.1 hy.1
  rw [show (mcS x).acronym = vstrS x.acronym from rfl, show (mcS y).acronym = vstrS y.acronym from rfl, hb,
    show (mcS x).known = x.known from rfl, show (mcS y).known = y.known from rfl]
  by_cases h1 : x.acronym.val = y.acronym.val
  · by_cases h2 : x.known = y.known
    · simp only [h1, h2, decide_true, if_true, beq_self_eq_true, Bool.true_and]
      rw [eval.same_settings_refines x y hx.2.2 hy.2.2]
    · simp [h1, h2]
  · simp [h1]

theorem eval.same_mods_refines (a b : Slice beatmap.mod_settings.ModConfig) (ha : ∀ m ∈ a.val, ev_mcOk m)
    (hb : ∀ m ∈ b.val, ev_mcOk m) :
    eval.same_mods a b = ok (OsuModel.Eval.sameMods (a.val.map mcS) (b.val.map mcS)) := by
  unfold eval.same_mods OsuModel.Eval.sameMods
  have ham := a.property
  by_cases hl : a.val.length = b.val.length
  · have hne : ¬ (Slice.len a != Slice.len b) = true := by simp [hl]
    rw [if_neg hne]
    unfold eval.same_mods_loop
    rw [ev_all_loop (fun x => eval.same_mods_loop.body a b x.1 x.2) a.val.length
      (fun j => ev_sameModS (mcS (a.val.getD j default)) (mcS (b.val.getD j default))) ham
      (by
        intro r i hi
        obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
        refine ⟨i1, ?_, hv1⟩
        have hiy : i.val < b.val.length := by omega
        have g1 : a.val.getD i.val default = a.val[i.val]'hi := by simp [List.getElem?_eq_getElem hi]
        have g2 : b.val.getD i.val default = b.val[i.val]'hiy := by simp [List.getElem?_eq_getElem hiy]
        rw [g1, g2]
        have hs := eval.same_mod_refines _ _ (ha _ (List.getElem_mem hi)) (hb _ (List.getElem_mem hiy))
        by_cases hm : ev_sameModS (mcS (a.val[i.val]'hi)) (mcS (b.val[i.val]'hiy)) = true
        · simp [eval.same_mods_loop.body, (slice_lt_len_iff i a).mpr hi, slice_index_ok a i hi, slice_index_ok b i hiy, hs, hm, hi1]
        · simp only [Bool.not_eq_true] at hm
          simp [eval.same_mods_loop.body, (slice_lt_len_iff i a).mpr hi, slice_index_ok a i hi, slice_index_ok b i hiy, hs, hm, hi1])
      (by intro r i hi; simp [eval.same_mods_loop.body, (show ¬ i < Slice.len a by scalar_tac)])
      true 0#usize (by simp)]
    congr 1
    simp only [List.length_map, hl, beq_self_eq_true, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, List.all_eq_true]
    constructor
    · intro h p hp
      obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem hp
      simp only [List.length_zip, List.length_map] at hj
      have := h j (by simp) (by omega)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < a.val.length by omega),
        List.getElem?_eq_getElem (show j < b.val.length by omega), Option.getD_some] at this
      rw [← hjp]; simp only [List.getElem_zip, List.getElem_map]; exact this
    · intro h j _ hj
      have hjy : j < b.val.length := by omega
      have := h ((a.val.map mcS)[j]'(by simp; omega), (b.val.map mcS)[j]'(by simp; omega))
        (by rw [List.mem_iff_getElem]; exact ⟨j, by simp; omega, by simp [List.getElem_zip]⟩)
      have hja : j < a.val.length := by omega
      have g1 : a.val.getD j default = a.val[j]'hja := by simp [List.getElem?_eq_getElem hja]
      have g2 : b.val.getD j default = b.val[j]'hjy := by simp [List.getElem?_eq_getElem hjy]
      rw [g1, g2]
      simp only [List.getElem_map] at this
      exact this
  · have hne : (Slice.len a != Slice.len b) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; exact hl (by simpa using congrArg (fun u : Usize => u.val) h)
    rw [if_pos hne]; simp [hl]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.decode_time_check_refines (A : EvalAssumptions) (d : beatmap.types.DecodedBeatmap)
    (dtm mods : Slice beatmap.mod_settings.ModConfig) (h1 : ∀ m ∈ dtm.val, ev_mcOk m) (h2 : ∀ m ∈ mods.val, ev_mcOk m)
    (hpb : ev_pbOk d dtm) :
    ∃ r, eval.decode_time_check d dtm mods = ok r ∧
      ev_rjRel id r (evS_dtCheck (dec_dbS d) (dtm.val.map mcS) (mods.val.map mcS)) := by
  unfold eval.decode_time_check evS_dtCheck
  rw [eval.same_mods_refines dtm mods h1 h2]; simp only [bind_ok]
  by_cases hs : OsuModel.Eval.sameMods (dtm.val.map mcS) (mods.val.map mcS) = true
  · exact ⟨.Ok (), by simp [hs], by simp [hs, ev_rjRel]⟩
  · simp only [hs, Bool.false_eq_true, if_false, Bool.not_false, if_true]
    obtain ⟨r, hr, hrel⟩ := A.playable d dtm h1 hpb
    unfold eval.playable_of; rw [hr]; simp only [bind_ok]
    revert hrel
    cases r with
    | Ok pb =>
      cases OsuModel.Eval.playableOf (dec_dbS d) (dtm.val.map mcS) with
      | ok PB => intro _; exact ⟨.Ok (), rfl, by simp [OsuModel.Eval.liftE, ev_rjRel, pure, Except.pure]⟩
      | error _ => intro h; exact h.elim
    | Err e =>
      cases OsuModel.Eval.playableOf (dec_dbS d) (dtm.val.map mcS) with
      | ok _ => intro h; exact h.elim
      | error _ => intro _; exact ⟨.Err ⟨.DecodeTimePlayable, .Decode e⟩, by simp [eval.reject],
          by simp [OsuModel.Eval.liftE, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]⟩

theorem eval.decode_osr_refines (A : EvalAssumptions) (b : Slice U8) (h64 : System.Platform.numBits = 64)
    (hb : b.val.length < 2^62) :
    ∃ r, eval.decode_osr b = ok r ∧
      (match r, OsuModel.Eval.liftE "replay-decode" (OsuModel.Replay.Osr.decode (bytesS b)) with
       | .Ok d, .ok D => ev_dsS d = D ∧ ev_dsOk d
       | .Err e, .error E => E.stage = ev_stageS e.stage
       | _, _ => False) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.decode_refines A.utf8 A.lzmaBound A.scoreInfo h64 b hb
  unfold eval.decode_osr; rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Ok d =>
    cases OsuModel.Replay.Osr.decode (bytesS b) with
    | ok D => intro h; exact ⟨.Ok d, rfl, by simpa [OsuModel.Eval.liftE, pure, Except.pure] using h⟩
    | error _ => intro h; exact h.elim
  | Err e =>
    cases OsuModel.Replay.Osr.decode (bytesS b) with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err ⟨.ReplayDecode, .Osr e⟩, by simp [eval.reject],
        by simp [OsuModel.Eval.liftE, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]⟩

theorem eval.decode_frames_refines (A : EvalAssumptions) (text : Option (alloc.vec.Vec U32)) (v : I64)
    (ht : ∀ t, text = some t → ev_VV t) :
    ∃ r, eval.decode_frames text v = ok r ∧
      ev_rjRel (fun fs => (fs.val.map abs).toArray) r (evS_frames (text.map vstrS) v.val) ∧
      ∀ fs, r = .Ok fs → fs.val.length < 2^62 ∧ ∀ f ∈ fs.val, f.actions.len.val ≤ 3 := by
  unfold eval.decode_frames evS_frames
  cases text with
  | none => exact ⟨.Ok (alloc.vec.Vec.new _), rfl, by simp [ev_rjRel], by intro fs h; simp at h; subst h; simp [alloc.vec.Vec.new]⟩
  | some t =>
    obtain ⟨hv, hl⟩ := ht t rfl
    obtain ⟨r, hr, hrel, hfl⟩ := A.frames (alloc.vec.Vec.deref t) v (by intro u hu; exact hv u (by simpa using hu))
      (by simpa using hl)
    simp only [Option.map_some]
    rw [hr]; simp only [bind_ok]
    have e : String.ofList (strS (alloc.vec.Vec.deref t)) = vstrS t := by simp [strS, vstrS]
    rw [e] at hrel
    revert hrel
    cases r with
    | Ok fs =>
      cases OsuModel.Replay.decode (vstrS t) v.val with
      | ok F => intro h; exact ⟨.Ok fs, rfl, by simp [ev_eRel] at h; simp [OsuModel.Eval.liftE, ev_rjRel, h, pure, Except.pure],
          by intro fs' h'; simp at h'; subst h'; have := hfl fs rfl; simp at this; exact ⟨by omega, this.2⟩⟩
      | error _ => intro h; exact h.elim
    | Err e =>
      cases OsuModel.Replay.decode (vstrS t) v.val with
      | ok _ => intro h; exact h.elim
      | error _ => intro _; exact ⟨.Err ⟨.ReplayFrames, .Frames e⟩, by simp [eval.reject],
          by simp [OsuModel.Eval.liftE, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS],
          by simp⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.step_times_of_refines (c : sim.state.Ctx) :
    ∃ v, eval.step_times_of c = ok v ∧ v.val = c.steps.val.map (·.time) := by
  have hmax := c.steps.property
  unfold eval.step_times_of eval.step_times_of_loop
  obtain ⟨r, hr, hv⟩ := loop_push_map (fun x => eval.step_times_of_loop.body c.steps x.1 x.2) c.steps.val.length
    (fun i => (c.steps.val.map (·.time)).getD i 0)
    (by
      intro ts i hi hm
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      have hpu : ts.val.length < Usize.max := by omega
      refine ⟨vpush ts (c.steps.val[i.val]'hi).time hpu, i1, by simp [eval.step_times_of_loop.body,
        (vec_lt_len_iff i c.steps).mpr hi, vec_index_eq _ _ hi, vec_push_ok ts _ hpu, hi1], by simp [hi], hv1⟩)
    (by intro ts i hi; simp [eval.step_times_of_loop.body, (show ¬ i < alloc.vec.Vec.len c.steps by scalar_tac)])
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len c.steps)) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity])
  refine ⟨r, hr, ?_⟩
  rw [hv]; simp [alloc.vec.Vec.with_capacity]
  apply List.ext_getElem (by simp)
  intro n h1 h2; simp at h1 ⊢; simp [List.getElem?_eq_getElem h1]
end OsuProofs
namespace OsuProofs
open OsuImpl

open OsuModel.Net

theorem eval.initial_speeds_refines (A : EvalAssumptions) (ds : Slice sim.mods.DynRate) :
    ∃ r, eval.initial_speeds ds = ok r ∧
      ev_eRel (fun v => v.val.toArray) r ((ds.val.map (abs : sim.mods.DynRate → OsuModel.Sim.DynRate)).toArray.mapM (·.initialSpeed)) ∧
      ∀ v, r = .Ok v → v.val.length = ds.val.length := by
  have hmax := ds.property
  let l : List OsuModel.Sim.DynRate := ds.val.map abs
  let P : Nat → Except NetExn (List F64) := fun i => (l.drop i).mapM (·.initialSpeed)
  have hS : (l.toArray.mapM (fun (d : OsuModel.Sim.DynRate) => d.initialSpeed)) =
      (l.mapM (fun (d : OsuModel.Sim.DynRate) => d.initialSpeed)).map List.toArray := by
    rw [List.mapM_toArray]; cases l.mapM (·.initialSpeed) <;> rfl
  unfold eval.initial_speeds eval.initial_speeds_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : alloc.vec.Vec F64 × Option net.basic.NetExn × Usize) =>
      eval.initial_speeds_loop.body ds x.1 x.2.1 x.2.2)
    (fun x => ds.val.length + 1 - x.2.2.val + (if x.2.1.isSome then 0 else 1))
    (fun x => x.2.2.val ≤ ds.val.length ∧
      (x.2.1 = none → x.1.val.length = x.2.2.val ∧ l.mapM (·.initialSpeed) = (P x.2.2.val).map (x.1.val ++ ·)) ∧
      (x.2.1.isSome → ∃ e, l.mapM (·.initialSpeed) = .error e))
    (fun y => (y.2 = none → l.mapM (·.initialSpeed) = .ok y.1.val ∧ y.1.val.length = ds.val.length) ∧
      (y.2.isSome → ∃ e, l.mapM (·.initialSpeed) = .error e))
    (by
      rintro ⟨out, err, i⟩ ⟨hi, hn, hs⟩
      dsimp only at hi hn hs ⊢
      cases err with
      | some e =>
        left; exact ⟨(out, some e), by simp [eval.initial_speeds_loop.body], by simp, fun _ => hs rfl⟩
      | none =>
        obtain ⟨hlen, hP⟩ := hn rfl
        by_cases hlt : i.val < ds.val.length
        · right
          obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
          obtain ⟨r, hr, hrel⟩ := A.dynInit (ds.val[i.val]'hlt)
          have hPi : P i.val = match (abs (ds.val[i.val]'hlt) : OsuModel.Sim.DynRate).initialSpeed with
              | .error e => .error e | .ok v => (P (i.val + 1)).map (v :: ·) := by
            simp only [P, l, List.map_drop]
            rw [List.drop_eq_getElem_cons (by simpa using hlt), List.mapM_cons]
            simp only [List.getElem_map]
            cases (abs (ds.val[i.val]'hlt) : OsuModel.Sim.DynRate).initialSpeed <;> rfl
          revert hrel
          cases r with
          | Ok v =>
            cases hI : (abs (ds.val[i.val]'hlt) : OsuModel.Sim.DynRate).initialSpeed with
            | error _ => intro h; exact h.elim
            | ok w =>
              intro h; simp only [ev_eRel, id] at h; subst h
              have hpu : out.val.length < Usize.max := by omega
              refine ⟨(vpush out v hpu, none, i1), by simp [eval.initial_speeds_loop.body, (slice_lt_len_iff i ds).mpr hlt,
                slice_index_ok ds i hlt, hr, vec_push_ok out v hpu, hi1], ⟨by dsimp only; omega, ?_, by simp⟩, by simp; omega⟩
              intro _; refine ⟨by simp; omega, ?_⟩
              rw [hP, hPi, hI, hv1]; cases P (i.val + 1) <;> simp [Except.map]
          | Err e =>
            cases hI : (abs (ds.val[i.val]'hlt) : OsuModel.Sim.DynRate).initialSpeed with
            | ok _ => intro h; exact h.elim
            | error e' =>
              intro _
              refine ⟨(out, some e, i1), by simp [eval.initial_speeds_loop.body, (slice_lt_len_iff i ds).mpr hlt,
                slice_index_ok ds i hlt, hr, hi1], ⟨by dsimp only; omega, by simp, ?_⟩, by simp; omega⟩
              intro _; exact ⟨e', by rw [hP, hPi, hI]; rfl⟩
        · left
          refine ⟨(out, none), by simp [eval.initial_speeds_loop.body, (show ¬ i < Slice.len ds by scalar_tac)], ?_, by simp⟩
          intro _
          have hP0 : P i.val = .ok [] := by
            simp only [P]; rw [List.drop_eq_nil_of_le (by simp [l]; omega)]; rfl
          rw [hP, hP0]; exact ⟨by simp [Except.map], by simp; omega⟩)
    (alloc.vec.Vec.new _, none, 0#usize) ⟨by simp, fun _ => ⟨by simp, by simp [P]; cases l.mapM (·.initialSpeed) <;> rfl⟩, by simp⟩
  obtain ⟨out, err⟩ := y
  obtain ⟨hy1, hy2⟩ := hq
  cases err with
  | none =>
    obtain ⟨h1, h2⟩ := hy1 rfl
    refine ⟨.Ok out, by simp [hy], ?_, by intro v hv; simp at hv; subst hv; exact h2⟩
    simp only [ev_eRel]; rw [hS, h1]; rfl
  | some e =>
    obtain ⟨e', h⟩ := hy2 rfl
    refine ⟨.Err e, by simp [hy], ?_, by simp⟩
    rw [hS, h]; trivial
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem ev_cfgRel_dynRates {c : sim.mods.Config} {C : OsuModel.Sim.Config} (h : ev_cfgRel c C) :
    C.dynRates = (c.dyn_rates.val.map (abs : sim.mods.DynRate → OsuModel.Sim.DynRate)).toArray := by
  have := congrArg OsuModel.Sim.Config.dynRates h
  simp [configS] at this; rw [← this]; rfl

theorem eval.true_gameplay_rate_refines (A : EvalAssumptions) (cfg : sim.mods.Config) (C : OsuModel.Sim.Config)
    (hc : ev_cfgRel cfg C) (hwf : ev_cfgWF cfg) :
    ∃ r, eval.true_gameplay_rate cfg = ok r ∧ ev_rjRel id r (evS_rate C) := by
  obtain ⟨r, hr, hrel, hlen⟩ := eval.initial_speeds_refines A (alloc.vec.Vec.deref cfg.dyn_rates)
  unfold eval.true_gameplay_rate evS_rate
  dsimp only
  rw [hr]; simp only [bind_ok]
  rw [ev_cfgRel_dynRates hc]
  simp only [ms_deref_val] at hrel hlen
  revert hrel hlen
  cases r with
  | Ok sp =>
    cases hM : (cfg.dyn_rates.val.map (abs : sim.mods.DynRate → OsuModel.Sim.DynRate)).toArray.mapM (·.initialSpeed) with
    | error _ => intro h; exact h.elim
    | ok SP =>
      intro h hl; simp only [ev_eRel] at h; subst h
      obtain ⟨x, hx, hX⟩ := A.trueRate cfg (alloc.vec.Vec.deref sp) C hc hwf (by simpa using hl sp rfl)
      refine ⟨.Ok x, by simp [hx], ?_⟩
      simp only [ms_deref_val] at hX
      simp [OsuModel.Eval.liftE, OsuModel.Sim.netStr, ev_rjRel, hX, pure, Except.pure]
  | Err e =>
    cases hM : (cfg.dyn_rates.val.map (abs : sim.mods.DynRate → OsuModel.Sim.DynRate)).toArray.mapM (·.initialSpeed) with
    | ok _ => intro h; exact h.elim
    | error _ =>
      intro _ _
      refine ⟨.Err ⟨.Sim, .Sim (.Net e)⟩, by simp [eval.sim_rej, eval.reject], ?_⟩
      simp [OsuModel.Eval.liftE, OsuModel.Sim.netStr, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw,
        ev_stageS]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Net

theorem ev_ctxRel_steps (c : sim.state.Ctx) (C : OsuModel.Sim.Ctx) (h : ev_ctxRel c C)
    (st : alloc.vec.Vec schedule.Step) (ST : Array OsuModel.Sim.Step) (hs : (st.val.map abs).toArray = ST) :
    ev_ctxRel { c with steps := st } { C with steps := ST } := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  have e : simCtxS ev_tn (alloc.vec.Vec.new _) { c with steps := st } =
      { simCtxS ev_tn (alloc.vec.Vec.new _) c with steps := (st.val.map abs).toArray } := rfl
  rw [e, h2, hs]

/-- result relation of `sched_ctx` -/
def ev_schedRel (cfg : sim.mods.Config) (C : OsuModel.Sim.Config) (spb : sim.playable.Playable) :
    core.result.Result (Usize × sim.state.Ctx) eval.Rejection → Except OsuModel.Eval.Rejection (Nat × OsuModel.Sim.Ctx) → Prop
  | .Ok (n, ctx), .ok (N, CTX) => N = n.val ∧ ctx.cfg = cfg ∧ CTX.cfg = C ∧ ctx.pb = spb ∧
      CTX.pb = playableS ev_tn spb ∧ ev_ctxRel ctx CTX
  | .Err e, .error E => E.stage = ev_stageS e.stage
  | _, _ => False

/-! ## D72: the explicit-schedule contract (`explicitRefsCheck`) and the step frame-index check (`stepFramesOk`) -/

/-- relation of a Rust `Result<(), Rejection>` check to a spec `Except String Unit` check, by stage -/
def ev_chkRel (st : String) : core.result.Result Unit eval.Rejection → Except String Unit → Prop
  | .Ok _, .ok _ => True
  | .Err e, .error _ => ev_stageS e.stage = st
  | _, _ => False

theorem ev_explicit_body (refs : Slice F64) (prev : F64) (i : Usize) (x : F64) (hlt : i.val < refs.val.length)
    (hx : refs.val[i.val]'hlt = x) :
    eval.explicit_refs_check_loop.body refs prev i =
      if (x - x == 0) = true then
        (if x < prev then ok (ControlFlow.done (core.result.Result.Err (eval.Rejection.mk eval.Stage.Sim (eval.Reason.Schedule eval.ScheduleErr.Decreasing))))
         else do let i2 ← i + 1#usize; ok (ControlFlow.cont (x, i2)))
      else ok (ControlFlow.done (core.result.Result.Err (eval.Rejection.mk eval.Stage.Sim (eval.Reason.Schedule eval.ScheduleErr.NonFinite)))) := by
  have hlt' : i < Slice.len refs := by rw [slice_lt_len_iff]; exact hlt
  simp only [eval.explicit_refs_check_loop.body, hlt', if_true, slice_index_ok _ _ hlt, hx, bind_ok,
    float.F64.sub, float.F64.eq, float.F64.lt, netx_F64_ZERO, eval.reject, decide_eq_true_eq]

theorem ev_explicit_loop (refs : Slice F64) :
    ∀ n (prev : F64) (i : Usize), refs.val.length - i.val = n → i.val ≤ refs.val.length →
      ∃ r, eval.explicit_refs_check_loop refs prev i = ok r ∧
        ev_chkRel "sim" r (OsuModel.Eval.explicitRefsScan (refs.val.drop i.val) prev) := by
  intro n
  induction n with
  | zero =>
    intro prev i hn hi
    have hdn : refs.val.drop i.val = [] := List.drop_of_length_le (by omega)
    refine ⟨.Ok (), ?_, by simp [hdn, OsuModel.Eval.explicitRefsScan, ev_chkRel, pure, Except.pure]⟩
    unfold eval.explicit_refs_check_loop; rw [loop_unfold]
    have : ¬ (i < Slice.len refs) := by rw [slice_lt_len_iff]; omega
    simp [eval.explicit_refs_check_loop.body, this]
  | succ n ih =>
    intro prev i hn hi
    have hlt : i.val < refs.val.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, refs.val[i.val]'hlt = x := ⟨_, rfl⟩
    rw [List.drop_eq_getElem_cons hlt, hx]
    have hU : i.val + 1 ≤ Usize.max := by have := refs.property; omega
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i hU
    have hb := ev_explicit_body refs prev i x hlt hx
    unfold eval.explicit_refs_check_loop; rw [loop_unfold]; dsimp only; rw [hb]
    by_cases hf : (x - x == 0) = true
    · by_cases hl : x < prev
      · refine ⟨.Err ⟨.Sim, .Schedule .Decreasing⟩, by simp [hf, hl], ?_⟩
        simp [OsuModel.Eval.explicitRefsScan, hf, hl, ev_chkRel, ev_stageS, throw, throwThe, MonadExceptOf.throw]
      · obtain ⟨r, hr, er⟩ := ih x i1 (by omega) (by omega)
        refine ⟨r, ?_, ?_⟩
        · simp only [hf, hl, if_true, if_false, hi1, bind_ok]
          unfold eval.explicit_refs_check_loop at hr; exact hr
        · rw [ei1] at er; simpa [OsuModel.Eval.explicitRefsScan, hf, hl] using er
    · refine ⟨.Err ⟨.Sim, .Schedule .NonFinite⟩, by simp [hf], ?_⟩
      simp [OsuModel.Eval.explicitRefsScan, hf, ev_chkRel, ev_stageS, throw, throwThe, MonadExceptOf.throw]

theorem eval.explicit_refs_check_refines (refs : Slice F64) :
    ∃ r, eval.explicit_refs_check refs = ok r ∧ ev_chkRel "sim" r (OsuModel.Eval.explicitRefsCheck refs.val.toArray) := by
  unfold eval.explicit_refs_check OsuModel.Eval.explicitRefsCheck
  by_cases h0 : refs.val.length = 0
  · have : Slice.len refs = 0#usize := by
      apply UScalar.eq_of_val_eq; simpa using h0
    refine ⟨.Err ⟨.Sim, .Schedule .Empty⟩, by simp [this, eval.reject], ?_⟩
    simp [h0, ev_chkRel, ev_stageS, throw, throwThe, MonadExceptOf.throw]
  · have : ¬ Slice.len refs = 0#usize := by
      intro h; apply h0; have := congrArg UScalar.val h; simpa using this
    obtain ⟨r, hr, er⟩ := ev_explicit_loop refs _ F64.negInf 0#usize rfl (by simp)
    refine ⟨r, by simp [this, netx_F64_NEG_INF, hr], ?_⟩
    simpa [h0] using er

/-- `stepFramesOk` on a list of Rust steps -/
def ev_stepOk (n : Nat) (st : schedule.Step) : Bool :=
  decide (-1 ≤ st.frame_index.val) && decide (st.frame_index.val < (n : Int))

theorem ev_step_body (h64 : System.Platform.numBits = 64) (steps : Slice schedule.Step) (nf : Usize) (i : Usize)
    (s : schedule.Step) (hlt : i.val < steps.val.length) (hs : steps.val[i.val]'hlt = s) :
    eval.step_frames_ok_loop.body steps nf i =
      if ev_stepOk nf.val s then (do let i2 ← i + 1#usize; ok (ControlFlow.cont i2))
      else ok (ControlFlow.done false) := by
  have hU := usize_max_64 h64
  have hlt' : i < Slice.len steps := by rw [slice_lt_len_iff]; exact hlt
  unfold eval.step_frames_ok_loop.body
  rw [if_pos hlt', slice_index_ok _ _ hlt, hs, bind_ok]
  by_cases h1 : s.frame_index < (-1)#i64
  · have hk : ev_stepOk nf.val s = false := by
      have : ¬ (-1 ≤ s.frame_index.val) := by scalar_tac
      simp [ev_stepOk, this]
    rw [if_pos h1, hk]; rfl
  · rw [if_neg h1]
    by_cases h2 : s.frame_index >= 0#i64
    · have h2v : 0 ≤ s.frame_index.val := by scalar_tac
      have hc := sim_i64_cast_usize s.frame_index h2v (by scalar_tac)
      rw [if_pos h2]
      simp only [lift, bind_ok]
      by_cases h3 : IScalar.hcast .Usize s.frame_index >= nf
      · have hk : ev_stepOk nf.val s = false := by
          have : ¬ (s.frame_index.val < (nf.val : Int)) := by scalar_tac
          simp [ev_stepOk, this]
        rw [if_pos h3, hk]; rfl
      · have hk : ev_stepOk nf.val s = true := by
          have : (s.frame_index.val < (nf.val : Int)) := by scalar_tac
          have : -1 ≤ s.frame_index.val := by scalar_tac
          simp [ev_stepOk, *]
        rw [if_neg h3, hk]; rfl
    · have hk : ev_stepOk nf.val s = true := by
        have : -1 ≤ s.frame_index.val := by scalar_tac
        have : s.frame_index.val < (nf.val : Int) := by scalar_tac
        simp [ev_stepOk, *]
      rw [if_neg h2, hk]; rfl

theorem ev_step_frames_loop (h64 : System.Platform.numBits = 64) (steps : Slice schedule.Step) (nf : Usize) :
    ∀ k (i : Usize), steps.val.length - i.val = k → i.val ≤ steps.val.length →
      eval.step_frames_ok_loop steps nf i = ok ((steps.val.drop i.val).all (ev_stepOk nf.val)) := by
  have hU := usize_max_64 h64
  intro k
  induction k with
  | zero =>
    intro i hn hi
    have hdn : steps.val.drop i.val = [] := List.drop_of_length_le (by omega)
    unfold eval.step_frames_ok_loop; rw [loop_unfold]
    have : ¬ (i < Slice.len steps) := by rw [slice_lt_len_iff]; omega
    simp [eval.step_frames_ok_loop.body, this, hdn]
  | succ k ih =>
    intro i hn hi
    have hlt : i.val < steps.val.length := by omega
    obtain ⟨s, hs⟩ : ∃ s, steps.val[i.val]'hlt = s := ⟨_, rfl⟩
    rw [List.drop_eq_getElem_cons hlt, hs, List.all_cons]
    have hUi : i.val + 1 ≤ Usize.max := by have := steps.property; omega
    obtain ⟨i1, hi1, ei1⟩ := usize_add_one i hUi
    have hrec := ih i1 (by omega) (by omega)
    rw [ei1] at hrec
    have hb := ev_step_body h64 steps nf i s hlt hs
    unfold eval.step_frames_ok_loop; rw [loop_unfold]; (try dsimp only); rw [hb]
    by_cases hk : ev_stepOk nf.val s = true
    · rw [if_pos hk, hk, Bool.true_and]
      simp only [hi1, bind_ok]
      unfold eval.step_frames_ok_loop at hrec; exact hrec
    · have hk' : ev_stepOk nf.val s = false := by simpa using hk
      rw [if_neg hk, hk', Bool.false_and]; simp only [bind_ok]

theorem eval.step_frames_ok_refines (h64 : System.Platform.numBits = 64) (steps : Slice schedule.Step) (nf : Usize) :
    eval.step_frames_ok steps nf =
      ok (OsuModel.Eval.stepFramesOk (steps.val.map (abs : schedule.Step → OsuModel.Sim.Step)).toArray nf.val) := by
  unfold eval.step_frames_ok
  rw [ev_step_frames_loop h64 steps nf _ 0#usize rfl (by simp)]
  simp [OsuModel.Eval.stepFramesOk, ev_stepOk, abs, List.all_map, Function.comp_def] <;> rfl

theorem eval.sched_ctx0_refines (A : EvalAssumptions) (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env)
    (cfg : sim.mods.Config) (spb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame)
    (sched : eval.Schedule) (C : OsuModel.Sim.Config) (hc : ev_cfgRel cfg C) (hfs : fs.val.length < 2^62)
    (hmb : ev_mkBounds spb fs)
    (hsched : ∀ refs, sched = .Explicit refs → refs.val.length * 100000000 + 4 < 2^61) :
    ∃ r, eval.sched_ctx0 env cfg spb fs sched = ok r ∧
      ev_schedRel cfg C spb r (evS_sched0 (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray (ev_schedS sched)) ∧
      ∀ n ctx, r = .Ok (n, ctx) → ev_ctxWF ctx := by
  have hU := usize_max_64 h64
  obtain ⟨ft, hft, eft⟩ := A.frameTimes (alloc.vec.Vec.deref fs)
  obtain ⟨g, hg, eg⟩ := A.gst spb
  obtain ⟨r0, hr0, er0⟩ := A.r0 spb
  obtain ⟨e, he, ee⟩ := A.endT spb
  simp only [ms_deref_val] at eft
  have hftl : ft.val.length = fs.val.length := by
    have := congrArg Array.size eft; simpa using this.symm
  unfold eval.sched_ctx0
  simp only [ms_deref_val]
  rw [hft, hg, hr0, he]; simp only [bind_ok]
  cases sched with
  | Kind k =>
    simp only [ev_schedS, evS_sched0]
    rw [er0, ee, eft]
    obtain ⟨rr, hrr, hrrel⟩ := A.references k r0 e (alloc.vec.Vec.deref ft) (by simp; omega)
    simp only [ms_deref_val] at hrrel
    rw [hrr]; simp only [bind_ok]
    revert hrrel
    cases rr with
    | Err x =>
      cases OsuModel.Sim.references (ev_kindS k) r0 e ft.val.toArray with
      | ok _ => intro h; exact h.elim
      | error _ => intro _; exact ⟨.Err ⟨.Sim, .Sim x⟩, by simp [eval.sim_rej, eval.reject],
          by simp [OsuModel.Eval.liftE, ev_schedRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS], fun _ _ h => by cases h⟩
    | Ok refs =>
      cases OsuModel.Sim.references (ev_kindS k) r0 e ft.val.toArray with
      | error _ => intro h; exact h.elim
      | ok RS =>
        intro h; simp only [ev_eRel] at h; subst h
        obtain ⟨mc, hmc, hmcrel, hwf⟩ := A.mkCtx env cfg spb fs k C hc hmb
        rw [hmc]; simp only [bind_ok]
        revert hmcrel
        cases mc with
        | Err x =>
          cases OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray (ev_kindS k) with
          | ok _ => intro h; exact h.elim
          | error _ => intro _; exact ⟨.Err ⟨.Sim, .Sim x⟩, by simp [eval.sim_rej, eval.reject],
              by simp [OsuModel.Eval.liftE, ev_schedRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS], fun _ _ h => by cases h⟩
        | Ok ctx =>
          cases OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray (ev_kindS k) with
          | error _ => intro h; exact h.elim
          | ok CTX =>
            intro h
            exact ⟨.Ok (alloc.vec.Vec.len refs, ctx), by simp, by simpa [OsuModel.Eval.liftE, ev_schedRel, pure, Except.pure] using h, fun _ _ h => by cases h; exact hwf ctx rfl⟩
  | Explicit refs =>
    simp only [ev_schedS, evS_sched0]
    rw [eg, eft]
    obtain ⟨ck, hck, eck⟩ := eval.explicit_refs_check_refines (alloc.vec.Vec.deref refs)
    simp only [ms_deref_val] at eck
    rw [hck]; simp only [bind_ok]
    revert eck
    cases ck with
    | Err x =>
      cases OsuModel.Eval.explicitRefsCheck refs.val.toArray with
      | ok _ => intro h; exact h.elim
      | error _ =>
        intro h
        exact ⟨.Err x, by simp, by
          simp only [ev_chkRel] at h
          simp [OsuModel.Eval.liftE, ev_schedRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, h],
          fun _ _ h => by cases h⟩
    | Ok u =>
    cases OsuModel.Eval.explicitRefsCheck refs.val.toArray with
    | error _ => intro h; exact h.elim
    | ok _ =>
    intro _
    simp only [OsuModel.Eval.liftE, pure, Except.pure]
    obtain ⟨mc, hmc, hmcrel, hwf⟩ := A.mkCtx env cfg spb fs .Catchup C hc hmb
    rw [hmc]; simp only [bind_ok]
    simp only [ev_kindS] at hmcrel
    revert hmcrel
    cases mc with
    | Err x =>
      cases OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray .catchup with
      | ok _ => intro h; exact h.elim
      | error _ => intro _; exact ⟨.Err ⟨.Sim, .Sim x⟩, by simp [eval.sim_rej, eval.reject],
          by simp [OsuModel.Eval.liftE, ev_schedRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS, ev_kindS], fun _ _ h => by cases h⟩
    | Ok ctx =>
      cases hM : OsuModel.Sim.mkCtx (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray .catchup with
      | error _ => intro h; exact h.elim
      | ok CTX =>
        intro h
        obtain ⟨h1, h2, h3, h4, h5⟩ := h
        simp only [OsuModel.Eval.liftE, pure, Except.pure]
        obtain ⟨ss, hss, hssrel⟩ := A.simulateSteps (alloc.vec.Vec.deref refs) (alloc.vec.Vec.deref ft) g (by simpa using hsched refs rfl)
        simp only [ms_deref_val] at hssrel
        rw [hss]; simp only [bind_ok]
        revert hssrel
        cases ss with
        | Err x =>
          cases OsuModel.Sim.simulateSteps refs.val.toArray ft.val.toArray g with
          | ok _ => intro h; exact h.elim
          | error _ => intro _; exact ⟨.Err ⟨.Sim, .Sim x⟩, by simp [eval.sim_rej, eval.reject],
              by simp [ev_schedRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS], fun _ _ h => by cases h⟩
        | Ok st =>
          cases OsuModel.Sim.simulateSteps refs.val.toArray ft.val.toArray g with
          | error _ => intro h; exact h.elim
          | ok ST =>
            intro h; simp only [ev_eRel] at h
            exact ⟨.Ok (alloc.vec.Vec.len refs, { ctx with steps := st }), by simp,
              by simp [ev_schedRel]; exact ⟨h1, h2, h3, h4, ev_ctxRel_steps ctx CTX h5 st ST h⟩, fun _ _ h => by cases h; exact ev_ctxWF_steps ctx st (hwf ctx rfl)⟩

/-- `sched_ctx`: `sched_ctx0`, then the `stepFramesOk` check (D72); on success every step's frame index is in range
(this replaces the former trusted row `SchedFramesIn`) -/
theorem eval.sched_ctx_refines (A : EvalAssumptions) (h64 : System.Platform.numBits = 64) (env : sim.geometry.Env)
    (cfg : sim.mods.Config) (spb : sim.playable.Playable) (fs : alloc.vec.Vec replay.frames.Frame)
    (sched : eval.Schedule) (C : OsuModel.Sim.Config) (hc : ev_cfgRel cfg C) (hfs : fs.val.length < 2^62)
    (hmb : ev_mkBounds spb fs)
    (hsched : ∀ refs, sched = .Explicit refs → refs.val.length * 100000000 + 4 < 2^61) :
    ∃ r, eval.sched_ctx env cfg spb fs sched = ok r ∧
      ev_schedRel cfg C spb r (evS_sched (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray (ev_schedS sched)) ∧
      (∀ n ctx, r = .Ok (n, ctx) → ev_ctxWF ctx) ∧
      (∀ n ctx, r = .Ok (n, ctx) → ∀ st ∈ ctx.steps.val,
        -1 ≤ st.frame_index.val ∧ st.frame_index.val < (ctx.frames.val.length : Int)) := by
  obtain ⟨r0, h0, rel0, wf0⟩ := eval.sched_ctx0_refines A h64 env cfg spb fs sched C hc hfs hmb hsched
  unfold eval.sched_ctx evS_sched
  rw [h0]; simp only [bind_ok]
  revert rel0
  cases r0 with
  | Err e =>
    cases evS_sched0 (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray (ev_schedS sched) with
    | ok _ => intro h; exact h.elim
    | error E =>
      intro h
      refine ⟨.Err e, rfl, h, ?_, ?_⟩ <;> intro _ _ hh <;> cases hh
  | Ok nc =>
    obtain ⟨n, ctx⟩ := nc
    cases evS_sched0 (abs env) C (playableS ev_tn spb) (fs.val.map abs).toArray (ev_schedS sched) with
    | error _ => intro h; exact h.elim
    | ok NC =>
      obtain ⟨N, CTX⟩ := NC
      intro hrel
      obtain ⟨hN, hcc, hCc, hcp, hCp, hr⟩ := hrel
      have hSt' : CTX.steps = abs ctx.steps := by
        have := congrArg OsuModel.Sim.Ctx.steps hr.2; simpa [simCtxS] using this.symm
      have hSt : CTX.steps = (ctx.steps.val.map abs).toArray := hSt'.trans rfl
      have hFr' : CTX.frames = abs ctx.frames := by
        have := congrArg OsuModel.Sim.Ctx.frames hr.2; simpa [simCtxS] using this.symm
      have hFr : CTX.frames.size = ctx.frames.val.length := by rw [hFr']; simp [abs]
      show ∃ r, (do
          let b ← eval.step_frames_ok (alloc.vec.Vec.deref ctx.steps) (alloc.vec.Vec.len ctx.frames)
          if b then ok (core.result.Result.Ok (n, ctx))
          else do
            let r1 ← eval.reject eval.Stage.Sim (eval.Reason.Schedule eval.ScheduleErr.FrameIndex)
            ok (core.result.Result.Err r1)) = ok r ∧ _
      rw [eval.step_frames_ok_refines h64]
      simp only [ms_deref_val, bind_ok]
      have hlen : (alloc.vec.Vec.len ctx.frames).val = ctx.frames.val.length := by simp
      rw [hlen, hSt, hFr]
      by_cases hb : OsuModel.Eval.stepFramesOk (ctx.steps.val.map abs).toArray ctx.frames.val.length = true
      · simp only [hb, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        refine ⟨.Ok (n, ctx), rfl, ⟨hN, hcc, hCc, hcp, hCp, hr⟩, fun _ _ h => wf0 _ _ h, ?_⟩
        intro n' c' hc' st hst
        cases hc'
        have e : OsuModel.Eval.stepFramesOk (ctx.steps.val.map abs).toArray ctx.frames.val.length =
            ctx.steps.val.all (ev_stepOk ctx.frames.val.length) := by
          simp [OsuModel.Eval.stepFramesOk, ev_stepOk, abs, List.all_map, Function.comp_def] <;> rfl
        rw [e, List.all_eq_true] at hb
        have := hb st hst
        simpa [ev_stepOk] using this
      · simp only [hb, Bool.not_false, if_true, Bool.false_eq_true, if_false]
        refine ⟨.Err ⟨.Sim, .Schedule .FrameIndex⟩, by simp [eval.reject], ?_, ?_, ?_⟩
        · simp [ev_schedRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS]
        · intro _ _ hh; cases hh
        · intro _ _ hh; cases hh
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Eval
open OsuModel.Beatmap (ModConfig)

def evR_base (d : List ModConfig) (o : OsuModel.Eval.Options) : List ModConfig :=
  let m0 := if (o.replaceMods && o.modsOverride.isSome) = true then [] else d
  if o.noClassic = true then m0.filter (fun m => !(m.known && m.acronym == "CL")) else m0

def evR_ov : List ModConfig → List ModConfig → EvalM (List ModConfig)
  | [], mods => .ok mods
  | m :: t, mods => if (!m.known) = true then reject "mods" s!"unknown mod acronym: {m.acronym}"
      else evR_ov t (mods.filter (fun x => x.acronym != m.acronym) ++ [m])

def evR_final (mods : List ModConfig) : EvalM (List ModConfig) :=
  if (mods.any fun m => m.known && (m.acronym == "AT" || m.acronym == "CN")) = true then
    reject "mods" "autoplay-type mods are not supported (they replace the replay)"
  else .ok mods

theorem evR_forIn (ov mods : List ModConfig) :
    (forIn ov mods fun m __s =>
      have mods := __s
      have __do_jp := fun (__r : PUnit) =>
        have mods := List.filter (fun x => x.acronym != m.acronym) mods ++ [m]
        (pure (ForInStep.yield mods) : EvalM _)
      if (!m.known) = true then do
        let __r ← reject "mods" (toString "unknown mod acronym: " ++ toString m.acronym)
        __do_jp __r
      else __do_jp ()) = evR_ov ov mods := by
  induction ov generalizing mods with
  | nil => rfl
  | cons m t ih =>
    rw [List.forIn_cons]
    by_cases hk : (!m.known) = true
    · simp only [hk, if_true, evR_ov, reject, throw, throwThe, MonadExceptOf.throw]; rfl
    · simp only [hk, Bool.false_eq_true, if_false, evR_ov]
      rw [← ih]; rfl

theorem evR_eq (d : List ModConfig) (o : OsuModel.Eval.Options) :
    resolveMods d o = (match (match o.modsOverride with
        | some ov => evR_ov ov (evR_base d o)
        | none => .ok (evR_base d o)) with
      | .error e => .error e
      | .ok mods => evR_final mods) := by
  unfold resolveMods evR_base evR_final
  cases hc : o.noClassic <;> cases ho : o.modsOverride <;> simp only [hc, ho, Bool.false_eq_true, if_false, if_true]
  all_goals (try rw [evR_forIn])
  all_goals (try (cases evR_ov _ _ <;> simp only [except_bind_ok, except_bind_error]))
  all_goals (split <;> rfl)
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.without_classic_refines (ms : alloc.vec.Vec beatmap.mod_settings.ModConfig) (hms : ∀ m ∈ ms.val, ev_mcOk m) :
    ∃ r, eval.without_classic ms = ok r ∧
      r.val = ms.val.filter (fun m => !((mcS m).known && (mcS m).acronym == "CL")) := by
  have hmax := ms.property
  unfold eval.without_classic eval.without_classic_loop
  have lCL : litS (Array.to_slice (Array.make 2#usize [67#u8, 76#u8])) = ['C', 'L'] := by decide
  have eCL : "CL" = String.ofList ['C', 'L'] := rfl
  obtain ⟨r, hr, hv⟩ := ev_filter_loop (fun x => eval.without_classic_loop.body ms x.1 x.2) ms.val
    (fun m => !((mcS m).known && (mcS m).acronym == "CL"))
    (by
      intro out i hi hlen
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      have hok := hms _ (List.getElem_mem hi)
      have hpu : out.val.length < Usize.max := hlen
      have hstr := ev_str_eq_vec (ms.val[i.val]'hi).acronym hok.1 (Array.to_slice (Array.make 2#usize [67#u8, 76#u8]))
      rw [lCL] at hstr
      have hk : ((mcS (ms.val[i.val]'hi)).known && ((mcS (ms.val[i.val]'hi)).acronym == "CL")) =
          ((ms.val[i.val]'hi).known && decide ((ms.val[i.val]'hi).acronym.val.map chOf = ['C', 'L'])) := by
        rw [eCL, show (mcS (ms.val[i.val]'hi)).acronym = vstrS (ms.val[i.val]'hi).acronym from rfl, ev_vstr_beq]; rfl
      rw [hk]
      by_cases h1 : (ms.val[i.val]'hi).known = true
      · by_cases h2 : (ms.val[i.val]'hi).acronym.val.map chOf = ['C', 'L']
        · refine ⟨out, i1, by simp [eval.without_classic_loop.body, (vec_lt_len_iff i ms).mpr hi, vec_index_eq _ _ hi,
            h1, lift, hstr, h2, hi1], by simp [h1, h2], hv1⟩
        · refine ⟨vpush out (ms.val[i.val]'hi) hpu, i1, by simp [eval.without_classic_loop.body, (vec_lt_len_iff i ms).mpr hi,
            vec_index_eq _ _ hi, h1, lift, hstr, h2, hi1, ev_mc_clone, vec_push_ok out _ hpu], by simp [h1, h2], hv1⟩
      · refine ⟨vpush out (ms.val[i.val]'hi) hpu, i1, by simp [eval.without_classic_loop.body, (vec_lt_len_iff i ms).mpr hi,
          vec_index_eq _ _ hi, h1, hi1, ev_mc_clone, vec_push_ok out _ hpu], by simp [h1], hv1⟩)
    (by intro out i hi; simp [eval.without_classic_loop.body, (show ¬ i < alloc.vec.Vec.len ms by scalar_tac)])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)
  exact ⟨r, hr, by simpa using hv⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_filter_loop2 {X C : Type} (body : alloc.vec.Vec X × Usize → Result (ControlFlow (alloc.vec.Vec X × Usize) (C × alloc.vec.Vec X)))
    (l : List X) (keep : X → Bool) (c : C)
    (hstep : ∀ out i (h : i.val < l.length), out.val.length < Usize.max →
      ∃ out' i', body (out, i) = ok (.cont (out', i')) ∧
        out'.val = (if keep (l[i.val]'h) then out.val ++ [l[i.val]'h] else out.val) ∧ i'.val = i.val + 1)
    (hend : ∀ out i, l.length ≤ i.val → body (out, i) = ok (.done (c, out))) :
    ∀ out i, i.val ≤ l.length → out.val.length + (l.length - i.val) ≤ Usize.max →
      ∃ r, loop body (out, i) = ok (c, r) ∧ r.val = out.val ++ (l.drop i.val).filter keep := by
  intro out i
  induction hk : l.length - i.val using Nat.strong_induction_on generalizing out i with
  | _ k ih =>
    intro hle hmax
    by_cases hlt : i.val < l.length
    · obtain ⟨out', i', hb, hout, hi⟩ := hstep out i hlt (by omega)
      have hl' : out'.val.length ≤ out.val.length + 1 := by rw [hout]; split <;> simp
      obtain ⟨r, hl, hr⟩ := ih (l.length - i'.val) (by omega) out' i' rfl (by omega) (by omega)
      refine ⟨r, by rw [loop_unfold, hb]; simpa using hl, ?_⟩
      rw [hr, hout, hi, List.drop_eq_getElem_cons hlt, List.filter_cons]
      split <;> simp_all
    · refine ⟨out, by rw [loop_unfold, hend out i (by omega)]; simp only [bind_ok], ?_⟩
      rw [List.drop_eq_nil_of_le (by omega)]; simp

theorem eval.replace_or_append_refines (ms : alloc.vec.Vec beatmap.mod_settings.ModConfig)
    (m : beatmap.mod_settings.ModConfig) (hlen : ms.val.length < Usize.max) :
    ∃ r, eval.replace_or_append ms m = ok r ∧
      r.val = ms.val.filter (fun x => !decide (x.acronym.val = m.acronym.val)) ++ [m] := by
  have hmax := ms.property
  unfold eval.replace_or_append eval.replace_or_append_loop
  obtain ⟨r, hr, hv⟩ := ev_filter_loop2 (fun x => eval.replace_or_append_loop.body ms m x.1 x.2) ms.val
    (fun x => !decide (x.acronym.val = m.acronym.val)) m
    (by
      intro out i hi hl
      obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
      by_cases h : (ms.val[i.val]'hi).acronym.val = m.acronym.val
      · refine ⟨out, i1, by simp [eval.replace_or_append_loop.body, (vec_lt_len_iff i ms).mpr hi, vec_index_eq _ _ hi,
          beatmap.dotnet.str_eq2_refines, h, hi1], by simp [h], hv1⟩
      · refine ⟨vpush out (ms.val[i.val]'hi) hl, i1, by simp [eval.replace_or_append_loop.body, (vec_lt_len_iff i ms).mpr hi,
          vec_index_eq _ _ hi, beatmap.dotnet.str_eq2_refines, h, hi1, ev_mc_clone, vec_push_ok out _ hl], by simp [h], hv1⟩)
    (by intro out i hi; simp [eval.replace_or_append_loop.body, (show ¬ i < alloc.vec.Vec.len ms by scalar_tac)])
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp)
  have hrl : r.val.length < Usize.max := by
    rw [hv]; simp; exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) hlen
  refine ⟨vpush r m hrl, by simp [hr, ev_mc_clone, vec_push_ok r m hrl], by simp [hv]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

/-- the override loop on Rust values (`none`: an unknown override mod) -/
def ev_rov : List beatmap.mod_settings.ModConfig → List beatmap.mod_settings.ModConfig →
    Option (List beatmap.mod_settings.ModConfig)
  | [], ms => some ms
  | m :: t, ms => if !m.known then none else ev_rov t (ms.filter (fun x => !decide (x.acronym.val = m.acronym.val)) ++ [m])

theorem ev_rov_len : ∀ (ov ms : List beatmap.mod_settings.ModConfig) r, ev_rov ov ms = some r →
    r.length ≤ ms.length + ov.length := by
  intro ov
  induction ov with
  | nil => intro ms r h; simp [ev_rov] at h; subst h; simp
  | cons m t ih =>
    intro ms r h
    simp only [ev_rov] at h
    split at h
    · simp at h
    · have := ih _ r h
      have := List.length_filter_le (fun x => !decide (x.acronym.val = m.acronym.val)) ms
      simp at *; omega

theorem ev_rov_ok : ∀ (ov ms : List beatmap.mod_settings.ModConfig) r, ev_rov ov ms = some r →
    (∀ x ∈ ms, ev_mcOk x) → (∀ x ∈ ov, ev_mcOk x) → ∀ x ∈ r, ev_mcOk x := by
  intro ov
  induction ov with
  | nil => intro ms r h hm _; simp [ev_rov] at h; subst h; exact hm
  | cons m t ih =>
    intro ms r h hm ho
    simp only [ev_rov] at h
    split at h
    · simp at h
    · refine ih _ r h ?_ (fun x hx => ho x (by simp [hx]))
      intro x hx; simp at hx; rcases hx with hx | hx
      · exact hm x hx.1
      · subst hx; exact ho _ (by simp)

theorem ev_rov_spec : ∀ (ov ms : List beatmap.mod_settings.ModConfig), (∀ x ∈ ms, ev_mcOk x) → (∀ x ∈ ov, ev_mcOk x) →
    (match ev_rov ov ms, evR_ov (ov.map mcS) (ms.map mcS) with
     | some r, .ok R => R = r.map mcS
     | none, .error E => E.stage = "mods"
     | _, _ => False) := by
  intro ov
  induction ov with
  | nil => intro ms _ _; simp [ev_rov, evR_ov]
  | cons m t ih =>
    intro ms hm ho
    have hmo := ho m (by simp)
    by_cases hk : m.known = true
    · have hk' : (!(mcS m).known) = false := by simp [mcS, hk]
      simp only [ev_rov, List.map_cons, evR_ov, hk, hk', Bool.not_true, Bool.false_eq_true, if_false]
      have hf : (ms.map mcS).filter (fun x => x.acronym != (mcS m).acronym) ++ [mcS m] =
          (ms.filter (fun x => !decide (x.acronym.val = m.acronym.val)) ++ [m]).map mcS := by
        rw [List.map_append, ← ev_filter_mcS]; congr 2
        apply List.filter_congr; intro x hx
        rw [show (mcS x).acronym = vstrS x.acronym from rfl, show (mcS m).acronym = vstrS m.acronym from rfl,
          bne, ev_vstr_beq_vec _ _ (hm x hx).1 hmo.1]
      rw [hf]
      apply ih
      · intro x hx; simp at hx; rcases hx with hx | hx; exact hm x hx.1; subst hx; exact hmo
      · intro x hx; exact ho x (by simp [hx])
    · have hk' : (!(mcS m).known) = true := by simp [mcS] at hk ⊢; exact hk
      simp only [ev_rov, List.map_cons, evR_ov, hk', if_true]
      simp at hk; simp [hk, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.apply_overrides_refines (ms0 : alloc.vec.Vec beatmap.mod_settings.ModConfig)
    (ov : Slice beatmap.mod_settings.ModConfig) (hlen : ms0.val.length + ov.val.length < Usize.max) :
    ∃ r, eval.apply_overrides ms0 ov = ok r ∧
      (match r, ev_rov ov.val ms0.val with
       | .Ok v, some l => v.val = l
       | .Err e, none => e.stage = .Mods
       | _, _ => False) := by
  unfold eval.apply_overrides eval.apply_overrides_loop
  let T := ev_rov ov.val ms0.val
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : alloc.vec.Vec beatmap.mod_settings.ModConfig × Option (alloc.vec.Vec U32) × Usize) =>
      eval.apply_overrides_loop.body ov x.1 x.2.1 x.2.2)
    (fun x => ov.val.length + 1 - x.2.2.val + (if x.2.1.isSome then 0 else 1))
    (fun x => x.2.2.val ≤ ov.val.length ∧
      (x.2.1 = none → ev_rov (ov.val.drop x.2.2.val) x.1.val = T ∧ x.1.val.length ≤ ms0.val.length + x.2.2.val) ∧
      (x.2.1.isSome → T = none))
    (fun y => (y.2 = none → T = some y.1.val) ∧ (y.2.isSome → T = none))
    (by
      rintro ⟨ms, err, i⟩ ⟨hi, hn, hs⟩
      dsimp only at hi hn hs ⊢
      cases err with
      | some a => left; exact ⟨(ms, some a), by simp [eval.apply_overrides_loop.body], by simp, fun _ => hs rfl⟩
      | none =>
        obtain ⟨hT, hl⟩ := hn rfl
        by_cases hlt : i.val < ov.val.length
        · right
          obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
          have hd : ov.val.drop i.val = (ov.val[i.val]'hlt) :: ov.val.drop (i.val + 1) := List.drop_eq_getElem_cons hlt
          by_cases hk : (ov.val[i.val]'hlt).known = true
          · obtain ⟨ms', hms', hv'⟩ := eval.replace_or_append_refines ms (ov.val[i.val]'hlt) (by omega)
            refine ⟨(ms', none, i1), by simp [eval.apply_overrides_loop.body, (slice_lt_len_iff i ov).mpr hlt,
              slice_index_ok ov i hlt, hk, hms', hi1], ⟨by dsimp only; omega, ?_, by simp⟩, by simp; omega⟩
            intro _
            refine ⟨?_, ?_⟩
            · rw [← hT, hd, hv1]; simp only [ev_rov, hk, Bool.not_true, Bool.false_eq_true, if_false, hv']
            · rw [hv', hv1]; simp; have := List.length_filter_le (fun x => !decide (x.acronym.val = (ov.val[i.val]'hlt).acronym.val)) ms.val
              omega
          · refine ⟨(ms, some (ov.val[i.val]'hlt).acronym, i1), by simp [eval.apply_overrides_loop.body,
              (slice_lt_len_iff i ov).mpr hlt, slice_index_ok ov i hlt, hk, clone_vec_u32, hi1],
              ⟨by dsimp only; omega, by simp, ?_⟩, by simp; omega⟩
            intro _; rw [← hT, hd]; simp [ev_rov, hk]
        · left
          refine ⟨(ms, none), by simp [eval.apply_overrides_loop.body, (show ¬ i < Slice.len ov by scalar_tac)], ?_, by simp⟩
          intro _; rw [← hT, List.drop_eq_nil_of_le (by omega)]; rfl)
    (ms0, none, 0#usize) ⟨by simp, fun _ => ⟨by simp [T], by simp⟩, by simp⟩
  obtain ⟨ms, err⟩ := y
  obtain ⟨h1, h2⟩ := hq
  cases err with
  | none =>
    have := h1 rfl
    refine ⟨.Ok ms, by simp [hy], ?_⟩
    simp only [T] at this; rw [this]
  | some a =>
    have := h2 rfl
    refine ⟨.Err ⟨.Mods, .UnknownMod a⟩, by simp [hy, eval.reject], ?_⟩
    simp only [T] at this; rw [this]
end OsuProofs

namespace OsuProofs
open OsuImpl

def ev_isAutoS (m : OsuModel.Beatmap.ModConfig) : Bool := m.known && (m.acronym == "AT" || m.acronym == "CN")

theorem eval.is_autoplay_refines (m : beatmap.mod_settings.ModConfig) (hm : ev_mcOk m) :
    eval.is_autoplay m = ok (ev_isAutoS (mcS m)) := by
  have lAT : litS (Array.to_slice (Array.make 2#usize [65#u8, 84#u8])) = ['A', 'T'] := by decide
  have lCN : litS (Array.to_slice (Array.make 2#usize [67#u8, 78#u8])) = ['C', 'N'] := by decide
  have eAT : "AT" = String.ofList ['A', 'T'] := rfl
  have eCN : "CN" = String.ofList ['C', 'N'] := rfl
  unfold eval.is_autoplay ev_isAutoS
  rw [show (mcS m).known = m.known from rfl, show (mcS m).acronym = vstrS m.acronym from rfl, eAT, eCN,
    ev_vstr_beq, ev_vstr_beq]
  simp only [lift, bind_ok, ev_str_eq_vec _ hm.1, lAT, lCN]
  cases m.known <;> by_cases h1 : m.acronym.val.map chOf = ['A', 'T'] <;> simp [h1]

theorem eval.has_autoplay_refines (ms : Slice beatmap.mod_settings.ModConfig) (hms : ∀ m ∈ ms.val, ev_mcOk m) :
    eval.has_autoplay ms = ok ((ms.val.map mcS).any ev_isAutoS) := by
  have hmax := ms.property
  unfold eval.has_autoplay eval.has_autoplay_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Bool × Usize) => eval.has_autoplay_loop.body ms x.1 x.2)
    (fun x => ms.val.length - x.2.val)
    (fun x => x.2.val ≤ ms.val.length ∧ (x.1 = true ↔ ∃ j, j < x.2.val ∧ ev_isAutoS (mcS (ms.val.getD j default)) = true))
    (fun y => y = (ms.val.map mcS).any ev_isAutoS)
    (by
      rintro ⟨r, i⟩ ⟨hi, hr⟩
      dsimp only at hi hr ⊢
      by_cases hlt : i.val < ms.val.length
      · right
        obtain ⟨i1, hi1, hv1⟩ := usize_add_one i (by omega)
        have ha := eval.is_autoplay_refines _ (hms _ (List.getElem_mem hlt))
        refine ⟨(r || ev_isAutoS (mcS (ms.val[i.val]'hlt)), i1), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · cases r <;> simp [eval.has_autoplay_loop.body, (slice_lt_len_iff i ms).mpr hlt, slice_index_ok ms i hlt, ha, hi1]
        · dsimp only; rw [Bool.or_eq_true, hr, hv1]
          constructor
          · rintro (⟨j, hj, h⟩ | h)
            · exact ⟨j, by omega, h⟩
            · exact ⟨i.val, by omega, by simpa [List.getElem?_eq_getElem hlt] using h⟩
          · rintro ⟨j, hj, h⟩
            by_cases hji : j < i.val
            · exact Or.inl ⟨j, hji, h⟩
            · have : j = i.val := by omega
              subst this; exact Or.inr (by simpa [List.getElem?_eq_getElem hlt] using h)
      · left
        refine ⟨r, by simp [eval.has_autoplay_loop.body, (show ¬ i < Slice.len ms by scalar_tac)], ?_⟩
        rw [Bool.eq_iff_iff, hr, List.any_eq_true]
        constructor
        · rintro ⟨j, hj, h⟩
          have hj' : j < ms.val.length := by omega
          exact ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem hj', rfl⟩, by simpa [List.getElem?_eq_getElem hj'] using h⟩
        · rintro ⟨x, hx, h⟩
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
          exact ⟨j, by omega, by simpa [List.getElem?_eq_getElem hj] using h⟩)
    (false, 0#usize) ⟨by simp, by simp⟩
  rw [hy, hq]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.resolve_mods_refines (h64 : System.Platform.numBits = 64) (decoded : Slice beatmap.mod_settings.ModConfig)
    (o : eval.Options) (hd : ∀ m ∈ decoded.val, ev_mcOk m) (hdl : decoded.val.length < 2^62)
    (ho : ∀ ov, o.mods_override = some ov → (∀ m ∈ ov.val, ev_mcOk m) ∧ ov.val.length < 2^62) :
    ∃ r, eval.resolve_mods decoded o = ok r ∧
      ev_rjRel (fun v => v.val.map mcS) r (OsuModel.Eval.resolveMods (decoded.val.map mcS) (ev_optsS o)) ∧
      ∀ v, r = .Ok v → ∀ m ∈ v.val, ev_mcOk m := by
  have hU := usize_max_64 h64
  rw [evR_eq]
  -- the base list (replace / no-classic)
  let base : List beatmap.mod_settings.ModConfig :=
    let m0 := if (o.replace_mods && o.mods_override.isSome) = true then [] else decoded.val
    if o.no_classic = true then m0.filter (fun m => !((mcS m).known && (mcS m).acronym == "CL")) else m0
  have hbaseS : evR_base (decoded.val.map mcS) (ev_optsS o) = base.map mcS := by
    simp only [evR_base, ev_optsS, base, Option.isSome_map]
    split <;> split
    all_goals first
      | rfl
      | exact (ev_filter_mcS _ (fun m => !(m.known && m.acronym == "CL"))).symm
      | exact (ev_filter_mcS [] (fun m => !(m.known && m.acronym == "CL"))).symm
  have hsub : ∀ m ∈ base, m ∈ decoded.val := by
    intro m hm; simp only [base] at hm
    split at hm <;> split at hm
    all_goals first | exact (List.mem_filter.mp hm).1 | exact hm | simp at hm
  have hbase_ok : ∀ m ∈ base, ev_mcOk m := fun m hm => hd m (hsub m hm)
  have hbase_len : base.length ≤ decoded.val.length := by
    simp only [base]; split <;> split <;> simp <;> exact List.length_filter_le _ _
  -- the two tails
  have tailN : ∀ ms2 : alloc.vec.Vec beatmap.mod_settings.ModConfig, ms2.val = base →
      ∃ r, (do let b ← eval.has_autoplay (alloc.vec.Vec.deref ms2)
               if b then do let r ← eval.reject eval.Stage.Mods eval.Reason.Autoplay; ok (core.result.Result.Err r)
               else ok (core.result.Result.Ok ms2)) = ok r ∧
        ev_rjRel (fun v => v.val.map mcS) r (evR_final (base.map mcS)) ∧ ∀ v, r = .Ok v → ∀ m ∈ v.val, ev_mcOk m := by
    intro ms2 hv
    rw [eval.has_autoplay_refines _ (by simpa [hv] using hbase_ok)]
    simp only [bind_ok, ms_deref_val, hv]
    unfold evR_final
    have e : (fun m : OsuModel.Beatmap.ModConfig => m.known && (m.acronym == "AT" || m.acronym == "CN")) = ev_isAutoS := rfl
    rw [e]
    by_cases hb : (base.map mcS).any ev_isAutoS = true
    · exact ⟨.Err ⟨.Mods, .Autoplay⟩, by simp [hb, eval.reject], by
        simp [hb, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS], by simp⟩
    · exact ⟨.Ok ms2, by simp [hb], by simp [hb, ev_rjRel, hv], by intro v h; simp at h; subst h; rw [hv]; exact hbase_ok⟩
  have tailS : ∀ (ms2 : alloc.vec.Vec beatmap.mod_settings.ModConfig) (ov : alloc.vec.Vec beatmap.mod_settings.ModConfig),
      ms2.val = base → (∀ m ∈ ov.val, ev_mcOk m) → ov.val.length < 2^62 →
      ∃ r, (do let r ← eval.apply_overrides ms2 (alloc.vec.Vec.deref ov)
               match r with
               | core.result.Result.Ok v => do
                 let b ← eval.has_autoplay (alloc.vec.Vec.deref v)
                 if b then do let r1 ← eval.reject eval.Stage.Mods eval.Reason.Autoplay; ok (core.result.Result.Err r1)
                 else ok r
               | core.result.Result.Err _ => ok r) = ok r ∧
        ev_rjRel (fun v => v.val.map mcS) r
          (match evR_ov (ov.val.map mcS) (base.map mcS) with
           | .error e => .error e
           | .ok mods => evR_final mods) ∧ ∀ v, r = .Ok v → ∀ m ∈ v.val, ev_mcOk m := by
    intro ms2 ov hv hov hovl
    obtain ⟨ra, hra, hrel⟩ := eval.apply_overrides_refines ms2 (alloc.vec.Vec.deref ov) (by simp [hv]; omega)
    have hspec := ev_rov_spec ov.val base hbase_ok hov
    rw [hra]; simp only [bind_ok]
    simp only [ms_deref_val, hv] at hrel
    revert hspec hrel
    cases hR : ev_rov ov.val base with
    | none =>
      cases ra with
      | Ok _ => intro a b; simp_all
      | Err e =>
        cases evR_ov (ov.val.map mcS) (base.map mcS) with
        | ok _ => intro a b; simp_all
        | error E =>
          intro a b
          have h1 : e.stage = .Mods := by first | exact a | exact b
          have h2 : E.stage = "mods" := by first | exact a | exact b
          exact ⟨.Err e, rfl, by simp only [ev_rjRel]; rw [h2, h1]; rfl, by simp⟩
    | some l =>
      cases ra with
      | Err _ => intro a b; simp_all
      | Ok v =>
        cases evR_ov (ov.val.map mcS) (base.map mcS) with
        | error _ => intro a b; simp_all
        | ok L =>
          intro a b
          have h1 : v.val = l := by first | exact a | exact b
          have h2 : L = l.map mcS := by first | exact a | exact b
          simp only
          have hlok := ev_rov_ok ov.val base l hR hbase_ok hov
          rw [eval.has_autoplay_refines _ (by simpa [h1] using hlok)]
          simp only [bind_ok, ms_deref_val, h2, h1]
          unfold evR_final
          have e : (fun m : OsuModel.Beatmap.ModConfig => m.known && (m.acronym == "AT" || m.acronym == "CN")) = ev_isAutoS := rfl
          rw [e]
          by_cases hb : (l.map mcS).any ev_isAutoS = true
          · exact ⟨.Err ⟨.Mods, .Autoplay⟩, by simp [hb, eval.reject], by
              simp [hb, ev_rjRel, OsuModel.Eval.reject, throw, throwThe, MonadExceptOf.throw, ev_stageS], by simp⟩
          · exact ⟨.Ok v, by simp [hb], by simp [hb, ev_rjRel, h1], by intro w h; simp at h; subst h; rw [h1]; exact hlok⟩
  -- the prefix
  have hdv : (⟨decoded⟩ : alloc.vec.Vec beatmap.mod_settings.ModConfig).val = decoded.val := rfl
  obtain ⟨wc, hwc, hwcv⟩ := eval.without_classic_refines ⟨decoded⟩ hd
  obtain ⟨wn, hwn, hwnv⟩ := eval.without_classic_refines (alloc.vec.Vec.new _) (by simp)
  rw [hdv] at hwcv
  unfold eval.resolve_mods
  rw [hbaseS]
  cases hr : o.replace_mods <;> cases hc : o.no_classic <;> cases ho2 : o.mods_override
  all_goals simp only [hr, hc, ho2, Bool.false_eq_true, if_false, if_true, ev_to_vec_mc, bind_ok, Option.isSome_some,
    Option.isSome_none, hwc, hwn, ev_optsS, Option.map, core.option.Option.is_some, Option.isSome]
  all_goals first
    | exact tailN _ (by simp [base, hr, hc, ho2, hwcv, hwnv, hdv])
    | exact tailS _ _ (by simp [base, hr, hc, ho2, hwcv, hwnv, hdv]) (ho _ ho2).1 (ho _ ho2).2
    | skip
end OsuProofs
