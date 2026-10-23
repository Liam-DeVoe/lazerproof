/-
`beatmap::text` (Rust) refines `OsuModel.Beatmap` `Text.lean`: `StreamReader` decoding
(BOM detection, UTF-8 with maximal-subpart U+FFFD replacement, UTF-16 BE/LE) and `ReadLine`.
Bytes `&[u8]` ↦ `ByteArray` via `bytesS`; scalar-value strings ↦ `Array Char`/`String` via `chOf`.
Every decoded scalar value is a valid `Char` (`ValidL`), which the string helpers downstream need.
Loops are in lockstep with the spec's `for _ in [0:n+1]` loops (`loop_iterId`).
-/
import OsuProofs.Beatmap.DotNetStr
import OsuProofs.Net.Parse2
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.deprecated false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Beatmap

namespace OsuProofs
open OsuImpl

def bytesS (b : Slice U8) : ByteArray := ⟨(b.val.map (fun x => UInt8.ofBitVec x.bv)).toArray⟩
theorem bytesS_size (b : Slice U8) : (bytesS b).size = b.val.length := by simp [bytesS, ByteArray.size]
theorem bytesS_get (b : Slice U8) (i : Nat) (h : i < b.val.length) : ((bytesS b)[i]!).toNat = (b.val[i]'h).val := by
  rw [getElem!_pos (bytesS b) i (by rw [bytesS_size]; exact h)]
  simp [bytesS, ByteArray.getElem_eq_getElem_data]

theorem iterId_fix {β} (g : β → ForInStep β) (b : β) (h : g b = .yield b) : ∀ k, iterId g k b = b
  | 0 => rfl
  | k+1 => by simp only [iterId, h]; exact iterId_fix g b h k

/-- Lockstep: a Rust `loop` against `n` iterations of an `Id`-loop body (`iterId`). The Rust loop
may take one extra `cont` step after the spec exits early (`ForInStep.done`). -/
theorem loop_iterId {α β σ : Type} (body : α → Result (ControlFlow α β)) (g : σ → ForInStep σ)
    (μ : α → Nat) (R : α → σ → Prop) (Q : β → σ → Prop)
    (h : ∀ x s, R x s →
      (∃ y, body x = ok (.done y) ∧ g s = .yield s ∧ Q y s) ∨
      (∃ y s', body x = ok (.done y) ∧ g s = .done s' ∧ Q y s') ∨
      (∃ x' s', body x = ok (.cont x') ∧ g s = .yield s' ∧ R x' s' ∧ μ x' < μ x) ∨
      (∃ x' s', body x = ok (.cont x') ∧ g s = .done s' ∧ ∃ y, loop body x' = ok y ∧ Q y s')) :
    ∀ k x s, R x s → μ x < k → ∃ y, loop body x = ok y ∧ Q y (iterId g k s) := by
  intro k
  induction k with
  | zero => intro x s _ hk; omega
  | succ k ih =>
    intro x s hr hk
    rcases h x s hr with ⟨y, hb, hg, hq⟩ | ⟨y, s', hb, hg, hq⟩ | ⟨x', s', hb, hg, hr', hm⟩ | ⟨x', s', hb, hg, y, hy, hq⟩
    · refine ⟨y, by rw [loop_unfold, hb]; simp, ?_⟩
      rw [iterId_fix g s hg]; exact hq
    · refine ⟨y, by rw [loop_unfold, hb]; simp, ?_⟩
      simp only [iterId, hg]; exact hq
    · obtain ⟨y, hy, hq⟩ := ih x' s' hr' (by omega)
      refine ⟨y, by rw [loop_unfold, hb]; simpa using hy, ?_⟩
      simp only [iterId, hg]; exact hq
    · refine ⟨y, by rw [loop_unfold, hb]; simpa using hy, ?_⟩
      simp only [iterId, hg]; exact hq
theorem chOf_eq_lit (u : U32) (c : Char) (hc : c.toNat ≠ 0) : (chOf u = c) ↔ u.val = c.toNat := by
  unfold chOf
  constructor
  · intro h
    have h2 := congrArg Char.toNat h
    unfold Char.ofNat at h2
    split at h2
    · simpa [Char.ofNatAux] using h2
    · simp at h2; omega
  · intro h; rw [h]; simp
theorem chOf_beq_lit (u : U32) (c : Char) (hc : c.toNat ≠ 0) : (chOf u == c) = decide (u.val = c.toNat) := by
  by_cases h : u.val = c.toNat
  · simp [h, (chOf_eq_lit u c hc).mpr h]
  · have : ¬ chOf u = c := fun h' => h ((chOf_eq_lit u c hc).mp h')
    simp [h, this]
theorem ofList_push (l : List Char) (c : Char) : (String.ofList l).push c = String.ofList (l ++ [c]) := by
  simp [String.ofList_append]

def strV (v : alloc.vec.Vec U32) : String := String.ofList (v.val.map chOf)
def linesS (v : alloc.vec.Vec (alloc.vec.Vec U32)) : _root_.Array String := (v.val.map strV).toArray
def ValidL (l : List U32) : Prop := ∀ u ∈ l, u.val.isValidChar

abbrev RLX := alloc.vec.Vec (alloc.vec.Vec U32) × alloc.vec.Vec U32 × Usize × Bool
abbrev RLS := _root_.Array String × String × Nat × Bool

def rlR (cs : Slice U32) (x : RLX) (s : RLS) : Prop :=
  s = (linesS x.1, strV x.2.1, x.2.2.1.val, x.2.2.2) ∧ x.2.2.1.val ≤ cs.val.length ∧
  x.1.val.length + x.2.1.val.length ≤ x.2.2.1.val ∧ (x.2.2.2 = true → 1 ≤ x.2.1.val.length) ∧
  (∀ l ∈ x.1.val, ValidL l.val) ∧ ValidL x.2.1.val

theorem strS_get! (cs : Slice U32) (i : Nat) (h : i < cs.val.length) : (strS cs).toArray[i]! = chOf (cs.val[i]'h) := by
  rw [getElem!_pos _ i (by simpa [strS] using h)]; simp [strS]

def rlG (cs : _root_.Array Char) (__s : RLS) : ForInStep RLS :=
  have lines := __s.1; have cur := __s.2.1; have i := __s.2.2.1; have pending := __s.2.2.2
  if i < cs.size then
    have c := cs[i]!
    if (c == '\n') = true then ForInStep.yield (lines.push cur, "", i + 1, false)
    else if (c == '\x0d') = true then
      ForInStep.yield (lines.push cur, "", if (decide (i + 1 < cs.size) && cs[i + 1]! == '\n') = true then i + 2 else i + 1, false)
    else ForInStep.yield (lines, cur.push c, i + 1, true)
  else ForInStep.yield (lines, cur, i, pending)

theorem readLines_eq (cs : _root_.Array Char) : readLines cs =
    (let r := iterId (rlG cs) (cs.size + 1) (#[], "", 0, false); if r.2.2.2 then r.1.push r.2.1 else r.1) := by
  unfold readLines
  simp only [Id.run]
  rw [forIn_range_id' _ (fun _ _ => rfl)]
  rfl

theorem read_lines_step (cs : Slice U32) (hs : ValidStr cs) (x : RLX) (s : RLS) (hr : rlR cs x s) :
    let g := rlG (strS cs).toArray
    (∃ y, beatmap.text.read_lines_loop.body cs (Slice.len cs) x.1 x.2.1 x.2.2.1 x.2.2.2 = ok (.done y) ∧ g s = .yield s ∧
        y = (x.1, x.2.1, x.2.2.2) ∧ x.2.2.1.val = cs.val.length) ∨
    (∃ x' s', beatmap.text.read_lines_loop.body cs (Slice.len cs) x.1 x.2.1 x.2.2.1 x.2.2.2 = ok (.cont x') ∧ g s = .yield s' ∧
        rlR cs x' s' ∧ cs.val.length - x'.2.2.1.val < cs.val.length - x.2.2.1.val) := by
  intro g
  obtain ⟨lines, cur, i, pending⟩ := x
  obtain ⟨rfl, hi, hlen, hpend, hvl, hvc⟩ := hr
  dsimp only at hi hlen hpend hvl hvc ⊢
  have hsz : (strS cs).toArray.size = cs.val.length := by simp [strS]
  by_cases hlt : i.val < cs.val.length
  · right
    have hlt' : i < Slice.len cs := by show i.val < (Slice.len cs).val; simpa using hlt
    have hc := strS_get! cs i.val hlt
    have hmax : cs.val.length ≤ Usize.max := cs.property
    obtain ⟨l1, hl1, hl1v⟩ := push_eq lines cur (by omega)
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have hvalid : (cs.val[i.val]'hlt).val.isValidChar := hs _ (List.getElem_mem hlt)
    by_cases h10 : (cs.val[i.val]'hlt).val = 10
    · have e : cs.val[i.val]'hlt = 10#u32 := UScalar.eq_of_val_eq (by simpa using h10)
      refine ⟨(l1, alloc.vec.Vec.new U32, i1, false), (linesS l1, strV (alloc.vec.Vec.new U32), i1.val, false), ?_, ?_, ⟨rfl, ?_⟩, by dsimp only; omega⟩
      · simp [beatmap.text.read_lines_loop.body, hlt', index_eq cs i hlt, e, hl1, hi1]
      · simp only [g, rlG, hsz, hlt, if_true, hc, chOf_beq_lit _ _ (by decide : '\n'.toNat ≠ 0), h10, decide_true]
        simp [linesS, hl1v, strV, hi1v, alloc.vec.Vec.new]
      · refine ⟨by dsimp only; omega, by dsimp only; rw [hl1v]; simp [alloc.vec.Vec.new]; omega, by simp, ?_, by simp [ValidL, alloc.vec.Vec.new]⟩
        · intro l hl; rw [hl1v] at hl; simp at hl; rcases hl with hl | hl
          · exact hvl l hl
          · rw [hl]; exact hvc
    · have h10' : ¬ cs.val[i.val]'hlt = 10#u32 := fun e => h10 (by rw [e]; rfl)
      by_cases h13 : (cs.val[i.val]'hlt).val = 13
      · have e : cs.val[i.val]'hlt = 13#u32 := UScalar.eq_of_val_eq (by simpa using h13)
        by_cases hn : ∃ hn1 : i.val + 1 < cs.val.length, (cs.val[i.val + 1]'hn1).val = 10
        · obtain ⟨hn1, hn2⟩ := hn
          have hn1' : i1 < Slice.len cs := by show i1.val < (Slice.len cs).val; simp; omega
          have e2 : cs.val[i1.val]'(by omega) = 10#u32 := UScalar.eq_of_val_eq (by simp [hi1v]; simpa using hn2)
          obtain ⟨i2, hi2, hi2v0⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := 2#usize) (by simp; omega))
          have hi2v : i2.val = i.val + 2 := by rw [hi2v0]; simp
          refine ⟨(l1, alloc.vec.Vec.new U32, i2, false), (linesS l1, strV (alloc.vec.Vec.new U32), i2.val, false), ?_, ?_, ⟨rfl, ?_⟩, by dsimp only; omega⟩
          · have hn1'' : i1.val < cs.val.length := by omega
            simp [beatmap.text.read_lines_loop.body, hlt', index_eq cs i hlt, h10', e, hl1, hi1, hn1', hn1'', index_eq cs i1 (by omega), e2, hi2]
          · have hc2 := strS_get! cs (i.val + 1) hn1
            simp only [g, rlG, hsz, hlt, if_true, hc, hc2, chOf_beq_lit _ _ (by decide : '\n'.toNat ≠ 0),
              chOf_beq_lit _ _ (by decide : '\x0d'.toNat ≠ 0), h10, h13, hn1, hn2, decide_true]
            simp [linesS, hl1v, strV, hi2v, alloc.vec.Vec.new]
          · refine ⟨by dsimp only; omega, by dsimp only; rw [hl1v]; simp [alloc.vec.Vec.new]; omega, by simp, ?_, by simp [ValidL, alloc.vec.Vec.new]⟩
            intro l hl; rw [hl1v] at hl; simp at hl; rcases hl with hl | hl
            · exact hvl l hl
            · rw [hl]; exact hvc
        · refine ⟨(l1, alloc.vec.Vec.new U32, i1, false), (linesS l1, strV (alloc.vec.Vec.new U32), i1.val, false), ?_, ?_, ⟨rfl, ?_⟩, by dsimp only; omega⟩
          · by_cases hn1 : i.val + 1 < cs.val.length
            · have hn2 : ¬ (cs.val[i.val + 1]'(by omega)).val = 10 := fun h => hn ⟨hn1, h⟩
              have hn1' : i1 < Slice.len cs := by show i1.val < (Slice.len cs).val; simp; omega
              have e2 : ¬ cs.val[i1.val]'(by omega) = 10#u32 := fun e => hn2 (by
                have := congrArg UScalar.val e; simp [hi1v] at this; simpa using this)
              simp [beatmap.text.read_lines_loop.body, hlt', index_eq cs i hlt, h10', e, hl1, hi1, hn1', index_eq cs i1 (by omega), e2]
            · have hn1' : ¬ i1 < Slice.len cs := by show ¬ i1.val < (Slice.len cs).val; simp; omega
              have hn1'' : ¬ i1.val < cs.val.length := by omega
              simp [beatmap.text.read_lines_loop.body, hlt', index_eq cs i hlt, h10', e, hl1, hi1, hn1', hn1'']
          · have hif : (decide (i.val + 1 < cs.val.length) && (strS cs).toArray[i.val + 1]! == '\n') = false := by
              by_cases hn1 : i.val + 1 < cs.val.length
              · have hn2 : ¬ (cs.val[i.val + 1]'(by omega)).val = 10 := fun h => hn ⟨hn1, h⟩
                rw [strS_get! cs (i.val + 1) hn1, chOf_beq_lit _ _ (by decide)]; simp [hn2]
              · simp [hn1]
            simp only [g, rlG, hsz, hlt, if_true, hc, chOf_beq_lit _ _ (by decide : '\n'.toNat ≠ 0),
              chOf_beq_lit _ _ (by decide : '\x0d'.toNat ≠ 0), h10, h13, decide_true, decide_false, hif]
            simp [linesS, hl1v, strV, hi1v, alloc.vec.Vec.new]
          · refine ⟨by dsimp only; omega, by dsimp only; rw [hl1v]; simp [alloc.vec.Vec.new]; omega, by simp, ?_, by simp [ValidL, alloc.vec.Vec.new]⟩
            intro l hl; rw [hl1v] at hl; simp at hl; rcases hl with hl | hl
            · exact hvl l hl
            · rw [hl]; exact hvc
      · have h13' : ¬ cs.val[i.val]'hlt = 13#u32 := fun e => h13 (by rw [e]; rfl)
        obtain ⟨c1, hc1, hc1v⟩ := push_eq cur (cs.val[i.val]'hlt) (by omega)
        refine ⟨(lines, c1, i1, true), (linesS lines, strV c1, i1.val, true), ?_, ?_, ⟨rfl, ?_⟩, by dsimp only; omega⟩
        · simp [beatmap.text.read_lines_loop.body, hlt', index_eq cs i hlt, h10', h13', hc1, hi1]
        · simp only [g, rlG, hsz, hlt, if_true, hc, chOf_beq_lit _ _ (by decide : '\n'.toNat ≠ 0),
            chOf_beq_lit _ _ (by decide : '\x0d'.toNat ≠ 0), h10, h13, decide_false]
          simp [strV, hc1v, hi1v, h10, h13]
        · refine ⟨by dsimp only; omega, by dsimp only; rw [hc1v]; simp; omega, by intro; rw [hc1v]; simp, hvl, ?_⟩
          intro u hu; rw [hc1v] at hu; simp at hu; rcases hu with hu | hu
          · exact hvc u hu
          · rw [hu]; exact hvalid
  · left
    have hlt' : ¬ i < Slice.len cs := by show ¬ i.val < (Slice.len cs).val; simpa using hlt
    refine ⟨_, by simp [beatmap.text.read_lines_loop.body, hlt'], ?_, rfl, by omega⟩
    simp only [g, rlG, hsz, hlt, if_false]

theorem beatmap.text.read_lines_refines (cs : Slice U32) (hs : ValidStr cs) :
    ∃ v, beatmap.text.read_lines cs = ok v ∧ linesS v = readLines (strS cs).toArray ∧ ∀ l ∈ v.val, ValidL l.val := by
  have hsz : (strS cs).toArray.size = cs.val.length := by simp [strS]
  obtain ⟨y, hy, hq⟩ := loop_iterId
    (fun (x : RLX) => beatmap.text.read_lines_loop.body cs (Slice.len cs) x.1 x.2.1 x.2.2.1 x.2.2.2)
    (rlG (strS cs).toArray) (fun x => cs.val.length - x.2.2.1.val) (rlR cs)
    (fun y s => rlR cs (y.1, y.2.1, Slice.len cs, y.2.2) s)
    (by
      intro x s hr
      rcases read_lines_step cs hs x s hr with ⟨y, hb, hg, hy, hi⟩ | ⟨x', s', hb, hg, hr', hm⟩
      · left; refine ⟨y, hb, hg, ?_⟩
        obtain ⟨a, b, c, d⟩ := x
        dsimp only at hy hi; subst hy
        have : c = Slice.len cs := UScalar.eq_of_val_eq (by simp [hi])
        subst this; exact hr
      · right; right; left; exact ⟨x', s', hb, hg, hr', hm⟩)
    (cs.val.length + 1) (alloc.vec.Vec.new _, alloc.vec.Vec.new U32, 0#usize, false) (#[], "", 0, false)
    ⟨by simp [linesS, strV, alloc.vec.Vec.new], by simp, by simp [alloc.vec.Vec.new], by simp,
      by simp [alloc.vec.Vec.new], by simp [ValidL, alloc.vec.Vec.new]⟩ (by simp)
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨hs', _, hlen, hpend, hvl, hvc⟩ := hq
  dsimp only at hs' hlen hpend hvl hvc
  rw [← hsz] at hs'
  unfold beatmap.text.read_lines
  rw [readLines_eq, hs']
  have hl : beatmap.text.read_lines_loop cs (alloc.vec.Vec.new _) (alloc.vec.Vec.new U32) 0#usize (Slice.len cs) false
      = ok (y1, y2, y3) := by
    unfold beatmap.text.read_lines_loop; exact hy
  simp only [hl, bind_ok]
  cases y3 with
  | false => exact ⟨y1, by simp, by simp, hvl⟩
  | true =>
    have hmax : cs.val.length ≤ Usize.max := cs.property
    have := hpend rfl
    simp at hlen
    obtain ⟨w, hw, hwv⟩ := push_eq y1 y2 (by omega)
    refine ⟨w, by simp [hw], by simp [linesS, hwv], ?_⟩
    intro l hl; rw [hwv] at hl; simp at hl; rcases hl with hl | hl
    · exact hvl l hl
    · rw [hl]; exact hvc

def byteAt (b : Slice U8) (j : Nat) : Nat := if h : j < b.val.length then (b.val[j]'h).val else 0

theorem bytesS_get' (b : Slice U8) (j : Nat) : ((bytesS b)[j]!).toNat = byteAt b j := by
  unfold byteAt
  split
  · rename_i h; exact bytesS_get b j h
  · rename_i h; rw [getElem!_neg (bytesS b) j (by rw [bytesS_size]; exact h)]; rfl

/-- One UTF-8 decoding step on byte values: (scalar value pushed, bytes consumed). -/
def u8dec (B : Nat → Nat) (n i : Nat) : Nat × Nat :=
  if B i < 128 then (B i, 1)
  else if B i < 194 then (65533, 1)
  else if B i < 224 then
    if i + 1 < n ∧ B (i+1) &&& 192 = 128 then ((B i &&& 31) <<< 6 ||| B (i+1) &&& 63, 2) else (65533, 1)
  else if B i < 240 then
    if i + 1 < n ∧ (if B i = 224 then 160 else 128) ≤ B (i+1) ∧ B (i+1) ≤ (if B i = 237 then 159 else 191) then
      if i + 2 < n ∧ B (i+2) &&& 192 = 128 then
        ((B i &&& 15) <<< 12 ||| (B (i+1) &&& 63) <<< 6 ||| B (i+2) &&& 63, 3)
      else (65533, 2)
    else (65533, 1)
  else if B i < 245 then
    if i + 1 < n ∧ (if B i = 240 then 144 else 128) ≤ B (i+1) ∧ B (i+1) ≤ (if B i = 244 then 143 else 191) then
      if i + 2 < n ∧ B (i+2) &&& 192 = 128 then
        if i + 3 < n ∧ B (i+3) &&& 192 = 128 then
          ((B i &&& 7) <<< 18 ||| (B (i+1) &&& 63) <<< 12 ||| (B (i+2) &&& 63) <<< 6 ||| B (i+3) &&& 63, 4)
        else (65533, 3)
      else (65533, 2)
    else (65533, 1)
  else (65533, 1)

def utf8G (b : ByteArray) (__s : _root_.Array Char × Nat) : ForInStep (_root_.Array Char × Nat) :=
  have out := __s.1
  have i := __s.2
  have n := b.size
  have repl := '�'
  have cont := fun (x : UInt8) => x &&& 192 == 128
  if i < n then
    have c0 := b[i]!
    if c0 < 128 then ForInStep.yield (out.push (Char.ofNat c0.toNat), i + 1)
    else if c0 < 194 then ForInStep.yield (out.push repl, i + 1)
    else if c0 < 224 then
      if (decide (i + 1 < n) && cont b[i + 1]!) = true then
        ForInStep.yield (out.push (Char.ofNat ((c0.toNat &&& 31) <<< 6 ||| b[i + 1]!.toNat &&& 63)), i + 2)
      else ForInStep.yield (out.push repl, i + 1)
    else if c0 < 240 then
      have lo : UInt8 := if (c0 == 224) = true then 160 else 128
      have hi : UInt8 := if (c0 == 237) = true then 159 else 191
      if (decide (i + 1 < n) && decide (lo ≤ b[i + 1]!) && decide (b[i + 1]! ≤ hi)) = true then
        if (decide (i + 2 < n) && cont b[i + 2]!) = true then
          ForInStep.yield (out.push (Char.ofNat ((c0.toNat &&& 15) <<< 12 ||| (b[i + 1]!.toNat &&& 63) <<< 6 ||| b[i + 2]!.toNat &&& 63)), i + 3)
        else ForInStep.yield (out.push repl, i + 2)
      else ForInStep.yield (out.push repl, i + 1)
    else if c0 < 245 then
      have lo : UInt8 := if (c0 == 240) = true then 144 else 128
      have hi : UInt8 := if (c0 == 244) = true then 143 else 191
      if (decide (i + 1 < n) && decide (lo ≤ b[i + 1]!) && decide (b[i + 1]! ≤ hi)) = true then
        if (decide (i + 2 < n) && cont b[i + 2]!) = true then
          if (decide (i + 3 < n) && cont b[i + 3]!) = true then
            ForInStep.yield (out.push (Char.ofNat ((c0.toNat &&& 7) <<< 18 ||| (b[i + 1]!.toNat &&& 63) <<< 12 |||
              (b[i + 2]!.toNat &&& 63) <<< 6 ||| b[i + 3]!.toNat &&& 63)), i + 4)
          else ForInStep.yield (out.push repl, i + 3)
        else ForInStep.yield (out.push repl, i + 2)
      else ForInStep.yield (out.push repl, i + 1)
    else ForInStep.yield (out.push repl, i + 1)
  else ForInStep.yield (out, i)

theorem decodeUtf8_eq (b : ByteArray) (start : Nat) :
    decodeUtf8 b start = (iterId (utf8G b) (b.size + 1) (Array.mkEmpty b.size, start)).1 := by
  unfold decodeUtf8
  simp only [Id.run]
  rw [forIn_range_id' _ (fun _ _ => rfl)]
  rfl

theorem utf8G_lt (b : Slice U8) (out : _root_.Array Char) (i : Nat) (hi : i < b.val.length) :
    utf8G (bytesS b) (out, i) = .yield (out.push (Char.ofNat (u8dec (byteAt b) b.val.length i).1),
      i + (u8dec (byteAt b) b.val.length i).2) := by
  simp only [utf8G, u8dec, bytesS_size, hi, if_true, UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le, bytesS_get',
    ← UInt8.toNat_inj, beq_iff_eq, UInt8.toNat_and, Bool.and_eq_true, decide_eq_true_eq, UInt8.reduceToNat,
    apply_ite UInt8.toNat, and_assoc]
  split_ifs <;> first | rfl | (simp_all; done) | omega

theorem nat_or_mul_add (q r k : Nat) (hr : r < 2^k) : (q * 2^k) ||| r = q * 2^k + r := by
  have := Nat.two_pow_add_eq_or_of_lt hr q
  rw [Nat.mul_comm]; exact this.symm
theorem and_mask (x k : Nat) : x &&& (2^k - 1) = x % 2^k := Nat.and_two_pow_sub_one_eq_mod x k
theorem and7 (x : Nat) : x &&& 7 = x % 8 := and_mask x 3
theorem and15 (x : Nat) : x &&& 15 = x % 16 := and_mask x 4
theorem and31 (x : Nat) : x &&& 31 = x % 32 := and_mask x 5
theorem and63 (x : Nat) : x &&& 63 = x % 64 := and_mask x 6
theorem shl_or_add (q r k : Nat) (hr : r < 2^k) : q <<< k ||| r = q * 2^k + r := by
  rw [Nat.shiftLeft_eq]; exact nat_or_mul_add q r k hr
theorem or_mul_pow (a b k : Nat) : a * 2^k ||| b * 2^k = (a ||| b) * 2^k := by
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_or_distrib]
theorem m64 (y : Nat) : y % 64 < 2^6 := Nat.mod_lt _ (by decide)
theorem cp2_eq (x y : Nat) : ((x &&& 31) <<< 6 ||| y &&& 63) = (x % 32) * 64 + y % 64 := by
  rw [and31, and63, Nat.shiftLeft_eq, nat_or_mul_add _ _ 6 (m64 y)]; rfl
theorem cp3_eq (x y z : Nat) : ((x &&& 15) <<< 12 ||| (y &&& 63) <<< 6 ||| z &&& 63) = (x % 16) * 4096 + (y % 64) * 64 + z % 64 := by
  rw [and15, and63, and63, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    show x % 16 * 2^12 = (x % 16 * 2^6) * 2^6 by rw [Nat.mul_assoc]; rfl, or_mul_pow,
    nat_or_mul_add _ _ 6 (m64 y), nat_or_mul_add _ _ 6 (m64 z)]
  simp only [Nat.reducePow]; omega
theorem cp4_eq (x y z w : Nat) : ((x &&& 7) <<< 18 ||| (y &&& 63) <<< 12 ||| (z &&& 63) <<< 6 ||| w &&& 63) =
    (x % 8) * 262144 + (y % 64) * 4096 + (z % 64) * 64 + w % 64 := by
  rw [and7, and63, and63, and63, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    show x % 8 * 2^18 = ((x % 8 * 2^6) * 2^6) * 2^6 by rw [Nat.mul_assoc, Nat.mul_assoc]; rfl,
    show y % 64 * 2^12 = (y % 64 * 2^6) * 2^6 by rw [Nat.mul_assoc]; rfl, or_mul_pow, or_mul_pow, or_mul_pow,
    nat_or_mul_add _ _ 6 (m64 y), nat_or_mul_add _ _ 6 (m64 z), nat_or_mul_add _ _ 6 (m64 w)]
  simp only [Nat.reducePow]; omega
set_option maxRecDepth 20000 in
theorem cont_range : ∀ y < 256, y &&& 192 = 128 → 128 ≤ y ∧ y < 192 := by decide

theorem u8dec_props (B : Nat → Nat) (hB : ∀ j, B j < 256) (n i : Nat) (hi : i < n) :
    (u8dec B n i).1.isValidChar ∧ 1 ≤ (u8dec B n i).2 ∧ i + (u8dec B n i).2 ≤ n := by
  have h0 := hB i; have h1 := hB (i+1); have h2 := hB (i+2); have h3 := hB (i+3)
  unfold u8dec Nat.isValidChar
  split_ifs with c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 <;>
    simp only [cp2_eq, cp3_eq, cp4_eq] <;>
    (have r1 := cont_range _ h1; have r2 := cont_range _ h2; have r3 := cont_range _ h3; omega)

theorem take_succ_eq_iff {α} (l m : List α) (k : Nat) (hl : k < l.length) (hm : k < m.length) :
    (l.take (k+1) = m.take (k+1)) ↔ (l.take k = m.take k ∧ l[k] = m[k]) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hm]
  simp only [Option.toList_some]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

theorem has_prefix_loop_ok (b p : Slice U8) (hn : p.val.length ≤ b.val.length) :
    ∀ (i : Usize) (acc : Bool), i.val ≤ p.val.length → acc = decide (b.val.take i.val = p.val.take i.val) →
      beatmap.text.has_prefix_loop b p i acc = ok (decide (b.val.take p.val.length = p.val)) := by
  intro i acc hi hacc
  unfold beatmap.text.has_prefix_loop
  have := loop_ok (fun (x : Usize × Bool) => beatmap.text.has_prefix_loop.body b p x.1 x.2)
    (fun (x : Usize × Bool) => p.val.length - x.1.val)
    (fun (x : Usize × Bool) => x.1.val ≤ p.val.length ∧ x.2 = decide (b.val.take x.1.val = p.val.take x.1.val))
    (fun (r : Bool) => r = decide (b.val.take p.val.length = p.val))
    (by
      rintro ⟨k, a⟩ ⟨hk, ha⟩
      dsimp only at hk ha ⊢
      by_cases hlt : k.val < p.val.length
      · right
        have hlt' : k < Slice.len p := by show k.val < (Slice.len p).val; simpa using hlt
        have hkb : k.val < b.val.length := by omega
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_one k (by have := p.property; omega)
        refine ⟨(k1, a && decide (b.val[k.val]'hkb = p.val[k.val]'hlt)), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        · simp only [beatmap.text.has_prefix_loop.body, hlt', if_true, index_eq b k hkb, index_eq p k hlt, bind_ok, hk1]
          by_cases hc : b.val[k.val]'hkb = p.val[k.val]'hlt <;> simp [hc]
        · dsimp only
          rw [ha, hk1v]
          by_cases h1 : b.val.take k.val = p.val.take k.val <;>
            by_cases hc : b.val[k.val]'hkb = p.val[k.val]'hlt <;> simp [take_succ_eq_iff _ _ _ hkb hlt, h1, hc]
      · left
        have hlt' : ¬ k < Slice.len p := by show ¬ k.val < (Slice.len p).val; simpa using hlt
        refine ⟨a, by simp [beatmap.text.has_prefix_loop.body, hlt'], ?_⟩
        have : k.val = p.val.length := by omega
        rw [ha, this, List.take_length])
    (i, acc) ⟨hi, hacc⟩
  obtain ⟨y, hy, rfl⟩ := this
  exact hy

/-- Helper (spec: the BOM tests `n ≥ k && b[0]! == p[0] && …` of `streamReaderDecode`). -/
theorem beatmap.text.has_prefix_refines (b p : Slice U8) :
    beatmap.text.has_prefix b p = ok (decide (b.val.take p.val.length = p.val)) := by
  unfold beatmap.text.has_prefix
  by_cases hl : b.val.length < p.val.length
  · have hl' : Slice.len b < Slice.len p := by show (Slice.len b).val < (Slice.len p).val; simpa using hl
    simp only [hl', if_true]
    congr 1; symm; simp only [decide_eq_false_iff_not]
    intro h; have := congrArg List.length h; simp at this; omega
  · have hl' : ¬ Slice.len b < Slice.len p := by show ¬ (Slice.len b).val < (Slice.len p).val; simpa using hl
    simp only [hl', if_false]
    exact has_prefix_loop_ok b p (by omega) 0#usize true (by simp) (by simp)

theorem is_cont_nat (x : U8) : beatmap.text.is_cont x = ok (decide (x.val &&& 192 = 128)) := by
  unfold beatmap.text.is_cont
  simp only [lift, bind_ok]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro h; have := congrArg UScalar.val h; simpa using this
  · intro h; apply UScalar.eq_of_val_eq; simpa using h
theorem shl_ok (x : U32) (k : I32) (h0 : 0 ≤ k.val) (h1 : k.val < 32) :
    ∃ z, x <<< k = ok z ∧ z.val = x.val <<< k.toNat % 2^32 := by
  obtain ⟨z, hz, h1, _⟩ := eq_ok_of_spec (U32.ShiftLeft_IScalar_spec x k h0 h1)
  exact ⟨z, hz, by rw [h1]; simp [U32.size, U32.numBits]⟩
/-- The result of a `push` that cannot overflow. -/
noncomputable def pushV {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) : alloc.vec.Vec α :=
  Classical.choose (push_eq v x h)
theorem push_ok' {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    alloc.vec.Vec.push v x = ok (pushV v x h) := (Classical.choose_spec (push_eq v x h)).1
@[simp] theorem pushV_val {α} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    (pushV v x h).val = v.val ++ [x] := (Classical.choose_spec (push_eq v x h)).2
theorem usize_add_k (i : Usize) (k : Usize) (h : i.val + k.val ≤ Usize.max) :
    ∃ z, i + k = ok z ∧ z.val = i.val + k.val := by
  obtain ⟨z, hz, hv⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := k) h)
  exact ⟨z, hz, hv⟩
theorem byteAt_lt (b : Slice U8) (j : Nat) (h : j < b.val.length) : byteAt b j = (b.val[j]'h).val := by
  simp [byteAt, h]
theorem byteAt_lt256 (b : Slice U8) (j : Nat) : byteAt b j < 256 := by
  unfold byteAt; split
  · rename_i h; have := (b.val[j]'h).hBounds; simp at this ⊢; omega
  · omega

theorem and_shl_small (x m k : Nat) (h : m * 2^k < 2^32) : (x &&& m) <<< k % 4294967296 = (x &&& m) <<< k := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := Nat.and_le_right (n := x) (m := m)
  have : (x &&& m) * 2^k ≤ m * 2^k := Nat.mul_le_mul_right _ this
  omega
theorem ite_u8_le (c : Prop) [Decidable c] (a b x : U8) : ((if c then a else b) ≤ x) ↔ (if c then a.val else b.val) ≤ x.val := by
  split <;> rfl
theorem u8_le_ite (c : Prop) [Decidable c] (a b x : U8) : (x ≤ (if c then a else b)) ↔ x.val ≤ (if c then a.val else b.val) := by
  split <;> rfl
theorem utf8_body (b : Slice U8) (out : alloc.vec.Vec U32) (i : Usize) (hi : i.val < b.val.length)
    (hout : out.val.length < Usize.max) :
    ∃ u i', beatmap.text.decode_utf8_loop.body b (Slice.len b) out i = ok (.cont (pushV out u hout, i')) ∧
      u.val = (u8dec (byteAt b) b.val.length i.val).1 ∧
      i'.val = i.val + (u8dec (byteAt b) b.val.length i.val).2 := by
  have hmax : b.val.length ≤ Usize.max := b.property
  have hi' : i < Slice.len b := by show i.val < (Slice.len b).val; simpa using hi
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
  have B0 := byteAt_lt b i.val hi
  have L := fun x => push_ok' out x hout
  simp only [beatmap.text.decode_utf8_loop.body, hi', if_true, index_eq b i hi, bind_ok, lift, is_cont_nat, ite_ok, hi1]
  generalize hc0 : b.val[i.val]'hi = c0 at *
  by_cases k1 : c0.val < 128
  · exact ⟨UScalar.cast .U32 c0, i1, by simp [k1, L], by simp [u8dec, B0, k1], by simp [u8dec, B0, k1, hi1v]⟩
  by_cases k2 : c0.val < 194
  · exact ⟨beatmap.text.REPL, i1, by simp [k1, k2, L], by simp [u8dec, B0, k1, k2, beatmap.text.REPL],
      by simp [u8dec, B0, k1, k2, hi1v]⟩
  by_cases k3 : c0.val < 224
  · by_cases hn1 : i1.val < b.val.length
    · have B1 := byteAt_lt b (i.val + 1) (by omega)
      have e1 : b.val[i1.val]'hn1 = b.val[i.val + 1]'(by omega) := by simp [hi1v]
      generalize hc1 : b.val[i.val + 1]'(by omega) = c1 at *
      by_cases kc : c1.val &&& 192 = 128
      · obtain ⟨z, hz, hzv⟩ := shl_ok (UScalar.cast .U32 c0 &&& 31#u32) 6#i32 (by simp) (by simp)
        obtain ⟨i2, hi2, hi2v⟩ := usize_add_k i 2#usize (by simp; omega)
        refine ⟨z ||| (UScalar.cast .U32 c1 &&& 63#u32), i2, ?_, ?_, ?_⟩
        · simp [k1, k2, k3, L, hn1, index_eq b i1 hn1, e1, kc, hz, hi2]
        · have := and_shl_small c0.val 31 6 (by decide)
          simp at hzv
          simp [u8dec, B0, B1, k1, k2, k3, kc, hzv, this, show i.val + 1 < b.val.length by omega]
        · simp [u8dec, B0, B1, k1, k2, k3, kc, hi2v, show i.val + 1 < b.val.length by omega]
      · exact ⟨beatmap.text.REPL, i1, by simp [k1, k2, k3, L, hn1, index_eq b i1 hn1, e1, kc],
          by simp [u8dec, B0, B1, k1, k2, k3, kc, beatmap.text.REPL], by simp [u8dec, B0, B1, k1, k2, k3, kc, hi1v]⟩
    · exact ⟨beatmap.text.REPL, i1, by simp [k1, k2, k3, L, hn1],
        by simp [u8dec, B0, k1, k2, k3, beatmap.text.REPL, show ¬ i.val + 1 < b.val.length by omega],
        by simp [u8dec, B0, k1, k2, k3, hi1v, show ¬ i.val + 1 < b.val.length by omega]⟩
  by_cases k4 : c0.val < 240
  · have Lo : ∀ x : U8, ((if c0 = 224#u8 then 160#u8 else 128#u8) ≤ x) ↔ (if c0.val = 224 then 160 else 128) ≤ x.val := by
      intro x; by_cases h : c0.val = 224
      · have : c0 = 224#u8 := UScalar.eq_of_val_eq (by simpa using h)
        simp [this, h]
      · have : ¬ c0 = 224#u8 := fun e => h (by rw [e]; rfl)
        simp [this, h]
    have Hi : ∀ x : U8, (x ≤ (if c0 = 237#u8 then 159#u8 else 191#u8)) ↔ x.val ≤ (if c0.val = 237 then 159 else 191) := by
      intro x; by_cases h : c0.val = 237
      · have : c0 = 237#u8 := UScalar.eq_of_val_eq (by simpa using h)
        simp [this, h]
      · have : ¬ c0 = 237#u8 := fun e => h (by rw [e]; rfl)
        simp [this, h]
    have K : ¬ c0.val < 128 ∧ ¬ c0.val < 194 ∧ ¬ c0.val < 224 ∧ c0.val < 240 := ⟨k1, k2, k3, k4⟩
    by_cases hn1 : i1.val < b.val.length
    · have B1 := byteAt_lt b (i.val + 1) (by omega)
      have e1 : b.val[i1.val]'hn1 = b.val[i.val + 1]'(by omega) := by simp [hi1v]
      generalize hc1 : b.val[i.val + 1]'(by omega) = c1 at *
      obtain ⟨i2, hi2, hi2v⟩ := usize_add_k i 2#usize (by simp; omega)
      have hi2v' : i2.val = i.val + 2 := by simpa using hi2v
      by_cases kl : (if c0.val = 224 then 160 else 128) ≤ c1.val ∧ c1.val ≤ (if c0.val = 237 then 159 else 191)
      · by_cases hn2 : i2.val < b.val.length
        · have B2 := byteAt_lt b (i.val + 2) (by omega)
          have e2 : b.val[i2.val]'hn2 = b.val[i.val + 2]'(by omega) := by simp [hi2v']
          generalize hc2 : b.val[i.val + 2]'(by omega) = c2 at *
          by_cases kc : c2.val &&& 192 = 128
          · obtain ⟨z1, hz1, hz1v⟩ := shl_ok (UScalar.cast .U32 c0 &&& 15#u32) 12#i32 (by simp) (by simp)
            obtain ⟨z2, hz2, hz2v⟩ := shl_ok (UScalar.cast .U32 c1 &&& 63#u32) 6#i32 (by simp) (by simp)
            obtain ⟨i3, hi3, hi3v⟩ := usize_add_k i 3#usize (by simp; omega)
            refine ⟨z1 ||| z2 ||| (UScalar.cast .U32 c2 &&& 63#u32), i3, ?_, ?_, ?_⟩
            · simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2, index_eq b i2 hn2, e2, kc, hz1, hz2, hi3]
            · have a1 := and_shl_small c0.val 15 12 (by decide)
              have a2 := and_shl_small c1.val 63 6 (by decide)
              simp at hz1v hz2v
              simp [u8dec, B0, B1, B2, K, kl, kc, hz1v, hz2v, a1, a2, show i.val + 1 < b.val.length by omega,
                show i.val + 2 < b.val.length by omega]
            · simp [u8dec, B0, B1, B2, K, kl, kc, hi3v, show i.val + 1 < b.val.length by omega,
                show i.val + 2 < b.val.length by omega]
          · exact ⟨beatmap.text.REPL, i2, by simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2, index_eq b i2 hn2, e2, kc],
              by simp [u8dec, B0, B1, B2, K, kl, kc, beatmap.text.REPL, show i.val + 1 < b.val.length by omega],
              by simp [u8dec, B0, B1, B2, K, kl, kc, hi2v', show i.val + 1 < b.val.length by omega]⟩
        · exact ⟨beatmap.text.REPL, i2, by simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2],
            by simp [u8dec, B0, B1, K, kl, beatmap.text.REPL, show i.val + 1 < b.val.length by omega, show ¬ i.val + 2 < b.val.length by omega],
            by simp [u8dec, B0, B1, K, kl, hi2v', show i.val + 1 < b.val.length by omega, show ¬ i.val + 2 < b.val.length by omega]⟩
      · have kl' : ¬ ((if c0.val = 224 then 160 else 128) ≤ c1.val) ∨ ¬ (c1.val ≤ (if c0.val = 237 then 159 else 191)) := by
          by_cases h : (if c0.val = 224 then 160 else 128) ≤ c1.val
          · exact Or.inr (fun h' => kl ⟨h, h'⟩)
          · exact Or.inl h
        refine ⟨beatmap.text.REPL, i1, ?_, ?_, ?_⟩
        · rcases kl' with kl' | kl'
          · simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl']
          · by_cases kl0 : (if c0.val = 224 then 160 else 128) ≤ c1.val <;> simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl', kl0]
        · simp only [u8dec, B0, B1, K, if_false, if_true, show i.val + 1 < b.val.length by omega, true_and]
          rw [if_neg kl]; simp [beatmap.text.REPL]
        · simp only [u8dec, B0, B1, K, if_false, if_true, show i.val + 1 < b.val.length by omega, true_and]
          rw [if_neg kl]; simp [hi1v]
    · exact ⟨beatmap.text.REPL, i1, by simp [K, L, Lo, Hi, hn1],
        by simp [u8dec, B0, K, beatmap.text.REPL, show ¬ i.val + 1 < b.val.length by omega],
        by simp [u8dec, B0, K, hi1v, show ¬ i.val + 1 < b.val.length by omega]⟩
  by_cases k5 : c0.val < 245
  · have Lo : ∀ x : U8, ((if c0 = 240#u8 then 144#u8 else 128#u8) ≤ x) ↔ (if c0.val = 240 then 144 else 128) ≤ x.val := by
      intro x; by_cases h : c0.val = 240
      · have : c0 = 240#u8 := UScalar.eq_of_val_eq (by simpa using h)
        simp [this, h]
      · have : ¬ c0 = 240#u8 := fun e => h (by rw [e]; rfl)
        simp [this, h]
    have Hi : ∀ x : U8, (x ≤ (if c0 = 244#u8 then 143#u8 else 191#u8)) ↔ x.val ≤ (if c0.val = 244 then 143 else 191) := by
      intro x; by_cases h : c0.val = 244
      · have : c0 = 244#u8 := UScalar.eq_of_val_eq (by simpa using h)
        simp [this, h]
      · have : ¬ c0 = 244#u8 := fun e => h (by rw [e]; rfl)
        simp [this, h]
    have K : ¬ c0.val < 128 ∧ ¬ c0.val < 194 ∧ ¬ c0.val < 224 ∧ ¬ c0.val < 240 ∧ c0.val < 245 := ⟨k1, k2, k3, k4, k5⟩
    by_cases hn1 : i1.val < b.val.length
    · have B1 := byteAt_lt b (i.val + 1) (by omega)
      have e1 : b.val[i1.val]'hn1 = b.val[i.val + 1]'(by omega) := by simp [hi1v]
      generalize hc1 : b.val[i.val + 1]'(by omega) = c1 at *
      obtain ⟨i2, hi2, hi2v⟩ := usize_add_k i 2#usize (by simp; omega)
      have hi2v' : i2.val = i.val + 2 := by simpa using hi2v
      by_cases kl : (if c0.val = 240 then 144 else 128) ≤ c1.val ∧ c1.val ≤ (if c0.val = 244 then 143 else 191)
      · by_cases hn2 : i2.val < b.val.length
        · have B2 := byteAt_lt b (i.val + 2) (by omega)
          have e2 : b.val[i2.val]'hn2 = b.val[i.val + 2]'(by omega) := by simp [hi2v']
          generalize hc2 : b.val[i.val + 2]'(by omega) = c2 at *
          by_cases kc : c2.val &&& 192 = 128
          · obtain ⟨i3, hi3, hi3v⟩ := usize_add_k i 3#usize (by simp; omega)
            have hi3v' : i3.val = i.val + 3 := by simpa using hi3v
            by_cases hn3 : i3.val < b.val.length
            · have B3 := byteAt_lt b (i.val + 3) (by omega)
              have e3 : b.val[i3.val]'hn3 = b.val[i.val + 3]'(by omega) := by simp [hi3v']
              generalize hc3 : b.val[i.val + 3]'(by omega) = c3 at *
              by_cases kc3 : c3.val &&& 192 = 128
              · obtain ⟨z1, hz1, hz1v⟩ := shl_ok (UScalar.cast .U32 c0 &&& 7#u32) 18#i32 (by simp) (by simp)
                obtain ⟨z2, hz2, hz2v⟩ := shl_ok (UScalar.cast .U32 c1 &&& 63#u32) 12#i32 (by simp) (by simp)
                obtain ⟨z3, hz3, hz3v⟩ := shl_ok (UScalar.cast .U32 c2 &&& 63#u32) 6#i32 (by simp) (by simp)
                obtain ⟨i4, hi4, hi4v⟩ := usize_add_k i 4#usize (by simp; omega)
                refine ⟨z1 ||| z2 ||| z3 ||| (UScalar.cast .U32 c3 &&& 63#u32), i4, ?_, ?_, ?_⟩
                · simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2, index_eq b i2 hn2, e2, kc, hi3, hn3,
                    index_eq b i3 hn3, e3, kc3, hz1, hz2, hz3, hi4]
                · have a1 := and_shl_small c0.val 7 18 (by decide)
                  have a2 := and_shl_small c1.val 63 12 (by decide)
                  have a3 := and_shl_small c2.val 63 6 (by decide)
                  simp at hz1v hz2v hz3v
                  simp [u8dec, B0, B1, B2, B3, K, kl, kc, kc3, hz1v, hz2v, hz3v, a1, a2, a3,
                    show i.val + 1 < b.val.length by omega, show i.val + 2 < b.val.length by omega,
                    show i.val + 3 < b.val.length by omega]
                · simp [u8dec, B0, B1, B2, B3, K, kl, kc, kc3, hi4v, show i.val + 1 < b.val.length by omega,
                    show i.val + 2 < b.val.length by omega, show i.val + 3 < b.val.length by omega]
              · exact ⟨beatmap.text.REPL, i3, by simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2, index_eq b i2 hn2, e2, kc, hi3, hn3, index_eq b i3 hn3, e3, kc3],
                  by simp [u8dec, B0, B1, B2, B3, K, kl, kc, kc3, beatmap.text.REPL, show i.val + 1 < b.val.length by omega, show i.val + 2 < b.val.length by omega],
                  by simp [u8dec, B0, B1, B2, B3, K, kl, kc, kc3, hi3v', show i.val + 1 < b.val.length by omega, show i.val + 2 < b.val.length by omega]⟩
            · exact ⟨beatmap.text.REPL, i3, by simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2, index_eq b i2 hn2, e2, kc, hi3, hn3],
                by simp [u8dec, B0, B1, B2, K, kl, kc, beatmap.text.REPL, show i.val + 1 < b.val.length by omega, show i.val + 2 < b.val.length by omega, show ¬ i.val + 3 < b.val.length by omega],
                by simp [u8dec, B0, B1, B2, K, kl, kc, hi3v', show i.val + 1 < b.val.length by omega, show i.val + 2 < b.val.length by omega, show ¬ i.val + 3 < b.val.length by omega]⟩
          · exact ⟨beatmap.text.REPL, i2, by simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2, index_eq b i2 hn2, e2, kc],
              by simp [u8dec, B0, B1, B2, K, kl, kc, beatmap.text.REPL, show i.val + 1 < b.val.length by omega],
              by simp [u8dec, B0, B1, B2, K, kl, kc, hi2v', show i.val + 1 < b.val.length by omega]⟩
        · exact ⟨beatmap.text.REPL, i2, by simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl, hi2, hn2],
            by simp [u8dec, B0, B1, K, kl, beatmap.text.REPL, show i.val + 1 < b.val.length by omega, show ¬ i.val + 2 < b.val.length by omega],
            by simp [u8dec, B0, B1, K, kl, hi2v', show i.val + 1 < b.val.length by omega, show ¬ i.val + 2 < b.val.length by omega]⟩
      · have kl' : ¬ ((if c0.val = 240 then 144 else 128) ≤ c1.val) ∨ ¬ (c1.val ≤ (if c0.val = 244 then 143 else 191)) := by
          by_cases h : (if c0.val = 240 then 144 else 128) ≤ c1.val
          · exact Or.inr (fun h' => kl ⟨h, h'⟩)
          · exact Or.inl h
        refine ⟨beatmap.text.REPL, i1, ?_, ?_, ?_⟩
        · rcases kl' with kl' | kl'
          · simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl']
          · by_cases kl0 : (if c0.val = 240 then 144 else 128) ≤ c1.val <;> simp [K, L, hn1, index_eq b i1 hn1, e1, Lo, Hi, kl', kl0]
        · simp only [u8dec, B0, B1, K, if_false, if_true, show i.val + 1 < b.val.length by omega, true_and]
          rw [if_neg kl]; simp [beatmap.text.REPL]
        · simp only [u8dec, B0, B1, K, if_false, if_true, show i.val + 1 < b.val.length by omega, true_and]
          rw [if_neg kl]; simp [hi1v]
    · exact ⟨beatmap.text.REPL, i1, by simp [K, L, Lo, Hi, hn1],
        by simp [u8dec, B0, K, beatmap.text.REPL, show ¬ i.val + 1 < b.val.length by omega],
        by simp [u8dec, B0, K, hi1v, show ¬ i.val + 1 < b.val.length by omega]⟩
  have K : ¬ c0.val < 128 ∧ ¬ c0.val < 194 ∧ ¬ c0.val < 224 ∧ ¬ c0.val < 240 ∧ ¬ c0.val < 245 := ⟨k1, k2, k3, k4, k5⟩
  exact ⟨beatmap.text.REPL, i1, by simp [K, L], by simp [u8dec, B0, K, beatmap.text.REPL], by simp [u8dec, B0, K, hi1v]⟩

theorem utf8G_ge (b : ByteArray) (out : _root_.Array Char) (i : Nat) (hi : ¬ i < b.size) :
    utf8G b (out, i) = .yield (out, i) := by simp [utf8G, hi]

theorem beatmap.text.decode_utf8_refines (b : Slice U8) (start : Usize) :
    ∃ v, beatmap.text.decode_utf8 b start = ok v ∧ (v.val.map chOf).toArray = decodeUtf8 (bytesS b) start.val ∧
      ValidL v.val := by
  have hmax : b.val.length ≤ Usize.max := b.property
  obtain ⟨y, hy, hq⟩ := loop_iterId
    (fun (x : alloc.vec.Vec U32 × Usize) => beatmap.text.decode_utf8_loop.body b (Slice.len b) x.1 x.2)
    (utf8G (bytesS b)) (fun x => b.val.length - x.2.val)
    (fun x s => s = ((x.1.val.map chOf).toArray, x.2.val) ∧ ValidL x.1.val ∧ x.1.val.length ≤ x.2.val)
    (fun y s => s.1 = (y.val.map chOf).toArray ∧ ValidL y.val)
    (by
      rintro ⟨out, i⟩ s ⟨rfl, hv, hl⟩
      dsimp only at hv hl ⊢
      by_cases hi : i.val < b.val.length
      · right; right; left
        obtain ⟨u, i', hb, hu, hi'⟩ := utf8_body b out i hi (by omega)
        have P := u8dec_props (byteAt b) (byteAt_lt256 b) b.val.length i.val hi
        refine ⟨_, _, hb, ?_, ⟨rfl, ?_, ?_⟩, ?_⟩
        · rw [utf8G_lt b _ _ hi]; simp [hu, hi', chOf]
        · intro w hw; simp at hw; rcases hw with hw | hw
          · exact hv w hw
          · rw [hw, hu]; exact P.1
        · simp; omega
        · simp; omega
      · left
        have hi' : ¬ i < Slice.len b := by show ¬ i.val < (Slice.len b).val; simpa using hi
        exact ⟨out, by simp [beatmap.text.decode_utf8_loop.body, hi'], utf8G_ge _ _ _ (by rw [bytesS_size]; exact hi),
          rfl, hv⟩)
    (b.val.length + 1) (alloc.vec.Vec.with_capacity U32 (Slice.len b), start) (Array.mkEmpty (bytesS b).size, start.val)
    ⟨by simp [alloc.vec.Vec.with_capacity, Array.mkEmpty], by simp [ValidL, alloc.vec.Vec.with_capacity],
      by simp [alloc.vec.Vec.with_capacity]⟩ (by omega)
  refine ⟨y, ?_, ?_, hq.2⟩
  · unfold beatmap.text.decode_utf8 beatmap.text.decode_utf8_loop; exact hy
  · rw [decodeUtf8_eq, ← hq.1, bytesS_size]

def unitN (b : Slice U8) (be : Bool) (j : Nat) : Nat :=
  if be = true then byteAt b j * 256 + byteAt b (j + 1) else byteAt b (j + 1) * 256 + byteAt b j

theorem unitN_lt (b : Slice U8) (be : Bool) (j : Nat) : unitN b be j < 65536 := by
  have := byteAt_lt256 b j; have := byteAt_lt256 b (j+1)
  unfold unitN; split <;> omega

/-- Helper (spec: the local `unit` of `decodeUtf16`). -/
theorem beatmap.text.unit16_refines (b : Slice U8) (i : Usize) (be : Bool) (h : i.val + 1 < b.val.length) :
    ∃ u, beatmap.text.unit16 b i be = ok u ∧ u.val = unitN b be i.val := by
  have hmax : b.val.length ≤ Usize.max := b.property
  obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
  have B0 := byteAt_lt b i.val (by omega)
  have B1 := byteAt_lt b (i.val + 1) h
  have e1 : b.val[i1.val]'(by omega) = b.val[i.val + 1]'h := by simp [hi1v]
  have l0 := (b.val[i.val]'(by omega)).hBounds
  have l1 := (b.val[i.val+1]'h).hBounds
  simp at l0 l1
  unfold beatmap.text.unit16
  cases be with
  | true =>
    obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (U32.mul_spec (x := UScalar.cast .U32 (b.val[i.val]'(by omega))) (y := 256#u32) (by simp [U32.max, U32.numBits]; omega))
    obtain ⟨a, ha, hav⟩ := eq_ok_of_spec (U32.add_spec (x := m) (y := UScalar.cast .U32 (b.val[i.val+1]'h)) (by simp [U32.max, U32.numBits] at hmv ⊢; omega))
    refine ⟨a, ?_, ?_⟩
    · simp [index_eq b i (by omega), lift, hm, hi1, index_eq b i1 (by omega), e1, ha]
    · simp at hmv hav; simp [unitN, B0, B1, hav, hmv]
  | false =>
    obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (U32.mul_spec (x := UScalar.cast .U32 (b.val[i.val+1]'h)) (y := 256#u32) (by simp [U32.max, U32.numBits]; omega))
    obtain ⟨a, ha, hav⟩ := eq_ok_of_spec (U32.add_spec (x := m) (y := UScalar.cast .U32 (b.val[i.val]'(by omega))) (by simp [U32.max, U32.numBits] at hmv ⊢; omega))
    refine ⟨a, ?_, ?_⟩
    · simp [index_eq b i (by omega), lift, hm, hi1, index_eq b i1 (by omega), e1, ha]
    · simp at hmv hav; simp [unitN, B0, B1, hav, hmv]

abbrev U16S := Option (Option (_root_.Array Char)) × _root_.Array Char × Nat

def u16G (b : ByteArray) (bigEndian : Bool) (__s : U16S) : ForInStep U16S :=
  have n := b.size
  have unit := fun i =>
      if bigEndian = true then b[i]!.toNat * 256 + b[i + 1]!.toNat else b[i + 1]!.toNat * 256 + b[i]!.toNat
  have __s := __s.2
  have out := __s.1
  have i := __s.2
  if i + 1 < n then
    have u := unit i
    if (decide (u < 55296) || decide (u > 57343)) = true then
      ForInStep.yield (none, out.push (Char.ofNat u), i + 2)
    else
      if (decide (u ≤ 56319) && decide (i + 3 < n) && decide (56320 ≤ unit (i + 2)) &&
          decide (unit (i + 2) ≤ 57343)) = true then
        ForInStep.yield (none, out.push (Char.ofNat (65536 + (u - 55296) <<< 10 + (unit (i + 2) - 56320))), i + 4)
      else ForInStep.done (some none, out, i)
  else
    if i < n then ForInStep.yield (none, out.push '�', i + 1)
    else ForInStep.yield (none, out, i)

theorem decodeUtf16_eq (b : ByteArray) (start : Nat) (be : Bool) :
    decodeUtf16 b start be =
      Id.run (do
        let r ← (iterId (u16G b be) (b.size + 1) (none, #[], start) : Id U16S)
        match r.1 with
        | some r => pure r
        | none => pure (some r.2.1)) := by
  unfold decodeUtf16
  simp only [Id.run]
  rw [forIn_range_id' _ (fun _ _ => rfl)]
  congr 1
  funext s
  rcases s with ⟨_ | _, o, i⟩ <;> rfl

theorem unit_spec_eq (b : Slice U8) (be : Bool) (j : Nat) :
    (if be = true then (bytesS b)[j]!.toNat * 256 + (bytesS b)[j + 1]!.toNat
      else (bytesS b)[j + 1]!.toNat * 256 + (bytesS b)[j]!.toNat) = unitN b be j := by
  simp only [bytesS_get', unitN]

abbrev U16X := alloc.vec.Vec U32 × Usize × Bool

def u16R (b : Slice U8) (x : U16X) (s : U16S) : Prop :=
  x.2.2 = false ∧ s = (none, (x.1.val.map chOf).toArray, x.2.1.val) ∧ ValidL x.1.val ∧ x.1.val.length ≤ x.2.1.val

def u16Q (y : alloc.vec.Vec U32 × Bool) (s : U16S) : Prop :=
  (y.2 = false ∧ s.1 = none ∧ s.2.1 = (y.1.val.map chOf).toArray ∧ ValidL y.1.val) ∨ (y.2 = true ∧ s.1 = some none)

theorem u16_step (b : Slice U8) (be : Bool) (hb : b.val.length < Usize.max) (x : U16X) (s : U16S) (hr : u16R b x s) :
    let body := fun (x : U16X) => beatmap.text.decode_utf16_loop.body b be (Slice.len b) x.1 x.2.1 x.2.2
    (∃ y, body x = ok (.done y) ∧ u16G (bytesS b) be s = .yield s ∧ u16Q y s) ∨
    (∃ x' s', body x = ok (.cont x') ∧ u16G (bytesS b) be s = .yield s' ∧ u16R b x' s' ∧
      b.val.length - x'.2.1.val < b.val.length - x.2.1.val) ∨
    (∃ x' s', body x = ok (.cont x') ∧ u16G (bytesS b) be s = .done s' ∧ ∃ y, loop body x' = ok y ∧ u16Q y s') := by
  intro body
  obtain ⟨out, i, bad⟩ := x
  obtain ⟨rfl, rfl, hv, hl⟩ := hr
  dsimp only [body] at hv hl ⊢
  have hsz := bytesS_size b
  by_cases hi : i.val < b.val.length
  · have hi' : i < Slice.len b := by show i.val < (Slice.len b).val; simpa using hi
    obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
    have L := fun x => push_ok' out x (by omega)
    by_cases hn1 : i.val + 1 < b.val.length
    · have hn1' : i1 < Slice.len b := by show i1.val < (Slice.len b).val; simp; omega
      have hn1v : i1.val < b.val.length := by omega
      obtain ⟨u, hu, huv⟩ := beatmap.text.unit16_refines b i be hn1
      have hu65 := unitN_lt b be i.val
      obtain ⟨i2, hi2, hi2v⟩ := usize_add_k i 2#usize (by simp; omega)
      have hi2v' : i2.val = i.val + 2 := by simpa using hi2v
      by_cases kA : u.val < 55296 ∨ u.val > 57343
      · right; left
        refine ⟨(pushV out u (by omega), i2, false), (none, ((out.val ++ [u]).map chOf).toArray, i2.val), ?_, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
        · rcases kA with kA | kA
          · simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA, L, hi2]
          · have : ¬ u.val < 55296 := by omega
            simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA, this, L, hi2]
        · simp only [u16G, unit_spec_eq, ← huv, hsz, hn1, if_true]
          have : (decide (u.val < 55296) || decide (u.val > 57343)) = true := by simpa using kA
          simp [this, chOf, hi2v']
        · simp
        · intro w hw; simp at hw; rcases hw with hw | hw
          · exact hv w hw
          · rw [hw]; simp [Nat.isValidChar]; omega
        · dsimp only; simp; omega
        · dsimp only; omega
      · have kA' : ¬ u.val < 55296 := by omega
        have kA'' : ¬ u.val > 57343 := by omega
        have BAD : ∃ y, loop body (out, i, true) = ok y ∧ u16Q y (some none, (out.val.map chOf).toArray, i.val) :=
          ⟨(out, true), by rw [loop_unfold]; simp [body, beatmap.text.decode_utf16_loop.body], Or.inr ⟨rfl, rfl⟩⟩
        have SP : (decide (u.val ≤ 56319) && decide (i.val + 3 < b.val.length) && decide (56320 ≤ unitN b be (i.val + 2)) &&
              decide (unitN b be (i.val + 2) ≤ 57343)) = false →
            u16G (bytesS b) be (none, (out.val.map chOf).toArray, i.val) = .done (some none, (out.val.map chOf).toArray, i.val) := by
          intro h
          simp only [u16G, unit_spec_eq, ← huv, hsz, hn1, if_true]
          have : (decide (u.val < 55296) || decide (u.val > 57343)) = false := by simp; omega
          rw [this, h]; rfl
        by_cases kB : u.val ≤ 56319
        · obtain ⟨i3, hi3, hi3v⟩ := usize_add_k i 3#usize (by simp; omega)
          have hi3v' : i3.val = i.val + 3 := by simpa using hi3v
          by_cases hn3 : i.val + 3 < b.val.length
          · have hn3v : i3.val < b.val.length := by omega
            obtain ⟨w, hw, hwv⟩ := beatmap.text.unit16_refines b i2 be (by omega)
            rw [hi2v'] at hwv
            have hw65 := unitN_lt b be (i.val + 2)
            by_cases kw : 56320 ≤ w.val ∧ w.val ≤ 57343
            · right; left
              obtain ⟨i6, hi6, hi6v⟩ := eq_ok_of_spec (U32.sub_spec (x := u) (y := 55296#u32) (by simp; omega))
              have hi6v' : i6.val = u.val - 55296 := by simpa using hi6v.1
              obtain ⟨i7, hi7, hi7v⟩ := shl_ok i6 10#i32 (by simp) (by simp)
              have hi7v' : i7.val = (u.val - 55296) * 1024 := by
                rw [hi7v, hi6v']; simp [Nat.shiftLeft_eq]; omega
              obtain ⟨i8, hi8, hi8v⟩ := eq_ok_of_spec (U32.add_spec (x := 65536#u32) (y := i7) (by simp [U32.max, U32.numBits]; omega))
              obtain ⟨i10, hi10, hi10v⟩ := eq_ok_of_spec (U32.sub_spec (x := w) (y := 56320#u32) (by simp; omega))
              have hi8v' : i8.val = 65536 + (u.val - 55296) * 1024 := by rw [hi8v, hi7v']; simp
              have hi10v' : i10.val = w.val - 56320 := by simpa using hi10v.1
              obtain ⟨i11, hi11, hi11v⟩ := eq_ok_of_spec (U32.add_spec (x := i8) (y := i10) (by simp [U32.max, U32.numBits]; omega))
              have hi11v' : i11.val = 65536 + (u.val - 55296) * 1024 + (w.val - 56320) := by rw [hi11v, hi8v', hi10v']
              obtain ⟨i12, hi12, hi12v⟩ := usize_add_k i 4#usize (by simp; omega)
              have hi12v' : i12.val = i.val + 4 := by simpa using hi12v
              refine ⟨(pushV out i11 (by omega), i12, false), (none, ((out.val ++ [i11]).map chOf).toArray, i12.val), ?_, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
              · simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA', kA'', kB, hi3, hn3v, hi2, hw, kw, hi6, hi7, hi8, hi10, hi11, L, hi12]
              · simp only [u16G, unit_spec_eq, ← huv, hsz, hn1, if_true, ← hwv]
                have : (decide (u.val < 55296) || decide (u.val > 57343)) = false := by simp; omega
                have h2 : (decide (u.val ≤ 56319) && decide (i.val + 3 < b.val.length) && decide (56320 ≤ w.val) &&
                    decide (w.val ≤ 57343)) = true := by simp; omega
                rw [this, h2]; simp [chOf, hi11v', hi12v', Nat.shiftLeft_eq]
              · simp
              · intro z hz; simp at hz; rcases hz with hz | hz
                · exact hv z hz
                · rw [hz, hi11v']; simp [Nat.isValidChar]; omega
              · dsimp only; simp; omega
              · dsimp only; omega
            · right; right
              refine ⟨(out, i, true), (some none, (out.val.map chOf).toArray, i.val), ?_, ?_, BAD⟩
              · by_cases kw1 : 56320 ≤ w.val
                · have kw2 : ¬ w.val ≤ 57343 := fun h => kw ⟨kw1, h⟩
                  simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA', kA'', kB, hi3, hn3v, hi2, hw, kw1, kw2]
                · simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA', kA'', kB, hi3, hn3v, hi2, hw, kw1]
              · apply SP
                rw [← hwv]; simp; omega
          · right; right
            refine ⟨(out, i, true), (some none, (out.val.map chOf).toArray, i.val), ?_, ?_, BAD⟩
            · have : ¬ i3.val < b.val.length := by omega
              simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA', kA'', kB, hi3, this]
            · apply SP
              simp; omega
        · right; right
          refine ⟨(out, i, true), (some none, (out.val.map chOf).toArray, i.val), ?_, ?_, BAD⟩
          · simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1', hn1v, hu, kA', kA'', kB]
          · apply SP
            simp; omega
    · right; left
      have hn1v : ¬ i1.val < b.val.length := by omega
      refine ⟨(pushV out beatmap.text.REPL (by omega), i1, false), (none, ((out.val ++ [beatmap.text.REPL]).map chOf).toArray, i1.val), ?_, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      · simp [beatmap.text.decode_utf16_loop.body, hi', hi1, hn1v, L]
      · simp [u16G, hsz, hn1, hi, hi1v, beatmap.text.REPL]; rfl
      · simp
      · intro z hz; simp at hz; rcases hz with hz | hz
        · exact hv z hz
        · rw [hz]; simp [beatmap.text.REPL, Nat.isValidChar]
      · dsimp only; simp; omega
      · dsimp only; omega
  · left
    have hi' : ¬ i < Slice.len b := by show ¬ i.val < (Slice.len b).val; simpa using hi
    refine ⟨(out, false), by simp [beatmap.text.decode_utf16_loop.body, hi'], ?_, Or.inl ⟨rfl, rfl, rfl, hv⟩⟩
    simp [u16G, hsz, hi, show ¬ i.val + 1 < b.val.length by omega]

def optS (o : Option (alloc.vec.Vec U32)) : Option (_root_.Array Char) := o.map (fun v => (v.val.map chOf).toArray)

theorem beatmap.text.decode_utf16_refines (b : Slice U8) (start : Usize) (be : Bool) (hb : b.val.length < Usize.max) :
    ∃ v, beatmap.text.decode_utf16 b start be = ok v ∧ optS v = decodeUtf16 (bytesS b) start.val be ∧
      ∀ o, v = some o → ValidL o.val := by
  obtain ⟨y, hy, hq⟩ := loop_iterId
    (fun (x : U16X) => beatmap.text.decode_utf16_loop.body b be (Slice.len b) x.1 x.2.1 x.2.2)
    (u16G (bytesS b) be) (fun x => b.val.length - x.2.1.val) (u16R b) u16Q
    (by
      intro x s hr
      rcases u16_step b be hb x s hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    (b.val.length + 1) (alloc.vec.Vec.new U32, start, false) (none, #[], start.val)
    ⟨rfl, by simp [alloc.vec.Vec.new], by simp [ValidL, alloc.vec.Vec.new], by simp [alloc.vec.Vec.new]⟩ (by omega)
  have hl : beatmap.text.decode_utf16_loop b be (Slice.len b) (alloc.vec.Vec.new U32) start false = ok y := by
    unfold beatmap.text.decode_utf16_loop; exact hy
  unfold beatmap.text.decode_utf16
  simp only [hl, bind_ok]
  rw [decodeUtf16_eq, bytesS_size]
  simp only [Id.run]
  obtain ⟨yo, yb⟩ := y
  rcases hq with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · dsimp only at h1 h2 h3 h4; subst h1
    refine ⟨some yo, by simp, ?_, fun o ho => by cases ho; exact h4⟩
    revert h2 h3
    generalize iterId (u16G (bytesS b) be) (b.val.length + 1) (none, #[], start.val) = r
    rcases r with ⟨_ | _, o, i⟩ <;> intro h2 h3 <;> simp_all [optS] <;> rfl
  · dsimp only at h1 h2; subst h1
    refine ⟨none, by simp, ?_, fun o ho => by cases ho⟩
    revert h2
    generalize iterId (u16G (bytesS b) be) (b.val.length + 1) (none, #[], start.val) = r
    rcases r with ⟨_ | _, o, i⟩ <;> intro h2 <;> simp_all [optS] <;> rfl

theorem byteAt_list (b : Slice U8) (j : Nat) : byteAt b j = ((b.val[j]?).map (·.val)).getD 0 := by
  unfold byteAt; split
  · rename_i h; simp [h]
  · rename_i h; simp [show b.val.length ≤ j by omega]

theorem bom_spec (b : Slice U8) (k : Nat) (c : Nat) (hc : c < 256) :
    ((bytesS b)[k]! == (UInt8.ofNat c)) = decide (byteAt b k = c) := by
  rw [← bytesS_get']
  by_cases h : ((bytesS b)[k]!).toNat = c
  · have : (bytesS b)[k]! = UInt8.ofNat c := by
      apply UInt8.toNat_inj.mp; rw [h]; simp; omega
    simp [this, h, hc]
  · have : ¬ (bytesS b)[k]! = UInt8.ofNat c := by
      intro e; apply h; rw [e]; simp; omega
    simp [this, h, hc]

theorem u8_eq_iff (a b : U8) : a = b ↔ a.val = b.val := ⟨congrArg _, UScalar.eq_of_val_eq⟩

theorem bom4 (b : Slice U8) (x0 x1 x2 x3 : U8) : (b.val.take 4 = [x0, x1, x2, x3]) ↔
    (b.val.length ≥ 4 ∧ byteAt b 0 = x0.val ∧ byteAt b 1 = x1.val ∧ byteAt b 2 = x2.val ∧ byteAt b 3 = x3.val) := by
  simp only [byteAt_list]
  generalize b.val = l
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, t⟩⟩⟩⟩ <;> simp [u8_eq_iff]
theorem bom3 (b : Slice U8) (x0 x1 x2 : U8) : (b.val.take 3 = [x0, x1, x2]) ↔
    (b.val.length ≥ 3 ∧ byteAt b 0 = x0.val ∧ byteAt b 1 = x1.val ∧ byteAt b 2 = x2.val) := by
  simp only [byteAt_list]
  generalize b.val = l
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, t⟩⟩⟩ <;> simp [u8_eq_iff]
theorem bom2 (b : Slice U8) (x0 x1 : U8) : (b.val.take 2 = [x0, x1]) ↔
    (b.val.length ≥ 2 ∧ byteAt b 0 = x0.val ∧ byteAt b 1 = x1.val) := by
  simp only [byteAt_list]
  generalize b.val = l
  rcases l with _ | ⟨a0, _ | ⟨a1, t⟩⟩ <;> simp [u8_eq_iff]

theorem bomFF (b : Slice U8) (k : Nat) : ((bytesS b)[k]! == 0xFF) = decide (byteAt b k = 255) := bom_spec b k 255 (by decide)
theorem bomFE (b : Slice U8) (k : Nat) : ((bytesS b)[k]! == 0xFE) = decide (byteAt b k = 254) := bom_spec b k 254 (by decide)
theorem bom00 (b : Slice U8) (k : Nat) : ((bytesS b)[k]! == 0) = decide (byteAt b k = 0) := bom_spec b k 0 (by decide)
theorem bomEF (b : Slice U8) (k : Nat) : ((bytesS b)[k]! == 0xEF) = decide (byteAt b k = 239) := bom_spec b k 239 (by decide)
theorem bomBB (b : Slice U8) (k : Nat) : ((bytesS b)[k]! == 0xBB) = decide (byteAt b k = 187) := bom_spec b k 187 (by decide)
theorem bomBF (b : Slice U8) (k : Nat) : ((bytesS b)[k]! == 0xBF) = decide (byteAt b k = 191) := bom_spec b k 191 (by decide)

theorem beatmap.text.stream_reader_decode_refines (b : Slice U8) (hb : b.val.length < Usize.max) :
    ∃ v, beatmap.text.stream_reader_decode b = ok v ∧ optS v = streamReaderDecode (bytesS b) ∧
      ∀ o, v = some o → ValidL o.val := by
  obtain ⟨v1, h1, h1s, h1v⟩ := beatmap.text.decode_utf16_refines b 2#usize true hb
  obtain ⟨v2, h2, h2s, h2v⟩ := beatmap.text.decode_utf16_refines b 2#usize false hb
  obtain ⟨v3, h3, h3s, h3v⟩ := beatmap.text.decode_utf8_refines b 3#usize
  obtain ⟨v4, h4, h4s, h4v⟩ := beatmap.text.decode_utf8_refines b 0#usize
  unfold beatmap.text.stream_reader_decode streamReaderDecode
  simp only [lift, bind_ok, beatmap.text.has_prefix_refines, Array.to_slice, Array.make, bom4, bom3, bom2,
    bomFF, bomFE, bom00, bomEF, bomBB, bomBF, bytesS_size, h1, h2, h3, h4, Slice.from_val, Array.from_val]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, bom4, bom3, bom2]
  have l255 : (255#u8 : U8).val = 255 := rfl
  have l254 : (254#u8 : U8).val = 254 := rfl
  have l0 : (0#u8 : U8).val = 0 := rfl
  have l239 : (239#u8 : U8).val = 239 := rfl
  have l187 : (187#u8 : U8).val = 187 := rfl
  have l191 : (191#u8 : U8).val = 191 := rfl
  simp only [l255, l254, l0, l239, l187, l191, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  split_ifs <;> first
    | exact ⟨_, rfl, rfl, fun o ho => by cases ho⟩
    | exact ⟨_, rfl, h1s, h1v⟩
    | exact ⟨_, rfl, h2s, h2v⟩
    | exact ⟨_, rfl, by simp [optS, h3s], fun o ho => by cases ho; exact h3v⟩
    | exact ⟨_, rfl, by simp [optS, h4s], fun o ho => by cases ho; exact h4v⟩


/-- Helper (spec: the local `cont` of `decodeUtf8`, `x &&& 0xC0 == 0x80`). -/
theorem beatmap.text.is_cont_refines (x : U8) : beatmap.text.is_cont x = ok (decide (x.val &&& 192 = 128)) :=
  is_cont_nat x

end OsuProofs
