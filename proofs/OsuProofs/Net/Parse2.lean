/-
`net::parse` part 2: the number grammar (`expLoop`, `parseExp`, `digitsLoop`, `parseNumber`),
`int.Parse`, the Infinity/NaN fallback, `double/float.Parse` and lazer's `Parsing.*`.
-/
import OsuProofs.Net.Parse
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Aeneas Aeneas.Std Result
open OsuModel.Net OsuModel.Net.Parse

namespace OsuProofs
open OsuImpl

theorem digitVal_chOf (u : U32) (h : u.val.isValidChar) : digitVal (chOf u) = u.val - 48 := by
  simp [digitVal, chOf_toNat u h]

theorem isDigit_chOf (u : U32) (h : u.val.isValidChar) :
    isDigit (chOf u) = (decide (48 ≤ u.val) && decide (u.val ≤ 57)) := by
  have e := chOf_toNat u h
  have l1 : ('0' ≤ chOf u) ↔ 48 ≤ u.val := by
    rw [Char.le_def, UInt32.le_iff_toNat_le]; show '0'.toNat ≤ (chOf u).toNat ↔ _; rw [e]; rfl
  have l2 : (chOf u ≤ '9') ↔ u.val ≤ 57 := by
    rw [Char.le_def, UInt32.le_iff_toNat_le]; show (chOf u).toNat ≤ '9'.toNat ↔ _; rw [e]; rfl
  unfold isDigit
  by_cases h1 : 48 ≤ u.val <;> by_cases h2 : u.val ≤ 57 <;> simp [l1, l2, h1, h2]

theorem exp_loop_spec (s : Slice U32) (hs : ValidStr s) (start : Usize) :
    ∃ e sat r, net.parse.exp_loop s start = ok (e, sat, r) ∧ 0 ≤ e.val ∧
      ((e.val.toNat, sat, (strS s).drop r.val) = expLoop ((strS s).drop start.val) 0 false) := by
  let T := expLoop ((strS s).drop start.val) 0 false
  unfold net.parse.exp_loop net.parse.exp_loop_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : I64 × Bool × Usize) => net.parse.exp_loop_loop.body s x.1 x.2.1 x.2.2)
    (fun x => s.val.length - x.2.2.val)
    (fun x => 0 ≤ x.1.val ∧ x.1.val ≤ 999999999 ∧ expLoop ((strS s).drop x.2.2.val) x.1.val.toNat x.2.1 = T)
    (fun y => 0 ≤ y.1.val ∧ (y.1.val.toNat, y.2.1, (strS s).drop y.2.2.val) = T)
    (by
      rintro ⟨e, sat, i⟩ ⟨he0, he1, hT⟩
      dsimp only at he0 he1 hT ⊢
      have hl := Slice.length_ineq s
      by_cases hlt : i < Slice.len s
      · have hlt' : i.val < s.val.length := by simpa using hlt
        have hc := hs.get i.val hlt'
        rw [strS_drop s i.val hlt'] at hT
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        by_cases hd : isDigit (chOf (s.val[i.val]'hlt')) = true
        · right
          have hdv : 48 ≤ (s.val[i.val]'hlt').val ∧ (s.val[i.val]'hlt').val ≤ 57 := by
            rw [isDigit_chOf _ hc] at hd; simpa using hd
          by_cases hsat : sat = true ∨ e.val ≥ 100000000
          · refine ⟨(e, true, i1), ?_, ⟨he0, he1, ?_⟩, by dsimp only; omega⟩
            · rcases hsat with h | h
              · simp [net.parse.exp_loop_loop.body, hlt, index_eq s i hlt', net.parse.is_digit_refines _ hc, hd, h, hi1]
              · have h' : e >= 100000000#i64 := by simpa using h
                by_cases hs' : sat = true
                · simp [net.parse.exp_loop_loop.body, hlt, index_eq s i hlt', net.parse.is_digit_refines _ hc, hd, hs', hi1]
                · simp [net.parse.exp_loop_loop.body, hlt, index_eq s i hlt', net.parse.is_digit_refines _ hc, hd, hs', h', hi1]
            · dsimp only; rw [hi1v, ← hT]
              have : (sat || decide (e.val.toNat ≥ 100000000)) = true := by
                rcases hsat with h | h
                · simp [h]
                · simp; right; omega
              simp [expLoop, hd, this]
          · have hs' : sat = false := by simpa using (not_or.mp hsat).1
            have hlt8 : e.val < 100000000 := by have := (not_or.mp hsat).2; omega
            have h' : ¬ (e >= 100000000#i64) := by simp; omega
            obtain ⟨m, hm, hmv⟩ := eq_ok_of_spec (I64.mul_spec (x := e) (y := 10#i64)
              (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
            obtain ⟨d, hd', hdv', _⟩ := eq_ok_of_spec (U32.sub_spec (x := s.val[i.val]'hlt') (y := 48#u32)
              (by simp; omega))
            have hcd : (UScalar.hcast .I64 d).val = (d.val : Int) := by
              rw [UScalar.hcast_val_eq]
              have hb : d.val < 2^32 := by have := d.hBounds; simpa using this
              exact Int.bmod_eq_of_le (by simp) (by simp; omega)
            simp at hmv hdv'
            obtain ⟨e2, he2, he2v⟩ := eq_ok_of_spec (I64.add_spec (x := m) (y := UScalar.hcast .I64 d)
              (by rw [hcd, hmv]; simp [I64.min_eq]; omega) (by rw [hcd, hmv]; simp [I64.max_eq]; omega))
            rw [hcd, hmv] at he2v
            refine ⟨(e2, false, i1), ?_, ⟨?_, ?_, ?_⟩, by dsimp only; omega⟩
            · simp [net.parse.exp_loop_loop.body, hlt, index_eq s i hlt', net.parse.is_digit_refines _ hc, hd, hs', h',
                hm, hd', lift, he2, hi1]
            · dsimp only; rw [he2v]; omega
            · dsimp only; rw [he2v]; omega
            · dsimp only; rw [hi1v, ← hT]
              have : (sat || decide (e.val.toNat ≥ 100000000)) = false := by simp [hs']; omega
              simp only [expLoop, hd, this, ite_true, Bool.false_eq_true, ite_false, digitVal_chOf _ hc, he2v]
              congr 1; omega
        · left
          refine ⟨(e, sat, i), by simp [net.parse.exp_loop_loop.body, hlt, index_eq s i hlt',
            net.parse.is_digit_refines _ hc, hd], he0, ?_⟩
          dsimp only; rw [← hT, strS_drop s i.val hlt']; simp [expLoop, hd]
      · left
        have : s.val.length ≤ i.val := by
          have : ¬ i.val < s.val.length := by simpa using hlt
          omega
        refine ⟨(e, sat, i), by simp [net.parse.exp_loop_loop.body, hlt], he0, ?_⟩
        have e' : (strS s).drop i.val = [] := List.drop_eq_nil_of_le (by simp [strS_length]; omega)
        dsimp only; rw [← hT, e']; simp [expLoop]) (0#i64, false, start) (by simp [T])
  obtain ⟨e, sat, r⟩ := y
  exact ⟨e, sat, r, hy, hq⟩

theorem chOf_eq_iff (u : U32) (h : u.val.isValidChar) (c : Char) : chOf u = c ↔ u.val = c.toNat := by
  constructor
  · intro e; rw [← e, chOf_toNat u h]
  · intro e; apply Char.ext; apply UInt32.toNat_inj.mp; show (chOf u).toNat = c.toNat; rw [chOf_toNat u h, e]

/-- Spec tail of `parseExp` after the optional sign. -/
def peTail (negE : Bool) (r s0 : List Char) : Int × Option Bool × List Char :=
  match r with
  | d :: _ =>
    if isDigit d then
      let (e, sat, r') := expLoop r 0 false
      if sat then (0, some negE, r') else ((if negE then -(e : Int) else e), none, r')
    else (0, none, s0)
  | [] => (0, none, s0)

def signSplit : List Char → Bool × List Char
  | '+' :: r => (false, r)
  | '-' :: r => (true, r)
  | r => (false, r)

theorem parseExp_cons (c : Char) (rest : List Char) : parseExp (c :: rest) =
    if c == 'e' || c == 'E' then peTail (signSplit rest).1 (signSplit rest).2 (c :: rest)
    else (0, none, c :: rest) := by
  by_cases h : (c == 'e' || c == 'E') = true
  · simp only [parseExp, h, ite_true]
    rcases rest with _ | ⟨x, r⟩
    · simp [signSplit]; rfl
    · by_cases hp : x = '+'
      · subst hp; simp [signSplit]; rfl
      · by_cases hm : x = '-'
        · subst hm; simp [signSplit]; rfl
        · simp only [signSplit]; split <;> simp_all [peTail]
  · simp only [parseExp, h, ite_false, Bool.false_eq_true]

/-- Verbatim copy of the generated tail of `net.parse.parse_exp` (after the optional sign). -/
def peTailImpl (s : Slice U32) (i r1 : Usize) (neg_e : Bool) : Result (I64 × Option Bool × Usize) := do
  let i4 := Slice.len s
  if r1 < i4
  then
    let i5 ← Slice.index_usize s r1
    let b ← net.parse.is_digit i5
    if b
    then
      let (e, sat, r2) ← net.parse.exp_loop s r1
      if sat
      then ok (0#i64, some neg_e, r2)
      else
        if neg_e
        then let e1 ← -. e
             ok (e1, none, r2)
        else ok (e, none, r2)
    else ok (0#i64, none, i)
  else ok (0#i64, none, i)

/-- Verbatim copy of the generated sign step of `net.parse.parse_exp`. -/
def peSignImpl (s : Slice U32) (r : Usize) : Result (Usize × Bool) := do
  let i3 := Slice.len s
  if r < i3
  then
    do
    let i4 ← Slice.index_usize s r
    if i4 = 43#u32
    then let r2 ← r + 1#usize
         ok (r2, false)
    else
      let i5 := Slice.len s
      if r < i5
      then
        if i4 = 45#u32
        then let r2 ← r + 1#usize
             ok (r2, true)
        else ok (r, false)
      else ok (r, false)
  else
    let i4 := Slice.len s
    if r < i4
    then
      do
      let i5 ← Slice.index_usize s r
      if i5 = 45#u32
      then let r2 ← r + 1#usize
           ok (r2, true)
      else ok (r, false)
    else ok (r, false)

theorem parse_exp_eq (s : Slice U32) (i : Usize) : net.parse.parse_exp s i =
    (if i < Slice.len s then do
      let i2 ← Slice.index_usize s i
      if i2 = 101#u32 ∨ i2 = 69#u32 then do
        let r ← i + 1#usize
        let (r1, neg_e) ← peSignImpl s r
        peTailImpl s i r1 neg_e
      else ok (0#i64, none, i)
    else ok (0#i64, none, i)) := by
  unfold net.parse.parse_exp
  by_cases hi : i < Slice.len s <;> simp only [hi, ite_true, ite_false]
  congr 1; funext i2
  by_cases h1 : i2 = 101#u32 <;> by_cases h2 : i2 = 69#u32 <;> simp only [h1, h2, true_or, or_true, or_false,
    ite_true, ite_false] <;> first | rfl | (subst h1; simp at h2)

theorem drop_nil_of_ge (s : Slice U32) (j : Nat) (h : s.val.length ≤ j) : (strS s).drop j = [] :=
  List.drop_eq_nil_of_le (by simp [strS_length]; omega)

theorem pe_sign_spec (s : Slice U32) (hs : ValidStr s) (r : Usize) (hr : r.val ≤ s.val.length) :
    ∃ r1 negE, peSignImpl s r = ok (r1, negE) ∧ r1.val ≤ s.val.length ∧
      signSplit ((strS s).drop r.val) = (negE, (strS s).drop r1.val) := by
  have hl := Slice.length_ineq s
  unfold peSignImpl
  by_cases hlt : r < Slice.len s
  · have hlt' : r.val < s.val.length := by simpa using hlt
    have hc := hs.get r.val hlt'
    obtain ⟨r2, hr2, hr2v⟩ := usize_add_one r (by omega)
    rw [strS_drop s r.val hlt']
    by_cases hp : (s.val[r.val]'hlt').val = 43
    · refine ⟨r2, false, by simp [hlt, index_eq s r hlt', u32_eq_val, hp, hr2], by omega, ?_⟩
      have : chOf (s.val[r.val]'hlt') = '+' := (chOf_eq_iff _ hc _).mpr (by simp [hp])
      rw [this, hr2v]; rfl
    · by_cases hm : (s.val[r.val]'hlt').val = 45
      · refine ⟨r2, true, by simp [hlt, index_eq s r hlt', u32_eq_val, hp, hm, hr2], by omega, ?_⟩
        have : chOf (s.val[r.val]'hlt') = '-' := (chOf_eq_iff _ hc _).mpr (by simp [hm])
        rw [this, hr2v]; rfl
      · refine ⟨r, false, by simp [hlt, index_eq s r hlt', u32_eq_val, hp, hm], by omega, ?_⟩
        have h1 : chOf (s.val[r.val]'hlt') ≠ '+' := fun e => hp (by rw [(chOf_eq_iff _ hc _).mp e]; rfl)
        have h2 : chOf (s.val[r.val]'hlt') ≠ '-' := fun e => hm (by rw [(chOf_eq_iff _ hc _).mp e]; rfl)
        rw [strS_drop s r.val hlt']
        simp only [signSplit]; split <;> simp_all
  · have hge : s.val.length ≤ r.val := by have : ¬ r.val < s.val.length := by simpa using hlt
                                          omega
    refine ⟨r, false, by simp [hlt], by omega, ?_⟩
    rw [drop_nil_of_ge s r.val hge]; rfl

theorem pe_tail_spec (s : Slice U32) (hs : ValidStr s) (i r1 : Usize) (negE : Bool) :
    ∃ x, peTailImpl s i r1 negE = ok x ∧
      (x.1.val, x.2.1, (strS s).drop x.2.2.val) = peTail negE ((strS s).drop r1.val) ((strS s).drop i.val) := by
  unfold peTailImpl
  by_cases hlt : r1 < Slice.len s
  · have hlt' : r1.val < s.val.length := by simpa using hlt
    have hc := hs.get r1.val hlt'
    rw [strS_drop s r1.val hlt']
    by_cases hd : isDigit (chOf (s.val[r1.val]'hlt')) = true
    · obtain ⟨e, sat, r2, he, he0, hT⟩ := exp_loop_spec s hs r1
      rw [strS_drop s r1.val hlt'] at hT
      simp only [peTail, hd, ite_true, ← hT]
      by_cases hsat : sat = true
      · exact ⟨(0#i64, some negE, r2), by simp [hlt, index_eq s r1 hlt', net.parse.is_digit_refines _ hc, hd, he, hsat],
          by simp [hsat]⟩
      · have hsat' : sat = false := by simpa using hsat
        by_cases hn : negE = true
        · have hb := e.hmax
          obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step e (by simp [IScalar.min, I64.min_eq]; omega))
          exact ⟨(q, none, r2), by simp [hlt, index_eq s r1 hlt', net.parse.is_digit_refines _ hc, hd, he, hsat',
            hn, HNeg.hNeg, hq], by simp [hsat', hn, hqv]; omega⟩
        · have hn' : negE = false := by simpa using hn
          exact ⟨(e, none, r2), by simp [hlt, index_eq s r1 hlt', net.parse.is_digit_refines _ hc, hd, he, hsat', hn'],
            by simp [hsat', hn']; omega⟩
    · exact ⟨(0#i64, none, i), by simp [hlt, index_eq s r1 hlt', net.parse.is_digit_refines _ hc, hd],
        by simp [peTail, hd]⟩
  · have hge : s.val.length ≤ r1.val := by have : ¬ r1.val < s.val.length := by simpa using hlt
                                           omega
    exact ⟨(0#i64, none, i), by simp [hlt], by rw [drop_nil_of_ge s r1.val hge]; simp [peTail]⟩

theorem net.parse.parse_exp_refines (s : Slice U32) (hs : ValidStr s) (i : Usize) :
    ∃ e o r, net.parse.parse_exp s i = ok (e, o, r) ∧
      (e.val, o, (strS s).drop r.val) = parseExp ((strS s).drop i.val) := by
  have hl := Slice.length_ineq s
  rw [parse_exp_eq]
  by_cases hlt : i < Slice.len s
  · have hlt' : i.val < s.val.length := by simpa using hlt
    have hc := hs.get i.val hlt'
    rw [strS_drop s i.val hlt', parseExp_cons]
    by_cases he : (s.val[i.val]'hlt').val = 101 ∨ (s.val[i.val]'hlt').val = 69
    · have he' : (chOf (s.val[i.val]'hlt') == 'e' || chOf (s.val[i.val]'hlt') == 'E') = true := by
        rcases he with h | h
        · have : chOf (s.val[i.val]'hlt') = 'e' := (chOf_eq_iff _ hc _).mpr (by simp [h])
          simp [this]
        · have : chOf (s.val[i.val]'hlt') = 'E' := (chOf_eq_iff _ hc _).mpr (by simp [h])
          simp [this]
      have he'' : (s.val[i.val]'hlt') = 101#u32 ∨ (s.val[i.val]'hlt') = 69#u32 := by
        simpa [u32_eq_val] using he
      obtain ⟨r, hr, hrv⟩ := usize_add_one i (by omega)
      obtain ⟨r1, negE, hsg, hr1, hsgv⟩ := pe_sign_spec s hs r (by omega)
      obtain ⟨x, hx, hxv⟩ := pe_tail_spec s hs i r1 negE
      refine ⟨x.1, x.2.1, x.2.2, by simp [hlt, index_eq s i hlt', he'', hr, hsg, hx], ?_⟩
      rw [he']; simp only [ite_true]; rw [← strS_drop s i.val hlt', hxv, ← hrv, hsgv]
    · have he' : (chOf (s.val[i.val]'hlt') == 'e' || chOf (s.val[i.val]'hlt') == 'E') = false := by
        have h1 : chOf (s.val[i.val]'hlt') ≠ 'e' := fun e => he (Or.inl (by rw [(chOf_eq_iff _ hc _).mp e]; rfl))
        have h2 : chOf (s.val[i.val]'hlt') ≠ 'E' := fun e => he (Or.inr (by rw [(chOf_eq_iff _ hc _).mp e]; rfl))
        simp [h1, h2]
      have he'' : ¬ ((s.val[i.val]'hlt') = 101#u32 ∨ (s.val[i.val]'hlt') = 69#u32) := by
        simpa [u32_eq_val] using he
      refine ⟨0#i64, none, i, by simp only [hlt, ite_true, index_eq s i hlt', bind_ok, he'', ite_false], ?_⟩
      rw [he']; simp [strS_drop s i.val hlt']
  · have hge : s.val.length ≤ i.val := by have : ¬ i.val < s.val.length := by simpa using hlt
                                          omega
    refine ⟨0#i64, none, i, by simp [hlt], ?_⟩
    rw [drop_nil_of_ge s i.val hge]; rfl

def mOf (d : List U8) : Nat := (digitsVal d).getD 0

theorem digitsVal_append (l : List U8) (d : U8) :
    digitsVal (l ++ [d]) = (digitsVal l).bind fun a => if d.val < 10 then some (10 * a + d.val) else none := by
  simp [digitsVal, List.foldl_append]

/-- digit vectors: all digit values < 10 (so `digitsVal` is `some`), and empty iff the value is 0. -/
def DigOk (d : List U8) : Prop := (∀ x ∈ d, x.val < 10) ∧ (d = [] ↔ mOf d = 0)

theorem digitsVal_some (d : List U8) (h : ∀ x ∈ d, x.val < 10) : digitsVal d = some (mOf d) := by
  induction d using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    have hl : ∀ y ∈ l, y.val < 10 := fun y hy => h y (by simp [hy])
    have hx : x.val < 10 := h x (by simp)
    simp only [mOf] at ih ⊢
    rw [digitsVal_append, ih hl]; simp [hx]

theorem mOf_push (l : List U8) (d : U8) (hl : ∀ x ∈ l, x.val < 10) (hd : d.val < 10) :
    mOf (l ++ [d]) = mOf l * 10 + d.val := by
  have := digitsVal_some l hl
  simp only [mOf] at this ⊢
  rw [digitsVal_append, this]; simp [hd]; ring

abbrev DLState := alloc.vec.Vec U8 × I64 × Bool × Bool × Usize × Bool

def dlInv (s : Slice U32) (T : Nat × Nat × Bool × List Char) (x : DLState) : Prop :=
  DigOk x.1.val ∧ x.1.val.length ≤ x.2.2.2.2.1.val ∧ 0 ≤ x.2.1.val ∧ x.2.1.val ≤ x.2.2.2.2.1.val ∧
  x.2.2.2.2.1.val ≤ s.val.length ∧
  (if x.2.2.2.2.2 then digitsLoop ((strS s).drop x.2.2.2.2.1.val) (mOf x.1.val) x.2.1.val.toNat x.2.2.1 x.2.2.2.1 = T
   else (mOf x.1.val, x.2.1.val.toNat, x.2.2.1, (strS s).drop x.2.2.2.2.1.val) = T)

theorem digits_loop_spec (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62) (start : Usize)
    (hst : start.val ≤ s.val.length) (inDec : Bool) :
    ∃ d, net.parse.digits_loop s start inDec = ok d ∧ DigOk d.digits.val ∧ 0 ≤ d.nf.val ∧
      d.nf.val ≤ s.val.length ∧ d.rest.val ≤ s.val.length ∧
      (mOf d.digits.val, d.nf.val.toNat, d.seen, (strS s).drop d.rest.val) =
        digitsLoop ((strS s).drop start.val) 0 0 false inDec := by
  let T := digitsLoop ((strS s).drop start.val) 0 0 false inDec
  have hl := Slice.length_ineq s
  unfold net.parse.digits_loop net.parse.digits_loop_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : DLState) => net.parse.digits_loop_loop.body s x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (fun x => 2 * (s.val.length - x.2.2.2.2.1.val) + (if x.2.2.2.2.2 then 1 else 0))
    (dlInv s T)
    (fun y => DigOk y.1.val ∧ 0 ≤ y.2.1.val ∧ y.2.1.val ≤ s.val.length ∧ y.2.2.2.val ≤ s.val.length ∧
      (mOf y.1.val, y.2.1.val.toNat, y.2.2.1, (strS s).drop y.2.2.2.val) = T)
    (by
      rintro ⟨dg, nf, seen, ind, i, go⟩ ⟨hdok, hdl, hnf0, hnf1, hil, hT⟩
      dsimp only at hdok hdl hnf0 hnf1 hil hT ⊢
      cases go with
      | false =>
        left
        simp only [Bool.false_eq_true, ite_false] at hT
        exact ⟨(dg, nf, seen, i), by simp [net.parse.digits_loop_loop.body], hdok, hnf0, by dsimp only; omega, hil, hT⟩
      | true =>
        simp only [ite_true] at hT
        by_cases hlt : i < Slice.len s
        · right
          have hlt' : i.val < s.val.length := by simpa using hlt
          have hc := hs.get i.val hlt'
          rw [strS_drop s i.val hlt'] at hT
          obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
          have hidx := index_eq s i hlt'
          generalize hu : s.val[i.val]'hlt' = u at hc hT hidx
          have hdig := isDigit_chOf u hc
          by_cases hd : 48 ≤ u.val ∧ u.val ≤ 57
          · have hd' : isDigit (chOf u) = true := by rw [hdig]; simp [hd.1, hd.2]
            -- the new digit vector
            obtain ⟨dg1, hdg1, hdg1ok, hdg1m, hdg1l⟩ : ∃ dg1 : alloc.vec.Vec U8,
                (∀ {β : Type} (f : alloc.vec.Vec U8 → Result β),
                  (do let i2 := alloc.vec.Vec.len dg
                      let digits1 ← (if i2 = 0#usize then
                          (if u = 48#u32 then ok dg else do
                            let i3 ← u - 48#u32
                            let i4 ← lift (UScalar.cast .U8 i3)
                            alloc.vec.Vec.push dg i4)
                        else do
                          let i3 ← u - 48#u32
                          let i4 ← lift (UScalar.cast .U8 i3)
                          alloc.vec.Vec.push dg i4)
                      f digits1) = f dg1) ∧
                DigOk dg1.val ∧ mOf dg1.val = mOf dg.val * 10 + (u.val - 48) ∧ dg1.val.length ≤ i.val + 1 := by
              obtain ⟨hdall, hdz⟩ := hdok
              have hlen0 : (alloc.vec.Vec.len dg = 0#usize) ↔ dg.val = [] := by
                constructor
                · intro h; have := congrArg UScalar.val h; simpa using this
                · intro h; apply UScalar.eq_of_val_eq; simp [h]
              by_cases hz : dg.val = [] ∧ u.val = 48
              · refine ⟨dg, ?_, ⟨hdall, hdz⟩, ?_, by omega⟩
                · intro β f
                  have h1 : alloc.vec.Vec.len dg = 0#usize := hlen0.mpr hz.1
                  have h2 : u = 48#u32 := by rw [u32_eq_val]; simp [hz.2]
                  simp [h1, h2]
                · have : mOf dg.val = 0 := hdz.mp hz.1
                  rw [this, hz.2]
              · obtain ⟨d, hdd, hdv, _⟩ := eq_ok_of_spec (U32.sub_spec (x := u) (y := 48#u32) (by simp; omega))
                simp at hdv
                have hd8 : (UScalar.cast .U8 d).val = u.val - 48 := by
                  rw [UScalar.cast_val_eq]; simp; omega
                obtain ⟨dg1, hp, hpv⟩ := push_eq dg (UScalar.cast .U8 d) (by have := dg.property; omega)
                have hall1 : ∀ x ∈ dg1.val, x.val < 10 := by
                  rw [hpv]; intro x hx; simp at hx; rcases hx with hx | hx
                  · exact hdall x hx
                  · rw [hx, hd8]; omega
                have hm1 : mOf dg1.val = mOf dg.val * 10 + (u.val - 48) := by
                  rw [hpv, mOf_push _ _ hdall (by rw [hd8]; omega), hd8]
                refine ⟨dg1, ?_, ⟨hall1, ?_⟩, hm1, by rw [hpv]; simp; omega⟩
                · intro β f
                  by_cases he : dg.val = []
                  · have h1 : alloc.vec.Vec.len dg = 0#usize := hlen0.mpr he
                    have h2 : ¬ u = 48#u32 := by rw [u32_eq_val]; simp; intro h; exact hz ⟨he, h⟩
                    simp [h1, h2, hdd, lift, hp]
                  · have h1 : ¬ alloc.vec.Vec.len dg = 0#usize := fun h => he (hlen0.mp h)
                    simp [h1, hdd, lift, hp]
                · rw [hm1, hpv]; simp
                  intro h0
                  by_cases he : dg.val = []
                  · have : u.val ≠ 48 := fun h => hz ⟨he, h⟩
                    omega
                  · have := mt hdz.mpr he
                    have : mOf dg.val * 10 = 0 := by omega
                    omega
            have hnf : ∃ nf1 : I64, (if ind then nf + 1#i64 else ok nf) = ok nf1 ∧
                nf1.val = (if ind then nf.val + 1 else nf.val) := by
              cases ind
              · exact ⟨nf, by simp, by simp⟩
              · obtain ⟨z, hz, hzv⟩ := eq_ok_of_spec (I64.add_spec (x := nf) (y := 1#i64)
                  (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
                exact ⟨z, by simp [hz], by simpa using hzv⟩
            obtain ⟨nf1, hnfe, hnf1v⟩ := hnf
            refine ⟨(dg1, nf1, true, ind, i1, true), ?_, ⟨hdg1ok, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
            · simp only [net.parse.digits_loop_loop.body, ite_true, hlt, hidx, bind_ok,
                net.parse.is_digit_refines _ hc, hd']
              rw [hdg1]; simp [hnfe, hi1]
            · dsimp only; omega
            · dsimp only; rw [hnf1v]; split <;> omega
            · dsimp only; rw [hnf1v]; split <;> omega
            · dsimp only; omega
            · dsimp only; simp only [ite_true]; rw [← hT, hi1v, hdg1m, hnf1v]
              simp only [digitsLoop, hd', ite_true, digitVal_chOf _ hc]
              congr 2; cases ind <;> simp; omega
            · dsimp only; simp only [ite_true]; omega
          · have hd' : isDigit (chOf u) = false := by
              rw [hdig]; simp; intro h; omega
            have hdot : (chOf u == '.') = decide (u.val = 46) := by
              by_cases h : u.val = 46
              · simp [h, (chOf_eq_iff u hc '.').mpr (by simp [h])]
              · have : chOf u ≠ '.' := fun e => h (by rw [(chOf_eq_iff u hc '.').mp e]; rfl)
                simp [h, this]
            have hcom : (chOf u == ',') = decide (u.val = 44) := by
              by_cases h : u.val = 44
              · simp [h, (chOf_eq_iff u hc ',').mpr (by simp [h])]
              · have : chOf u ≠ ',' := fun e => h (by rw [(chOf_eq_iff u hc ',').mp e]; rfl)
                simp [h, this]
            have hT' := hT
            simp only [digitsLoop, hd', Bool.false_eq_true, ite_false, hdot, hcom] at hT'
            have h46 : (u = 46#u32) ↔ u.val = 46 := by rw [u32_eq_val]; simp
            have h44 : (u = 44#u32) ↔ u.val = 44 := by rw [u32_eq_val]; simp
            have hstop (hc' : digitsLoop (chOf u :: (strS s).drop (i.val + 1)) (mOf dg.val) nf.val.toNat seen ind =
                (mOf dg.val, nf.val.toNat, seen, chOf u :: (strS s).drop (i.val + 1))) :
                dlInv s T (dg, nf, seen, ind, i, false) := by
              refine ⟨hdok, hdl, hnf0, hnf1, hil, ?_⟩
              dsimp only; simp only [Bool.false_eq_true, ite_false, ↓reduceIte]
              rw [strS_drop s i.val hlt', hu, ← hT, hc']
            by_cases h1 : u.val = 46
            · have hu46 : (u = 46#u32) = True := eq_true (h46.mpr h1)
              have hn44 : (u = 44#u32) = False := eq_false (by rw [h44]; omega)
              cases ind
              · refine ⟨(dg, nf, seen, true, i1, true), by
                  simp only [net.parse.digits_loop_loop.body, ite_true, hlt, hidx, bind_ok,
                    net.parse.is_digit_refines _ hc, hd', hu46, Bool.false_eq_true, ite_false, hi1, ↓reduceIte],
                  ⟨hdok, by dsimp only; omega, hnf0, by dsimp only; omega, by dsimp only; omega, ?_⟩, by dsimp only; simp; omega⟩
                dsimp only; simp only [ite_true]; rw [hi1v, ← hT]
                simp [digitsLoop, hd', hdot, h1]
              · refine ⟨(dg, nf, seen, true, i, false), by
                  simp only [net.parse.digits_loop_loop.body, ite_true, hlt, hidx, bind_ok,
                    net.parse.is_digit_refines _ hc, hd', hu46, hn44, Bool.false_eq_true, ite_false, ↓reduceIte],
                  hstop (by simp [digitsLoop, hd', hdot, hcom, h1]), by dsimp only; simp⟩
            · have hn46 : (u = 46#u32) = False := eq_false (by rw [h46]; exact h1)
              by_cases h2 : u.val = 44
              · have hu44 : (u = 44#u32) = True := eq_true (h44.mpr h2)
                by_cases hsi : seen = true ∧ ind = false
                · obtain ⟨hs1, hi0⟩ := hsi
                  subst hs1; subst hi0
                  refine ⟨(dg, nf, true, false, i1, true), by
                    simp only [net.parse.digits_loop_loop.body, ite_true, hlt, hidx, bind_ok,
                      net.parse.is_digit_refines _ hc, hd', hn46, hu44, Bool.false_eq_true, ite_false, hi1, ↓reduceIte],
                    ⟨hdok, by dsimp only; omega, hnf0, by dsimp only; omega, by dsimp only; omega, ?_⟩,
                    by dsimp only; simp; omega⟩
                  dsimp only; simp only [ite_true]; rw [hi1v, ← hT]
                  simp [digitsLoop, hd', hdot, hcom, h1, h2]
                · refine ⟨(dg, nf, seen, ind, i, false), ?_, hstop ?_, by dsimp only; simp⟩
                  · cases seen <;> cases ind <;> simp at hsi <;>
                      simp only [net.parse.digits_loop_loop.body, ite_true, hlt, hidx, bind_ok,
                        net.parse.is_digit_refines _ hc, hd', hn46, hu44, Bool.false_eq_true, ite_false, ↓reduceIte]
                  · cases seen <;> cases ind <;> simp at hsi <;> simp [digitsLoop, hd', hdot, hcom, h1, h2]
              · have hn44 : (u = 44#u32) = False := eq_false (by rw [h44]; exact h2)
                refine ⟨(dg, nf, seen, ind, i, false), by
                  simp only [net.parse.digits_loop_loop.body, ite_true, hlt, hidx, bind_ok,
                    net.parse.is_digit_refines _ hc, hd', hn46, hn44, Bool.false_eq_true, ite_false, ↓reduceIte],
                  hstop (by simp [digitsLoop, hd', hdot, hcom, h1, h2]), by dsimp only; simp⟩
        · left
          have : i.val = s.val.length := by have : ¬ i.val < s.val.length := by simpa using hlt
                                            omega
          refine ⟨(dg, nf, seen, i), by simp [net.parse.digits_loop_loop.body, hlt], hdok, hnf0, by dsimp only; omega, hil, ?_⟩
          rw [← hT, drop_nil_of_ge s i.val (by omega)]; simp [digitsLoop])
    (alloc.vec.Vec.new U8, 0#i64, false, inDec, start, true)
    ⟨by simp [DigOk, mOf, digitsVal], by simp, by simp, by simp, hst, by simp [T, mOf, digitsVal]⟩
  obtain ⟨dg, nf, seen, r⟩ := y
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  exact ⟨⟨dg, nf, seen, r⟩, by simp [hy], h1, h2, h3, h4, h5⟩

theorem isDigit_digitVal (c : Char) (h : isDigit c = true) : digitVal c ≤ 9 := by
  simp [isDigit] at h
  have h2 := h.2
  rw [Char.le_def, UInt32.le_iff_toNat_le] at h2
  simp [digitVal]
  change c.toNat ≤ 57 at h2
  omega

theorem expLoop_bound (l : List Char) (e : Nat) (sat : Bool) (h : e ≤ 999999999) :
    (expLoop l e sat).1 ≤ 999999999 := by
  induction l generalizing e sat with
  | nil => simpa [expLoop] using h
  | cons c t ih =>
    simp only [expLoop]
    split
    · rename_i hd
      have hdv := isDigit_digitVal c hd
      split
      · exact ih _ _ h
      · rename_i h1; apply ih; simp at h1; omega
    · simpa using h

theorem peTail_bound (n : Bool) (t s0 : List Char) :
    -999999999 ≤ (peTail n t s0).1 ∧ (peTail n t s0).1 ≤ 999999999 := by
  unfold peTail
  split
  next d tl =>
    split
    · have hb := expLoop_bound (d :: tl) 0 false (by omega)
      generalize expLoop (d :: tl) 0 false = r at hb ⊢
      obtain ⟨e, sat, r'⟩ := r
      simp only at hb ⊢
      cases sat <;> cases n <;> simp <;> omega
    · simp
  · simp

theorem parseExp_bound (l : List Char) : -999999999 ≤ (parseExp l).1 ∧ (parseExp l).1 ≤ 999999999 := by
  cases l with
  | nil => simp [parseExp]
  | cons c rest =>
    rw [parseExp_cons]; split
    · exact peTail_bound _ _ _
    · simp

theorem parse_number_eq (s : Slice U32) : net.parse.parse_number s = (do
    let i ← net.parse.skip_white s 0#usize
    let (i2, neg) ← peSignImpl s i
    let d ← net.parse.digits_loop s i2 false
    if d.seen then
      let (e, sat, j) ← net.parse.parse_exp s d.rest
      let k ← net.parse.skip_white s j
      let b ← net.parse.all_nul s k
      if b then
        let i3 ← e - d.nf
        ok (some { neg, digits := d.digits, exp10 := i3, sat })
      else ok none
    else ok none) := by
  rfl

def numRel (n : net.parse.Num) (n' : Parse.Num) : Prop :=
  n.neg = n'.neg ∧ DigOk n.digits.val ∧ mOf n.digits.val = n'.mant ∧ n.exp10.val = n'.exp10 ∧ n.sat = n'.sat

def optRelN : Option net.parse.Num → Option Parse.Num → Prop
  | none, none => True
  | some a, some b => numRel a b
  | _, _ => False

theorem skip_white_le (s : Slice U32) (hs : ValidStr s) (i : Usize) (hi : i.val ≤ s.val.length) :
    ∃ j, net.parse.skip_white s i = ok j ∧ i.val ≤ j.val ∧ j.val ≤ s.val.length ∧
      (strS s).drop j.val = dropWhile isWhite ((strS s).drop i.val) := by
  obtain ⟨j, hj, hij, hjl, hjv⟩ := net.parse.skip_white_refines s hs i
  exact ⟨j, hj, hij, hjl hi, hjv⟩

/-- `parseNumber` with the sign `match` replaced by `signSplit`. -/
def parseNumber' (l : List Char) : Option Num :=
  let s := dropWhile isWhite l
  let (neg, s) := signSplit s
  let (m, nf, seen, s) := digitsLoop s 0 0 false false
  if !seen then none else
  let (e, sat, s) := parseExp s
  let s := dropWhile isWhite s
  if !allNul s then none else
  some { neg, mant := m, exp10 := e - nf, sat }

theorem parseNumber_eq (l : List Char) : parseNumber l = parseNumber' l := by
  unfold parseNumber parseNumber'
  generalize dropWhile isWhite l = t
  rcases t with _ | ⟨x, r⟩
  · rfl
  · by_cases hp : x = '+'
    · subst hp; rfl
    · by_cases hm : x = '-'
      · subst hm; rfl
      · simp only [signSplit]; split <;> simp_all

theorem net.parse.parse_number_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62) :
    ∃ r, net.parse.parse_number s = ok r ∧ optRelN r (parseNumber (strS s)) := by
  rw [parse_number_eq, parseNumber_eq]
  unfold parseNumber'
  obtain ⟨j0, hj0, -, hj0l, hj0v⟩ := skip_white_le s hs 0#usize (by simp)
  simp only [show ((0#usize : Usize).val) = 0 from rfl, List.drop_zero] at hj0v
  obtain ⟨i2, neg, hsg, hi2l, hsgv⟩ := pe_sign_spec s hs j0 hj0l
  obtain ⟨d, hd, hdok, hnf0, hnfl, hrl, hdv⟩ := digits_loop_spec s hs hsz i2 hi2l false
  rw [hj0, bind_ok, hsg, bind_ok]
  simp only [hd, bind_ok]
  rw [← hj0v, hsgv]
  simp only
  rw [← hdv]
  simp only
  cases hseen : d.seen
  · exact ⟨none, by simp [hd, hseen], by simp [optRelN]⟩
  · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false, hseen]
    obtain ⟨e, o, j, he, hev⟩ := net.parse.parse_exp_refines s hs d.rest
    have hb := parseExp_bound ((strS s).drop d.rest.val)
    rw [← hev] at hb ⊢
    simp only at hb ⊢
    obtain ⟨k, hk, -, -, hkv⟩ := net.parse.skip_white_refines s hs j
    rw [← hkv]
    cases han : allNul ((strS s).drop k.val)
    · exact ⟨none, by simp [hd, hseen, he, hk, net.parse.all_nul_refines s hs k, han], by simp [optRelN]⟩
    · obtain ⟨x, hx, hxv⟩ := eq_ok_of_spec (I64.sub_spec (x := e) (y := d.nf)
        (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
      refine ⟨some { neg := neg, digits := d.digits, exp10 := x, sat := o }, by simp [hd, hseen, he, hk, net.parse.all_nul_refines s hs k, han, hx], ?_⟩
      simp only [optRelN, numRel, Bool.not_true, ite_false, Bool.false_eq_true]
      refine ⟨trivial, hdok, trivial, ?_, trivial⟩
      rw [hxv]; omega

@[simp] theorem basic_F64_POS_INF : net.basic.F64_POS_INF = ok (F64.ofBitsN (Fmt.f64.encInf false)) := by
  simp [net.basic.F64_POS_INF, F64.ofBitsN]; decide
@[simp] theorem basic_F32_POS_INF : net.basic.F32_POS_INF = ok (F32.ofBitsN (Fmt.f32.encInf false)) := by
  simp [net.basic.F32_POS_INF, F32.ofBitsN]; decide
theorem f64_neg_inf : -(F64.ofBitsN (Fmt.f64.encInf false)) = F64.ofBitsN (Fmt.f64.encInf true) := by decide
theorem f32_neg_inf : -(F32.ofBitsN (Fmt.f32.encInf false)) = F32.ofBitsN (Fmt.f32.encInf true) := by decide

theorem net.parse.num_to_f64_refines (n : net.parse.Num) (n' : Parse.Num) (h : numRel n n') :
    net.parse.num_to_f64 n = ok (F64.ofBitsN (numToBits Fmt.f64 n')) := by
  obtain ⟨hneg, ⟨hall, hz⟩, hm, he, hsat⟩ := h
  have hdv := digitsVal_some _ hall
  have hderef : (alloc.vec.Vec.deref n.digits).val = n.digits.val := by simp [alloc.vec.Vec.deref]
  have e1 : digitsVal (Std.Array.empty U8).val = some 0 := by simp [Std.Array.empty, digitsVal]
  unfold net.parse.num_to_f64 numToBits
  rw [hsat]
  cases hs : n'.sat with
  | none =>
    simp [float.F64.parse_decimal, hderef, hdv, hm, he, hneg]
  | some negExp =>
    have hlen0 : (alloc.vec.Vec.len n.digits = 0#usize) ↔ n'.mant = 0 := by
      rw [← hm, ← hz]
      constructor
      · intro h; have := congrArg UScalar.val h; simpa using this
      · intro h; apply UScalar.eq_of_val_eq; simp [h]
    have e0 : digitsVal (Std.Array.to_slice (Std.Array.empty U8)).val = some 0 := by
      simp [Std.Array.to_slice, Std.Array.empty, digitsVal]
    by_cases hm0 : n'.mant = 0
    · have : alloc.vec.Vec.len n.digits = 0#usize := hlen0.mpr hm0
      simp [this, hm0, lift, float.F64.parse_decimal, e0, e1, decToBits, hneg]
    · have : ¬ alloc.vec.Vec.len n.digits = 0#usize := fun h => hm0 (hlen0.mp h)
      cases negExp
      · cases hn : n.neg <;> simp [this, hm0, hn, ← hneg, f64_neg_inf]
      · simp [this, hm0, lift, float.F64.parse_decimal, e0, e1, decToBits, hneg]

theorem net.parse.num_to_f32_refines (n : net.parse.Num) (n' : Parse.Num) (h : numRel n n') :
    net.parse.num_to_f32 n = ok (F32.ofBitsN (numToBits Fmt.f32 n')) := by
  obtain ⟨hneg, ⟨hall, hz⟩, hm, he, hsat⟩ := h
  have hdv := digitsVal_some _ hall
  have hderef : (alloc.vec.Vec.deref n.digits).val = n.digits.val := by simp [alloc.vec.Vec.deref]
  have e1 : digitsVal (Std.Array.empty U8).val = some 0 := by simp [Std.Array.empty, digitsVal]
  unfold net.parse.num_to_f32 numToBits
  rw [hsat]
  cases hs : n'.sat with
  | none =>
    simp [float.F32.parse_decimal, hderef, hdv, hm, he, hneg]
  | some negExp =>
    have hlen0 : (alloc.vec.Vec.len n.digits = 0#usize) ↔ n'.mant = 0 := by
      rw [← hm, ← hz]
      constructor
      · intro h; have := congrArg UScalar.val h; simpa using this
      · intro h; apply UScalar.eq_of_val_eq; simp [h]
    have e0 : digitsVal (Std.Array.to_slice (Std.Array.empty U8)).val = some 0 := by
      simp [Std.Array.to_slice, Std.Array.empty, digitsVal]
    by_cases hm0 : n'.mant = 0
    · have : alloc.vec.Vec.len n.digits = 0#usize := hlen0.mpr hm0
      simp [this, hm0, lift, float.F32.parse_decimal, e0, e1, decToBits, hneg]
    · have : ¬ alloc.vec.Vec.len n.digits = 0#usize := fun h => hm0 (hlen0.mp h)
      cases negExp
      · cases hn : n.neg <;> simp [this, hm0, hn, ← hneg, f32_neg_inf]
      · simp [this, hm0, lift, float.F32.parse_decimal, e0, e1, decToBits, hneg]

theorem ps_loop0_spec (s : Slice U32) (hs : ValidStr s) :
    ∃ lo, net.parse.parse_symbol_loop0 s 0#usize = ok lo ∧ lo.val ≤ s.val.length ∧
      (strS s).drop lo.val = dropWhile isUnicodeWhiteSpace (strS s) := by
  let T := dropWhile isUnicodeWhiteSpace (strS s)
  unfold net.parse.parse_symbol_loop0
  apply loop_ok _ (fun j => s.val.length - j.val)
    (fun j => j.val ≤ s.val.length ∧ dropWhile isUnicodeWhiteSpace ((strS s).drop j.val) = T)
  · rintro j ⟨hjl, hT⟩
    have hl := slice_len_lt s
    by_cases hlt : j < Slice.len s
    · have hlt' : j.val < s.val.length := by simpa using hlt
      have hc := hs.get j.val hlt'
      rw [strS_drop s j.val hlt'] at hT
      by_cases hw : isUnicodeWhiteSpace (chOf (s.val[j.val]'hlt')) = true
      · right
        obtain ⟨j1, hj1, hv⟩ := usize_add_one j (by omega)
        refine ⟨j1, by simp [net.parse.parse_symbol_loop0.body, hlt, index_eq s j hlt',
          net.parse.is_unicode_white_space_refines _ hc, hw, hj1], ⟨by omega, ?_⟩, by omega⟩
        rw [hv]; simpa [dropWhile, hw] using hT
      · left
        refine ⟨j, by simp [net.parse.parse_symbol_loop0.body, hlt, index_eq s j hlt',
          net.parse.is_unicode_white_space_refines _ hc, hw], hjl, ?_⟩
        rw [strS_drop s j.val hlt']; simpa [dropWhile, hw] using hT
    · left
      have : s.val.length ≤ j.val := by
        have : ¬ j.val < s.val.length := by simpa using hlt
        omega
      refine ⟨j, by simp [net.parse.parse_symbol_loop0.body, hlt], hjl, ?_⟩
      rw [drop_nil_of_ge s j.val this] at hT ⊢; simpa [dropWhile] using hT
  · exact ⟨by simp, by simp [T]⟩

theorem take_drop_succ (l : List Char) (lo k : Nat) (h : lo + k < l.length) :
    (l.drop lo).take (k + 1) = (l.drop lo).take k ++ [l[lo + k]'h] := by
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h]; rfl

theorem ps_loop1_spec (s : Slice U32) (hs : ValidStr s) (lo : Usize) (hlo : lo.val ≤ s.val.length) :
    ∃ hi, net.parse.parse_symbol_loop1 s lo (Slice.len s) = ok hi ∧ lo.val ≤ hi.val ∧ hi.val ≤ s.val.length ∧
      ((strS s).drop lo.val).take (hi.val - lo.val) =
        (dropWhile isUnicodeWhiteSpace ((strS s).drop lo.val).reverse).reverse := by
  let T := (dropWhile isUnicodeWhiteSpace ((strS s).drop lo.val).reverse).reverse
  unfold net.parse.parse_symbol_loop1
  apply loop_ok _ (fun j => j.val)
    (fun j => lo.val ≤ j.val ∧ j.val ≤ s.val.length ∧
      (dropWhile isUnicodeWhiteSpace (((strS s).drop lo.val).take (j.val - lo.val)).reverse).reverse = T)
  · rintro j ⟨hlj, hjl, hT⟩
    by_cases hgt : j > lo
    · have hgt' : lo.val < j.val := hgt
      obtain ⟨j1, hj1, hj1v, _⟩ := eq_ok_of_spec (Usize.sub_spec (x := j) (y := 1#usize) (by simp; omega))
      simp at hj1v
      have hj1l : j1.val < s.val.length := by omega
      have hc := hs.get j1.val hj1l
      have htk := take_drop_succ (strS s) lo.val (j1.val - lo.val) (by simp [strS_length]; omega)
      have e1 : j.val - lo.val = (j1.val - lo.val) + 1 := by omega
      have e2 : lo.val + (j1.val - lo.val) = j1.val := by omega
      rw [e1, htk] at hT
      have hget : (strS s)[lo.val + (j1.val - lo.val)]'(by simp [strS_length]; omega) = chOf (s.val[j1.val]'hj1l) := by
        simp [strS, e2]
      rw [hget] at hT
      by_cases hw : isUnicodeWhiteSpace (chOf (s.val[j1.val]'hj1l)) = true
      · right
        refine ⟨j1, by simp [net.parse.parse_symbol_loop1.body, hgt, hj1, index_eq s j1 hj1l,
          net.parse.is_unicode_white_space_refines _ hc, hw], ⟨by omega, by omega, ?_⟩, by omega⟩
        simpa [dropWhile, hw] using hT
      · left
        refine ⟨j, by simp [net.parse.parse_symbol_loop1.body, hgt, hj1, index_eq s j1 hj1l,
          net.parse.is_unicode_white_space_refines _ hc, hw], hlj, hjl, ?_⟩
        rw [e1, htk, hget]; simpa [dropWhile, hw] using hT
    · left
      have : j.val = lo.val := by have : ¬ lo.val < j.val := hgt; omega
      refine ⟨j, by simp [net.parse.parse_symbol_loop1.body, hgt], hlj, hjl, ?_⟩
      rw [this, Nat.sub_self] at hT ⊢; rw [List.take_zero]; simp [dropWhile] at hT; exact hT.symm
  · refine ⟨hlo, by simp, ?_⟩
    have : ((strS s).drop lo.val).take ((Slice.len s).val - lo.val) = (strS s).drop lo.val := by
      apply List.take_of_length_le; simp [strS_length]
    rw [this]

theorem lit_inf : litS (Std.Array.to_slice (Std.Array.make 8#usize [73#u8, 110#u8, 102#u8, 105#u8, 110#u8, 105#u8, 116#u8, 121#u8])) = "Infinity".toList := by
  simp [litS, Std.Array.to_slice, Std.Array.make]
theorem lit_minf : litS (Std.Array.to_slice (Std.Array.make 9#usize [45#u8, 73#u8, 110#u8, 102#u8, 105#u8, 110#u8, 105#u8, 116#u8, 121#u8])) = '-' :: "Infinity".toList := by
  simp [litS, Std.Array.to_slice, Std.Array.make]
theorem lit_nan : litS (Std.Array.to_slice (Std.Array.make 3#usize [78#u8, 97#u8, 78#u8])) = "NaN".toList := by
  simp [litS, Std.Array.to_slice, Std.Array.make]

theorem net.parse.parse_symbol_refines (s : Slice U32) (hs : ValidStr s) :
    net.parse.parse_symbol s = ok (parseSymbol (strS s)) := by
  obtain ⟨lo, hlo, hlol, hlov⟩ := ps_loop0_spec s hs
  obtain ⟨hi, hhi, hlh, hhil, hhiv⟩ := ps_loop1_spec s hs lo hlol
  have eqc := fun lit => net.parse.eq_ignore_case_refines s hs lo hi hlh hhil lit
  unfold net.parse.parse_symbol parseSymbol
  simp only [hlo, hhi, bind_ok, lift, eqc, lit_inf, lit_minf, lit_nan]
  rw [← hlov, ← hhiv]
  generalize ht : ((strS s).drop lo.val).take (hi.val - lo.val) = t
  by_cases h1 : eqIgnoreCase t "Infinity".toList = true
  · simp only [h1, ite_true]
  by_cases h2 : eqIgnoreCase t ('-' :: "Infinity".toList) = true
  · simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]
  by_cases h3 : eqIgnoreCase t "NaN".toList = true
  · simp only [h1, h2, h3, ite_true, Bool.false_eq_true, ite_false]
  simp only [h1, h2, h3, Bool.false_eq_true, ite_false]
  by_cases hlt : lo < hi
  · have hlt' : lo.val < hi.val := hlt
    have hl := Slice.length_ineq s
    have hlos : lo.val < s.val.length := by omega
    have hc := hs.get lo.val hlos
    obtain ⟨l1, hl1, hl1v⟩ := usize_add_one lo (by omega)
    have eqc1 := fun lit => net.parse.eq_ignore_case_refines s hs l1 hi (by omega) hhil lit
    have htc : t = chOf (s.val[lo.val]'hlos) :: ((strS s).drop l1.val).take (hi.val - l1.val) := by
      rw [← ht, strS_drop s lo.val hlos, hl1v]
      have : hi.val - lo.val = (hi.val - (lo.val + 1)) + 1 := by omega
      rw [this, List.take_succ_cons]
    rw [htc]
    simp only [hlt, ite_true, index_eq s lo hlos, bind_ok, hl1, eqc1, lift, lit_inf, lit_nan]
    by_cases hp : (s.val[lo.val]'hlos).val = 43
    · have hp' : (s.val[lo.val]'hlos) = 43#u32 := by rw [u32_eq_val]; simp [hp]
      have hpc : chOf (s.val[lo.val]'hlos) = '+' := (chOf_eq_iff _ hc _).mpr (by simp [hp])
      simp only [hp', ite_true, hpc]
      split <;> (try simp_all) <;> (split <;> simp_all)
    · have hp' : ¬ (s.val[lo.val]'hlos) = 43#u32 := by rw [u32_eq_val]; simpa using hp
      by_cases hm : (s.val[lo.val]'hlos).val = 45
      · have hm' : (s.val[lo.val]'hlos) = 45#u32 := by rw [u32_eq_val]; simp [hm]
        have hmc : chOf (s.val[lo.val]'hlos) = '-' := (chOf_eq_iff _ hc _).mpr (by simp [hm])
        simp only [hp', hm', ite_true, ite_false, hmc, hlt]
        split <;> (try simp_all) <;> (split <;> simp_all)
      · have hm' : ¬ (s.val[lo.val]'hlos) = 45#u32 := by rw [u32_eq_val]; simpa using hm
        have h1c : chOf (s.val[lo.val]'hlos) ≠ '+' := fun e => hp (by rw [(chOf_eq_iff _ hc _).mp e]; rfl)
        have h2c : chOf (s.val[lo.val]'hlos) ≠ '-' := fun e => hm (by rw [(chOf_eq_iff _ hc _).mp e]; rfl)
        simp only [hp', hm', ite_false, hlt, ite_true]
        split <;> (try simp_all) <;> (split <;> simp_all)
  · have : hi.val = lo.val := by have : ¬ lo.val < hi.val := hlt; omega
    have ht0 : t = [] := by rw [← ht, this, Nat.sub_self, List.take_zero]
    simp [hlt, ht0]

@[simp] theorem basic_F64_NAN : net.basic.F64_NAN = ok (F64.ofBitsN Fmt.f64.encNaN) := by
  simp [net.basic.F64_NAN, F64.ofBitsN]; decide
@[simp] theorem basic_F32_NAN : net.basic.F32_NAN = ok (F32.ofBitsN Fmt.f32.encNaN) := by
  simp [net.basic.F32_NAN, F32.ofBitsN]; decide

theorem net.parse.double_parse_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62) :
    net.parse.double_parse s = ok (exceptI id (doubleParseChars (strS s))) := by
  obtain ⟨r, hr, hrel⟩ := net.parse.parse_number_refines s hs hsz
  unfold net.parse.double_parse doubleParseChars parseFloatBits
  rw [hr, bind_ok]
  cases r with
  | none =>
    cases hn : parseNumber (strS s) with
    | some _ => simp [hn, optRelN] at hrel
    | none =>
      simp only [net.parse.parse_symbol_refines s hs, bind_ok]
      rcases parseSymbol (strS s) with _ | _ | neg
      · simp [exceptI, exnI]
      · simp [exceptI]
      · cases neg <;> simp [exceptI, f64_neg_inf]
  | some n =>
    cases hn : parseNumber (strS s) with
    | none => simp [hn, optRelN] at hrel
    | some n' =>
      simp [hn, optRelN] at hrel
      simp [net.parse.num_to_f64_refines n n' hrel, exceptI]

theorem net.parse.float_parse_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62) :
    net.parse.float_parse s = ok (exceptI id (floatParseChars (strS s))) := by
  obtain ⟨r, hr, hrel⟩ := net.parse.parse_number_refines s hs hsz
  unfold net.parse.float_parse floatParseChars parseFloatBits
  rw [hr, bind_ok]
  cases r with
  | none =>
    cases hn : parseNumber (strS s) with
    | some _ => simp [hn, optRelN] at hrel
    | none =>
      simp only [net.parse.parse_symbol_refines s hs, bind_ok]
      rcases parseSymbol (strS s) with _ | _ | neg
      · simp [exceptI, exnI]
      · simp [exceptI]
      · cases neg <;> simp [exceptI, f32_neg_inf]
  | some n =>
    cases hn : parseNumber (strS s) with
    | none => simp [hn, optRelN] at hrel
    | some n' =>
      simp [hn, optRelN] at hrel
      simp [net.parse.num_to_f32_refines n n' hrel, exceptI]

def CAP : Int := 2^40

theorem INT_CAP_eq : net.parse.INT_CAP = ok (⟨BitVec.ofNat 64 (2^40)⟩ : I64) := by
  unfold net.parse.INT_CAP; rfl

theorem INT_CAP_val : (⟨BitVec.ofNat 64 (2^40)⟩ : I64).val = CAP := by rfl

theorem pi_loop_spec (s : Slice U32) (hs : ValidStr s) (i2 : Usize) :
    ∃ i5 m, net.parse.parse_integer_value_loop s i2 0#i64 = ok (i5, m) ∧ 0 ≤ m.val ∧
      m.val = min ((digitsLoop ((strS s).drop i2.val) 0 0 false true).1 : Int) CAP ∧
      (strS s).drop i5.val = (digitsLoop ((strS s).drop i2.val) 0 0 false true).2.2.2 := by
  let T := digitsLoop ((strS s).drop i2.val) 0 0 false true
  have hl := Slice.length_ineq s
  unfold net.parse.parse_integer_value_loop
  obtain ⟨y, hy, hq⟩ := loop_ok (fun (x : Usize × I64) => net.parse.parse_integer_value_loop.body s x.1 x.2)
    (fun x => s.val.length - x.1.val)
    (fun x => 0 ≤ x.2.val ∧ x.2.val ≤ CAP ∧ ∃ (M : Nat) (nf : Nat) (seen : Bool), x.2.val = min (M : Int) CAP ∧
      digitsLoop ((strS s).drop x.1.val) M nf seen true = T)
    (fun y => 0 ≤ y.2.val ∧ y.2.val = min (T.1 : Int) CAP ∧ (strS s).drop y.1.val = T.2.2.2)
    (by
      rintro ⟨i, m⟩ ⟨hm0, hmc, M, nf, seen, hM, hT⟩
      dsimp only at hm0 hmc hM hT ⊢
      by_cases hlt : i < Slice.len s
      · have hlt' : i.val < s.val.length := by simpa using hlt
        have hc := hs.get i.val hlt'
        rw [strS_drop s i.val hlt'] at hT
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
        have hidx := index_eq s i hlt'
        generalize hu : s.val[i.val]'hlt' = u at hc hT hidx
        by_cases hd : isDigit (chOf u) = true
        · right
          have hdv : 48 ≤ u.val ∧ u.val ≤ 57 := by rw [isDigit_chOf _ hc] at hd; simpa using hd
          have hcap : CAP = 1099511627776 := rfl
          obtain ⟨m10, hm10, hm10v⟩ := eq_ok_of_spec (I64.mul_spec (x := m) (y := 10#i64)
            (by simp [I64.min_eq]; omega) (by simp [I64.max_eq]; omega))
          obtain ⟨d, hd', hdv', _⟩ := eq_ok_of_spec (U32.sub_spec (x := u) (y := 48#u32) (by simp; omega))
          have hcd : (UScalar.hcast .I64 d).val = (d.val : Int) := by
            rw [UScalar.hcast_val_eq]
            have hb : d.val < 2^32 := by have := d.hBounds; simpa using this
            exact Int.bmod_eq_of_le (by simp) (by simp; omega)
          simp at hm10v hdv'
          obtain ⟨m1, hm1, hm1v⟩ := eq_ok_of_spec (I64.add_spec (x := m10) (y := UScalar.hcast .I64 d)
            (by rw [hcd, hm10v]; simp [I64.min_eq]; omega) (by rw [hcd, hm10v]; simp [I64.max_eq]; omega))
          rw [hcd, hm10v] at hm1v
          let m2 : I64 := if m1 > (⟨BitVec.ofNat 64 (2^40)⟩ : I64) then ⟨BitVec.ofNat 64 (2^40)⟩ else m1
          have hm2v : m2.val = min (m1.val) CAP := by
            simp only [m2]; split
            · rename_i h; have : CAP < m1.val := by have := INT_CAP_val; rw [← this]; exact h
              rw [INT_CAP_val]; omega
            · rename_i h; have : ¬ CAP < m1.val := by have := INT_CAP_val; rw [← this]; exact h
              omega
          refine ⟨(i1, m2), ?_, ⟨?_, ?_, M * 10 + digitVal (chOf u), if true then nf + 1 else nf, true, ?_, ?_⟩, ?_⟩
          · simp [net.parse.parse_integer_value_loop.body, hlt, hidx, net.parse.is_digit_refines _ hc, hd,
              hm10, hd', lift, hm1, INT_CAP_eq, hi1, m2]
          · dsimp only; rw [hm2v]; omega
          · dsimp only; rw [hm2v]; omega
          · dsimp only; rw [hm2v, hm1v, digitVal_chOf _ hc, hM]; omega
          · dsimp only; rw [hi1v, ← hT]; simp [digitsLoop, hd]
          · dsimp only; omega
        · left
          refine ⟨(i, m), by simp [net.parse.parse_integer_value_loop.body, hlt, hidx, net.parse.is_digit_refines _ hc, hd],
            hm0, ?_, ?_⟩
          · rw [← hT]; simpa [digitsLoop, hd] using hM
          · rw [← hT, strS_drop s i.val hlt', hu]; simp [digitsLoop, hd]
      · left
        have : s.val.length ≤ i.val := by have : ¬ i.val < s.val.length := by simpa using hlt
                                          omega
        refine ⟨(i, m), by simp [net.parse.parse_integer_value_loop.body, hlt], hm0, ?_, ?_⟩
        · rw [← hT, drop_nil_of_ge s i.val this]; simpa [digitsLoop] using hM
        · rw [← hT, drop_nil_of_ge s i.val this]; simp [digitsLoop])
    (i2, 0#i64) ⟨by simp, by simp [CAP], 0, 0, false, by simp [CAP], rfl⟩
  obtain ⟨i5, m⟩ := y
  exact ⟨i5, m, hy, hq⟩

def parseIntegerValue' (l : List Char) : Option Int :=
  let s := dropWhile isWhite l
  let (neg, s) := signSplit s
  match s with
  | d :: _ =>
    if !isDigit d then none else
    let (m, _, _, rest) := digitsLoop s 0 0 false true
    let rest := dropWhile isWhite rest
    if !allNul rest then none else
    some (if neg then -(m : Int) else m)
  | [] => none

theorem parseIntegerValue_eq (l : List Char) : parseIntegerValue l = parseIntegerValue' l := by
  unfold parseIntegerValue parseIntegerValue'
  generalize dropWhile isWhite l = t
  rcases t with _ | ⟨x, r⟩
  · rfl
  · by_cases hp : x = '+'
    · subst hp; rfl
    · by_cases hm : x = '-'
      · subst hm; rfl
      · simp only [signSplit]; split <;> simp_all

theorem parse_integer_value_eq (s : Slice U32) : net.parse.parse_integer_value s = (do
    let i ← net.parse.skip_white s 0#usize
    let (i2, neg) ← peSignImpl s i
    if i2 < Slice.len s then
      let i4 ← Slice.index_usize s i2
      let b ← net.parse.is_digit i4
      if b then
        let (i5, m) ← net.parse.parse_integer_value_loop s i2 0#i64
        let k ← net.parse.skip_white s i5
        let b1 ← net.parse.all_nul s k
        if b1 then if neg then let m1 ← -. m; ok (some m1) else ok (some m)
        else ok none
      else ok none
    else ok none) := by
  rfl

def capRel : Option I64 → Option Int → Prop
  | none, none => True
  | some v, some w => v.val = (if 0 ≤ w then min w CAP else max w (-CAP))
  | _, _ => False

theorem net.parse.parse_integer_value_refines (s : Slice U32) (hs : ValidStr s) :
    ∃ r, net.parse.parse_integer_value s = ok r ∧ capRel r (parseIntegerValue (strS s)) := by
  rw [parse_integer_value_eq, parseIntegerValue_eq]
  unfold parseIntegerValue'
  obtain ⟨j0, hj0, -, hj0l, hj0v⟩ := skip_white_le s hs 0#usize (by simp)
  simp only [show ((0#usize : Usize).val) = 0 from rfl, List.drop_zero] at hj0v
  obtain ⟨i2, neg, hsg, hi2l, hsgv⟩ := pe_sign_spec s hs j0 hj0l
  rw [hj0, bind_ok, hsg, bind_ok]
  rw [← hj0v]
  dsimp only
  rw [hsgv]
  dsimp only
  have hl := Slice.length_ineq s
  by_cases hlt : i2 < Slice.len s
  · have hlt' : i2.val < s.val.length := by simpa using hlt
    have hc := hs.get i2.val hlt'
    rw [strS_drop s i2.val hlt']
    by_cases hd : isDigit (chOf (s.val[i2.val]'hlt')) = true
    · obtain ⟨i5, m, hlp, hm0, hmv, hrest⟩ := pi_loop_spec s hs i2
      rw [strS_drop s i2.val hlt'] at hmv hrest
      obtain ⟨k, hk, -, -, hkv⟩ := net.parse.skip_white_refines s hs i5
      simp only [hd, Bool.not_true, Bool.false_eq_true, ite_false]
      generalize hT : digitsLoop (chOf (s.val[i2.val]'hlt') :: (strS s).drop (i2.val + 1)) 0 0 false true = T at hmv hrest
      obtain ⟨M, nf', seen', rest⟩ := T
      simp only at hmv hrest ⊢
      rw [← hrest, ← hkv]
      cases han : allNul ((strS s).drop k.val)
      · exact ⟨none, by simp [hlt, hlt', index_eq s i2 hlt', net.parse.is_digit_refines _ hc, hd, hlp, hk,
          net.parse.all_nul_refines s hs k, han], by simp [capRel]⟩
      · cases neg
        · exact ⟨some m, by simp [hlt, hlt', index_eq s i2 hlt', net.parse.is_digit_refines _ hc, hd, hlp, hk,
            net.parse.all_nul_refines s hs k, han], by simp [capRel, hmv]⟩
        · have hb := m.hmax
          obtain ⟨q, hq, hqv⟩ := eq_ok_of_spec (IScalar.neg_step m (by simp [IScalar.min, I64.min_eq]; omega))
          refine ⟨some q, by simp [hlt, hlt', index_eq s i2 hlt', net.parse.is_digit_refines _ hc, hd, hlp, hk,
            net.parse.all_nul_refines s hs k, han, HNeg.hNeg, hq], ?_⟩
          simp only [capRel, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          rw [hqv, hmv]
          by_cases hM : M = 0
          · subst hM; simp [CAP]
          · have h0 : ¬ (0 ≤ -(M : Int)) := by omega
            rw [ite_eq_right_iff.mpr (fun h => absurd h h0)]; unfold CAP; omega
    · exact ⟨none, by simp [hlt, hlt', index_eq s i2 hlt', net.parse.is_digit_refines _ hc, hd], by simp [hd, capRel]⟩
  · have hge : s.val.length ≤ i2.val := by have : ¬ i2.val < s.val.length := by simpa using hlt
                                           omega
    have hn : ¬ (i2.val < s.val.length) := by omega
    exact ⟨none, by simp [hlt, hn], by rw [drop_nil_of_ge s i2.val hge]; simp [capRel]⟩

theorem net.parse.int_parse_refines (s : Slice U32) (hs : ValidStr s) :
    net.parse.int_parse s = ok (exceptI i32I (intParseChars (strS s))) := by
  obtain ⟨r, hr, hrel⟩ := net.parse.parse_integer_value_refines s hs
  unfold net.parse.int_parse intParseChars
  rw [hr, bind_ok]
  cases r with
  | none =>
    cases hn : parseIntegerValue (strS s) with
    | some _ => simp [hn, capRel] at hrel
    | none => simp [exceptI, exnI]
  | some v =>
    cases hn : parseIntegerValue (strS s) with
    | none => simp [hn, capRel] at hrel
    | some w =>
      simp only [hn, capRel] at hrel
      have hcap : CAP = 1099511627776 := rfl
      have hlo : v < (-2147483648)#i64 ↔ w < -2^31 := by
        show v.val < -2147483648 ↔ _
        rw [hrel]; split <;> omega
      have hhi : v > 2147483647#i64 ↔ w > 2^31 - 1 := by
        show 2147483647 < v.val ↔ _
        rw [hrel]; split <;> omega
      by_cases h1 : w < -2^31
      · have : w < -2147483648 ∨ 2147483647 < w := by omega
        simp [hlo.mpr h1, this, exceptI, exnI]
      · by_cases h2 : w > 2^31 - 1
        · have : w < -2147483648 ∨ 2147483647 < w := by omega
          simp [(hlo.not).mpr h1, hhi.mpr h2, this, exceptI, exnI]
        · have hv : v.val = w := by rw [hrel]; split <;> omega
          simp only [(hlo.not).mpr h1, (hhi.not).mpr h2, ite_false, lift, bind_ok, exceptI]
          have : ¬ (decide (w < -2^31) || decide (w > 2^31 - 1)) = true := by simp; omega
          simp only [this, ite_false, Bool.false_eq_true]
          congr 2
          apply IScalar.eq_of_val_eq
          rw [IScalar.cast_val_eq, hv]
          show _ = (Int32.ofInt w).toBitVec.toInt
          rw [← Int32.toInt, Int32.toInt_ofInt]
          rfl

theorem toList_ofList (l : List Char) : (String.ofList l).toList = l := by simp

theorem net.parse.parsing_parse_double_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62)
    (lim : F64) (an : Bool) :
    net.parse.parsing_parse_double s lim an = ok (exceptI id (Parsing.parseDouble (String.ofList (strS s)) lim an)) := by
  unfold net.parse.parsing_parse_double Parsing.parseDouble doubleParse
  rw [net.parse.double_parse_refines s hs hsz, bind_ok, toList_ofList]
  cases doubleParseChars (strS s) with
  | error e => simp [exceptI]
  | ok v =>
    by_cases h1 : v < -lim <;> by_cases h2 : lim < v <;> by_cases h3 : v.isNaN = true <;> cases an <;>
      simp [exceptI, exnI, h1, h2, h3]

theorem net.parse.parsing_parse_float_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62)
    (lim : F32) (an : Bool) :
    net.parse.parsing_parse_float s lim an = ok (exceptI id (Parsing.parseFloat (String.ofList (strS s)) lim an)) := by
  unfold net.parse.parsing_parse_float Parsing.parseFloat floatParse
  rw [net.parse.float_parse_refines s hs hsz, bind_ok, toList_ofList]
  cases floatParseChars (strS s) with
  | error e => simp [exceptI]
  | ok v =>
    by_cases h1 : v < -lim <;> by_cases h2 : lim < v <;> by_cases h3 : v.isNaN = true <;> cases an <;>
      simp [exceptI, exnI, h1, h2, h3]

theorem net.parse.parsing_parse_int_refines (s : Slice U32) (hs : ValidStr s) (lim : I32) :
    net.parse.parsing_parse_int s lim = ok (exceptI i32I (Parsing.parseInt (String.ofList (strS s)) (i32S lim))) := by
  unfold net.parse.parsing_parse_int Parsing.parseInt intParse
  rw [net.parse.int_parse_refines s hs, bind_ok, toList_ofList]
  cases intParseChars (strS s) with
  | error e => simp [exceptI]
  | ok v =>
    have hneg : (core.num.I32.wrapping_sub 0#i32 lim).val = (-(i32S lim)).toInt := by
      rw [core.num.I32.wrapping_sub_val_eq, Int32.toInt_neg, i32S_toInt]
      simp
    have h1 : (i32I v < core.num.I32.wrapping_sub 0#i32 lim) ↔ v < -(i32S lim) := by
      rw [Int32.lt_iff_toInt_lt, ← hneg]; rfl
    have h2 : (i32I v > lim) ↔ v > i32S lim := by
      rw [gt_iff_lt, gt_iff_lt, Int32.lt_iff_toInt_lt, i32S_toInt]; rfl
    have h1' := h1; have h2' := h2
    simp only [gt_iff_lt] at h2'
    simp at h1' h2'
    by_cases c1 : v < -(i32S lim) <;> by_cases c2 : v > i32S lim <;>
      simp [exceptI, exnI, lift, h1', h2', c1, c2]

@[simp] theorem parse_MAX_PARSE_VALUE : net.parse.MAX_PARSE_VALUE = ok Parsing.MAX_PARSE_VALUE := by
  simp [net.parse.MAX_PARSE_VALUE, Parsing.MAX_PARSE_VALUE] <;> decide
@[simp] theorem parse_MAX_PARSE_VALUE_F32 : net.parse.MAX_PARSE_VALUE_F32 = ok Parsing.MAX_PARSE_VALUE.toF32 := by
  simp [net.parse.MAX_PARSE_VALUE_F32, Parsing.MAX_PARSE_VALUE] <;> decide

/-- `Parsing.ParseDouble(input)` (default limit and `allowNaN = false`). -/
theorem net.parse.parse_double_default_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62) :
    net.parse.parse_double_default s = ok (exceptI id (Parsing.parseDouble (String.ofList (strS s)))) := by
  simp [net.parse.parse_double_default, net.parse.parsing_parse_double_refines s hs hsz]
theorem net.parse.parse_float_default_refines (s : Slice U32) (hs : ValidStr s) (hsz : s.val.length < 2^62) :
    net.parse.parse_float_default s = ok (exceptI id (Parsing.parseFloat (String.ofList (strS s)))) := by
  simp [net.parse.parse_float_default, net.parse.parsing_parse_float_refines s hs hsz]
theorem net.parse.parse_int_default_refines (s : Slice U32) (hs : ValidStr s) :
    net.parse.parse_int_default s = ok (exceptI i32I (Parsing.parseInt (String.ofList (strS s)))) := by
  simp [net.parse.parse_int_default, net.parse.parsing_parse_int_refines s hs]; rfl

end OsuProofs
