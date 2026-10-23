/-
`eval/osr.rs` refines `OsuModel.Replay.Osr` (`RdM` readers and the container): read_le, read_byte, read_int32,
read_int64, read_uint16, read_boolean, read_bytes, read_byte_array, read_date_time, read7bit_loop /
read7bit_encoded_int, read_string, read_header, read_body, skip_online_id, read_container, ...
Relation: reader position `p` and input slice `b` correspond to spec state `p` over `bytesS b` (`ev_rRel`).
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Eval.Adapter
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
open OsuModel.Replay.Osr
theorem ev_rd_read {α} (f : ByteArray → RdM α) (B : ByteArray) (p : Nat) : (readThe ByteArray >>= f) B p = f B B p := rfl
theorem ev_rd_get {α} (f : Nat → RdM α) (B : ByteArray) (p : Nat) :
    ((liftM (StateT.get : StateT Nat (Except String) Nat) : RdM Nat) >>= f) B p = f p B p := rfl
theorem ev_rd_set_map {α} (g : PUnit → α) (B : ByteArray) (p q : Nat) : (g <$> (set q : RdM PUnit)) B p = .ok (g ⟨⟩, q) := rfl
theorem ev_rd_throw {α} (m : String) (B : ByteArray) (p : Nat) : (throw m : RdM α) B p = .error m := rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

/-- little-endian value of `n` bytes at `p` -/
def ev_le (B : List UInt8) (p n : Nat) : Nat := (List.range' 0 n).foldl (fun s i => s + (B.getD (p + i) 0).toNat <<< (8 * i)) 0

theorem ev_ba_getElem (B : ByteArray) (i : Nat) (hi : i < B.size) : B[i] = B.data.toList.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, ByteArray.getElem_eq_getElem_data, hi]

theorem ev_readLE_spec (B : ByteArray) (p n : Nat) : ((readLE n).run B).run p =
    if p + n ≤ B.size then .ok (ev_le B.data.toList p n, p + n)
    else .error "EndOfStreamException: Unable to read beyond the end of the stream." := by
  unfold readLE
  simp only [ReaderT.run, StateT.run]
  simp only [read, MonadReader.read, ev_rd_read, get, getThe, MonadStateOf.get, ev_rd_get]
  by_cases h : p + n ≤ B.size
  · simp only [dif_pos h, if_pos h, Std.Legacy.Range.forIn'_eq_forIn'_range']
    simp
    rw [ev_rd_set_map]
    simp only [ev_ba_getElem, ev_le]
    congr 2
    exact List.foldl_attach (l := List.range' 0 n) (f := fun b x => b + (B.data.toList.getD (p + x) 0).toNat <<< (8 * x)) (b := 0)
  · simp only [h, dif_neg h, if_neg h]; rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

/-- a reader result: same value and position, or both errors -/
def ev_rRel {α β} (f : α → β) : core.result.Result (α × Usize) eval.osr.OsrErr → Except String (β × Nat) → Prop
  | .Ok (a, q), .ok (b, n) => f a = b ∧ n = q.val
  | .Err _, .error _ => True
  | _, _ => False

theorem ev_bytesS_getD (b : Slice U8) (i : Nat) (h : i < b.val.length) :
    ((bytesS b).data.toList.getD i 0).toNat = (b.val[i]'h).val := by
  simp [bytesS, List.getElem?_eq_getElem h, UInt8.toNat_ofBitVec]

theorem ev_le_succ (B : List UInt8) (p i : Nat) :
    ev_le B p (i + 1) = ev_le B p i + (B.getD (p + i) 0).toNat <<< (8 * i) := by
  simp [ev_le, List.range'_concat, List.foldl_append]

theorem ev_le_lt (B : List UInt8) (p : Nat) : ∀ i, ev_le B p i < 2 ^ (8 * i) := by
  intro i
  induction i with
  | zero => simp [ev_le]
  | succ i ih =>
    rw [ev_le_succ]
    have hb : (B.getD (p + i) 0).toNat < 2^8 := UInt8.toNat_lt _
    rw [Nat.shiftLeft_eq]
    have : 2 ^ (8 * (i + 1)) = 2^(8*i) * 2^8 := by rw [← Nat.pow_add]; ring_nf
    rw [this]
    calc ev_le B p i + (B.getD (p + i) 0).toNat * 2 ^ (8 * i) < 2^(8*i) + (B.getD (p + i) 0).toNat * 2 ^ (8 * i) := by omega
      _ = 2^(8*i) * (1 + (B.getD (p + i) 0).toNat) := by ring
      _ ≤ 2^(8*i) * 2^8 := Nat.mul_le_mul_left _ (by omega)
end OsuProofs
namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem eval.osr.read_le_refines (b : Slice U8) (p n : Usize) (hn : n.val ≤ 8)
    (hp : p.val + n.val ≤ Usize.max) :
    ∃ r, eval.osr.read_le b p n = ok r ∧ ev_rRel (·.val) r (((readLE n.val).run (bytesS b)).run p.val) := by
  rw [ev_readLE_spec]
  have hsz := bytesS_size b
  obtain ⟨e, he, hev⟩ := ev_usize_add p n hp
  unfold eval.osr.read_le
  by_cases hle : p.val + n.val ≤ b.val.length
  · have hle' : e ≤ Slice.len b := by simp [UScalar.le_equiv, hev]; omega
    let BL := (bytesS b).data.toList
    obtain ⟨v, hv, hvv⟩ := loop_ok (fun (x : U64 × Usize) => eval.osr.read_le_loop.body b p n x.1 x.2)
      (fun x => n.val - x.2.val)
      (fun x => x.2.val ≤ n.val ∧ x.1.val = ev_le BL p.val x.2.val)
      (fun v => v.val = ev_le BL p.val n.val)
      (by
        rintro ⟨v, i⟩ ⟨hi, hv⟩
        dsimp only at hi hv ⊢
        by_cases hin : i.val < n.val
        · right
          obtain ⟨pi, hpi, hpiv⟩ := ev_usize_add p i (by omega)
          have hpl : pi.val < b.val.length := by omega
          obtain ⟨s8, hs8, hs8v⟩ := eq_ok_of_spec (Usize.mul_spec (x := 8#usize) (y := i) (by simp; scalar_tac))
          obtain ⟨sh, hsh, hshv, -⟩ := eq_ok_of_spec (U64.ShiftLeft_spec (UScalar.cast .U64 (b.val[pi.val]'hpl)) s8
            (by simp at hs8v; simp [hs8v]; omega))
          obtain ⟨i1, hi1, hi1v⟩ := usize_add_one i (by omega)
          have hbyte : (b.val[pi.val]'hpl).val < 2^8 := by have := (b.val[pi.val]'hpl).hBounds; simpa using this
          refine ⟨(v ||| sh, i1), ?_, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
          · simp [eval.osr.read_le_loop.body, (show i < n by scalar_tac), hpi, slice_index_ok b pi hpl, lift, hs8, hsh, hi1]
          · dsimp only
            rw [UScalar.val_or, hshv, hi1v, ev_le_succ, ← hv]
            simp at hs8v
            have hgd : (BL.getD (p.val + i.val) 0).toNat = (b.val[pi.val]'hpl).val := by
              simp only [BL]; rw [← hpiv]; exact ev_bytesS_getD b pi.val hpl
            rw [hgd, hs8v]
            have hlt : (b.val[pi.val]'hpl).val <<< (8 * i.val) < 2^64 := by
              rw [Nat.shiftLeft_eq]
              calc (b.val[pi.val]'hpl).val * 2 ^ (8 * i.val) < 2^8 * 2^(8 * i.val) := Nat.mul_lt_mul_of_pos_right hbyte (by positivity)
                _ = 2^(8 + 8 * i.val) := by rw [Nat.pow_add]
                _ ≤ 2^64 := Nat.pow_le_pow_right (by omega) (by omega)
            simp only [U8.cast_U64_val_eq]
            rw [Nat.mod_eq_of_lt (by simpa [U64.size, U64.numBits] using hlt)]
            have hvlt : v.val < 2^(8*i.val) := by rw [hv]; exact ev_le_lt BL p.val i.val
            rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hvlt, Nat.add_comm]
        · left
          refine ⟨v, by simp [eval.osr.read_le_loop.body, (show ¬ i < n by scalar_tac)], ?_⟩
          rw [hv]; congr 1; omega)
      (0#u64, 0#usize) ⟨by simp, by simp [ev_le]⟩
    refine ⟨.Ok (v, e), ?_, ?_⟩
    · simp only [hle', if_true, he, bind_ok]
      rw [show eval.osr.read_le_loop b p n 0#u64 0#usize = _ from hv]; simp [he]
    · rw [if_pos (by omega)]; exact ⟨hvv, by omega⟩
  · have hle' : ¬ e ≤ Slice.len b := by simp [UScalar.le_equiv, hev]; omega
    refine ⟨.Err .Eos, by simp [he, hle', eq_false (show ¬ e.val ≤ b.val.length by omega)], ?_⟩
    rw [if_neg (by omega)]; trivial
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_rd_bind {α β} (x : RdM α) (f : α → RdM β) (B : ByteArray) (p : Nat) :
    (x >>= f) B p = (match x B p with | .ok (a, q) => f a B q | .error e => .error e) := by
  show (do let r ← x B p; f r.1 B r.2) = _
  cases x B p <;> rfl
theorem ev_rd_pure {α} (a : α) (B : ByteArray) (p : Nat) : (pure a : RdM α) B p = .ok (a, p) := rfl
theorem ev_rd_set_bind {α} (q : Nat) (f : PUnit → RdM α) (B : ByteArray) (p : Nat) :
    ((set q : RdM PUnit) >>= f) B p = f ⟨⟩ B q := rfl

theorem ev_readByte_spec (B : ByteArray) (p : Nat) : (readByte.run B).run p =
    if h : p < B.size then .ok (B[p], p + 1) else .error "EndOfStreamException: Unable to read beyond the end of the stream." := by
  unfold readByte
  simp only [ReaderT.run, StateT.run, read, MonadReader.read, ev_rd_read, get, getThe, MonadStateOf.get, ev_rd_get]
  split <;> rfl

theorem eval.osr.read_byte_refines (b : Slice U8) (p : Usize) (hp : p.val + 1 ≤ Usize.max) :
    ∃ r, eval.osr.read_byte b p = ok r ∧ ev_rRel (fun x : U8 => UInt8.ofBitVec x.bv) r ((readByte.run (bytesS b)).run p.val) := by
  rw [ev_readByte_spec]
  have hsz := bytesS_size b
  unfold eval.osr.read_byte
  by_cases h : p.val < b.val.length
  · obtain ⟨q, hq, hqv⟩ := usize_add_one p hp
    refine ⟨.Ok (b.val[p.val]'h, q), by simp [(slice_lt_len_iff p b).mpr h, slice_index_ok b p h, hq], ?_⟩
    rw [dif_pos (by omega)]
    exact ⟨by simp [bytesS, ByteArray.getElem_eq_getElem_data], by omega⟩
  · refine ⟨.Err .Eos, by simp [(show ¬ p < Slice.len b by rw [slice_lt_len_iff]; exact h)], ?_⟩
    rw [dif_neg (by omega)]; trivial
theorem ev_i32_of_u64 (v : U64) : i32S (UScalar.hcast .I32 (UScalar.cast .U32 v)) = Int32.ofNat v.val := by
  apply Int32.toBitVec_inj.mp
  simp only [i32S, UScalar.hcast, UScalar.cast, Int32.toBitVec_ofBitVec]
  show BitVec.zeroExtend 32 (BitVec.zeroExtend 32 v.bv) = BitVec.ofNat 32 v.val
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
  show v.bv.toNat % 2^32 % 2^32 = v.bv.toNat % 2^32
  rw [Nat.mod_mod]
theorem ev_i64_of_u64 (v : U64) : (Int64.ofBitVec (UScalar.hcast .I64 v).bv : Int64) = Int64.ofNat v.val := by
  apply Int64.toBitVec_inj.mp
  simp only [UScalar.hcast, Int64.toBitVec_ofBitVec]
  show BitVec.zeroExtend 64 v.bv = BitVec.ofNat 64 v.val
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
  show v.bv.toNat % 2^64 = v.bv.toNat % 2^64
  rfl

theorem eval.osr.read_int32_refines (b : Slice U8) (p : Usize) (hp : p.val + 4 ≤ Usize.max) :
    ∃ r, eval.osr.read_int32 b p = ok r ∧ ev_rRel i32S r ((readInt32.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_le_refines b p 4#usize (by simp) (by simpa using hp)
  unfold eval.osr.read_int32 readInt32
  simp only [ReaderT.run, StateT.run] at hrel ⊢
  rw [ev_rd_bind]
  rw [hr]; simp only [bind_ok]
  revert hrel
  simp only [show (4#usize).val = 4 by simp]
  cases r with
  | Ok vq =>
    obtain ⟨v, q⟩ := vq
    cases hL : readLE 4 (bytesS b) p.val with
    | error _ => intro h; exact h.elim
    | ok wn =>
      obtain ⟨w, n⟩ := wn
      intro h; obtain ⟨h1, h2⟩ := h
      refine ⟨.Ok (UScalar.hcast .I32 (UScalar.cast .U32 v), q), by simp [lift], ?_⟩
      simp only [ev_rd_pure]
      exact ⟨by rw [ev_i32_of_u64, ← h1], h2⟩
  | Err e =>
    cases hL : readLE 4 (bytesS b) p.val with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err e, rfl, trivial⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

def ev_i64S (x : I64) : Int64 := Int64.ofBitVec x.bv

theorem eval.osr.read_int64_refines (b : Slice U8) (p : Usize) (hp : p.val + 8 ≤ Usize.max) :
    ∃ r, eval.osr.read_int64 b p = ok r ∧ ev_rRel ev_i64S r ((readInt64.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_le_refines b p 8#usize (by simp) (by simpa using hp)
  unfold eval.osr.read_int64 readInt64
  simp only [ReaderT.run, StateT.run] at hrel ⊢
  rw [ev_rd_bind]
  rw [hr]; simp only [bind_ok]
  revert hrel
  simp only [show (8#usize).val = 8 by simp]
  cases r with
  | Ok vq =>
    obtain ⟨v, q⟩ := vq
    cases hL : readLE 8 (bytesS b) p.val with
    | error _ => intro h; exact h.elim
    | ok wn =>
      obtain ⟨w, n⟩ := wn
      intro h; obtain ⟨h1, h2⟩ := h
      refine ⟨.Ok (UScalar.hcast .I64 v, q), by simp [lift], ?_⟩
      simp only [ev_rd_pure]
      exact ⟨by simp only [ev_i64S]; rw [ev_i64_of_u64, ← h1], h2⟩
  | Err e =>
    cases hL : readLE 8 (bytesS b) p.val with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err e, rfl, trivial⟩

theorem eval.osr.read_uint16_refines (b : Slice U8) (p : Usize) (hp : p.val + 2 ≤ Usize.max) :
    ∃ r, eval.osr.read_uint16 b p = ok r ∧ ev_rRel (·.val) r ((readUInt16.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_le_refines b p 2#usize (by simp) (by simpa using hp)
  exact ⟨r, hr, by simpa [readUInt16] using hrel⟩

theorem eval.osr.read_boolean_refines (b : Slice U8) (p : Usize) (hp : p.val + 1 ≤ Usize.max) :
    ∃ r, eval.osr.read_boolean b p = ok r ∧ ev_rRel id r ((readBoolean.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_byte_refines b p hp
  unfold eval.osr.read_boolean readBoolean
  simp only [ReaderT.run, StateT.run] at hrel ⊢
  rw [ev_rd_bind]
  rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Ok vq =>
    obtain ⟨v, q⟩ := vq
    cases hL : readByte (bytesS b) p.val with
    | error _ => intro h; exact h.elim
    | ok wn =>
      obtain ⟨w, n⟩ := wn
      intro h; obtain ⟨h1, h2⟩ := h
      refine ⟨.Ok (v != 0#u8, q), by simp, ?_⟩
      simp only [ev_rd_pure]
      refine ⟨?_, h2⟩
      subst h1
      by_cases hv : v = 0#u8
      · subst hv; rfl
      · have : UInt8.ofBitVec v.bv ≠ 0 := by
          intro hh; apply hv; apply UScalar.eq_of_val_eq
          have := congrArg UInt8.toNat hh; simpa [UInt8.toNat_ofBitVec] using this
        rw [bne_iff_ne.mpr hv, bne_iff_ne.mpr this]; rfl
  | Err e =>
    cases hL : readByte (bytesS b) p.val with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err e, rfl, trivial⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_readBytes_spec (B : ByteArray) (p c : Nat) : ((readBytes c).run B).run p =
    .ok (B.extract p (p + min c (B.size - p)), p + min c (B.size - p)) := by
  unfold readBytes
  simp only [ReaderT.run, StateT.run, read, MonadReader.read, ev_rd_read, get, getThe, MonadStateOf.get, ev_rd_get,
    ev_rd_set_bind, ev_rd_pure]

theorem ev_bytesS_extract (b : Slice U8) (p n : Nat) :
    ((bytesS b).extract p (p + n)).data.toList = (((b.val.drop p).take n).map fun x => UInt8.ofBitVec x.bv) := by
  rw [ByteArray.data_extract]
  simp [bytesS, List.map_take, List.map_drop, Nat.add_sub_cancel_left]

theorem eval.osr.read_bytes_refines (b : Slice U8) (p count : Usize) (hp : p.val ≤ b.val.length) :
    ∃ v q, eval.osr.read_bytes b p count = ok (v, q) ∧
      ((readBytes count.val).run (bytesS b)).run p.val = .ok (bytesS (alloc.vec.Vec.deref v), q.val) := by
  have hsz := bytesS_size b
  have hmax := b.property
  rw [ev_readBytes_spec, hsz]
  let n := min count.val (b.val.length - p.val)
  have hav : ∃ av : Usize, (if p ≤ Slice.len b then Slice.len b - p else ok 0#usize) = ok av ∧ av.val = b.val.length - p.val := by
    have hle : p ≤ Slice.len b := by simp [UScalar.le_equiv]; omega
    obtain ⟨av, hav, hv, -⟩ := eq_ok_of_spec (Usize.sub_spec (x := Slice.len b) (y := p) (by simp; omega))
    exact ⟨av, by simp [hle, hav], by simp at hv; omega⟩
  obtain ⟨av, hav1, hav2⟩ := hav
  have hn : ∃ nn : Usize, (if count < av then ok count else ok av) = ok nn ∧ nn.val = n := by
    by_cases hc : count.val < av.val
    · exact ⟨count, by simp [UScalar.lt_equiv, hc], by simp [n]; omega⟩
    · exact ⟨av, by simp [UScalar.lt_equiv, hc], by simp [n]; omega⟩
  obtain ⟨nn, hnn1, hnn2⟩ := hn
  have hpn : p.val + nn.val ≤ b.val.length := by omega
  obtain ⟨q, hq, hqv⟩ := ev_usize_add p nn (by omega)
  obtain ⟨r, hr, hrv⟩ := ev_map_loop (fun x => eval.osr.read_bytes_loop.body b p nn x.1 x.2)
    ((b.val.drop p.val).take nn.val) id
    (by
      intro out i hi hl
      simp at hi
      obtain ⟨pi, hpi, hpiv⟩ := ev_usize_add p i (by omega)
      obtain ⟨i1, hi1, hiv⟩ := usize_add_one i (by omega)
      have hpl : pi.val < b.val.length := by omega
      refine ⟨vpush out (b.val[pi.val]'hpl) hl, i1, by simp [eval.osr.read_bytes_loop.body,
        (show i < nn by scalar_tac), hpi, slice_index_ok b pi hpl, vec_push_ok out _ hl, hi1], ?_, hiv⟩
      simp [hpiv])
    (by intro out i hi; simp at hi; simp [eval.osr.read_bytes_loop.body, (show ¬ i < nn by scalar_tac)])
    (alloc.vec.Vec.with_capacity _ nn) 0#usize (by simp) (by simp [alloc.vec.Vec.with_capacity]; omega)
  refine ⟨r, q, ?_, ?_⟩
  · unfold eval.osr.read_bytes
    simp only [hav1, bind_ok, hnn1]
    rw [show eval.osr.read_bytes_loop b p nn (alloc.vec.Vec.with_capacity U8 nn) 0#usize = ok r from hr]
    simp [hq]
  · refine congrArg Except.ok (Prod.ext ?_ ?_)
    · apply ByteArray.ext
      apply Array.toList_inj.mp
      show ((bytesS b).extract p.val (p.val + n)).data.toList = _
      rw [ev_bytesS_extract]
      simp [bytesS, hrv, alloc.vec.Vec.with_capacity, ← hnn2]
    · show p.val + n = q.val
      rw [hqv, hnn2]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_readInt32_pos (B : ByteArray) (p : Nat) (a : Int32) (q : Nat) (h : (readInt32.run B).run p = .ok (a, q)) :
    q ≤ B.size := by
  unfold readInt32 at h
  simp only [ReaderT.run, StateT.run, ev_rd_bind] at h
  have hl := ev_readLE_spec B p 4
  simp only [ReaderT.run, StateT.run] at hl
  rw [hl] at h
  split at h
  · rename_i hc; simp [ev_rd_pure] at h
    obtain ⟨-, rfl⟩ := h
    split at hc
    · simp at hc; omega
    · simp at hc
  · simp at h

theorem ev_i32S_pos (x : I32) : (i32S x > 0) ↔ 0 < x.val := by
  have := abs_i32S_lt_iff 0#i32 x; rw [ev_i32S_zero] at this; simpa using this
theorem ev_i32S_neg (x : I32) : (i32S x < 0) ↔ x.val < 0 := by
  have := abs_i32S_lt_iff x 0#i32; rw [ev_i32S_zero] at this; simpa using this

theorem eval.osr.read_byte_array_refines (b : Slice U8) (p : Usize) (hp : p.val + 4 ≤ Usize.max) :
    ∃ r, eval.osr.read_byte_array b p = ok r ∧
      ev_rRel (fun o : Option (alloc.vec.Vec U8) => o.map fun v => bytesS (alloc.vec.Vec.deref v)) r
        ((readByteArray.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_int32_refines b p hp
  unfold eval.osr.read_byte_array readByteArray
  simp only [ReaderT.run, StateT.run, ev_rd_bind] at hrel ⊢
  rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Err e =>
    cases hI : readInt32 (bytesS b) p.val with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err e, rfl, trivial⟩
  | Ok lq =>
    obtain ⟨len, q⟩ := lq
    cases hI : readInt32 (bytesS b) p.val with
    | error _ => intro h; exact h.elim
    | ok aq =>
      obtain ⟨a, n⟩ := aq
      intro h; obtain ⟨h1, h2⟩ := h
      subst h1 h2
      have hqs := ev_readInt32_pos (bytesS b) p.val _ _ hI
      rw [bytesS_size] at hqs
      by_cases hpos : 0 < len.val
      · have hc : (IScalar.hcast .Usize len).val = len.val.toNat := by
          simp [IScalar.hcast_val_eq]; have := len.hBounds
          have h2 : len.val < 2^31 := by simpa using this.2
          have hnb : (2:Int)^31 < (2:Int)^System.Platform.numBits := by
            cases System.Platform.numBits_eq <;> simp [*]
          rw [Int.emod_eq_of_lt (by omega) (by omega)]
        obtain ⟨v, q2, hv, hspec⟩ := eval.osr.read_bytes_refines b q (IScalar.hcast .Usize len) hqs
        refine ⟨.Ok (some v, q2), by simp [IScalar.lt_equiv, hpos, lift, hv], ?_⟩
        simp only [if_pos ((ev_i32S_pos len).mpr hpos), ev_rd_bind]
        rw [show (i32S len).toNatClampNeg = (IScalar.hcast .Usize len).val by
          rw [hc]; simp [Int32.toNatClampNeg, i32S_toInt]]
        simp only [ReaderT.run, StateT.run] at hspec
        rw [hspec]; exact ⟨rfl, rfl⟩
      · by_cases hneg : len.val < 0
        · refine ⟨.Ok (none, q), by simp [IScalar.lt_equiv, hpos, hneg], ?_⟩
          simp only [if_neg (fun hh => hpos ((ev_i32S_pos len).mp hh)), if_pos ((ev_i32S_neg len).mpr hneg), ev_rd_pure]
          exact ⟨rfl, rfl⟩
        · refine ⟨.Ok (some (alloc.vec.Vec.new _), q), by simp [IScalar.lt_equiv, hpos, hneg], ?_⟩
          simp only [if_neg (fun hh => hpos ((ev_i32S_pos len).mp hh)), if_neg (fun hh => hneg ((ev_i32S_neg len).mp hh)), ev_rd_pure]
          exact ⟨by simp [bytesS]; rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_i64S_toInt (x : I64) : (ev_i64S x).toInt = x.val := by
  simp [ev_i64S, Int64.toInt_ofBitVec]

theorem ev_i64S_neg (x : I64) : (ev_i64S x < 0) ↔ x.val < 0 := by
  rw [Int64.lt_iff_toInt_lt, ev_i64S_toInt]; simp

theorem eval.osr.read_date_time_refines (b : Slice U8) (p : Usize) (hp : p.val + 8 ≤ Usize.max) :
    ∃ r, eval.osr.read_date_time b p = ok r ∧ ev_rRel ev_i64S r ((readDateTime.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_int64_refines b p hp
  unfold eval.osr.read_date_time readDateTime
  simp only [ReaderT.run, StateT.run, ev_rd_bind] at hrel ⊢
  rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Err e =>
    cases hI : readInt64 (bytesS b) p.val with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err e, rfl, trivial⟩
  | Ok tq =>
    obtain ⟨t, q⟩ := tq
    cases hI : readInt64 (bytesS b) p.val with
    | error _ => intro h; exact h.elim
    | ok aq =>
      obtain ⟨a, n⟩ := aq
      intro h; obtain ⟨h1, h2⟩ := h
      subst h1 h2
      simp only
      by_cases hneg : t.val < 0
      · refine ⟨.Err .BadTicks, by simp [IScalar.lt_equiv, hneg], ?_⟩
        rw [if_pos ((ev_i64S_neg t).mpr hneg)]; simp [ev_rd_bind, ev_rd_throw, ev_rRel]
      · by_cases hbig : t.val > 3155378975999999999
        · refine ⟨.Err .TicksRange, by simp [IScalar.lt_equiv, hneg, eval.osr.MAX_TICKS]; omega, ?_⟩
          rw [if_neg (fun hh => hneg ((ev_i64S_neg t).mp hh)), if_pos (by rw [ev_i64S_toInt]; exact hbig)]; trivial
        · refine ⟨.Ok (t, q), by simp [IScalar.lt_equiv, hneg, eval.osr.MAX_TICKS]; omega, ?_⟩
          rw [if_neg (fun hh => hneg ((ev_i64S_neg t).mp hh)), if_neg (by rw [ev_i64S_toInt]; exact hbig)]
          exact ⟨rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

/-- the body of the `for i in [0:4]` loop of `read7BitEncodedInt` -/
def ev_7body (i : Nat) (s : Option Int32 × Nat) : RdM (ForInStep (Option Int32 × Nat)) := do
  let b ← readByte
  if b ≤ 127 then pure (ForInStep.done (some (Int32.ofNat (s.2 ||| (b.toNat &&& 127) <<< (7 * i))),
      s.2 ||| (b.toNat &&& 127) <<< (7 * i)))
  else pure (ForInStep.yield (none, s.2 ||| (b.toNat &&& 127) <<< (7 * i)))

/-- the tail after the loop -/
def ev_7tail (s : Option Int32 × Nat) : RdM Int32 :=
  match s.1 with
  | some r => pure r
  | none => do
    let b ← readByte
    if 15 < b then
        (fun (_ : Int32) => Int32.ofNat (s.2 ||| b.toNat <<< 28)) <$>
          throw "FormatException: Too many bytes in what should have been a 7-bit encoded integer."
      else pure (Int32.ofNat (s.2 ||| b.toNat <<< 28))

theorem ev_read7_spec (B : ByteArray) (p : Nat) : (read7BitEncodedInt.run B).run p =
    (forIn (List.range' 0 4) (none, 0) ev_7body >>= ev_7tail) B p := by
  unfold read7BitEncodedInt
  simp only [ReaderT.run, StateT.run, Std.Legacy.Range.forIn'_eq_forIn'_range']
  simp
  refine congrArg (fun m : RdM Int32 => m B p) ?_
  congr 1
  funext s
  unfold ev_7tail
  rcases s with ⟨_ | r, R⟩
  all_goals first
    | rfl
    | (congr 1; funext bb; split <;> first | rfl | (funext B' p'; rfl))

theorem ev_rd_forIn_cons {α σ} (x : α) (l : List α) (s : σ) (f : α → σ → RdM (ForInStep σ)) (B : ByteArray) (p : Nat) :
    (forIn (x :: l) s f) B p = (match f x s B p with
      | .ok (.done s', q) => .ok (s', q)
      | .ok (.yield s', q) => (forIn l s' f) B q
      | .error e => .error e) := by
  rw [List.forIn_cons, ev_rd_bind]
  rcases f x s B p with e | ⟨st, q⟩
  · rfl
  · cases st <;> rfl
theorem ev_rd_forIn_nil {α σ} (s : σ) (f : α → σ → RdM (ForInStep σ)) (B : ByteArray) (p : Nat) :
    (forIn ([] : List α) s f) B p = .ok (s, p) := rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_7ll_eq (b : Slice U8) (result : U32) (p : Usize) (i : U32) (d : Bool) (e : Option eval.osr.OsrErr) :
    eval.osr.read7bit_loop_loop b result p i d e = (do
      let r ← eval.osr.read7bit_loop_loop.body b result p i d e
      match r with
      | .cont (a, q, j, d', e') => eval.osr.read7bit_loop_loop b a q j d' e'
      | .done y => ok y) := by
  conv_lhs => rw [eval.osr.read7bit_loop_loop, loop_unfold]
  dsimp only
  congr 1; funext r
  rcases r with ⟨a, q, j, d', e'⟩ | y
  · rfl
  · rfl

theorem ev_7ll_done (b : Slice U8) (result : U32) (p : Usize) (i : U32) :
    eval.osr.read7bit_loop_loop b result p i true none = ok (result, p, true, none) := by
  rw [ev_7ll_eq]; simp [eval.osr.read7bit_loop_loop.body]

theorem ev_7ll_err (b : Slice U8) (result : U32) (p : Usize) (i : U32) (d : Bool) (e : eval.osr.OsrErr) :
    eval.osr.read7bit_loop_loop b result p i d (some e) = ok (result, p, d, some e) := by
  rw [ev_7ll_eq]; simp [eval.osr.read7bit_loop_loop.body]

theorem ev_bytesS_getElem (b : Slice U8) (i : Nat) (h : i < (bytesS b).size) (h' : i < b.val.length) :
    ((bytesS b)[i]'h).toNat = (b.val[i]'h').val := by
  rw [ev_ba_getElem _ _ h]; exact ev_bytesS_getD b i h'
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

def ev_7rel : (U32 × Usize × Bool × Option eval.osr.OsrErr) → Except String ((Option Int32 × Nat) × Nat) → Prop
  | (r, q, d, none), .ok ((o, R), Q) => r.val = R ∧ Q = q.val ∧ o = (if d then some (Int32.ofNat R) else none) ∧
      (d = false → R < 2^28)
  | (_, _, _, some _), .error _ => True
  | _, _ => False

theorem ev_7chunk_lt (x i : Nat) (hi : i < 4) : (x &&& 127) <<< (7 * i) < 2 ^ (7 * (i + 1)) := by
  rw [Nat.shiftLeft_eq]
  have h1 : x &&& 127 < 2^7 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  calc (x &&& 127) * 2 ^ (7 * i) < 2^7 * 2^(7*i) := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 2 ^ (7 * (i + 1)) := by rw [← Nat.pow_add]; ring_nf

theorem ev_7loop (b : Slice U8) : ∀ n (i result : U32) (p : Usize), i.val + n = 4 → p.val + n ≤ Usize.max →
    result.val < 2 ^ (7 * i.val) →
    ∃ out, eval.osr.read7bit_loop_loop b result p i false none = ok out ∧
      ev_7rel out ((forIn (List.range' i.val n) ((none : Option Int32), result.val) ev_7body : RdM _) (bytesS b) p.val) := by
  intro n
  induction n with
  | zero =>
    intro i result p hi hp hr
    refine ⟨(result, p, false, none), ?_, ?_⟩
    · rw [ev_7ll_eq]; simp [eval.osr.read7bit_loop_loop.body, (show ¬ i < 4#u32 by scalar_tac)]
    · have : i.val = 4 := by omega
      rw [this] at hr
      simp only [List.range'_zero, ev_rd_forIn_nil, ev_7rel]
      simpa using hr
  | succ n ih =>
    intro i result p hi hp hr
    have hi4 : i < 4#u32 := by scalar_tac
    have hsz := bytesS_size b
    have hrb : readByte (bytesS b) p.val = if h : p.val < (bytesS b).size then .ok ((bytesS b)[p.val], p.val + 1)
        else .error "EndOfStreamException: Unable to read beyond the end of the stream." := ev_readByte_spec _ _
    rw [List.range'_succ, ev_rd_forIn_cons]
    simp only [ev_7body, ev_rd_bind, hrb]
    by_cases hpl : p.val < b.val.length
    · rw [dif_pos (by omega)]
      dsimp only
      have hB := ev_bytesS_getElem b p.val (by omega) hpl
      obtain ⟨x, hx⟩ : ∃ x, x = b.val[p.val]'hpl := ⟨_, rfl⟩
      rw [← hx] at hB
      obtain ⟨p1, hp1, hp1v⟩ := usize_add_one p (by omega)
      obtain ⟨m7, hm7, hm7v⟩ := eq_ok_of_spec (U32.mul_spec (x := 7#u32) (y := i) (by scalar_tac))
      have hm7' : m7.val = 7 * i.val := by simpa using hm7v
      obtain ⟨sh, hsh, hshv, -⟩ := eq_ok_of_spec (U32.ShiftLeft_spec (UScalar.cast .U32 x &&& 127#u32) m7
        (by rw [hm7']; omega))
      obtain ⟨i6, hi6, hi6v⟩ := eq_ok_of_spec (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      have hi6' : i6.val = i.val + 1 := by simpa using hi6v
      have hchunk := ev_7chunk_lt x.val i.val (by omega)
      have hsh' : sh.val = (x.val &&& 127) <<< (7 * i.val) := by
        rw [hshv, hm7', UScalar.val_and, U8.cast_U32_val_eq]
        have : (x.val &&& (127#u32).val) = x.val &&& 127 := by simp
        rw [this]; apply Nat.mod_eq_of_lt
        have h32 : 2 ^ (7 * (i.val + 1)) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by omega)
        exact lt_of_lt_of_le hchunk (le_of_le_of_eq h32 (by simp [U32.size, U32.numBits]))
      have hres : result.val ||| (x.val &&& 127) <<< (7 * i.val) < 2 ^ (7 * (i.val + 1)) :=
        Nat.or_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega))) hchunk
      have hbody : eval.osr.read7bit_loop_loop.body b result p i false none =
          ok (.cont (result ||| sh, p1, i6, decide (x.val ≤ 127), none)) := by
        simp only [eval.osr.read7bit_loop_loop.body]
        simp [hi4, (slice_lt_len_iff p b).mpr hpl, slice_index_ok b p hpl, hp1, lift,
          hm7, hsh, hi6, ← hx]
      have hle : ((bytesS b)[p.val]'(by omega) ≤ 127) ↔ x.val ≤ 127 := by
        rw [UInt8.le_iff_toNat_le, hB]; simp
      by_cases hx7 : x.val ≤ 127
      · refine ⟨(result ||| sh, p1, true, none), ?_, ?_⟩
        · rw [ev_7ll_eq, hbody]; simp only [bind_ok, decide_eq_true hx7, ev_7ll_done]
        · rw [if_pos (hle.mpr hx7)]
          simp only [ev_rd_pure, ev_7rel, UScalar.val_or, hsh', hB]
          exact ⟨by first | trivial | rfl, by omega, by simp, by simp⟩
      · rw [if_neg (fun h => hx7 (hle.mp h))]
        simp only [ev_rd_pure]
        obtain ⟨out, hout, hrel⟩ := ih i6 (result ||| sh) p1 (by omega) (by omega)
          (by rw [UScalar.val_or, hsh', hi6']; exact hres)
        refine ⟨out, ?_, ?_⟩
        · rw [ev_7ll_eq, hbody]; simp only [bind_ok, show decide (x.val ≤ 127) = false by simp [hx7]]; exact hout
        · rw [hi6', UScalar.val_or, hsh', hp1v] at hrel; rw [hB]; exact hrel
    · rw [dif_neg (by omega)]
      dsimp only
      refine ⟨(result, p, false, some .Eos), ?_, trivial⟩
      rw [ev_7ll_eq]
      simp [eval.osr.read7bit_loop_loop.body, hi4,
        (show ¬ p < Slice.len b by rw [slice_lt_len_iff]; exact hpl), ev_7ll_err]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_read_byte_refines_total (b : Slice U8) (p : Usize) :
    ∃ r, eval.osr.read_byte b p = ok r ∧ ev_rRel (fun x : U8 => UInt8.ofBitVec x.bv) r ((readByte.run (bytesS b)).run p.val) := by
  by_cases h : p.val < b.val.length
  · exact eval.osr.read_byte_refines b p (by have := b.property; omega)
  · rw [ev_readByte_spec]
    refine ⟨.Err .Eos, by simp [eval.osr.read_byte, (show ¬ p < Slice.len b by rw [slice_lt_len_iff]; exact h)], ?_⟩
    rw [dif_neg (by rw [bytesS_size]; exact h)]; trivial

theorem ev_i32_of_u32 (v : U32) : i32S (UScalar.hcast .I32 v) = Int32.ofNat v.val := by
  apply Int32.toBitVec_inj.mp
  simp only [i32S, UScalar.hcast, Int32.toBitVec_ofBitVec]
  show BitVec.zeroExtend 32 v.bv = BitVec.ofNat 32 v.val
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_ofNat]
  rfl

theorem eval.osr.read7bit_encoded_int_refines (b : Slice U8) (p : Usize) (hp : p.val + 4 ≤ Usize.max) :
    ∃ r, eval.osr.read7bit_encoded_int b p = ok r ∧
      ev_rRel i32S r ((read7BitEncodedInt.run (bytesS b)).run p.val) := by
  rw [ev_read7_spec, ev_rd_bind]
  obtain ⟨out, hout, hrel⟩ := ev_7loop b 4 0#u32 0#u32 p (by simp) (by simpa using hp) (by simp)
  simp only [show (0#u32).val = 0 by simp] at hrel
  unfold eval.osr.read7bit_encoded_int eval.osr.read7bit_loop
  rw [hout]
  obtain ⟨r, q, d, e⟩ := out
  revert hrel
  cases hF : (forIn (List.range' 0 4) ((none : Option Int32), 0) ev_7body : RdM _) (bytesS b) p.val with
  | error msg =>
    intro hrel
    cases e with
    | none => exact hrel.elim
    | some e => exact ⟨.Err e, by simp, trivial⟩
  | ok sQ =>
    obtain ⟨⟨o, R⟩, Q⟩ := sQ
    intro hrel
    cases e with
    | some e => exact hrel.elim
    | none =>
      obtain ⟨hR, hQ, ho, hlt⟩ := hrel
      subst hR hQ
      cases d with
      | true =>
        simp only [if_true] at ho; subst ho
        refine ⟨.Ok (UScalar.hcast .I32 r, q), by simp [lift], ?_⟩
        exact ⟨ev_i32_of_u32 r, rfl⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at ho; subst ho
        have hlt := hlt rfl
        obtain ⟨rb, hrb, hrbrel⟩ := ev_read_byte_refines_total b q
        simp only [ev_7tail]
        rw [ev_rd_bind]
        simp only [bind_ok, Bool.false_eq_true, if_false, hrb]
        revert hrbrel
        simp only [ReaderT.run, StateT.run]
        cases rb with
        | Err e =>
          cases hRB : readByte (bytesS b) q.val with
          | ok _ => intro h; exact h.elim
          | error _ => intro _; exact ⟨.Err e, by simp [hrb], trivial⟩
        | Ok xq =>
          obtain ⟨x, q'⟩ := xq
          cases hRB : readByte (bytesS b) q.val with
          | error _ => intro h; exact h.elim
          | ok yn =>
            obtain ⟨y, n⟩ := yn
            intro h; obtain ⟨hy, hn⟩ := h
            subst hy hn
            have hyx : (UInt8.ofBitVec x.bv).toNat = x.val := by simp [UInt8.toNat_ofBitVec]
            by_cases h15 : x.val > 15
            · have : 15 < UInt8.ofBitVec x.bv := by rw [UInt8.lt_iff_toNat_lt, hyx]; simpa using h15
              refine ⟨.Err .Bad7Bit, by simp [hrb, show ¬ x.val ≤ 15 by omega, show x > 15#u8 by simp only [UScalar.lt_equiv]; simpa using h15], ?_⟩
              simp only [if_pos this]; trivial
            · have : ¬ 15 < UInt8.ofBitVec x.bv := by rw [UInt8.lt_iff_toNat_lt, hyx]; simpa using h15
              have hx16 : x.val < 16 := by omega
              obtain ⟨sh, hsh, hshv, -⟩ := eq_ok_of_spec (U32.ShiftLeft_IScalar_spec (UScalar.cast .U32 x) 28#i32
                (by simp) (by simp))
              have hsh' : sh.val = x.val <<< 28 := by
                rw [hshv, U8.cast_U32_val_eq]; apply Nat.mod_eq_of_lt
                rw [Nat.shiftLeft_eq]; simp [U32.size, U32.numBits]; omega
              refine ⟨.Ok (UScalar.hcast .I32 (r ||| sh), q'), by
                simp [hrb, show x.val ≤ 15 by omega, show ¬ x > 15#u8 by simp only [UScalar.lt_equiv]; simpa using h15, lift, hsh], ?_⟩
              simp only [if_neg this, ev_rd_pure]
              refine ⟨?_, rfl⟩
              rw [ev_i32_of_u32, UScalar.val_or, hsh', hyx]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_readByte_pos (B : ByteArray) (p : Nat) (x : UInt8) (n : Nat) (h : readByte B p = .ok (x, n)) : n ≤ B.size := by
  have hs := ev_readByte_spec B p
  simp only [ReaderT.run, StateT.run] at hs
  rw [hs] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  · cases h

theorem ev_7body_pos (B : ByteArray) (i : Nat) (s : Option Int32 × Nat) (p : Nat) st n
    (h : ev_7body i s B p = .ok (st, n)) : n ≤ B.size := by
  simp only [ev_7body, ev_rd_bind] at h
  cases hR : readByte B p with
  | error => rw [hR] at h; cases h
  | ok xq =>
    obtain ⟨x, q⟩ := xq
    rw [hR] at h
    have := ev_readByte_pos _ _ _ _ hR
    dsimp only at h
    split at h <;> (simp only [ev_rd_pure, Except.ok.injEq, Prod.mk.injEq] at h; omega)

theorem ev_7forIn_pos (B : ByteArray) : ∀ (l : List Nat) (s : Option Int32 × Nat) (p : Nat) st n, p ≤ B.size →
    (forIn l s ev_7body : RdM _) B p = .ok (st, n) → n ≤ B.size := by
  intro l
  induction l with
  | nil => intro s p st n hp h; rw [ev_rd_forIn_nil] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  | cons x l ih =>
    intro s p st n hp h
    rw [ev_rd_forIn_cons] at h
    cases hb : ev_7body x s B p with
    | error => rw [hb] at h; cases h
    | ok tq =>
      obtain ⟨t, q⟩ := tq
      have hq := ev_7body_pos _ _ _ _ _ _ hb
      rw [hb] at h
      cases t with
      | done s' => simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      | yield s' => exact ih s' q st n hq h

theorem ev_read7_pos (B : ByteArray) (p : Nat) (v : Int32) (n : Nat) (hp : p ≤ B.size)
    (h : (read7BitEncodedInt.run B).run p = .ok (v, n)) : n ≤ B.size := by
  rw [ev_read7_spec, ev_rd_bind] at h
  cases hF : (forIn (List.range' 0 4) ((none : Option Int32), 0) ev_7body : RdM _) B p with
  | error => rw [hF] at h; cases h
  | ok sq =>
    obtain ⟨s, q⟩ := sq
    have hq := ev_7forIn_pos B _ _ _ _ _ hp hF
    rw [hF] at h
    dsimp only at h
    obtain ⟨o, R⟩ := s
    cases o with
    | some r => simp only [ev_7tail, ev_rd_pure, Except.ok.injEq, Prod.mk.injEq] at h; omega
    | none =>
      simp only [ev_7tail] at h
      rw [ev_rd_bind] at h
      cases hR : readByte B q with
      | error => rw [hR] at h; cases h
      | ok xq =>
        obtain ⟨x, q'⟩ := xq
        have := ev_readByte_pos _ _ _ _ hR
        rw [hR] at h
        dsimp only at h
        split at h
        · cases h
        · simp only [ev_rd_pure, Except.ok.injEq, Prod.mk.injEq] at h; omega

theorem ev_readByte_succ (B : ByteArray) (p : Nat) (x : UInt8) (n : Nat) (h : readByte B p = .ok (x, n)) : n = p + 1 := by
  have hs := ev_readByte_spec B p
  simp only [ReaderT.run, StateT.run] at hs
  rw [hs] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  · cases h

theorem ev_i32S_beq0 (x : I32) : ((i32S x == 0) = true) ↔ x.val = 0 := by
  rw [beq_iff_eq]
  constructor
  · intro h; have := congrArg Int32.toInt h; rw [i32S_toInt] at this; simpa using this
  · intro h; apply Int32.toInt_inj.mp; rw [i32S_toInt, h]; rfl

theorem eval.osr.read_string_refines (b : Slice U8) (p : Usize) (hp : p.val + 5 ≤ Usize.max) :
    ∃ r, eval.osr.read_string b p = ok r ∧
      ev_rRel (fun o : Option (alloc.vec.Vec U32) => o.map fun v => String.ofList (v.val.map chOf)) r
        ((readString.run (bytesS b)).run p.val) := by
  obtain ⟨r, hr, hrel⟩ := ev_read_byte_refines_total b p
  unfold eval.osr.read_string readString
  simp only [ReaderT.run, StateT.run, ev_rd_bind] at hrel ⊢
  rw [hr]; simp only [bind_ok]
  revert hrel
  cases r with
  | Err e =>
    cases hB : readByte (bytesS b) p.val with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨.Err e, rfl, trivial⟩
  | Ok xq =>
    obtain ⟨x, q⟩ := xq
    cases hB : readByte (bytesS b) p.val with
    | error _ => intro h; exact h.elim
    | ok yn =>
      obtain ⟨y, n⟩ := yn
      intro h; obtain ⟨h1, h2⟩ := h
      subst h1 h2
      have hq := ev_readByte_succ _ _ _ _ hB
      have hyx : (UInt8.ofBitVec x.bv).toNat = x.val := by simp [UInt8.toNat_ofBitVec]
      have hy0 : ((UInt8.ofBitVec x.bv == 0) = true) ↔ x.val = 0 := by
        rw [beq_iff_eq, ← UInt8.toNat_inj, hyx]; simp
      dsimp only
      by_cases hx0 : x.val = 0
      · refine ⟨.Ok (none, q), by simp [show x = 0#u8 by scalar_tac], ?_⟩
        rw [if_pos (hy0.mpr hx0), ev_rd_pure]; exact ⟨rfl, rfl⟩
      · rw [if_neg (fun hh => hx0 (hy0.mp hh))]
        obtain ⟨r7, hr7, hrel7⟩ := eval.osr.read7bit_encoded_int_refines b q (by omega)
        simp only [ReaderT.run, StateT.run] at hrel7
        rw [ev_rd_bind]
        have hx0' : ¬ x = 0#u8 := by scalar_tac
        revert hrel7
        cases r7 with
        | Err e =>
          cases hR : read7BitEncodedInt (bytesS b) q.val with
          | ok _ => intro h; exact h.elim
          | error _ => intro _; exact ⟨.Err e, by simp [hx0', hr7], trivial⟩
        | Ok lq =>
          obtain ⟨len, q2⟩ := lq
          cases hR : read7BitEncodedInt (bytesS b) q.val with
          | error _ => intro h; exact h.elim
          | ok an =>
            obtain ⟨a, n⟩ := an
            intro h; obtain ⟨h1, h2⟩ := h
            subst h1 h2
            dsimp only
            have hq2 := ev_read7_pos (bytesS b) q.val _ _ (by have := ev_readByte_pos _ _ _ _ hB; omega) hR
            rw [bytesS_size] at hq2
            by_cases hneg : len.val < 0
            · refine ⟨.Err .InvalidStringLength, by simp [hx0', hr7, IScalar.lt_equiv, hneg], ?_⟩
              rw [if_pos ((ev_i32S_neg len).mpr hneg)]; trivial
            · rw [if_neg (fun hh => hneg ((ev_i32S_neg len).mp hh))]
              by_cases hz : len.val = 0
              · refine ⟨.Ok (some (alloc.vec.Vec.new _), q2), by simp [hx0', hr7, IScalar.lt_equiv, hneg, show len = 0#i32 by scalar_tac], ?_⟩
                rw [if_pos ((ev_i32S_beq0 len).mpr hz), ev_rd_pure]
                exact ⟨by simp <;> rfl, rfl⟩
              · have hpos : 0 < len.val := by omega
                rw [if_neg (fun hh => hz ((ev_i32S_beq0 len).mp hh))]
                have hmod : len.val % 2 ^ System.Platform.numBits = len.val := by
                  have := len.hBounds
                  have h2 : len.val < 2^31 := by simpa using this.2
                  have hnb : (2:Int)^31 < (2:Int)^System.Platform.numBits := by
                    cases System.Platform.numBits_eq <;> simp [*]
                  rw [Int.emod_eq_of_lt (by omega) (by omega)]
                have hc : (IScalar.hcast .Usize len).val = len.val.toNat := by
                  simp [IScalar.hcast_val_eq, hmod]
                obtain ⟨v, q3, hv, hspec⟩ := eval.osr.read_bytes_refines b q2 (IScalar.hcast .Usize len) hq2
                simp only [ReaderT.run, StateT.run] at hspec
                rw [ev_rd_bind]
                rw [show (i32S len).toNatClampNeg = (IScalar.hcast .Usize len).val by
                  rw [hc]; simp [Int32.toNatClampNeg, i32S_toInt]]
                rw [hspec]
                dsimp only
                rw [bytesS_size]
                have hlen0 : ¬ len = 0#i32 := by scalar_tac
                by_cases hlt : (alloc.vec.Vec.deref v).val.length < (IScalar.hcast .Usize len).val
                · have hnle : ¬ (len.val ≤ ((v.val.length : Nat) : Int)) := by
                    have : (alloc.vec.Vec.deref v).val.length = v.val.length := by simp
                    omega
                  refine ⟨.Err .Eos, by simp [hx0', hr7, IScalar.lt_equiv, hneg, hlen0, lift, hv, hmod, hnle], ?_⟩
                  rw [if_pos hlt]; trivial
                · obtain ⟨v2, hv2, hv2s, -⟩ := beatmap.text.decode_utf8_refines (alloc.vec.Vec.deref v) 0#usize
                  have hle : len.val ≤ ((v.val.length : Nat) : Int) := by
                    have : (alloc.vec.Vec.deref v).val.length = v.val.length := by simp
                    omega
                  refine ⟨.Ok (some v2, q3), by simp [hx0', hr7, IScalar.lt_equiv, hneg, hlen0, lift, hv, hmod, hle, hv2], ?_⟩
                  rw [if_neg hlt, ev_rd_pure]
                  refine ⟨?_, rfl⟩
                  simp only [Option.map_some]
                  congr 2
                  rw [show (0#usize).val = 0 by simp] at hv2s
                  rw [← hv2s]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

def ev_hdrS : RdM (Int32 × Option String) := do
  let version ← readInt32
  let beatmapHash ← readString
  let _player ← readString
  let _md5 ← readString
  let _ ← readUInt16
  let _ ← readUInt16
  let _ ← readUInt16
  let _ ← readUInt16
  let _ ← readUInt16
  let _ ← readUInt16
  let _totalScore ← readInt32
  let _maxCombo ← readUInt16
  let _perfect ← readBoolean
  pure (version, beatmapHash)

def ev_skipS (version : Int32) : RdM Unit :=
  if version ≥ 20140721 then do let _ ← readInt64; pure ()
  else if version ≥ 20121008 then do let _ ← readInt32; pure ()
  else pure ()

def ev_bodyS (version : Int32) : RdM (Int32 × Option ByteArray × Option ByteArray) := do
  let legacyMods ← readInt32
  let _hp ← readString
  let _date ← readDateTime
  let cr ← readByteArray
  ev_skipS version
  let ci ← if version ≥ 30000001 then readByteArray else pure none
  pure (legacyMods, cr, ci)

theorem ev_ite_bind {α β} (c : Prop) [Decidable c] (a b : RdM α) (f : α → RdM β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by split <;> rfl

theorem ev_readContainer_eq : readContainer = (do
    let rulesetId ← readByte
    if rulesetId != 0 then throw s!"InvalidOperationException: only the osu! ruleset is supported (replay ruleset id {rulesetId})"
    let vh ← ev_hdrS
    let body ← ev_bodyS vh.1
    pure { rulesetId, version := vh.1, beatmapHash := vh.2, legacyMods := body.1, compressedReplay := body.2.1,
           compressedScoreInfo := body.2.2 }) := by
  unfold readContainer ev_hdrS ev_bodyS ev_skipS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_assoc, pure_bind, ev_ite_bind,
    show (List.range' (Std.Legacy.Range.mk 0 6 1 (by decide)).start (Std.Legacy.Range.mk 0 6 1 (by decide)).size
      (Std.Legacy.Range.mk 0 6 1 (by decide)).step) = [0, 1, 2, 3, 4, 5] from rfl,
    List.forIn_cons, List.forIn_nil]

end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

/-- a reader never moves past the end of the input -/
structure ev_bnd {α} (r : RdM α) : Prop where
  h : ∀ B p v n, p ≤ B.size → r B p = .ok (v, n) → n ≤ B.size

theorem ev_bnd_bind {α β} (x : RdM α) (f : α → RdM β) (hx : ev_bnd x) (hf : ∀ a, ev_bnd (f a)) : ev_bnd (x >>= f) := by
  constructor; intro B p v n hp h
  rw [ev_rd_bind] at h
  cases hX : x B p with
  | error => rw [hX] at h; cases h
  | ok aq =>
    obtain ⟨a, q⟩ := aq
    rw [hX] at h
    exact (hf a).h B q v n (hx.h B p a q hp hX) h
theorem ev_bnd_pure {α} (a : α) : ev_bnd (pure a : RdM α) := by
  constructor; intro B p v n hp h; rw [ev_rd_pure] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
theorem ev_bnd_throw {α} (e : String) : ev_bnd (throw e : RdM α) := by
  constructor; intro B p v n hp h; cases h
theorem ev_bnd_ite {α} (c : Prop) [Decidable c] (a b : RdM α) (ha : ev_bnd a) (hb : ev_bnd b) :
    ev_bnd (if c then a else b) := by split <;> assumption
theorem ev_bnd_readByte : ev_bnd readByte := ⟨fun B p _ n _ h => ev_readByte_pos B p _ n h⟩
theorem ev_bnd_readLE (k : Nat) : ev_bnd (readLE k) := by
  constructor; intro B p v n hp h
  have hs := ev_readLE_spec B p k
  simp only [ReaderT.run, StateT.run] at hs
  rw [hs] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  · cases h
theorem ev_bnd_readBytes (k : Nat) : ev_bnd (readBytes k) := by
  constructor; intro B p v n hp h
  have hs := ev_readBytes_spec B p k
  simp only [ReaderT.run, StateT.run] at hs
  rw [hs] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
theorem ev_bnd_read7 : ev_bnd read7BitEncodedInt := ⟨fun B p v n hp h => ev_read7_pos B p v n hp h⟩

macro "ev_bnd_tac" : tactic => `(tactic| repeat (first
  | exact ev_bnd_pure _
  | exact ev_bnd_throw _
  | exact ev_bnd_readByte
  | exact ev_bnd_readLE _
  | exact ev_bnd_readBytes _
  | exact ev_bnd_read7
  | (apply ev_bnd_bind; rotate_left; intro _)
  | apply ev_bnd_ite))

theorem ev_bnd_readInt32 : ev_bnd readInt32 := by unfold readInt32; ev_bnd_tac
theorem ev_bnd_readInt64 : ev_bnd readInt64 := by unfold readInt64; ev_bnd_tac
theorem ev_bnd_readUInt16 : ev_bnd readUInt16 := ev_bnd_readLE 2
theorem ev_bnd_readBoolean : ev_bnd readBoolean := by unfold readBoolean; ev_bnd_tac
theorem ev_bnd_readString : ev_bnd readString := by unfold readString; ev_bnd_tac
theorem ev_bnd_readDateTime : ev_bnd readDateTime := by unfold readDateTime; ev_bnd_tac
theorem ev_bnd_readByteArray : ev_bnd readByteArray := by unfold readByteArray; ev_bnd_tac
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_chain {α β γ δ : Type} (f : α → β) (r : core.result.Result (α × Usize) eval.osr.OsrErr)
    (sr : RdM β) (B : ByteArray) (p : Nat) (kS : β → RdM δ)
    (M : core.result.Result (α × Usize) eval.osr.OsrErr → Result (core.result.Result γ eval.osr.OsrErr))
    (Rel : core.result.Result γ eval.osr.OsrErr → Except String (δ × Nat) → Prop)
    (hM : ∀ e, M (.Err e) = ok (.Err e))
    (hE : ∀ e msg, Rel (.Err e) (.error msg))
    (hrel : ev_rRel f r (sr B p))
    (h2 : ∀ a q, sr B p = .ok (f a, q.val) → ∃ r', M (.Ok (a, q)) = ok r' ∧ Rel r' (kS (f a) B q.val)) :
    ∃ r', M r = ok r' ∧ Rel r' ((sr >>= kS) B p) := by
  rw [ev_rd_bind]
  revert hrel
  cases r with
  | Err e =>
    cases hS : sr B p with
    | ok _ => intro h; exact h.elim
    | error msg => intro _; exact ⟨.Err e, hM e, hE e msg⟩
  | Ok aq =>
    obtain ⟨a, q⟩ := aq
    cases hS : sr B p with
    | error _ => intro h; exact h.elim
    | ok bn =>
      obtain ⟨b', n⟩ := bn
      intro h; obtain ⟨h1, h2'⟩ := h
      subst h1 h2'
      exact h2 a q hS

/-- one reader step: `ev_step h as a q hs` with `h : ∃ r, rust = ok r ∧ ev_rRel f r (spec B p)` -/
macro "ev_step " h:term " as " a:ident q:ident hs:ident : tactic => `(tactic| (
  obtain ⟨_r, _hr, _hrel⟩ := $h
  rw [_hr]; simp only [bind_ok]
  simp only [ReaderT.run, StateT.run] at _hrel
  apply ev_chain _ _ _ _ _ _ _ _ _ _ _hrel
  rotate_left
  · intro _; rfl
  · intro _ _; trivial
  intro $a $q $hs
  try simp only [Aeneas.Std.uncurry_apply_pair]))

theorem ev_bnd_at {α} {r : RdM α} (hr : ev_bnd r) (b : Slice U8) (p q : Nat) (v : α) (hp : p ≤ b.val.length)
    (h : r (bytesS b) p = .ok (v, q)) : q ≤ b.val.length := by
  have := hr.h _ _ _ _ (by rw [bytesS_size]; exact hp) h; rwa [bytesS_size] at this

def ev_hRel : core.result.Result (I32 × Option (alloc.vec.Vec U32) × Usize) eval.osr.OsrErr →
    Except String ((Int32 × Option String) × Nat) → Prop
  | .Ok (v, h, q), .ok ((v', h'), n) => i32S v = v' ∧ h.map (fun v => String.ofList (v.val.map chOf)) = h' ∧ n = q.val
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.read_header_refines (b : Slice U8) (p : Usize) (hb : b.val.length + 8 ≤ Usize.max)
    (hp : p.val ≤ b.val.length) :
    ∃ r, eval.osr.read_header b p = ok r ∧ ev_hRel r (ev_hdrS (bytesS b) p.val) := by
  unfold eval.osr.read_header ev_hdrS
  ev_step (eval.osr.read_int32_refines b p (by omega)) as v1 p1 h1
  have hp1 := ev_bnd_at ev_bnd_readInt32 b _ _ _ hp h1
  ev_step (eval.osr.read_string_refines b p1 (by omega)) as v2 p2 h2
  have hp2 := ev_bnd_at ev_bnd_readString b _ _ _ hp1 h2
  ev_step (eval.osr.read_string_refines b p2 (by omega)) as v3 p3 h3
  have hp3 := ev_bnd_at ev_bnd_readString b _ _ _ hp2 h3
  ev_step (eval.osr.read_string_refines b p3 (by omega)) as v4 p4 h4
  have hp4 := ev_bnd_at ev_bnd_readString b _ _ _ hp3 h4
  ev_step (eval.osr.read_uint16_refines b p4 (by omega)) as v5 p5 h5
  have hp5 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp4 h5
  ev_step (eval.osr.read_uint16_refines b p5 (by omega)) as v6 p6 h6
  have hp6 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp5 h6
  ev_step (eval.osr.read_uint16_refines b p6 (by omega)) as v7 p7 h7
  have hp7 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp6 h7
  ev_step (eval.osr.read_uint16_refines b p7 (by omega)) as v8 p8 h8
  have hp8 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp7 h8
  ev_step (eval.osr.read_uint16_refines b p8 (by omega)) as v9 p9 h9
  have hp9 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp8 h9
  ev_step (eval.osr.read_uint16_refines b p9 (by omega)) as v10 p10 h10
  have hp10 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp9 h10
  ev_step (eval.osr.read_int32_refines b p10 (by omega)) as v11 p11 h11
  have hp11 := ev_bnd_at ev_bnd_readInt32 b _ _ _ hp10 h11
  ev_step (eval.osr.read_uint16_refines b p11 (by omega)) as v12 p12 h12
  have hp12 := ev_bnd_at ev_bnd_readUInt16 b _ _ _ hp11 h12
  ev_step (eval.osr.read_boolean_refines b p12 (by omega)) as v13 p13 h13
  exact ⟨_, rfl, rfl, rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_i32S_ge (v : I32) (k : Int32) : (i32S v ≥ k) ↔ k.toInt ≤ v.val := by
  rw [ge_iff_le, Int32.le_iff_toInt_le, i32S_toInt]

def ev_oRel : core.result.Result Usize eval.osr.OsrErr → Except String (Unit × Nat) → Prop
  | .Ok q, .ok (_, n) => n = q.val
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.skip_online_id_refines (b : Slice U8) (p : Usize) (v : I32) (hb : b.val.length + 8 ≤ Usize.max)
    (hp : p.val ≤ b.val.length) :
    ∃ r, eval.osr.skip_online_id b p v = ok r ∧ ev_oRel r (ev_skipS (i32S v) (bytesS b) p.val) := by
  unfold eval.osr.skip_online_id ev_skipS
  by_cases h1 : 20140721 ≤ v.val
  · rw [if_pos (show v >= 20140721#i32 by scalar_tac), if_pos (show i32S v ≥ 20140721 from (ev_i32S_ge v _).mpr (by simpa using h1))]
    ev_step (eval.osr.read_int64_refines b p (by omega)) as x q hq
    exact ⟨_, rfl, rfl⟩
  · rw [if_neg (show ¬ v >= 20140721#i32 by scalar_tac), if_neg (show ¬ (i32S v ≥ 20140721) from fun h => h1 (by simpa using (ev_i32S_ge v _).mp h))]
    by_cases h2 : 20121008 ≤ v.val
    · rw [if_pos (show v >= 20121008#i32 by scalar_tac), if_pos (show i32S v ≥ 20121008 from (ev_i32S_ge v _).mpr (by simpa using h2))]
      ev_step (eval.osr.read_int32_refines b p (by omega)) as x q hq
      exact ⟨_, rfl, rfl⟩
    · rw [if_neg (show ¬ v >= 20121008#i32 by scalar_tac), if_neg (show ¬ (i32S v ≥ 20121008) from fun h => h2 (by simpa using (ev_i32S_ge v _).mp h))]
      exact ⟨_, rfl, rfl⟩

theorem ev_bnd_skipS (v : Int32) : ev_bnd (ev_skipS v) := by
  unfold ev_skipS; ev_bnd_tac
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_chainU {γ δ : Type} (r : core.result.Result Usize eval.osr.OsrErr)
    (sr : RdM Unit) (B : ByteArray) (p : Nat) (kS : Unit → RdM δ)
    (M : core.result.Result Usize eval.osr.OsrErr → Result (core.result.Result γ eval.osr.OsrErr))
    (Rel : core.result.Result γ eval.osr.OsrErr → Except String (δ × Nat) → Prop)
    (hM : ∀ e, M (.Err e) = ok (.Err e))
    (hE : ∀ e msg, Rel (.Err e) (.error msg))
    (hrel : ev_oRel r (sr B p))
    (h2 : ∀ q, sr B p = .ok ((), q.val) → ∃ r', M (.Ok q) = ok r' ∧ Rel r' (kS () B q.val)) :
    ∃ r', M r = ok r' ∧ Rel r' ((sr >>= kS) B p) := by
  rw [ev_rd_bind]
  revert hrel
  cases r with
  | Err e =>
    cases hS : sr B p with
    | ok _ => intro h; exact h.elim
    | error msg => intro _; exact ⟨.Err e, hM e, hE e msg⟩
  | Ok q =>
    cases hS : sr B p with
    | error _ => intro h; exact h.elim
    | ok bn =>
      obtain ⟨⟨⟩, n⟩ := bn
      intro h
      subst h
      exact h2 q hS

def ev_bodyRel : core.result.Result (I32 × Option (alloc.vec.Vec U8) × Option (alloc.vec.Vec U8)) eval.osr.OsrErr →
    Except String ((Int32 × Option ByteArray × Option ByteArray) × Nat) → Prop
  | .Ok (lm, cr, ci), .ok ((lm', cr', ci'), _) => i32S lm = lm' ∧
      cr.map (fun v => bytesS (alloc.vec.Vec.deref v)) = cr' ∧ ci.map (fun v => bytesS (alloc.vec.Vec.deref v)) = ci'
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.read_body_refines (b : Slice U8) (p : Usize) (v : I32) (hb : b.val.length + 8 ≤ Usize.max)
    (hp : p.val ≤ b.val.length) :
    ∃ r, eval.osr.read_body b p v = ok r ∧ ev_bodyRel r (ev_bodyS (i32S v) (bytesS b) p.val) := by
  unfold eval.osr.read_body ev_bodyS
  ev_step (eval.osr.read_int32_refines b p (by omega)) as v1 p1 h1
  have hp1 := ev_bnd_at ev_bnd_readInt32 b _ _ _ hp h1
  ev_step (eval.osr.read_string_refines b p1 (by omega)) as v2 p2 h2
  have hp2 := ev_bnd_at ev_bnd_readString b _ _ _ hp1 h2
  ev_step (eval.osr.read_date_time_refines b p2 (by omega)) as v3 p3 h3
  have hp3 := ev_bnd_at ev_bnd_readDateTime b _ _ _ hp2 h3
  ev_step (eval.osr.read_byte_array_refines b p3 (by omega)) as v4 p4 h4
  have hp4 := ev_bnd_at ev_bnd_readByteArray b _ _ _ hp3 h4
  obtain ⟨r5, hr5, hrel5⟩ := eval.osr.skip_online_id_refines b p4 v hb hp4
  rw [hr5]; simp only [bind_ok]
  apply ev_chainU _ _ _ _ _ _ _ _ _ hrel5
  rotate_left
  · intro _; rfl
  · intro _ _; trivial
  intro p5 h5
  dsimp only
  have hp5 := ev_bnd_at (ev_bnd_skipS _) b _ _ _ hp4 h5
  by_cases h30 : 30000001 ≤ v.val
  · rw [if_pos (show v >= 30000001#i32 by scalar_tac),
      if_pos (show i32S v ≥ 30000001 from (ev_i32S_ge v _).mpr (by simpa using h30))]
    ev_step (eval.osr.read_byte_array_refines b p5 (by omega)) as v6 p6 h6
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  · rw [if_neg (show ¬ v >= 30000001#i32 by scalar_tac),
      if_neg (show ¬ (i32S v ≥ 30000001) from fun h => h30 (by simpa using (ev_i32S_ge v _).mp h))]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

theorem ev_chainG {ρ β γ δ : Type} (R0 : core.result.Result ρ eval.osr.OsrErr → Except String (β × Nat) → Prop)
    (hOE : ∀ x e, ¬ R0 (.Ok x) (.error e)) (hEO : ∀ e y, ¬ R0 (.Err e) (.ok y))
    (r : core.result.Result ρ eval.osr.OsrErr) (sr : RdM β) (B : ByteArray) (p : Nat) (kS : β → RdM δ)
    (M : core.result.Result ρ eval.osr.OsrErr → Result (core.result.Result γ eval.osr.OsrErr))
    (Rel : core.result.Result γ eval.osr.OsrErr → Except String (δ × Nat) → Prop)
    (hM : ∀ e, M (.Err e) = ok (.Err e))
    (hE : ∀ e msg, Rel (.Err e) (.error msg))
    (hrel : R0 r (sr B p))
    (h2 : ∀ x b n, R0 (.Ok x) (.ok (b, n)) → sr B p = .ok (b, n) → ∃ r', M (.Ok x) = ok r' ∧ Rel r' (kS b B n)) :
    ∃ r', M r = ok r' ∧ Rel r' ((sr >>= kS) B p) := by
  rw [ev_rd_bind]
  revert hrel
  cases r with
  | Err e =>
    cases hS : sr B p with
    | ok y => intro h; exact (hEO e y h).elim
    | error msg => intro _; exact ⟨.Err e, hM e, hE e msg⟩
  | Ok x =>
    cases hS : sr B p with
    | error e => intro h; exact (hOE x e h).elim
    | ok bn =>
      obtain ⟨b', n⟩ := bn
      intro h
      exact h2 x b' n h hS

theorem ev_deref_slice {T} (v : alloc.vec.Vec T) : alloc.vec.Vec.deref v = v.slice := by
  exact Slice.val_from v.slice _

theorem ev_bnd_hdrS : ev_bnd ev_hdrS := by
  unfold ev_hdrS
  repeat (first | exact ev_bnd_readInt32 | exact ev_bnd_readString | exact ev_bnd_readUInt16 | exact ev_bnd_readBoolean | exact ev_bnd_pure _ | (apply ev_bnd_bind; rotate_left; intro _))

def ev_cRel : core.result.Result eval.osr.Container eval.osr.OsrErr → Except String (Container × Nat) → Prop
  | .Ok c, .ok (C, _) => ev_containerS c = C
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.read_container_refines (b : Slice U8) (hb : b.val.length + 8 ≤ Usize.max) :
    ∃ r, eval.osr.read_container b = ok r ∧ ev_cRel r (readContainer (bytesS b) 0) := by
  rw [ev_readContainer_eq]
  unfold eval.osr.read_container
  ev_step (eval.osr.read_byte_refines b 0#usize (by simp; omega)) as rid p1 h1
  have hp1 := ev_bnd_at ev_bnd_readByte b _ _ _ (by simp) h1
  have hyx : (UInt8.ofBitVec rid.bv).toNat = rid.val := by simp [UInt8.toNat_ofBitVec]
  by_cases h0 : rid.val = 0
  · have hz : (UInt8.ofBitVec rid.bv != 0) = false := by
      simp only [bne_eq_false_iff_eq]; apply UInt8.toNat_inj.mp; rw [hyx, h0]; rfl
    rw [if_neg (show ¬ (rid != 0#u8) by simp; scalar_tac), if_neg (by rw [hz]; simp)]
    obtain ⟨rh, hrh, hrelh⟩ := eval.osr.read_header_refines b p1 hb hp1
    rw [hrh]; simp only [bind_ok]
    apply ev_chainG ev_hRel (by intro x e h; obtain ⟨_, _, _⟩ := x; exact h) (by intro e y h; exact h)
      _ _ _ _ _ _ _ _ _ hrelh
    rotate_left
    · intro _; rfl
    · intro _ _; trivial
    intro x vh n hR hS
    obtain ⟨v, h, q⟩ := x
    obtain ⟨v', h'⟩ := vh
    obtain ⟨e1, e2, e3⟩ := hR
    subst e1 e2 e3
    simp only [Aeneas.Std.uncurry_apply_pair]
    have hq := ev_bnd_at ev_bnd_hdrS b _ _ _ hp1 hS
    obtain ⟨rb, hrb, hrelb⟩ := eval.osr.read_body_refines b q v hb hq
    rw [hrb]; simp only [bind_ok]
    apply ev_chainG ev_bodyRel (by intro x e h; obtain ⟨_, _, _⟩ := x; exact h) (by intro e y h; exact h)
      _ _ _ _ _ _ _ _ _ hrelb
    rotate_left
    · intro _; rfl
    · intro _ _; trivial
    intro x bd n hR hS2
    obtain ⟨lm, cr, ci⟩ := x
    obtain ⟨lm', cr', ci'⟩ := bd
    obtain ⟨e1, e2, e3⟩ := hR
    subst e1 e2 e3
    simp only [Aeneas.Std.uncurry_apply_pair]
    refine ⟨_, rfl, ?_⟩
    simp only [ev_rd_pure, ev_cRel, ev_containerS]
    simp [ev_deref_slice]
    rfl
  · have hz : (UInt8.ofBitVec rid.bv != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; apply h0; rw [← hyx, h]; rfl
    rw [if_pos (show rid != 0#u8 by simp; scalar_tac), if_pos hz]
    exact ⟨_, rfl, trivial⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_to_mod_known_acr (acr : alloc.vec.Vec U32) (defs : alloc.vec.Vec beatmap.mod_settings.SettingDef)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)) (r : beatmap.mod_settings.ModConfig)
    (h : beatmap.mod_settings.to_mod_known acr defs st = ok r) : r.acronym = acr := by
  obtain ⟨v0, hv0, -⟩ := ms_tmk_loop0 defs
  unfold beatmap.mod_settings.to_mod_known at h
  rw [hv0, bind_ok] at h
  simp only [] at h
  split at h
  · simp only [ok.injEq] at h; rw [← h]
  · generalize hL : beatmap.mod_settings.to_mod_known_loop1 acr defs st v0 0#usize = L at h
    cases L <;> simp at h
    all_goals rw [← h]

/-- `to_mod_refines` plus the well-formedness `ev_mcOk` of the result -/
theorem ev_to_mod_ok (a : Slice U32) (ha : ValidStr a) (hal : a.val.length < 2^62)
    (st : Slice (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal))
    (hv : ∀ p ∈ st.val, VValid p.1) (hj : ∀ p ∈ st.val, JOk' p.2) :
    ∃ r, beatmap.mod_settings.to_mod a st = ok r ∧
      mcS r = OsuModel.Beatmap.Settings.toMod (String.ofList (strS a)) (msSetS st.val) ∧ ev_mcOk r := by
  obtain ⟨r, hr, hrv⟩ := beatmap.mod_settings.to_mod_refines a ha st hv hj
  refine ⟨r, hr, hrv, ?_⟩
  obtain ⟨u, hu, hu1, hu2⟩ := ms_to_mod_loop a ha (alloc.vec.Vec.new U32) 0#usize (by simp) (by simp)
    (by intro x hx; simp at hx) (by simp)
  have hul : u.val.length = a.val.length := by
    have := congrArg List.length hu2; simpa [strS] using this
  obtain ⟨o, ho, hov⟩ := beatmap.mod_settings.table_refines (alloc.vec.Vec.deref u) (vvalid_deref u hu1)
  unfold beatmap.mod_settings.to_mod at hr
  simp only [hu, bind_ok, ho] at hr
  cases o with
  | none =>
    obtain ⟨v, hv1, hvv⟩ := beatmap.mod_settings.copy_str_refines a
    simp only [hv1, bind_ok, ok.injEq] at hr
    subst hr
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; simp only [hvv] at hx; exact ha x hx
    · simp only [hvv]; exact hal
    · intro p hp; simp at hp
  | some defs =>
    simp only [Option.map_some] at hov
    have hd : DefsOk defs.val := by
      intro d hdm
      have := ms_table_keys _ _ hov.symm (sdS d) (List.mem_map_of_mem hdm)
      exact (keyName_ne_empty _).mp this
    obtain ⟨r', hr', hk, -⟩ := beatmap.mod_settings.to_mod_known_refines u hu1 defs hd st hv hj
    simp only [hr', ok.injEq] at hr
    subst hr
    have hacr := ev_to_mod_known_acr u defs st r' hr'
    refine ⟨?_, ?_, hk⟩
    · rw [hacr]; exact hu1
    · rw [hacr, hul]; exact hal
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_has_bit_eq (m k : U32) (hk : k.val < 32) :
    eval.osr.has_bit m k = ok (decide ((m.val >>> k.val) % 2 = 1)) := by
  obtain ⟨i, hi, hiv, -⟩ := eq_ok_of_spec (U32.ShiftRight_spec m k hk)
  unfold eval.osr.has_bit
  simp only [hi, bind_ok, lift]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg UScalar.val h
    simp only [UScalar.val_and] at this
    rw [hiv] at this
    simpa [Nat.and_one_is_mod] using this
  · intro h
    apply UScalar.eq_of_val_eq
    simp only [UScalar.val_and]
    rw [hiv]
    simpa [Nat.and_one_is_mod] using h

theorem ev_lit_mod (out : alloc.vec.Vec beatmap.mod_settings.ModConfig) {n : Usize} (arr : Array U8 n)
    (hn : n.val < 2^62) (hout : out.val.length < Usize.max) :
    ∃ o mc, (do
      let s ← lift (Array.to_slice arr)
      let v ← beatmap.dotnet.lit_str s
      let s1 := alloc.vec.Vec.deref v
      let s2 :=
        alloc.vec.Vec.deref (alloc.vec.Vec.new ((alloc.vec.Vec Std.U32) ×
          beatmap.mod_settings.JsonVal))
      let mc ← beatmap.mod_settings.to_mod s1 s2
      alloc.vec.Vec.push out mc) = ok o ∧ o.val = out.val ++ [mc] ∧
      mcS mc = OsuModel.Beatmap.Settings.toMod (String.ofList (arr.val.map (fun x : U8 => Char.ofNat x.val))) [] ∧
      ev_mcOk mc := by
  obtain ⟨v, hv, hvv⟩ := beatmap.dotnet.lit_str_refines (Array.to_slice arr)
  have hvl : v.val.length = n.val := by
    have := congrArg List.length hvv; simp at this; rw [this]
  have hval : ValidStr (alloc.vec.Vec.deref v) := by
    intro u hu
    simp only [ms_deref_val] at hu
    have hu' : u.val ∈ v.val.map (·.val) := List.mem_map_of_mem hu
    rw [hvv] at hu'
    obtain ⟨x, -, hx⟩ := List.mem_map.mp hu'
    have h256 : x.val < 256 := by have := x.hBounds; simpa using this
    rw [← hx]
    simp only [Nat.isValidChar]; left; omega
  obtain ⟨mc, hmc, hmcv, hok⟩ := ev_to_mod_ok (alloc.vec.Vec.deref v) hval (by simp [hvl]; exact hn)
    (alloc.vec.Vec.deref (alloc.vec.Vec.new _)) (by simp) (by simp)
  refine ⟨vpush out mc hout, mc, by simp [lift, hv, hmc, vec_push_ok out mc hout], by simp, ?_, hok⟩
  rw [hmcv]
  congr 1
  · congr 1
    simp only [strS, ms_deref_val]
    have : v.val.map chOf = (v.val.map (·.val)).map Char.ofNat := by simp [chOf, Function.comp_def]
    rw [this, hvv]; simp [Function.comp_def]
end OsuProofs

namespace OsuProofs
open OsuImpl

abbrev ev_LIT (out : alloc.vec.Vec beatmap.mod_settings.ModConfig) {n : Usize} (arr : Array U8 n) :
    Result (alloc.vec.Vec beatmap.mod_settings.ModConfig) :=
  Std.bind (beatmap.dotnet.lit_str (Array.to_slice arr)) fun v =>
  Std.bind (beatmap.mod_settings.to_mod (alloc.vec.Vec.deref v)
    (alloc.vec.Vec.deref (alloc.vec.Vec.new (alloc.vec.Vec U32 × beatmap.mod_settings.JsonVal)))) fun mc =>
  alloc.vec.Vec.push out mc

theorem ev_lit_mod' (out : alloc.vec.Vec beatmap.mod_settings.ModConfig) {n : Usize} (arr : Array U8 n)
    (hn : n.val < 2^62) (hout : out.val.length < Usize.max) (s : String)
    (hs : String.ofList (arr.val.map (fun x : U8 => Char.ofNat x.val)) = s) :
    ∃ o mc, ev_LIT out arr = ok o ∧ o.val = out.val ++ [mc] ∧
      mcS mc = OsuModel.Beatmap.Settings.toMod s [] ∧ ev_mcOk mc := by
  obtain ⟨o, mc, h, h1, h2, h3⟩ := ev_lit_mod out arr hn hout
  refine ⟨o, mc, ?_, h1, by rw [h2, hs], h3⟩
  simpa [lift] using h

theorem ev_blk2 {β} (out : alloc.vec.Vec beatmap.mod_settings.ModConfig) (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    {n1 n2 : Usize} (arr1 : Array U8 n1) (arr2 : Array U8 n2) (s1 s2 : String)
    (hn1 : n1.val < 2^62) (hn2 : n2.val < 2^62)
    (hs1 : String.ofList (arr1.val.map (fun x : U8 => Char.ofNat x.val)) = s1)
    (hs2 : String.ofList (arr2.val.map (fun x : U8 => Char.ofNat x.val)) = s2)
    (hout : out.val.length < Usize.max) (hok : ∀ m ∈ out.val, ev_mcOk m)
    (K : alloc.vec.Vec beatmap.mod_settings.ModConfig → Result β) (Q : β → Prop)
    (h : ∀ O : alloc.vec.Vec beatmap.mod_settings.ModConfig,
      O.val.map mcS = out.val.map mcS ++ (if c1 then [OsuModel.Beatmap.Settings.toMod s1 []]
        else if c2 then [OsuModel.Beatmap.Settings.toMod s2 []] else []) →
      O.val.length ≤ out.val.length + 1 → (∀ m ∈ O.val, ev_mcOk m) → ∃ r, K O = ok r ∧ Q r) :
    ∃ r, Std.bind (if c1 then ev_LIT out arr1 else if c2 then ev_LIT out arr2 else ok out) K = ok r ∧ Q r := by
  obtain ⟨o1, mc1, h1, h1v, h1s, h1o⟩ := ev_lit_mod' out arr1 hn1 hout s1 hs1
  obtain ⟨o2, mc2, h2, h2v, h2s, h2o⟩ := ev_lit_mod' out arr2 hn2 hout s2 hs2
  by_cases hc1 : c1
  · rw [if_pos hc1, h1, bind_ok]
    apply h
    · rw [h1v, if_pos hc1]; simp [h1s]
    · rw [h1v]; simp
    · rw [h1v]; intro m hm; simp at hm; rcases hm with hm | hm
      · exact hok m hm
      · rw [hm]; exact h1o
  · rw [if_neg hc1]
    by_cases hc2 : c2
    · rw [if_pos hc2, h2, bind_ok]
      apply h
      · rw [h2v, if_neg hc1, if_pos hc2]; simp [h2s]
      · rw [h2v]; simp
      · rw [h2v]; intro m hm; simp at hm; rcases hm with hm | hm
        · exact hok m hm
        · rw [hm]; exact h2o
    · rw [if_neg hc2, bind_ok]
      apply h
      · rw [if_neg hc1, if_neg hc2]; simp
      · omega
      · exact hok

theorem ev_blk1 {β} (out : alloc.vec.Vec beatmap.mod_settings.ModConfig) (c1 : Prop) [Decidable c1]
    {n1 : Usize} (arr1 : Array U8 n1) (s1 : String)
    (hn1 : n1.val < 2^62)
    (hs1 : String.ofList (arr1.val.map (fun x : U8 => Char.ofNat x.val)) = s1)
    (hout : out.val.length < Usize.max) (hok : ∀ m ∈ out.val, ev_mcOk m)
    (K : alloc.vec.Vec beatmap.mod_settings.ModConfig → Result β) (Q : β → Prop)
    (h : ∀ O : alloc.vec.Vec beatmap.mod_settings.ModConfig,
      O.val.map mcS = out.val.map mcS ++ (if c1 then [OsuModel.Beatmap.Settings.toMod s1 []] else []) →
      O.val.length ≤ out.val.length + 1 → (∀ m ∈ O.val, ev_mcOk m) → ∃ r, K O = ok r ∧ Q r) :
    ∃ r, Std.bind (if c1 then ev_LIT out arr1 else ok out) K = ok r ∧ Q r := by
  obtain ⟨o1, mc1, h1, h1v, h1s, h1o⟩ := ev_lit_mod' out arr1 hn1 hout s1 hs1
  by_cases hc1 : c1
  · rw [if_pos hc1, h1, bind_ok]
    apply h
    · rw [h1v, if_pos hc1]; simp [h1s]
    · rw [h1v]; simp
    · rw [h1v]; intro m hm; simp at hm; rcases hm with hm | hm
      · exact hok m hm
      · rw [hm]; exact h1o
  · rw [if_neg hc1, bind_ok]
    apply h
    · rw [if_neg hc1]; simp
    · omega
    · exact hok
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_hcast_u32_val (mods : I32) : (i32S mods).toUInt32.toNat = (IScalar.hcast .U32 mods).val := by
  simp only [IScalar.hcast_val_eq]
  show mods.bv.toNat = _
  have hv : (mods.val : Int) = mods.bv.toInt := rfl
  rw [hv, BitVec.toInt_eq_toNat_cond]
  have := mods.bv.isLt
  simp only [UScalarTy.numBits]
  split <;> omega

theorem ev_spec_has (mods : I32) (k : Nat) (hk : k < 32) :
    (((i32S mods).toUInt32 >>> k.toUInt32) &&& 1 == 1) = decide (((IScalar.hcast .U32 mods).val >>> k) % 2 = 1) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← UInt32.toNat_inj]
  simp only [UInt32.toNat_and, UInt32.toNat_shiftRight, ev_hcast_u32_val, Nat.and_one_is_mod]
  have : (k.toUInt32).toNat % 32 = k := by
    simp [Nat.toUInt32, UInt32.toNat_ofNat]; omega
  rw [this]; simp
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_blk1_last (out : alloc.vec.Vec beatmap.mod_settings.ModConfig) (c1 : Prop) [Decidable c1]
    {n1 : Usize} (arr1 : Array U8 n1) (s1 : String)
    (hn1 : n1.val < 2^62)
    (hs1 : String.ofList (arr1.val.map (fun x : U8 => Char.ofNat x.val)) = s1)
    (hout : out.val.length < Usize.max) (hok : ∀ m ∈ out.val, ev_mcOk m)
    (Q : alloc.vec.Vec beatmap.mod_settings.ModConfig → Prop)
    (h : ∀ O : alloc.vec.Vec beatmap.mod_settings.ModConfig,
      O.val.map mcS = out.val.map mcS ++ (if c1 then [OsuModel.Beatmap.Settings.toMod s1 []] else []) →
      O.val.length ≤ out.val.length + 1 → (∀ m ∈ O.val, ev_mcOk m) → Q O) :
    ∃ r, (if c1 then ev_LIT out arr1 else ok out) = ok r ∧ Q r := by
  obtain ⟨o1, mc1, h1, h1v, h1s, h1o⟩ := ev_lit_mod' out arr1 hn1 hout s1 hs1
  by_cases hc1 : c1
  · rw [if_pos hc1, h1]
    refine ⟨_, rfl, ?_⟩
    apply h
    · rw [h1v, if_pos hc1]; simp [h1s]
    · rw [h1v]; simp
    · rw [h1v]; intro m hm; simp at hm; rcases hm with hm | hm
      · exact hok m hm
      · rw [hm]; exact h1o
  · rw [if_neg hc1]
    refine ⟨_, rfl, ?_⟩
    apply h
    · rw [if_neg hc1]; simp
    · omega
    · exact hok

theorem eval.osr.convert_from_legacy_mods_refines (mods : I32) :
    ∃ r, eval.osr.convert_from_legacy_mods mods = ok r ∧
      r.val.map mcS = (OsuModel.Replay.Osr.convertFromLegacyMods (i32S mods)).map (OsuModel.Beatmap.Settings.toMod · []) ∧
      (∀ m ∈ r.val, ev_mcOk m) ∧ r.val.length ≤ 15 := by
  unfold eval.osr.convert_from_legacy_mods
  have hb9 := ev_has_bit_eq (IScalar.hcast .U32 mods) 9#u32 (by simp)
  have hb6 := ev_has_bit_eq (IScalar.hcast .U32 mods) 6#u32 (by simp)
  have hb14 := ev_has_bit_eq (IScalar.hcast .U32 mods) 14#u32 (by simp)
  have hb5 := ev_has_bit_eq (IScalar.hcast .U32 mods) 5#u32 (by simp)
  have hb13 := ev_has_bit_eq (IScalar.hcast .U32 mods) 13#u32 (by simp)
  have hb22 := ev_has_bit_eq (IScalar.hcast .U32 mods) 22#u32 (by simp)
  have hb11 := ev_has_bit_eq (IScalar.hcast .U32 mods) 11#u32 (by simp)
  have hb1 := ev_has_bit_eq (IScalar.hcast .U32 mods) 1#u32 (by simp)
  have hb10 := ev_has_bit_eq (IScalar.hcast .U32 mods) 10#u32 (by simp)
  have hb8 := ev_has_bit_eq (IScalar.hcast .U32 mods) 8#u32 (by simp)
  have hb4 := ev_has_bit_eq (IScalar.hcast .U32 mods) 4#u32 (by simp)
  have hb3 := ev_has_bit_eq (IScalar.hcast .U32 mods) 3#u32 (by simp)
  have hb0 := ev_has_bit_eq (IScalar.hcast .U32 mods) 0#u32 (by simp)
  have hb7 := ev_has_bit_eq (IScalar.hcast .U32 mods) 7#u32 (by simp)
  have hb12 := ev_has_bit_eq (IScalar.hcast .U32 mods) 12#u32 (by simp)
  have hb23 := ev_has_bit_eq (IScalar.hcast .U32 mods) 23#u32 (by simp)
  have hb2 := ev_has_bit_eq (IScalar.hcast .U32 mods) 2#u32 (by simp)
  have hb29 := ev_has_bit_eq (IScalar.hcast .U32 mods) 29#u32 (by simp)
  simp only [lift, bind_ok, hb9, hb6, hb14, hb5, hb13, hb22, hb11, hb1, hb10, hb8, hb4, hb3, hb0, hb7, hb12, hb23, hb2, hb29]
  have hU : 20 < Usize.max := by scalar_tac
  have h0 : (alloc.vec.Vec.new beatmap.mod_settings.ModConfig).val.length = 0 := by simp
  apply ev_blk2 (alloc.vec.Vec.new _) _ _ (Array.make 2#usize [78#u8, 67#u8] (by simp)) (Array.make 2#usize [68#u8, 84#u8] (by simp)) "NC" "DT" (by simp) (by simp) (by decide) (by decide) (by simp; omega) (by simp)
  intro O1 hv1 hl1 hok1
  apply ev_blk2 O1 _ _ (Array.make 2#usize [80#u8, 70#u8] (by simp)) (Array.make 2#usize [83#u8, 68#u8] (by simp)) "PF" "SD" (by simp) (by simp) (by decide) (by decide) (by omega) hok1
  intro O2 hv2 hl2 hok2
  apply ev_blk1 O2 _ (Array.make 2#usize [65#u8, 80#u8] (by simp)) "AP" (by simp) (by decide) (by omega) hok2
  intro O3 hv3 hl3 hok3
  apply ev_blk2 O3 _ _ (Array.make 2#usize [67#u8, 78#u8] (by simp)) (Array.make 2#usize [65#u8, 84#u8] (by simp)) "CN" "AT" (by simp) (by simp) (by decide) (by decide) (by omega) hok3
  intro O4 hv4 hl4 hok4
  apply ev_blk1 O4 _ (Array.make 2#usize [69#u8, 90#u8] (by simp)) "EZ" (by simp) (by decide) (by omega) hok4
  intro O5 hv5 hl5 hok5
  apply ev_blk1 O5 _ (Array.make 2#usize [70#u8, 76#u8] (by simp)) "FL" (by simp) (by decide) (by omega) hok5
  intro O6 hv6 hl6 hok6
  apply ev_blk1 O6 _ (Array.make 2#usize [72#u8, 84#u8] (by simp)) "HT" (by simp) (by decide) (by omega) hok6
  intro O7 hv7 hl7 hok7
  apply ev_blk1 O7 _ (Array.make 2#usize [72#u8, 82#u8] (by simp)) "HR" (by simp) (by decide) (by omega) hok7
  intro O8 hv8 hl8 hok8
  apply ev_blk1 O8 _ (Array.make 2#usize [72#u8, 68#u8] (by simp)) "HD" (by simp) (by decide) (by omega) hok8
  intro O9 hv9 hl9 hok9
  apply ev_blk1 O9 _ (Array.make 2#usize [78#u8, 70#u8] (by simp)) "NF" (by simp) (by decide) (by omega) hok9
  intro O10 hv10 hl10 hok10
  apply ev_blk1 O10 _ (Array.make 2#usize [82#u8, 88#u8] (by simp)) "RX" (by simp) (by decide) (by omega) hok10
  intro O11 hv11 hl11 hok11
  apply ev_blk1 O11 _ (Array.make 2#usize [83#u8, 79#u8] (by simp)) "SO" (by simp) (by decide) (by omega) hok11
  intro O12 hv12 hl12 hok12
  apply ev_blk1 O12 _ (Array.make 2#usize [84#u8, 80#u8] (by simp)) "TP" (by simp) (by decide) (by omega) hok12
  intro O13 hv13 hl13 hok13
  apply ev_blk1 O13 _ (Array.make 2#usize [84#u8, 68#u8] (by simp)) "TD" (by simp) (by decide) (by omega) hok13
  intro O14 hv14 hl14 hok14
  apply ev_blk1_last O14 _ (Array.make 3#usize [83#u8, 86#u8, 50#u8] (by simp)) "SV2" (by simp) (by decide) (by omega) hok14
  intro O15 hv15 hl15 hok15
  refine ⟨?_, hok15, by simp at hl1; omega⟩
  rw [hv15, hv14, hv13, hv12, hv11, hv10, hv9, hv8, hv7, hv6, hv5, hv4, hv3, hv2, hv1]
  simp only [OsuModel.Replay.Osr.convertFromLegacyMods,
    ev_spec_has mods 9 (by norm_num), ev_spec_has mods 6 (by norm_num), ev_spec_has mods 14 (by norm_num), ev_spec_has mods 5 (by norm_num), ev_spec_has mods 13 (by norm_num), ev_spec_has mods 22 (by norm_num), ev_spec_has mods 11 (by norm_num), ev_spec_has mods 1 (by norm_num), ev_spec_has mods 10 (by norm_num), ev_spec_has mods 8 (by norm_num), ev_spec_has mods 4 (by norm_num), ev_spec_has mods 3 (by norm_num), ev_spec_has mods 0 (by norm_num), ev_spec_has mods 7 (by norm_num), ev_spec_has mods 12 (by norm_num), ev_spec_has mods 23 (by norm_num), ev_spec_has mods 2 (by norm_num), ev_spec_has mods 29 (by norm_num)]
  simp [List.map_append, apply_ite (List.map _)]
end OsuProofs

namespace OsuProofs
open OsuImpl

@[step] theorem ev_utf8_cont_spec (x : U8) : eval.osr.utf8_cont x ⦃ _ => True ⦄ := by
  unfold eval.osr.utf8_cont; step*

theorem ev_seq_len_spec (b : Slice U8) (i : Usize) (hi : i.val < b.val.length) (hb : b.val.length + 4 ≤ Usize.max) :
    eval.osr.utf8_seq_len b i ⦃ k => i.val + k.val ≤ b.val.length ⦄ := by
  unfold eval.osr.utf8_seq_len
  step* <;> (try split) <;> step* <;> (try split) <;> step*

theorem ev_utf8_valid_ok (b : Slice U8) (hb : b.val.length + 4 ≤ Usize.max) : ∃ v, eval.osr.utf8_valid b = ok v := by
  unfold eval.osr.utf8_valid eval.osr.utf8_valid_loop
  obtain ⟨y, hy, -⟩ := loop_ok (fun (x : Usize × Bool) => eval.osr.utf8_valid_loop.body b (Slice.len b) x.1 x.2)
    (fun x => 2 * (b.val.length - x.1.val) + (if x.2 then 1 else 0))
    (fun x => x.1.val ≤ b.val.length) (fun _ => True)
    (by
      rintro ⟨i, o⟩ hi
      dsimp only at hi ⊢
      cases o with
      | false => left; exact ⟨false, by simp [eval.osr.utf8_valid_loop.body], trivial⟩
      | true =>
        by_cases hin : i.val < b.val.length
        · right
          obtain ⟨k, hk, hkv⟩ := eq_ok_of_spec (ev_seq_len_spec b i hin hb)
          by_cases hk0 : k.val = 0
          · refine ⟨(i, false), ?_, by simpa using hi, by simp⟩
            simp [eval.osr.utf8_valid_loop.body, (show i < Slice.len b by rw [slice_lt_len_iff]; exact hin), hk,
              show k = 0#usize by scalar_tac]
          · obtain ⟨i1, hi1, hi1v⟩ := eq_ok_of_spec (Usize.add_spec (x := i) (y := k) (by scalar_tac))
            refine ⟨(i1, true), ?_, by simp at hi1v ⊢; omega, by simp at hi1v ⊢; omega⟩
            simp [eval.osr.utf8_valid_loop.body, (show i < Slice.len b by rw [slice_lt_len_iff]; exact hin), hk,
              show ¬ k = 0#usize by scalar_tac, hi1]
        · left
          exact ⟨true, by simp [eval.osr.utf8_valid_loop.body, (show ¬ i < Slice.len b by rw [slice_lt_len_iff]; exact hin)], trivial⟩)
    (0#usize, true) (by simp)
  exact ⟨y, by rw [← hy]⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem ev_seq_len_ascii (b : Slice U8) (i : Usize) (hi : i.val < b.val.length) (hc : (b.val[i.val]'hi).val < 128) :
    eval.osr.utf8_seq_len b i = ok 1#usize := by
  unfold eval.osr.utf8_seq_len
  simp [slice_index_ok b i hi, hc, show ¬ 128 ≤ (b.val[i.val]'hi).val by omega]

theorem ev_seq_len_hi (b : Slice U8) (i : Usize) (hi : i.val < b.val.length) (hc : 245 ≤ (b.val[i.val]'hi).val) :
    eval.osr.utf8_seq_len b i = ok 0#usize := by
  unfold eval.osr.utf8_seq_len
  simp [slice_index_ok b i hi, show ¬ (b.val[i.val]'hi).val < 128 by omega, show ¬ (b.val[i.val]'hi).val < 194 by omega,
    show ¬ (b.val[i.val]'hi).val < 224 by omega, show ¬ (b.val[i.val]'hi).val < 240 by omega,
    show ¬ (b.val[i.val]'hi).val < 245 by omega]

theorem ev_usize_add_lit (a b c : Usize) (h : a.val + b.val = c.val) : a + b = ok c := by
  obtain ⟨v, hv, hvv⟩ := eq_ok_of_spec (Usize.add_spec (x := a) (y := b) (by have := c.hBounds; scalar_tac))
  rw [hv]; congr 1; scalar_tac

theorem ev_utf8_valid_0000FE (b : Slice U8) (h4 : 3 ≤ b.val.length) (h0 : (b.val[0]'(by omega)).val = 0)
    (h1 : (b.val[1]'(by omega)).val = 0) (h2 : (b.val[2]'(by omega)).val = 254) :
    eval.osr.utf8_valid b = ok false := by
  unfold eval.osr.utf8_valid eval.osr.utf8_valid_loop
  have e0 := ev_seq_len_ascii b 0#usize (by simp; omega) (by simp [h0])
  have e1 := ev_seq_len_ascii b 1#usize (by simp; omega) (by simp [h1])
  have e2 := ev_seq_len_hi b 2#usize (by simp; omega) (by simp [h2])
  have l0 : (0#usize : Usize) < Slice.len b := by rw [slice_lt_len_iff]; simp; omega
  have l1 : (1#usize : Usize) < Slice.len b := by rw [slice_lt_len_iff]; simp; omega
  have l2 : (2#usize : Usize) < Slice.len b := by rw [slice_lt_len_iff]; simp; omega
  have a1 := ev_usize_add_lit 0#usize 1#usize 1#usize (by simp)
  have a2 := ev_usize_add_lit 1#usize 1#usize 2#usize (by simp)
  rw [loop_unfold]; simp only [eval.osr.utf8_valid_loop.body, l0, e0, a1, if_true, bind_ok]
  simp only [show ¬ (1#usize : Usize) = 0#usize by decide, if_false, bind_ok]
  rw [loop_unfold]; simp only [eval.osr.utf8_valid_loop.body, l1, e1, a2, if_true, bind_ok]
  simp only [show ¬ (1#usize : Usize) = 0#usize by decide, if_false, bind_ok]
  rw [loop_unfold]; simp only [eval.osr.utf8_valid_loop.body, l2, e2, if_true, bind_ok]
  rw [loop_unfold]; simp [eval.osr.utf8_valid_loop.body]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

def ev_hasBomS (raw : ByteArray) : Bool :=
  match (raw[0]? : Option UInt8), (raw[1]? : Option UInt8) with
  | some b0, some b1 => (b0 == 0xEF && b1 == 0xBB) || (b0 == 0xFE && b1 == 0xFF) || (b0 == 0xFF && b1 == 0xFE)
  | _, _ => false

theorem ev_bytesS_getElem? (b : Slice U8) (i : Nat) (h : i < b.val.length) :
    ((bytesS b)[i]? : Option UInt8) = some (UInt8.ofBitVec (b.val[i]'h).bv) := by
  have hs : i < (bytesS b).size := by rw [bytesS_size]; exact h
  rw [getElem?_pos (bytesS b) i hs]
  congr 1
  apply UInt8.toNat_inj.mp
  rw [ev_bytesS_getElem b i hs h]; simp [UInt8.toNat_ofBitVec]

theorem ev_u8_beq (x : U8) (k : UInt8) : (UInt8.ofBitVec x.bv == k) = decide (x.val = k.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← UInt8.toNat_inj]; simp [UInt8.toNat_ofBitVec]

theorem eval.osr.has_bom_refines (raw : Slice U8) : eval.osr.has_bom raw = ok (ev_hasBomS (bytesS raw)) := by
  unfold eval.osr.has_bom ev_hasBomS
  by_cases hl : 2 ≤ raw.val.length
  · rw [ev_bytesS_getElem? raw 0 (by omega), ev_bytesS_getElem? raw 1 (by omega)]
    simp only [ev_u8_beq]
    have i0 : (0#usize : Usize).val < raw.val.length := by simp; omega
    have i1 : (1#usize : Usize).val < raw.val.length := by simp; omega
    simp only [show Slice.len raw ≥ 2#usize by simp [UScalar.le_equiv]; omega, if_true, slice_index_ok raw _ i0,
      slice_index_ok raw _ i1, bind_ok]
    simp only [show (0#usize : Usize).val = 0 by simp, show (1#usize : Usize).val = 1 by simp]
    split_ifs <;> simp_all
    all_goals (constructor <;> intro h <;> scalar_tac)
  · have h0 : ((bytesS raw)[1]? : Option UInt8) = none := by
      rw [getElem?_neg]; rw [bytesS_size]; omega
    simp only [show ¬ (Slice.len raw ≥ 2#usize) by simp [UScalar.le_equiv]; omega, if_false, h0]
    split <;> simp_all
end OsuProofs

namespace OsuProofs
open OsuModel.Beatmap

theorem ev_iterId_inv {β : Type} (g : β → ForInStep β) (P : β → Prop)
    (h : ∀ b, P b → match g b with | .done c => P c | .yield c => P c) : ∀ n b, P b → P (iterId g n b) := by
  intro n
  induction n with
  | zero => intro b hb; exact hb
  | succ n ih =>
    intro b hb
    have := h b hb
    simp only [iterId]
    revert this
    cases g b with
    | done c => intro hc; exact hc
    | yield c => intro hc; exact ih c hc

theorem ev_decodeUtf8_size (b : ByteArray) (start : Nat) : (decodeUtf8 b start).size ≤ b.size + 4 := by
  rw [decodeUtf8_eq]
  have := ev_iterId_inv (utf8G b) (fun s => s.1.size + start ≤ s.2 ∧ s.2 ≤ b.size + 4 + start)
    (by
      rintro ⟨out, i⟩ ⟨h1, h2⟩
      dsimp only at h1 h2
      unfold utf8G
      dsimp only
      split_ifs <;> simp <;> omega)
    (b.size + 1) (Array.mkEmpty b.size, start) (by simp)
  omega

theorem ev_decodeUtf16_size (b : ByteArray) (start : Nat) (be : Bool) (cs : Array Char)
    (h : decodeUtf16 b start be = some cs) : cs.size ≤ b.size + 4 + start := by
  rw [decodeUtf16_eq] at h
  have := ev_iterId_inv (u16G b be) (fun s => (∀ r, s.1 = some (some r) → r.size ≤ b.size + 4 + start) ∧
      s.2.1.size ≤ s.2.2 ∧ s.2.2 ≤ b.size + 4 + start)
    (by
      rintro ⟨o, out, i⟩ ⟨h0, h1, h2⟩
      dsimp only at h0 h1 h2
      unfold u16G
      dsimp only
      split_ifs <;> simp <;> omega)
    (b.size + 1) (none, #[], start) (by simp)
  revert this h
  generalize iterId (u16G b be) (b.size + 1) (none, #[], start) = r
  rcases r with ⟨o, out, i⟩
  intro h ⟨h0, h1, h2⟩
  cases o with
  | none =>
    have h' : some out = some cs := h
    simp only [Option.some.injEq] at h'; subst h'; simp at h1 h2; omega
  | some o =>
    cases o with
    | none =>
      have h' : (none : Option (Array Char)) = some cs := h
      simp at h'
    | some r =>
      have h' : some r = some cs := h
      simp only [Option.some.injEq] at h'; subst h'; exact h0 _ rfl

theorem ev_srd_size (b : ByteArray) (cs : Array Char) (h : streamReaderDecode b = some cs) : cs.size ≤ b.size + 6 := by
  unfold streamReaderDecode at h
  dsimp only at h
  split_ifs at h
  · have := ev_decodeUtf16_size b 2 true cs h; omega
  · have := ev_decodeUtf16_size b 2 false cs h; omega
  · simp at h; subst h; have := ev_decodeUtf8_size b 3; omega
  · simp at h; subst h; have := ev_decodeUtf8_size b 0; omega
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr OsuModel.Beatmap

/-- the spec `readCompressedText` after the LZMA step -/
def ev_payloadS (raw : ByteArray) : Except String String := do
  let hasBom := match (raw[0]? : Option UInt8), (raw[1]? : Option UInt8) with
    | some b0, some b1 => (b0 == 0xEF && b1 == 0xBB) || (b0 == 0xFE && b1 == 0xFF) || (b0 == 0xFF && b1 == 0xFE)
    | _, _ => false
  if !hasBom then
    if let some s := String.fromUTF8? raw then return s
  match OsuModel.Beatmap.streamReaderDecode raw with
  | some cs => return String.ofList cs.toList
  | none => throw "unsupported text encoding in compressed payload (UTF-32/invalid UTF-16; not modelled)"

theorem ev_readCompressedText_eq (data : ByteArray) : readCompressedText data =
    if data.size < 5 then .error "IOException: input .lzma is too short"
    else if data.size < 13 then .error "IOException: Can't Read 1"
    else match lzmaAloneDecode data maxPayload with
      | .ok r => ev_payloadS r
      | .error e => .error s!"lzma (trusted boundary): {e}" := by
  unfold readCompressedText ev_payloadS
  split_ifs <;> try rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr OsuModel.Beatmap

theorem ev_srd_nobom (B : ByteArray) (hb : ev_hasBomS B = false)
    (hc : ¬ (3 ≤ B.size ∧ B[0]! = 0 ∧ B[1]! = 0 ∧ B[2]! = 0xFE)) :
    streamReaderDecode B = some (decodeUtf8 B 0) := by
  unfold streamReaderDecode
  dsimp only
  rcases Nat.lt_or_ge B.size 2 with h | h
  · simp [show ¬ B.size ≥ 4 by omega, show ¬ B.size ≥ 2 by omega, show ¬ B.size ≥ 3 by omega]
  · have e0 : (B[0]? : Option UInt8) = some B[0]! := by
      rw [getElem?_pos B 0 (by omega), getElem!_pos B 0 (by omega)]
    have e1 : (B[1]? : Option UInt8) = some B[1]! := by
      rw [getElem?_pos B 1 (by omega), getElem!_pos B 1 (by omega)]
    unfold ev_hasBomS at hb
    rw [e0, e1] at hb
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hb
    split_ifs with c1 c2 c3 c4 c5
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c1; exfalso
      simp_all
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c2; exfalso
      exact hc ⟨by omega, c2.1.1.1.2, c2.1.1.2, c2.1.2⟩
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c3; exfalso
      simp_all
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c4; exfalso
      simp_all
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c5; exfalso
      simp_all
    · rfl
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr OsuModel.Beatmap

def ev_srdPart (raw : ByteArray) : Except String String :=
  match streamReaderDecode raw with
  | some cs => .ok (String.ofList cs.toList)
  | none => .error "unsupported text encoding in compressed payload (UTF-32/invalid UTF-16; not modelled)"

theorem ev_payloadS_eq (raw : ByteArray) : ev_payloadS raw =
    if ev_hasBomS raw = false then (match String.fromUTF8? raw with | some s => .ok s | none => ev_srdPart raw)
    else ev_srdPart raw := by
  unfold ev_payloadS ev_srdPart
  have : (match (raw[0]? : Option UInt8), (raw[1]? : Option UInt8) with
    | some b0, some b1 => (b0 == 0xEF && b1 == 0xBB) || (b0 == 0xFE && b1 == 0xFF) || (b0 == 0xFF && b1 == 0xFE)
    | _, _ => false) = ev_hasBomS raw := rfl
  simp only [this]
  cases ev_hasBomS raw
  · simp only [Bool.not_false, if_true]
    cases String.fromUTF8? raw <;> rfl
  · simp only [Bool.not_true]; rfl

def ev_txtRel : core.result.Result (alloc.vec.Vec U32) eval.osr.OsrErr → Except String String → Prop
  | .Ok v, .ok s => String.ofList (v.val.map chOf) = s ∧ ev_VV v
  | .Err _, .error _ => True
  | _, _ => False

theorem ev_srd_branch (raw : Slice U8) (h62 : raw.val.length + 6 < 2^62) (o : Option (alloc.vec.Vec U32))
    (hos : optS o = streamReaderDecode (bytesS raw)) (hov : ∀ c, o = some c → ValidL c.val) :
    ∃ r, (match o with
      | none => ok (core.result.Result.Err eval.osr.OsrErr.Encoding)
      | some cs => ok (core.result.Result.Ok cs)) = ok r ∧ ev_txtRel r (ev_srdPart (bytesS raw)) := by
  unfold ev_srdPart
  cases o with
  | none => rw [← hos]; exact ⟨_, rfl, trivial⟩
  | some cs =>
    refine ⟨_, rfl, ?_⟩
    have hsz := ev_srd_size (bytesS raw) _ hos.symm
    rw [← hos]
    simp only [optS, Option.map_some, ev_txtRel]
    refine ⟨by simp, hov cs rfl, ?_⟩
    rw [bytesS_size] at hsz; simp at hsz; omega

theorem ev_bytesS_getElem! (b : Slice U8) (i : Nat) (h : i < b.val.length) :
    ((bytesS b)[i]! : UInt8) = UInt8.ofBitVec (b.val[i]'h).bv := by
  rw [getElem!_pos (bytesS b) i (by rw [bytesS_size]; exact h)]
  apply UInt8.toNat_inj.mp
  rw [ev_bytesS_getElem b i _ h]; simp [UInt8.toNat_ofBitVec]

theorem eval.osr.decode_payload_text_refines (hU : ev_utf8Fact) (raw : Slice U8)
    (hb : raw.val.length + 4 ≤ Usize.max) (h62 : raw.val.length + 6 < 2^62) :
    ∃ r, eval.osr.decode_payload_text raw = ok r ∧ ev_txtRel r (ev_payloadS (bytesS raw)) := by
  obtain ⟨o, ho, hos, hov⟩ := beatmap.text.stream_reader_decode_refines raw (by omega)
  have hsrd := ev_srd_branch raw h62 o hos hov
  unfold eval.osr.decode_payload_text
  rw [eval.osr.has_bom_refines raw, bind_ok, ev_payloadS_eq]
  cases hB : ev_hasBomS (bytesS raw) with
  | true =>
    simp only [if_true, Bool.true_eq_false, if_false, ho, bind_ok]
    exact hsrd
  | false =>
    simp only [Bool.false_eq_true, if_false, if_true]
    obtain ⟨vb, hvb⟩ := ev_utf8_valid_ok raw hb
    rw [hvb, bind_ok]
    obtain ⟨v, hv, hvs, hvv⟩ := beatmap.text.decode_utf8_refines raw 0#usize
    rw [show (0#usize : Usize).val = 0 by simp] at hvs
    have hvlen : v.val.length ≤ raw.val.length + 4 := by
      have := congrArg Array.size hvs
      simp at this
      have h2 := ev_decodeUtf8_size (bytesS raw) 0
      rw [bytesS_size] at h2
      omega
    cases vb with
    | true =>
      simp only [if_true, hv, bind_ok]
      refine ⟨_, rfl, ?_⟩
      cases hF : String.fromUTF8? (bytesS raw) with
      | some s =>
        obtain ⟨hs, -⟩ := hU _ s hF
        refine ⟨?_, hvv, by omega⟩
        apply String.ext; simp only [String.toList_ofList]
        rw [hs, ← hvs]
      | none =>
        have hc : ¬ (3 ≤ (bytesS raw).size ∧ (bytesS raw)[0]! = 0 ∧ (bytesS raw)[1]! = 0 ∧ (bytesS raw)[2]! = 0xFE) := by
          rintro ⟨h3, h0, h1, h2⟩
          rw [bytesS_size] at h3
          rw [ev_bytesS_getElem! raw 0 (by omega), ← UInt8.toNat_inj] at h0
          rw [ev_bytesS_getElem! raw 1 (by omega), ← UInt8.toNat_inj] at h1
          rw [ev_bytesS_getElem! raw 2 (by omega), ← UInt8.toNat_inj] at h2
          simp [UInt8.toNat_ofBitVec] at h0 h1 h2
          have := ev_utf8_valid_0000FE raw h3 h0 h1 h2
          rw [hvb] at this; simp at this
        simp only [ev_srdPart, ev_srd_nobom _ hB hc]
        refine ⟨?_, hvv, by omega⟩
        rw [← hvs]
    | false =>
      simp only [Bool.false_eq_true, if_false, ho, bind_ok]
      cases hF : String.fromUTF8? (bytesS raw) with
      | none => exact hsrd
      | some s =>
        obtain ⟨hs, hc⟩ := hU _ s hF
        have hsd := ev_srd_nobom _ hB hc
        cases o with
        | none => rw [hsd] at hos; simp [optS] at hos
        | some cs =>
          refine ⟨_, rfl, ?_⟩
          rw [hsd] at hos
          simp only [optS, Option.map_some, Option.some.injEq] at hos
          have hsz := ev_decodeUtf8_size (bytesS raw) 0
          rw [← hos, bytesS_size] at hsz
          simp at hsz
          refine ⟨?_, hov cs rfl, by omega⟩
          apply String.ext; simp only [String.toList_ofList]
          rw [hs, ← hos]
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr OsuModel.Beatmap

theorem ev_payload_max : (USize.ofNat (eval.osr.MAX_PAYLOAD).val) = maxPayload := by
  unfold eval.osr.MAX_PAYLOAD; rfl

theorem ev_bytesS_from (r : ByteArray) (h : (r.data.toList.map fun x => (⟨x.toBitVec⟩ : U8)).length ≤ Usize.max) :
    bytesS (alloc.vec.Vec.deref (alloc.vec.Vec.from (r.data.toList.map fun x => (⟨x.toBitVec⟩ : U8)) h)) = r := by
  simp only [bytesS, ms_deref_val]
  cases r with
  | mk data =>
    congr 1
    simp [alloc.vec.Vec.from, Function.comp_def]
    show (List.map _ (Slice.from _ h).val).toArray = data
    rw [Slice.from_val]; simp [Function.comp_def]

theorem eval.osr.read_compressed_text_refines (hU : ev_utf8Fact) (hL : ev_lzmaBound) (h64 : System.Platform.numBits = 64)
    (data : Slice U8) :
    ∃ r, eval.osr.read_compressed_text data = ok r ∧ ev_txtRel r (readCompressedText (bytesS data)) := by
  rw [ev_readCompressedText_eq, bytesS_size]
  unfold eval.osr.read_compressed_text
  by_cases h5 : data.val.length < 5
  · refine ⟨.Err .LzmaTooShort, by simp [show Slice.len data < 5#usize by simp [UScalar.lt_equiv]; omega], ?_⟩
    rw [if_pos h5]; trivial
  · rw [if_neg h5]
    by_cases h13 : data.val.length < 13
    · refine ⟨.Err .LzmaRead1, by simp [show ¬ Slice.len data < 5#usize by simp [UScalar.lt_equiv]; omega,
        show Slice.len data < 13#usize by simp [UScalar.lt_equiv]; omega], ?_⟩
      rw [if_pos h13]; trivial
    · rw [if_neg h13]
      simp only [show ¬ Slice.len data < 5#usize by simp [UScalar.lt_equiv]; omega,
        show ¬ Slice.len data < 13#usize by simp [UScalar.lt_equiv]; omega, if_false]
      unfold lzma.lzma_alone_decode
      have hbs : lzma.bytesS data.val = bytesS data := rfl
      rw [hbs, ev_payload_max]
      cases hz : lzmaAloneDecode (bytesS data) maxPayload with
      | error e => dsimp only; exact ⟨.Err (.Lzma (lzma.lzmaErrOfMsg e)), by simp, trivial⟩
      | ok r =>
        have hsz := hL _ _ _ hz
        have hmp : maxPayload.toNat = 268435456 := by
          unfold maxPayload; simp [USize.toNat_ofNat, USize.size, h64]
        rw [hmp] at hsz
        have hUm : 268435456 + 8 ≤ Usize.max := by simp [Usize.max, Usize.numBits, h64]
        have hsz' : r.data.size ≤ 268435456 := hsz
        have hl : (r.data.toList.map fun x => (⟨x.toBitVec⟩ : U8)).length ≤ Usize.max := by
          simp only [List.length_map, Array.length_toList]; omega
        dsimp only
        simp only [dif_pos hl, bind_ok]
        have hrl : (alloc.vec.Vec.deref (alloc.vec.Vec.from (r.data.toList.map fun x => (⟨x.toBitVec⟩ : U8)) hl)).val.length
            = r.data.size := by
          simp only [ms_deref_val]
          show (Slice.from _ hl).val.length = _
          rw [Slice.from_val, List.length_map, Array.length_toList]
        obtain ⟨t, ht, hrel⟩ := eval.osr.decode_payload_text_refines hU _ (by rw [hrl]; omega)
          (by rw [hrl]; omega)
        rw [ev_bytesS_from] at hrel
        exact ⟨t, ht, hrel⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr OsuModel.Beatmap

theorem ev_mc_clone (m : beatmap.mod_settings.ModConfig) :
    beatmap.mod_settings.ModConfig.Insts.CoreCloneClone.clone m = ok m := by
  unfold beatmap.mod_settings.ModConfig.Insts.CoreCloneClone.clone
  obtain ⟨s', hs, hss⟩ := eq_ok_of_spec (Slice.clone_spec (clone := (BuiltinClone (U32 × beatmap.mod_settings.SettingValue)).clone)
    (s := m.settings.slice) (by intro x _; rfl))
  rw [clone_vec_u32]
  simp only [bind_ok, lift, core.clone.impls.CloneBool.clone]
  simp only [alloc.vec.CloneVec.clone, hs, bind_ok]
  rw [← hss]; simp

theorem ev_to_vec_mc (s : Slice beatmap.mod_settings.ModConfig) :
    alloc.slice.Slice.to_vec beatmap.mod_settings.ModConfig.Insts.CoreCloneClone s = ok ⟨s⟩ := by
  obtain ⟨v, hv, hvs⟩ := eq_ok_of_spec (alloc.slice.Slice.to_vec_spec beatmap.mod_settings.ModConfig.Insts.CoreCloneClone s
    (by intro x _; exact ev_mc_clone x))
  rw [hv, hvs]



def ev_ftRel : core.result.Result (Option (alloc.vec.Vec U32)) eval.osr.OsrErr → Except String (Option String) → Prop
  | .Ok o, .ok O => o.map vstrS = O ∧ ∀ t, o = some t → ev_VV t
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.frame_text_of_refines (hU : ev_utf8Fact) (hL : ev_lzmaBound) (h64 : System.Platform.numBits = 64)
    (c : eval.osr.Container) :
    ∃ r, eval.osr.frame_text_of c = ok r ∧ ev_ftRel r
      (match (ev_containerS c).compressedReplay with
       | some d => if d.size > 0 then some <$> readCompressedText d else pure none
       | none => pure none) := by
  unfold eval.osr.frame_text_of
  simp only [ev_containerS]
  cases hc : c.compressed_replay with
  | none => refine ⟨_, rfl, ?_⟩; simp only [Option.map_none]; exact ⟨rfl, by simp⟩
  | some d =>
    simp only [Option.map_some]
    have hsz : (bytesS d.slice).size = d.val.length := by rw [bytesS_size]; rfl
    by_cases h0 : 0 < d.val.length
    · rw [if_pos (show (bytesS d.slice).size > 0 by omega)]
      have hd : alloc.vec.Vec.deref d = d.slice := ev_deref_slice d
      obtain ⟨t, ht, hrel⟩ := eval.osr.read_compressed_text_refines hU hL h64 d.slice
      simp only [show alloc.vec.Vec.len d > 0#usize by simp [UScalar.lt_equiv]; omega, if_true, hd, ht, bind_ok]
      revert hrel
      cases t with
      | Err e =>
        cases readCompressedText (bytesS d.slice) with
        | ok _ => intro h; exact h.elim
        | error _ => intro _; exact ⟨_, rfl, trivial⟩
      | Ok v =>
        cases hR : readCompressedText (bytesS d.slice) with
        | error _ => intro h; exact h.elim
        | ok s =>
          intro h; obtain ⟨h1, h2⟩ := h
          refine ⟨_, rfl, ?_⟩
          show Option.map vstrS (some v) = some s ∧ ∀ t, some v = some t → ev_VV t
          refine ⟨?_, ?_⟩
          · simp only [Option.map_some]; rw [← h1]; rfl
          · intro t ht; simp at ht; subst ht; exact h2
    · rw [if_neg (show ¬ (bytesS d.slice).size > 0 by omega)]
      refine ⟨.Ok none, by simp [h0], ?_⟩
      exact ⟨rfl, by simp⟩

def ev_msRel : core.result.Result (alloc.vec.Vec beatmap.mod_settings.ModConfig) eval.osr.OsrErr →
    Except String (List ModConfig) → Prop
  | .Ok ms, .ok MS => ms.val.map mcS = MS ∧ (∀ m ∈ ms.val, ev_mcOk m) ∧ ms.val.length < 2^62
  | .Err _, .error _ => True
  | _, _ => False

theorem eval.osr.mods_of_refines (hU : ev_utf8Fact) (hL : ev_lzmaBound) (hS : ev_scoreInfoOk)
    (h64 : System.Platform.numBits = 64) (c : eval.osr.Container) (bm : Slice beatmap.mod_settings.ModConfig)
    (hbm : ∀ m ∈ bm.val, ev_mcOk m) (hbml : bm.val.length < 2^62) :
    ∃ r, eval.osr.mods_of c bm = ok r ∧ ev_msRel r
      (match (ev_containerS c).compressedScoreInfo with
       | some d => if d.size > 0 then do decodeScoreInfo (← readCompressedText d) else pure (bm.val.map mcS)
       | none => pure (bm.val.map mcS)) := by
  unfold eval.osr.mods_of
  simp only [ev_containerS]
  cases hc : c.compressed_score_info with
  | none =>
    refine ⟨.Ok ⟨bm⟩, by simp [ev_to_vec_mc], ?_⟩
    simp only [Option.map_none]
    exact ⟨rfl, hbm, hbml⟩
  | some d =>
    simp only [Option.map_some]
    have hsz : (bytesS d.slice).size = d.val.length := by rw [bytesS_size]; rfl
    by_cases h0 : 0 < d.val.length
    · rw [if_pos (show (bytesS d.slice).size > 0 by omega)]
      have hd : alloc.vec.Vec.deref d = d.slice := ev_deref_slice d
      obtain ⟨t, ht, hrel⟩ := eval.osr.read_compressed_text_refines hU hL h64 d.slice
      simp only [show alloc.vec.Vec.len d > 0#usize by simp [UScalar.lt_equiv]; omega, if_true, hd, ht, bind_ok]
      revert hrel
      cases t with
      | Err e =>
        cases readCompressedText (bytesS d.slice) with
        | ok _ => intro h; exact h.elim
        | error _ => intro _; exact ⟨_, rfl, trivial⟩
      | Ok v =>
        cases hR : readCompressedText (bytesS d.slice) with
        | error _ => intro h; exact h.elim
        | ok s =>
          intro h; obtain ⟨h1, h2⟩ := h
          show ∃ r, _ = ok r ∧ ev_msRel r (decodeScoreInfo s)
          obtain ⟨r, hr, hrel⟩ := hS (alloc.vec.Vec.deref v) (by intro u hu; exact h2.1 u (by simpa using hu))
            (by simpa using h2.2)
          refine ⟨r, hr, ?_⟩
          have hs : String.ofList (strS (alloc.vec.Vec.deref v)) = s := by rw [← h1]; simp [strS]
          rw [hs] at hrel
          revert hrel
          cases r <;> cases decodeScoreInfo s <;> simp [ev_msRel]
    · rw [if_neg (show ¬ (bytesS d.slice).size > 0 by omega)]
      refine ⟨.Ok ⟨bm⟩, by simp [h0, ev_to_vec_mc], ?_⟩
      exact ⟨rfl, hbm, hbml⟩
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr OsuModel.Beatmap

theorem ev_first_lazer_lt (v : I32) : (v < eval.osr.FIRST_LAZER_VERSION) ↔ v.val < 30000000 := by
  unfold eval.osr.FIRST_LAZER_VERSION; simp [IScalar.lt_equiv]
theorem ev_first_lazer_ltS (v : I32) : (i32S v < OsuModel.Replay.Osr.FIRST_LAZER_VERSION) ↔ v.val < 30000000 := by
  rw [Int32.lt_iff_toInt_lt, i32S_toInt]; simp [OsuModel.Replay.Osr.FIRST_LAZER_VERSION]

def ev_ftS (c : Container) : Except String (Option String) :=
  match c.compressedReplay with
  | some d => if d.size > 0 then some <$> readCompressedText d else pure none
  | none => pure none

def ev_msS (c : Container) (bf : List ModConfig) : Except String (List ModConfig) :=
  match c.compressedScoreInfo with
  | some d => if d.size > 0 then do decodeScoreInfo (← readCompressedText d) else pure bf
  | none => pure bf

theorem ev_E_ite_bind {α β : Type} (c : Prop) [Decidable c] (a b : Except String α) (f : α → Except String β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by split <;> rfl
theorem ev_E_optmatch_bind {α β γ : Type} (o : Option γ) (F : γ → Except String α) (G : Except String α)
    (f : α → Except String β) :
    ((match o with | some d => F d | none => G) >>= f) = (match o with | some d => F d >>= f | none => G >>= f) := by
  cases o <;> rfl
theorem ev_E_ok_bind {α β : Type} (a : α) (f : α → Except String β) : ((Except.ok a : Except String α) >>= f) = f a := rfl
theorem ev_E_map_bind {α β γ : Type} (g : α → γ) (x : Except String α) (f : γ → Except String β) :
    ((g <$> x) >>= f) = x >>= (fun a => f (g a)) := by cases x <;> rfl

theorem ev_decode_eq (bytes : ByteArray) : OsuModel.Replay.Osr.decode bytes = (do
    let c ← parseContainer bytes
    let isLegacyScore := c.version < OsuModel.Replay.Osr.FIRST_LAZER_VERSION
    let legacy := (convertFromLegacyMods c.legacyMods).map (OsuModel.Beatmap.Settings.toMod · [])
    let bitfieldMods := if isLegacyScore then legacy ++ [OsuModel.Beatmap.Settings.toMod "CL" []] else legacy
    let frameText ← ev_ftS c
    let mods ← ev_msS c bitfieldMods
    return { container := c, isLegacyScore, bitfieldMods, mods, frameText }) := by
  unfold OsuModel.Replay.Osr.decode ev_ftS ev_msS
  cases parseContainer bytes with
  | error e => rfl
  | ok c =>
    simp only [ev_E_ok_bind]
    cases hR : c.compressedReplay <;> cases hS : c.compressedScoreInfo <;> simp only [] <;>
      split_ifs <;> simp only [ev_E_map_bind, pure_bind, bind_assoc, ev_E_ok_bind]

theorem eval.osr.decode_refines (hU : ev_utf8Fact) (hL : ev_lzmaBound) (hS : ev_scoreInfoOk)
    (h64 : System.Platform.numBits = 64) (b : Slice U8) (hb : b.val.length < 2^62) :
    ∃ r, eval.osr.decode b = ok r ∧
      (match r, OsuModel.Replay.Osr.decode (bytesS b) with
       | .Ok d, .ok D => ev_dsS d = D ∧ ev_dsOk d
       | .Err _, .error _ => True
       | _, _ => False) := by
  have hUm : 2^62 + 8 ≤ Usize.max := by simp [Usize.max, Usize.numBits, h64]
  obtain ⟨rc, hrc, hrelc⟩ := eval.osr.read_container_refines b (by omega)
  unfold eval.osr.decode eval.osr.parse_container
  rw [ev_decode_eq]
  rw [hrc, bind_ok]
  have hpc : parseContainer (bytesS b) = (fun p => p.1) <$> readContainer (bytesS b) 0 := rfl
  rw [hpc]
  revert hrelc
  cases rc with
  | Err e =>
    cases readContainer (bytesS b) 0 with
    | ok _ => intro h; exact h.elim
    | error _ => intro _; exact ⟨_, rfl, trivial⟩
  | Ok c =>
    cases readContainer (bytesS b) 0 with
    | error _ => intro h; exact h.elim
    | ok Cn =>
      obtain ⟨C, n⟩ := Cn
      intro hC
      simp only [ev_cRel] at hC
      subst hC
      obtain ⟨bm, hbm, hbmv, hbmok, hbml⟩ := eval.osr.convert_from_legacy_mods_refines c.legacy_mods
      simp only [hbm, bind_ok, lift]
      simp only [ev_E_map_bind, ev_E_ok_bind]
      have hcl : (c.version < eval.osr.FIRST_LAZER_VERSION) ↔ (i32S c.version < OsuModel.Replay.Osr.FIRST_LAZER_VERSION) := by
        rw [ev_first_lazer_lt, ev_first_lazer_ltS]
      apply ev_blk1 bm _ (Array.make 2#usize [67#u8, 76#u8] (by simp)) "CL" (by simp) (by decide) (by omega) hbmok
      intro O hO hOl hOok
      obtain ⟨rf, hrf, hrelf⟩ := eval.osr.frame_text_of_refines hU hL h64 c
      have hrelf' : ev_ftRel rf (ev_ftS (ev_containerS c)) := hrelf
      rw [hrf, bind_ok]
      revert hrelf'
      cases rf with
      | Err e =>
        cases ev_ftS (ev_containerS c) with
        | ok _ => intro h; exact h.elim
        | error _ => intro _; exact ⟨_, rfl, trivial⟩
      | Ok o =>
        cases ev_ftS (ev_containerS c) with
        | error _ => intro h; exact h.elim
        | ok OT =>
          intro hft
          obtain ⟨hft1, hft2⟩ := hft
          simp only [ev_E_ok_bind]
          have hOl' : (alloc.vec.Vec.deref O).val.length < 2^62 := by simp; omega
          obtain ⟨rm, hrm, hrelm⟩ := eval.osr.mods_of_refines hU hL hS h64 c (alloc.vec.Vec.deref O)
            (by simpa using hOok) hOl'
          have hrelm' : ev_msRel rm (ev_msS (ev_containerS c) ((alloc.vec.Vec.deref O).val.map mcS)) := hrelm
          have hbf : (if (ev_containerS c).version < OsuModel.Replay.Osr.FIRST_LAZER_VERSION then
              List.map (fun x => Settings.toMod x []) (convertFromLegacyMods (ev_containerS c).legacyMods) ++
                [Settings.toMod "CL" []]
              else List.map (fun x => Settings.toMod x []) (convertFromLegacyMods (ev_containerS c).legacyMods)) =
              (alloc.vec.Vec.deref O).val.map mcS := by
            simp only [ms_deref_val, hO, hbmv, ev_containerS]
            by_cases hv : c.version.val < 30000000
            · have h1 := (ev_first_lazer_ltS c.version).mpr hv
              have h2 := (ev_first_lazer_lt c.version).mpr hv
              simp only [h1, h2, if_true]
            · have h1 : ¬ (i32S c.version < OsuModel.Replay.Osr.FIRST_LAZER_VERSION) := fun h => hv ((ev_first_lazer_ltS _).mp h)
              have h2 : ¬ (c.version < eval.osr.FIRST_LAZER_VERSION) := fun h => hv ((ev_first_lazer_lt _).mp h)
              simp only [h1, h2, if_false, List.append_nil]
          rw [hbf, hrm, bind_ok]
          revert hrelm'
          cases rm with
          | Err e =>
            cases ev_msS (ev_containerS c) ((alloc.vec.Vec.deref O).val.map mcS) with
            | ok _ => intro h; exact h.elim
            | error _ => intro _; exact ⟨_, rfl, trivial⟩
          | Ok ms =>
            cases ev_msS (ev_containerS c) ((alloc.vec.Vec.deref O).val.map mcS) with
            | error _ => intro h; exact h.elim
            | ok MS =>
              intro hms
              obtain ⟨hm1, hm2, hm3⟩ := hms
              refine ⟨_, rfl, ?_⟩
              simp only [ev_E_ok_bind]
              show ev_dsS _ = _ ∧ ev_dsOk _
              have hdl : decide (c.version < eval.osr.FIRST_LAZER_VERSION) =
                  decide (i32S c.version < OsuModel.Replay.Osr.FIRST_LAZER_VERSION) := by
                rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; exact hcl
              refine ⟨?_, ?_⟩
              · simp only [ev_dsS, ms_deref_val, hdl, ev_containerS]
                rw [hm1, ← hft1]
                rfl
              · unfold ev_dsOk
                first
                  | exact ⟨hOok, hm2, fun t ht => hft2 t ht, hm3⟩
                  | exact ⟨hOok, hm2, fun t ht => hft2 t ht⟩
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.env.f_refines (b : U32) : eval.env.f b = ok (Float32.ofBits b.bv.toNat.toUInt32) := by
  simp [eval.env.f, float.F32.from_bits]

theorem eval.env.nd_refines (p : Bool) (px py sx sy rot ox oy : U32) :
    eval.env.nd p px py sx sy rot ox oy = ok ⟨p, ⟨Float32.ofBits px.bv.toNat.toUInt32, Float32.ofBits py.bv.toNat.toUInt32⟩,
      ⟨Float32.ofBits sx.bv.toNat.toUInt32, Float32.ofBits sy.bv.toNat.toUInt32⟩, Float32.ofBits rot.bv.toNat.toUInt32,
      ⟨Float32.ofBits ox.bv.toNat.toUInt32, Float32.ofBits oy.bv.toNat.toUInt32⟩⟩ := by
  simp [eval.env.nd, eval.env.f_refines]

theorem ev_push_small {α} (hU : 100 < Usize.max) (v : alloc.vec.Vec α) (x : α) (h : v.val.length < 100) :
    v.push x = ok (alloc.vec.Vec.from (v.val ++ [x]) (by simp; omega)) := by
  rw [vec_push_ok v x (by omega)]
  congr 1
  apply alloc.vec.Vec.ext; simp


theorem eval.env.mat_refines (a b c d e g h i j : U32) :
    eval.env.mat a b c d e g h i j = ok ⟨Float32.ofBits a.bv.toNat.toUInt32, Float32.ofBits b.bv.toNat.toUInt32,
      Float32.ofBits c.bv.toNat.toUInt32, Float32.ofBits d.bv.toNat.toUInt32, Float32.ofBits e.bv.toNat.toUInt32,
      Float32.ofBits g.bv.toNat.toUInt32, Float32.ofBits h.bv.toNat.toUInt32, Float32.ofBits i.bv.toNat.toUInt32,
      Float32.ofBits j.bv.toNat.toUInt32⟩ := by
  simp [eval.env.mat, eval.env.f_refines]

theorem ev_abs_vfrom {α β} [AbsTo α β] (L : List α) (h : L.length ≤ Usize.max) :
    (abs (alloc.vec.Vec.from L h) : _root_.Array β) = (L.map abs).toArray := by
  show ((alloc.vec.Vec.from L h).val.map abs).toArray = _
  simp
theorem ev_abs_cn (n : sim.geometry.ChainNode) : (abs n : OsuModel.Sim.ChainNode) =
    { typeName := if n.is_pac then simPacName else "", pos := abs n.pos, scale := abs n.scale, rot := n.rot,
      origin := abs n.origin } := rfl

def ev_cnNorm (n : OsuModel.Sim.ChainNode) : OsuModel.Sim.ChainNode :=
  { n with typeName := if n.typeName = simPacName then simPacName else "" }
/-- the spec environment with the chain type names reduced to what the simulation tests (`== PAC`) -/
def ev_envNorm (E : OsuModel.Sim.Env) : OsuModel.Sim.Env :=
  { E with chainFirst := E.chainFirst.map ev_cnNorm, chain := E.chain.map ev_cnNorm }

/-- (D72, final-audit M2(a)) the spec's `defaultEnv` already has only the PAC type name -/
theorem ev_cnNorm_chainNode (nm : String) (px py sx sy rot ox oy : UInt32) :
    ev_cnNorm (OsuModel.Eval.chainNode nm px py sx sy rot ox oy) = OsuModel.Eval.chainNode nm px py sx sy rot ox oy := by
  unfold ev_cnNorm OsuModel.Eval.chainNode
  by_cases h : nm = OsuModel.Eval.pacName <;> simp [h, simPacName, OsuModel.Eval.pacName]

theorem ev_envNorm_defaultEnv : ev_envNorm OsuModel.Eval.defaultEnv = OsuModel.Eval.defaultEnv := by
  unfold ev_envNorm OsuModel.Eval.defaultEnv
  simp only [List.map_toArray, List.map_cons, List.map_nil, ev_cnNorm_chainNode]

theorem eval.env.default_env_refines :
    ∃ e, eval.env.default_env = ok e ∧ abs e = ev_envNorm OsuModel.Eval.defaultEnv := by
  have hU : 100 < Usize.max := by scalar_tac
  unfold eval.env.default_env eval.env.chain_first eval.env.chain
  simp only [eval.env.nd_refines, eval.env.mat_refines, bind_ok, eval.env.f_refines]
  simp only [alloc.vec.Vec.with_capacity]
  simp (config := {maxSteps := 2000000}) only [ev_push_small hU, List.length_append, List.length_cons,
    List.length_nil, List.nil_append, List.cons_append, bind_ok, Nat.reduceAdd, Nat.reduceLT, alloc.vec.Vec.new,
    alloc.vec.Vec.from_val, Slice.from_val]
  refine ⟨_, rfl, ?_⟩
  unfold ev_envNorm OsuModel.Eval.defaultEnv
  show OsuModel.Sim.Env.mk _ _ _ _ _ _ = OsuModel.Sim.Env.mk _ _ _ _ _ _
  congr 1
  all_goals first | rfl | (simp [ev_cnNorm, ev_abs_vfrom, ev_abs_cn, OsuModel.Eval.chainNode, OsuModel.Eval.pacName]; and_intros; all_goals first | rfl | (intro h; exfalso; revert h; decide))
end OsuProofs

namespace OsuProofs
open OsuImpl OsuModel.Replay.Osr

/-- `has_bit m k` is the spec's `has k` (`(m >>> k) &&& 1 == 1`, `convertFromLegacyMods`) on the bit pattern -/
theorem eval.osr.has_bit_refines (m k : U32) (hk : k.val < 32) :
    eval.osr.has_bit m k = ok (decide ((m.val >>> k.val) % 2 = 1)) := ev_has_bit_eq m k hk

theorem eval.osr.parse_container_refines (b : Slice U8) (hb : b.val.length + 8 ≤ Usize.max) :
    ∃ r, eval.osr.parse_container b = ok r ∧
      (match r, parseContainer (bytesS b) with
       | .Ok c, .ok C => ev_containerS c = C
       | .Err _, .error _ => True
       | _, _ => False) := by
  obtain ⟨r, hr, hrel⟩ := eval.osr.read_container_refines b hb
  refine ⟨r, by unfold eval.osr.parse_container; exact hr, ?_⟩
  have hpc : parseContainer (bytesS b) = (fun p => p.1) <$> readContainer (bytesS b) 0 := rfl
  rw [hpc]
  revert hrel
  cases r <;> cases readContainer (bytesS b) 0 <;> simp [ev_cRel, Functor.map, Except.map]
end OsuProofs

namespace OsuProofs
open OsuImpl

theorem eval.env.chain_first_refines :
    ∃ v, eval.env.chain_first = ok v ∧ (abs v : _root_.Array OsuModel.Sim.ChainNode) = (ev_envNorm OsuModel.Eval.defaultEnv).chainFirst := by
  have hU : 100 < Usize.max := by scalar_tac
  unfold eval.env.chain_first
  simp only [eval.env.nd_refines, bind_ok, alloc.vec.Vec.with_capacity]
  simp (config := {maxSteps := 2000000}) only [ev_push_small hU, List.length_append, List.length_cons,
    List.length_nil, List.nil_append, List.cons_append, bind_ok, Nat.reduceAdd, Nat.reduceLT, alloc.vec.Vec.new,
    alloc.vec.Vec.from_val, Slice.from_val]
  refine ⟨_, rfl, ?_⟩
  unfold ev_envNorm OsuModel.Eval.defaultEnv
  simp [ev_cnNorm, ev_abs_vfrom, ev_abs_cn]
  and_intros
  all_goals first | rfl | (intro h; exfalso; revert h; decide)

theorem eval.env.chain_refines :
    ∃ v, eval.env.chain = ok v ∧ (abs v : _root_.Array OsuModel.Sim.ChainNode) = (ev_envNorm OsuModel.Eval.defaultEnv).chain := by
  have hU : 100 < Usize.max := by scalar_tac
  unfold eval.env.chain
  simp only [eval.env.nd_refines, bind_ok, alloc.vec.Vec.with_capacity]
  simp (config := {maxSteps := 2000000}) only [ev_push_small hU, List.length_append, List.length_cons,
    List.length_nil, List.nil_append, List.cons_append, bind_ok, Nat.reduceAdd, Nat.reduceLT, alloc.vec.Vec.new,
    alloc.vec.Vec.from_val, Slice.from_val]
  refine ⟨_, rfl, ?_⟩
  unfold ev_envNorm OsuModel.Eval.defaultEnv
  simp [ev_cnNorm, ev_abs_vfrom, ev_abs_cn]
  and_intros
  all_goals first | rfl | (intro h; exfalso; revert h; decide)
end OsuProofs
