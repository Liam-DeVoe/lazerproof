/-
Hand-written: Lean meaning of the one opaque function of the end-to-end layer, `crate::lzma::lzma_alone_decode`
(a line-by-line port of the C shim `osu_lzma_alone_decode`, `model/c/lzma_shim.c`, onto the same system liblzma;
docs/proof-pipeline.md §4 "LZMA", D18). It *is* the spec's opaque `OsuModel.Replay.Osr.lzmaAloneDecode` on the same
bytes: an `.ok` payload is the Rust `Ok` vector (a payload longer than `usize::MAX` cannot exist on the machine;
it is mapped to `OutputTooLarge`), an `.error` message is the `LzmaErr` variant with that text (`lzma::message`).
TRUSTED (docs/proof-pipeline.md §4). The exact list is the `axiom` list of EvalFunsExternal_Template.lean.
-/
import Aeneas
import OsuProofs.Generated.EvalTypes
import OsuModel.Replay.Osr
open Aeneas Aeneas.Std Result ControlFlow Error

/-- `lzma::message` inverted (unknown texts: `Other`, the shim's "lzma: decode error"). -/
def lzma.lzmaErrOfMsg (e : String) : lzma.LzmaErr :=
  if e = "lzma: decoder init failed" then .InitFailed
  else if e = "lzma: out of memory" then .OutOfMemory
  else if e = "lzma: output too large" then .OutputTooLarge
  else if e = "lzma: format error" then .Format
  else if e = "lzma: data error" then .Data
  else if e = "lzma: truncated input" then .Truncated
  else .Other

/-- Rust bytes ↦ spec `ByteArray` (same values). -/
def lzma.bytesS (b : List Std.U8) : ByteArray := ⟨(b.map fun x => UInt8.ofBitVec x.bv).toArray⟩

def lzma.lzma_alone_decode (input : Slice Std.U8) (maxOut : Std.Usize) :
    Result (core.result.Result (alloc.vec.Vec Std.U8) lzma.LzmaErr) :=
  match OsuModel.Replay.Osr.lzmaAloneDecode (lzma.bytesS input.val) (USize.ofNat maxOut.val) with
  | .ok r =>
    let l : List Std.U8 := r.data.toList.map fun x => ⟨x.toBitVec⟩
    if h : l.length ≤ Usize.max then ok (.Ok (alloc.vec.Vec.from l h)) else ok (.Err .OutputTooLarge)
  | .error e => ok (.Err (lzma.lzmaErrOfMsg e))
