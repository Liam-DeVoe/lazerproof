/-
Discharge of two `EvalAssumptions` facts (Eval/E2EBase.lean, eval agent) by the json agent's proofs:
`utf8` (`ev_utf8Fact`, from Eval/JsonUtf8.lean) and, under 64-bit, `scoreInfo` (`ev_scoreInfoOk`, from
Eval/JsonScore.lean + Eval/JsonSize.lean). The EndToEnd owner can now drop these fields (or instantiate them).
-/
import OsuProofs.Eval.E2EBase
import OsuProofs.Eval.JsonSize
import OsuProofs.Eval.JsonUtf8
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl

theorem js_ev_utf8 : ev_utf8Fact := js_utf8Fact

theorem js_ev_scoreInfo (h64 : System.Platform.numBits = 64) : ev_scoreInfoOk := by
  intro text hs h62
  obtain ⟨r, hr, hrel⟩ := js_scoreInfoOk h64 text hs h62
  exact ⟨r, hr, hrel⟩

end OsuProofs
