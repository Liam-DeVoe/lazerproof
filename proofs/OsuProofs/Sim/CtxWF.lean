/-
`ev_ctxWF`: the well-formedness of the Rust sim context shared by mk_ctx (concludes it) and run_with (assumes it).
-/
import OsuProofs.Sim.ApplyResult
import OsuProofs.Sim3.SD_Play
open Aeneas Aeneas.Std Result

namespace OsuProofs
open OsuImpl OsuModel.Net

/-- Well-formedness of the Rust simulation context that `run_with` needs and `mk_ctx` establishes (E2E:
`EvalAssumptions.mkCtx` concludes it for the `Ok` case, `EvalAssumptions.runWith` assumes it). It does not mention
`ctx.steps` (eval replaces the steps of an explicit schedule, `ev_ctxWF_steps`). Fields may still be added while
`run_with` is being proved; consumers should use it only abstractly. -/
structure ev_ctxWF (c : sim.state.Ctx) : Prop where
  ar : SimARCtx c
  fuel : c.pb.objects.val.length + 4 ≤ U64.max
  objs_small : c.pb.objects.val.length < 2 ^ 32
  nested_small : ∀ o ∈ c.pb.objects.val, o.nested.val.length < 2 ^ 32
  tail : ∀ i (hi : i < c.pb.objects.val.length), (c.pb.objects.val[i]'hi).h.kind = .Slider →
    ∃ hti : i < c.tail_idx.val.length, (c.tail_idx.val[i]'hti).val < (c.pb.objects.val[i]'hi).nested.val.length
  vis_first : c.cfg.vis_mods.val.length ≤ c.first_obj.val.length
  /-- playfield_update's context facts (corner_pow, ap_frames bound, head indices, slider paths; sim3d) -/
  play : s3d_PCtx c
  /-- `strict_tail` is the strict-tracking tail flag (`type_id = 9`, the adapter's `T_STRICT_TRACKING_SLIDER_TAIL_CIRCLE`);
  with the eval type-name table this is sim7's `s7StrictOk ev_tn c i` (`js_s7StrictOk`, Eval/JsonMkCtxWF) -/
  strict : ∀ i (hi : i < c.pb.objects.val.length) j (hj : j < (c.pb.objects.val[i]'hi).nested.val.length),
    ((c.pb.objects.val[i]'hi).nested.val[j]'hj).strict_tail = (((c.pb.objects.val[i]'hi).nested.val[j]'hj).type_id.val == 9)
  /-- input_phase: the replay frame count fits an `i64` frame index (e2e2) -/
  frames_small : c.frames.val.length < 2 ^ 63
  /-- input_phase: every replay frame has at most 3 actions (`ActList` capacity; `replay::frames::decode`, e2e2) -/
  acts : ∀ f ∈ c.frames.val, f.actions.len.val ≤ 3
  /-- the number of judgement slots (objects + nested) is small (`ev_mkBounds`; sim9's initial `simEmitBud`/`simFutW`) -/
  nsum : (c.pb.objects.val.map (fun o => o.nested.val.length + 1)).sum < 2 ^ 62
  /-- 64-bit platform (`InputBounds.h64`; `usize` budgets of the initial state, sim9) -/
  h64 : System.Platform.numBits = 64
  /-- spinner(-bonus)-tick references belong to spinners (= sim8's `s8TKCtx c`, lifetime_update; from the trusted
  `ev_mkBoundsS` kind conjunct, e2e2) -/
  tk : ∀ r, simRefOk c r → ((simHobj c r).kind = .SpinnerTick ∨ (simHobj c r).kind = .SpinnerBonusTick) →
    ∀ j (hj : j < c.pb.objects.val.length), r.top.val = j → (c.pb.objects.val[j]'hj).h.kind = .Spinner

theorem ev_ctxWF_steps (c : sim.state.Ctx) (st : alloc.vec.Vec schedule.Step) (h : ev_ctxWF c) :
    ev_ctxWF { c with steps := st } :=
  ⟨⟨h.ar.hd, h.ar.pre, h.ar.tkn⟩, h.fuel, h.objs_small, h.nested_small, h.tail, h.vis_first, h.play, h.strict,
    h.frames_small, h.acts, h.nsum, h.h64, h.tk⟩
end OsuProofs
