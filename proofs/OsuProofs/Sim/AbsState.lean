/-
Abstraction maps (`AbsTo`) of the simulation state (`sim::state::{Ctx, St, OState, Inst}`, transforms, geometry
environment, replay frames, schedule steps) to the spec (`OsuModel.Sim` State/Transforms/Geometry/Schedule,
`OsuModel.Replay.Frames`). Representation choices (docs/rust-sim-port.md "Correspondence"):
* `ActList { items, len }` ↦ the first `len` items (`List Action` / `Array Action`);
* LIFO lists (`St.freeList`, `St.pools[k]`, `St.asSeen[k]`): Rust `Vec` with the head at the END ↦ spec `List` with
  the head first (`.reverse`);
* `ChainNode.typeName` ↦ `is_pac` (the only test is `== "OsuPlayfieldAdjustmentContainer"`);
* the spec's `Ctx.futureOrder` is the Rust `St.future_order` (filled by `initState`): `simCtxS c fo`;
* `St.dbg` (debug trace, never written in non-debug runs) ↦ `#[]`; `JRec.typeName` and `HObj.typeName` use the
  shell's type-name table `tn` (`simStS tn`, `simCtxS tn`).
-/
import OsuProofs.Sim.Abs
open Aeneas Aeneas.Std Result
open OsuModel.Net

namespace OsuProofs
open OsuImpl

/-! ## Replay frames, schedule -/
def actS : replay.frames.Action → OsuModel.Replay.Action
  | .Left => .left | .Right => .right | .Smoke => .smoke
instance : AbsTo replay.frames.Action OsuModel.Replay.Action := ⟨actS⟩
def actListS (l : replay.frames.ActList) : List OsuModel.Replay.Action := (l.items.val.take l.len.val).map actS
instance : AbsTo replay.frames.ActList (List OsuModel.Replay.Action) := ⟨actListS⟩
instance : AbsTo replay.frames.ActList (_root_.Array OsuModel.Replay.Action) := ⟨fun l => (actListS l).toArray⟩
instance : AbsTo replay.frames.Frame OsuModel.Replay.Frame := ⟨fun f => ⟨f.time, abs f.pos, actListS f.actions⟩⟩
instance : AbsTo schedule.Step OsuModel.Sim.Step := ⟨fun s => ⟨s.time, s.frame_index.val⟩⟩

/-! ## Geometry environment -/
def simPacName : String := "OsuPlayfieldAdjustmentContainer"
instance : AbsTo sim.geometry.ChainNode OsuModel.Sim.ChainNode :=
  ⟨fun n => { typeName := if n.is_pac then simPacName else "", pos := abs n.pos, scale := abs n.scale, rot := n.rot
              origin := abs n.origin }⟩
instance : AbsTo sim.geometry.Env OsuModel.Sim.Env :=
  ⟨fun e => { hocFirst := abs e.hoc_first, hoc := abs e.hoc, argonPathRadius := e.argon_path_radius
              hocSize := abs e.hoc_size, chainFirst := abs e.chain_first, chain := abs e.chain }⟩
instance : AbsTo sim.geometry.SliderGeom OsuModel.Sim.SliderGeom :=
  ⟨fun g => ⟨g.path_radius, abs g.size, abs g.origin, abs g.draw_info, abs g.head_receptor⟩⟩
instance : AbsTo sim.geometry.Placement OsuModel.Sim.Placement := ⟨fun p => ⟨abs p.pos, abs p.scale, p.rot⟩⟩
instance : AbsTo sim.geometry.SpinnerGeom OsuModel.Sim.SpinnerGeom := ⟨fun g => ⟨abs g.aspect, abs g.tracker_size⟩⟩

/-! ## Transforms -/
def memberS : sim.transforms.Member → OsuModel.Sim.Member
  | .Position => .position | .Scale => .scale | .Rotation => .rotation | .Alpha => .alpha
instance : AbsTo sim.transforms.Member OsuModel.Sim.Member := ⟨memberS⟩
instance : AbsTo net.framework.Easing OsuModel.Net.Framework.Easing := ⟨easingS⟩
instance : AbsTo sim.transforms.Tr OsuModel.Sim.Tr :=
  ⟨fun t => { id := t.id.val, member := memberS t.member, start := t.start, endT := t.end_t, sv := abs t.sv
              ev := abs t.ev, easing := easingS t.easing, offset := t.offset.map abs, applied := t.applied
              appliedToEnd := t.applied_to_end, hasStart := t.has_start }⟩
instance : AbsTo sim.transforms.Tracker OsuModel.Sim.Tracker :=
  ⟨fun t => { member := memberS t.member, ts := abs t.ts, counter := t.counter.val, lastApplied := t.last_applied.val }⟩
instance : AbsTo sim.transforms.TObj OsuModel.Sim.TObj :=
  ⟨fun o => { pos := abs o.pos, scale := abs o.scale, rot := o.rot, alpha := o.alpha, trackers := abs o.trackers
              lastUpdate := o.last_update, delay := o.delay }⟩

/-! ## Per-object state -/
def lifeS : sim.state.Life → OsuModel.Sim.Life | .Future => .future | .Alive => .alive | .Past => .past
instance : AbsTo sim.state.Life OsuModel.Sim.Life := ⟨lifeS⟩
def armedS : sim.state.Armed → OsuModel.Sim.Armed | .Idle => .idle | .Hit => .hit | .Miss => .miss
instance : AbsTo sim.state.Armed OsuModel.Sim.Armed := ⟨armedS⟩
instance : AbsTo sim.state.Res OsuModel.Sim.Res := ⟨fun r => (hrS r.ty, r.time)⟩
instance : AbsTo sim.state.Inst OsuModel.Sim.Inst :=
  ⟨fun i => { tf := abs i.tf, loaded := i.loaded, boundPos := abs i.bound_pos, boundStack := i.bound_stack.val
              boundScale := i.bound_scale, size := abs i.size, origin := abs i.origin, relAnchor := abs i.rel_anchor
              bodySize := abs i.body_size, bodyOffset := abs i.body_offset, bodyRadius := i.body_radius
              refreshPending := i.refresh_pending, bodyTf := abs i.body_tf, bodyLoaded := i.body_loaded
              drawableTracking := i.drawable_tracking, armed := armedS i.armed, ballPos := abs i.ball_pos }⟩
def ostateS (o : sim.state.OState) : OsuModel.Sim.OState :=
  { life := lifeS o.life, lifetimeStart := o.lifetime_start, lifetimeEnd := o.lifetime_end, childId := o.child_id.val
    result := o.result.map abs, nested := (o.nested.val.map (·.map abs)).toArray, hitAction := o.hit_action.map actS
    hovered := o.hovered, headLifetimeEnd := o.head_lifetime_end, headAlive := o.head_alive, tracking := o.tracking
    inst := o.inst.val, headInst := o.head_inst.val, armed := armedS o.armed, headArmed := armedS o.head_armed
    tickInsts := abs o.tick_insts, tickLive := abs o.tick_live, acceptAnyAfter := o.accept_any_after
    lastPressed := actListS o.last_pressed, sliderMouse := o.slider_mouse.map abs, spinTracking := o.spin_tracking
    spinMouse := o.spin_mouse.map abs, lastAngle := o.last_angle, totalAccumulated := o.total_accumulated
    accumulatedAtLastCompletion := o.accumulated_at_last_completion, currentSpinMax := o.current_spin_max
    completedSpins := o.completed_spins.val, lastReportTime := o.last_report_time
    completedFullSpins := o.completed_full_spins.val }
instance : AbsTo sim.state.OState OsuModel.Sim.OState := ⟨ostateS⟩

def jrecS (tn : Nat → String) (j : sim.state.JRec) : OsuModel.Sim.JRec :=
  { top := j.top.val, nested := j.nested.val, kind := kindS j.kind, typeName := tn j.type_id.val, result := hrS j.result
    time := j.time, combo := j.combo.val, health := j.health, failed := j.failed, comboRP := j.combo_rp.val
    healthRP := j.health_rp, failedRP := j.failed_rp }
instance : AbsTo sim.step.Ref (Nat × Int) := ⟨fun r => (r.top.val, r.nested.val)⟩

/-! ## Context and state -/
/-- `Ctx` with the shell's type-name table `tn` and the future order `fo` (Rust: `St.future_order`). -/
def simCtxS (tn : Nat → String) (fo : alloc.vec.Vec Usize) (c : sim.state.Ctx) : OsuModel.Sim.Ctx :=
  { env := abs c.env, cfg := abs c.cfg, pb := playableS tn c.pb, frames := abs c.frames, steps := abs c.steps
    futureOrder := abs fo, headIdx := abs c.head_idx, tailIdx := abs c.tail_idx, smax := abs c.smax
    hcfg := abs c.hcfg, lastFrameTime := c.last_frame_time, firstObj := abs c.first_obj
    precEnd := (c.prec_end.val.map fun p => (p.top, (p.nested.val).toArray)).toArray
    apFrames := (c.ap_frames.val.map fun a => (a.time, (abs a.pos : OsuModel.Sim.Vec2))).toArray
    blockPeriods := abs c.block_periods }

def simStS (tn : Nat → String) (s : sim.state.St) : OsuModel.Sim.St :=
  { k := s.k.val, t := s.t, objs := abs s.objs, firstLifetimeUpdate := s.first_lifetime_update
    nextFuture := s.next_future.val, futureOrder := abs s.future_order, active := abs s.active
    dictSlots := abs s.dict_slots, freeList := (s.free_list.val.map (·.val)).reverse, childCounter := s.child_counter.val
    mouseValid := s.mouse_valid, mouse := abs s.mouse, lastReplay := s.last_replay.map actListS
    pressed := (actListS s.pressed).toArray, score := abs s.score, health := abs s.health, scoreRP := abs s.score_rp
    healthRP := abs s.health_rp, out := (s.out.val.map (jrecS tn)).toArray, speed := abs s.speed
    asTarget := abs s.as_target, asRecent := abs s.as_recent
    asSeen := (s.as_seen.val.map fun l => (l.val.map (fun r => (abs r : Nat × Int))).reverse).toArray
    clockRate := s.clock_rate, relaxDown := s.relax_down, relaxWasLeft := s.relax_was_left, relaxLast := s.relax_last
    apFrame := s.ap_frame.val, blockLast := (s.block_last.val.map (·.map actS)).toArray, blockIdx := abs s.block_idx
    insts := abs s.insts, pools := (s.pools.val.map fun l => (l.val.map (·.map (·.val))).reverse).toArray
    brRot := s.br_rot, theta := s.theta, cursorPos := abs s.cursor_pos, dbg := #[] }

end OsuProofs
