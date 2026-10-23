//! Rejections of the total simulation (Lean G17, commit `e0e8215`, DECISIONS D15/D16): the spec's `Except String`
//! channel. Each variant names one spec `throw` site; the shell (`simtest_rs`) renders the spec's exact message text
//! (`sim_err_message`), so a rejected input prints the same `{"error":"sim: …"}` line as the Lean `simtest`.
//!
//! The spec's `internal: index … out of range` rejections (`getA`/`setA` on an array whose size is an invariant of the
//! simulation state) are Rust bounds checks (a panic, i.e. Aeneas' `fail`): they are unreachable, and a run whose spec
//! result is `.ok` never fails one (same arrays, same indices). The other `internal:` rejections (fuel exhaustion,
//! missing dictionary entry, HandleHit depth) are explicit `Internal` variants.
use crate::float::F64;
use crate::net::basic::NetExn;
use crate::sim::playable::Kind;

/// Which `internal:` rejection (message text in `simtest_rs`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Internal {
    /// `internal: ReportDelta fuel exhausted`
    ReportDeltaFuel,
    /// `internal: updateBonusScore fuel exhausted`
    BonusFuel,
    /// `internal: ComputeDrainRate fuel exhausted`
    DrainFuel,
    /// `internal: legacy ComputeDrainRate fuel exhausted`
    LegacyDrainFuel,
    /// `internal: HandleHit recursion deeper than the object count`
    HandleHitDepth,
    /// `internal: dead object {i} not in the alive dictionary`
    DeadNotAlive(usize),
    /// `internal: missing slider data` (`need … "slider data"`)
    MissingSliderData,
}

/// A rejection (`Except String` error of the spec).
#[derive(Clone, Copy)]
pub enum SimErr {
    /// `lazer would throw: {repr e}` (`liftNet`, `netStr`, AutoGen `liftN`)
    Net(NetExn),
    /// `lazer would throw: Math.Clamp {repr e} (frame times out of order at {idx})` (`simulateSteps`)
    ClampFrames(NetExn, i64),
    /// `lazer would throw: Math.Clamp {repr e} (drain bounds)` (`HealthSt.drain`)
    ClampDrain(NetExn),
    /// `lazer would throw: Math.Sign {repr e} (ComputeDrainRate)`
    SignDrain(NetExn),
    /// `lazer would throw: Math.Sign {repr e} (SpinnerSpinHistory)` (`reportDelta`)
    SignSpin(NetExn),
    /// `emptyPathMsg`: `lazer would throw: Path.Vertices[0] on an empty slider path (SnakingSliderBody.cs:119)`
    EmptyPath,
    /// `lazer would throw: cumulativeLength[{k}] out of range` (`SliderData.positionAt`)
    CumLen(usize),
    /// `InputBlockingMod: invalid period (start >= end), lazer throws`
    PeriodInvalid,
    /// `InputBlockingMod: break without a following object, lazer throws`
    PeriodNoFollowing,
    /// `malformed playable: slider at {start} without a {repr k}` (`mkCtx`)
    SliderWithout(F64, Kind),
    /// `malformed: slider without slider data` (AutoGen `addClickFrames`)
    NoSliderData,
    /// `schedule: dense reference list exceeds 1e8 entries`
    DenseFuel,
    /// `schedule: step fuel exhausted`
    StepFuel,
    /// `autogen: fuel exhausted in {what}`: 0 = `time < h.start`, 1 = `nextFrame < endT`, 2 = `j < sd.duration`
    AutogenFuel(u8),
    /// `internal: …`
    Internal(Internal),
}

/// `liftNet` on a `Result<_, NetExn>`
pub fn lift_net<T>(e: Result<T, NetExn>) -> Result<T, SimErr> {
    match e {
        Ok(v) => Ok(v),
        Err(x) => Err(SimErr::Net(x)),
    }
}
