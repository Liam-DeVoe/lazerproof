//! Simulation state. Spec: `model/OsuModel/Sim/State.lean` (`OState`, `JRec`, `Ctx`, `St`).
//! The spec's `SimM := ReaderT Ctx (StateM St)` becomes `(c: &Ctx, s: &mut St)` parameters.
use crate::float::{F32, F64};
use crate::replay::frames::{Action, ActList, Frame, ACTLIST_EMPTY};
use crate::sim::basic::{HitResult, Vec2, VEC2_ZERO};
use crate::sim::geometry::Env;
use crate::sim::mods::Config;
use crate::sim::playable::{Kind, Playable};
use crate::sim::schedule::Step;
use crate::sim::scoring::{HealthCfg, HealthSt, ScoreMax, ScoreSt};
use crate::sim::transforms::{tobj_new, TObj};
use alloc::vec::Vec;

/// `Life`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Life {
    Future,
    Alive,
    Past,
}

/// `Armed` (`DrawableHitObject.State`)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Armed {
    Idle,
    Hit,
    Miss,
}

/// `Inst`: a pooled drawable instance
#[derive(Clone)]
pub struct Inst {
    pub tf: TObj,
    pub loaded: bool,
    pub bound_pos: Vec2,
    pub bound_stack: i64,
    pub bound_scale: F32,
    pub size: Vec2,
    pub origin: Vec2,
    pub rel_anchor: Vec2,
    pub body_size: Vec2,
    pub body_offset: Vec2,
    pub body_radius: F32,
    pub refresh_pending: bool,
    pub body_tf: TObj,
    pub body_loaded: bool,
    pub drawable_tracking: bool,
    pub armed: Armed,
    pub ball_pos: Vec2,
}

/// `{} : Inst`
pub fn inst_new() -> Inst {
    Inst {
        tf: tobj_new(F32::from_bits(0)),
        loaded: false,
        bound_pos: VEC2_ZERO,
        bound_stack: 0,
        bound_scale: F32::from_bits(0),
        size: VEC2_ZERO,
        origin: VEC2_ZERO,
        rel_anchor: VEC2_ZERO,
        body_size: VEC2_ZERO,
        body_offset: VEC2_ZERO,
        body_radius: F32::from_bits(0),
        refresh_pending: false,
        body_tf: tobj_new(F32::from_bits(0x3F80_0000)),
        body_loaded: false,
        drawable_tracking: false,
        armed: Armed::Idle,
        ball_pos: VEC2_ZERO,
    }
}

/// `poolInitial`
pub const POOL_INITIAL: [usize; 6] = [20, 20, 20, 2, 10, 10];
/// `poolMax`
pub const POOL_MAX: [usize; 6] = [100, 100, 100, 20, 200, 200];

/// `Res` = `(Type, RawTime)`
#[derive(Clone, Copy)]
pub struct Res {
    pub ty: HitResult,
    pub time: F64,
}

/// `OState`
#[derive(Clone)]
pub struct OState {
    pub life: Life,
    pub lifetime_start: F64,
    pub lifetime_end: F64,
    pub child_id: u64,
    pub result: Option<Res>,
    pub nested: Vec<Option<Res>>,
    pub hit_action: Option<Action>,
    pub hovered: bool,
    pub head_lifetime_end: F64,
    pub head_alive: bool,
    pub tracking: bool,
    /// pooled instances in use (top-level DHO, slider head DHO)
    pub inst: usize,
    pub head_inst: usize,
    pub armed: Armed,
    pub head_armed: Armed,
    pub tick_insts: Vec<usize>,
    pub tick_live: Vec<bool>,
    pub accept_any_after: Option<F64>,
    pub last_pressed: ActList,
    pub slider_mouse: Option<Vec2>,
    pub spin_tracking: bool,
    pub spin_mouse: Option<Vec2>,
    pub last_angle: Option<F32>,
    pub total_accumulated: F32,
    pub accumulated_at_last_completion: F32,
    pub current_spin_max: F32,
    pub completed_spins: u64,
    pub last_report_time: F64,
    pub completed_full_spins: i64,
}

/// `JRec`
#[derive(Clone, Copy)]
pub struct JRec {
    pub top: usize,
    pub nested: i64,
    pub kind: Kind,
    pub type_id: u32,
    pub result: HitResult,
    pub time: F64,
    pub combo: u64,
    pub health: F64,
    pub failed: bool,
    pub combo_rp: u64,
    pub health_rp: F64,
    pub failed_rp: bool,
}

/// `Ctx`
pub struct Ctx {
    pub env: Env,
    pub cfg: Config,
    pub pb: Playable,
    pub frames: Vec<Frame>,
    pub steps: Vec<Step>,
    /// per slider: index of the head / tail in `nested` (`mkCtx` rejects a slider without one; 0 for other objects)
    pub head_idx: Vec<usize>,
    pub tail_idx: Vec<usize>,
    pub smax: ScoreMax,
    pub hcfg: HealthCfg,
    pub last_frame_time: Option<F64>,
    /// `receptorCornerRadiusPow` (a closed term in the spec, computed once here)
    pub corner_pow: F64,
    /// `precEnd` (`ModAdaptiveSpeed.precedingEndTimes`, only with AS)
    pub prec_end: Vec<PrecEnd>,
    /// `apFrames` (Autopilot: `OsuAutoGenerator` frames)
    pub ap_frames: Vec<ApFrame>,
    /// `blockPeriods` (`InputBlockingMod.nonGameplayPeriods`)
    pub block_periods: Vec<crate::sim::playable::Period>,
    /// `firstObj`: per `Config.visMods` entry, the top-level object containing `FirstObject`
    pub first_obj: Vec<Option<usize>>,
}

/// one entry of `precEnd`: (top-level, nested)
#[derive(Clone)]
pub struct PrecEnd {
    pub top: Option<F64>,
    pub nested: Vec<Option<F64>>,
}

/// one entry of `apFrames`: (time, gamefield position)
#[derive(Clone, Copy)]
pub struct ApFrame {
    pub time: F64,
    pub pos: Vec2,
}

/// `St`
#[derive(Clone)]
pub struct St {
    pub k: usize,
    pub t: F64,
    pub objs: Vec<OState>,
    pub first_lifetime_update: bool,
    pub next_future: usize,
    pub future_order: Vec<usize>,
    pub active: Vec<usize>,
    /// `dictSlots` (`None` = free slot)
    pub dict_slots: Vec<Option<usize>>,
    /// `freeList` (most recently freed = LAST element here, = head of the spec's list)
    pub free_list: Vec<usize>,
    pub child_counter: u64,
    pub mouse_valid: bool,
    pub mouse: Vec2,
    pub last_replay: Option<ActList>,
    pub pressed: ActList,
    pub score: ScoreSt,
    pub health: HealthSt,
    pub score_rp: ScoreSt,
    pub health_rp: HealthSt,
    pub out: Vec<JRec>,
    /// `speed`: `SpeedChange` of each time-varying rate mod
    pub speed: Vec<F64>,
    /// `asTarget`, `asRecent`, `asSeen` (per AS mod)
    pub as_target: Vec<F64>,
    pub as_recent: Vec<Vec<F64>>,
    pub as_seen: Vec<Vec<crate::sim::step::Ref>>,
    pub clock_rate: F64,
    /// `relaxDown`, `relaxWasLeft`, `relaxLast`
    pub relax_down: bool,
    pub relax_was_left: bool,
    pub relax_last: F64,
    /// `apFrame`
    pub ap_frame: i64,
    /// `blockLast`, `blockIdx` (per input-blocking mod)
    pub block_last: Vec<Option<Action>>,
    pub block_idx: Vec<usize>,
    /// pooled instances; per pool a LIFO stack (top = last element; `None` = a never-used prewarmed instance)
    pub insts: Vec<Inst>,
    pub pools: Vec<Vec<Option<usize>>>,
    /// BarrelRoll: `OsuPlayfieldAdjustmentContainer.Rotation`
    pub br_rot: F32,
    /// `OsuModTransform.theta`
    pub theta: F32,
    /// `Playfield.Cursor.ActiveCursor.DrawPosition`
    pub cursor_pos: Vec2,
}

/// A fresh `OState` (the spec's structure defaults + `lifetimeStart/End`, `nested`)
pub fn ostate_init(lifetime_start: F64, lifetime_end: F64, n_nested: usize) -> OState {
    let mut nested: Vec<Option<Res>> = Vec::new();
    let mut i: usize = 0;
    while i < n_nested {
        nested.push(None);
        i += 1;
    }
    OState {
        life: Life::Future,
        lifetime_start,
        lifetime_end,
        child_id: 0,
        result: None,
        nested,
        hit_action: None,
        hovered: false,
        head_lifetime_end: crate::sim::netx::F64_POS_INF,
        head_alive: false,
        tracking: false,
        inst: 0,
        head_inst: 0,
        armed: Armed::Idle,
        head_armed: Armed::Idle,
        tick_insts: Vec::new(),
        tick_live: Vec::new(),
        accept_any_after: None,
        last_pressed: ACTLIST_EMPTY,
        slider_mouse: None,
        spin_tracking: false,
        spin_mouse: None,
        last_angle: None,
        total_accumulated: F32::from_bits(0),
        accumulated_at_last_completion: F32::from_bits(0),
        current_spin_max: F32::from_bits(0),
        completed_spins: 0,
        last_report_time: crate::sim::netx::F64_NEG_INF,
        completed_full_spins: 0,
    }
}

pub const MOUSE_INIT: Vec2 = VEC2_ZERO;
