//! Replay frames: `.osr` frame text → `OsuReplayFrame` list.
//! Spec: `model/OsuModel/Replay/Frames.lean` (namespace `OsuModel.Replay`).
//! The text is given as Unicode scalar values (the decompressed LZMA payload, decoded as UTF-8).
use crate::float::{F32, F64};
use crate::net::basic::NetExn;
use crate::net::parse;
use crate::sim::basic::Vec2;
use alloc::vec::Vec;

/// `Action` (`OsuAction`: Left, Right, Smoke)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Action {
    Left,
    Right,
    Smoke,
}

/// A short ordered list of distinct actions (the spec's `List Action` / `Array Action` of
/// replay states, pressed actions etc.; at most 3 elements since there are 3 actions and every
/// such list is duplicate-free).
#[derive(Clone, Copy)]
pub struct ActList {
    pub items: [Action; 3],
    pub len: usize,
}

pub const ACTLIST_EMPTY: ActList = ActList { items: [Action::Left, Action::Left, Action::Left], len: 0 };

/// `List.contains`
pub fn act_contains(l: &ActList, a: Action) -> bool {
    let mut i: usize = 0;
    let mut found = false;
    while i < l.len {
        if l.items[i] == a {
            found = true;
        }
        i += 1;
    }
    found
}

/// `push` (callers guarantee `a` is not contained, so `len < 3`)
pub fn act_push(l: ActList, a: Action) -> ActList {
    let mut r = l;
    if r.len < 3 {
        r.items[r.len] = a;
        r.len += 1;
    }
    r
}

/// `filter (· != a)`
pub fn act_remove(l: ActList, a: Action) -> ActList {
    let mut r = ACTLIST_EMPTY;
    let mut i: usize = 0;
    while i < l.len {
        if l.items[i] != a {
            r = act_push(r, l.items[i]);
        }
        i += 1;
    }
    r
}

/// `l.filter (!other.contains ·)`
pub fn act_minus(l: &ActList, other: &ActList) -> ActList {
    let mut r = ACTLIST_EMPTY;
    let mut i: usize = 0;
    while i < l.len {
        if !act_contains(other, l.items[i]) {
            r = act_push(r, l.items[i]);
        }
        i += 1;
    }
    r
}

/// `List` equality
pub fn act_eq(a: &ActList, b: &ActList) -> bool {
    if a.len != b.len {
        false
    } else {
        let mut i: usize = 0;
        let mut same = true;
        while i < a.len {
            if a.items[i] != b.items[i] {
                same = false;
            }
            i += 1;
        }
        same
    }
}

/// `Frame` (`OsuReplayFrame`)
#[derive(Clone, Copy)]
pub struct Frame {
    pub time: F64,
    pub pos: Vec2,
    pub actions: ActList,
}

/// `LegacyFrame` (`LegacyReplayFrame`)
#[derive(Clone, Copy)]
pub struct LegacyFrame {
    pub time: F64,
    pub mouse_x: F32,
    pub mouse_y: F32,
    pub buttons: i32,
}

/// `intTryParse`
pub fn int_try_parse(s: &[u32], a: usize, b: usize) -> Option<i32> {
    match parse::int_parse(&s[a..b]) {
        Ok(v) => Some(v),
        Err(_) => None,
    }
}

/// `F32.ofInt32 Parsing.MAX_COORDINATE_VALUE` = 131072f
pub const MAX_COORDINATE_F32: F32 = F32::from_bits(0x4800_0000);

/// `"-12345"` as code points
const SKIP_MARKER: [u32; 6] = [0x2D, 0x31, 0x32, 0x33, 0x34, 0x35];

/// `s[a..b] == "-12345"`
pub fn is_skip_marker(s: &[u32], a: usize, b: usize) -> bool {
    if b - a != 6 {
        false
    } else {
        let mut i: usize = 0;
        let mut same = true;
        while i < 6 {
            if s[a + i] != SKIP_MARKER[i] {
                same = false;
            }
            i += 1;
        }
        same
    }
}

const C_PIPE: u32 = 0x7C;
const C_COMMA: u32 = 0x2C;

/// Field boundaries of one frame `fr.splitOn "|"`: the first four fields' ends (`None` if fewer than 4 fields).
pub fn split_fields(s: &[u32], a: usize, b: usize) -> Option<[usize; 4]> {
    let mut ends: [usize; 4] = [b, b, b, b];
    let mut k: usize = 0;
    let mut i = a;
    while i < b && k < 3 {
        if s[i] == C_PIPE {
            ends[k] = i;
            k += 1;
        }
        i += 1;
    }
    if k < 3 {
        None
    } else {
        // field 3 ends at the next '|' or at the end of the frame
        let mut j = i;
        let mut found = false;
        while j < b && !found {
            if s[j] == C_PIPE {
                found = true;
            } else {
                j += 1;
            }
        }
        ends[3] = j;
        Some(ends)
    }
}

/// The diff of one frame: `intTryParse`, else `(int)Math.Round((double)Parsing.ParseFloat(s0))`.
pub fn parse_diff(s: &[u32], a: usize, b: usize) -> Result<i32, NetExn> {
    match int_try_parse(s, a, b) {
        Some(d) => Ok(d),
        None => match parse::parse_float_default(&s[a..b]) {
            Ok(f) => Ok(crate::sim::netx::f64_round(f.to_f64()).to_i32_sat()),
            Err(e) => Err(e),
        },
    }
}

/// The parsed fields of one frame (before `lastTime` accumulation).
#[derive(Clone, Copy)]
pub struct RawFrame {
    pub diff: i32,
    pub mouse_x: F32,
    pub mouse_y: F32,
    pub buttons: i32,
}

/// The body of `parseLegacyFrames`' loop for the frame `text[a..b]`: `Ok(None)` = `continue`.
pub fn parse_one_frame(s: &[u32], a: usize, b: usize) -> Result<Option<RawFrame>, NetExn> {
    match split_fields(s, a, b) {
        None => Ok(None),
        Some(ends) => {
            let s1 = ends[0] + 1;
            let s2 = ends[1] + 1;
            let s3 = ends[2] + 1;
            if is_skip_marker(s, a, ends[0]) {
                Ok(None)
            } else {
                match parse_diff(s, a, ends[0]) {
                    Err(e) => Err(e),
                    Ok(diff) => match parse::parsing_parse_float(&s[s1..ends[1]], MAX_COORDINATE_F32, false) {
                        Err(e) => Err(e),
                        Ok(mouse_x) => match parse::parsing_parse_float(&s[s2..ends[2]], MAX_COORDINATE_F32, false) {
                            Err(e) => Err(e),
                            Ok(mouse_y) => match parse::parse_int_default(&s[s3..ends[3]]) {
                                Err(e) => Err(e),
                                Ok(buttons) => Ok(Some(RawFrame { diff, mouse_x, mouse_y, buttons })),
                            },
                        },
                    },
                }
            }
        }
    }
}

/// End of the comma-separated segment starting at `a` (`text.splitOn ","`).
pub fn segment_end(s: &[u32], a: usize) -> usize {
    let mut i = a;
    while i < s.len() && s[i] != C_COMMA {
        i += 1;
    }
    i
}

/// `parseLegacyFrames`
pub fn parse_legacy_frames(text: &[u32], beatmap_offset: i64) -> Result<Vec<LegacyFrame>, NetExn> {
    let mut last_time: i64 = beatmap_offset;
    let mut out: Vec<LegacyFrame> = Vec::new();
    let mut err: Option<NetExn> = None;
    let mut a: usize = 0;
    let mut more = true;
    while more && err.is_none() {
        let b = segment_end(text, a);
        match parse_one_frame(text, a, b) {
            Err(e) => {
                err = Some(e);
            }
            Ok(None) => {}
            Ok(Some(f)) => {
                last_time = last_time.wrapping_add(f.diff as i64);
                out.push(LegacyFrame {
                    time: F64::from_i64(last_time),
                    mouse_x: f.mouse_x,
                    mouse_y: f.mouse_y,
                    buttons: f.buttons,
                });
            }
        }
        if b < text.len() {
            a = b + 1;
        } else {
            more = false;
        }
    }
    match err {
        Some(e) => Err(e),
        None => Ok(out),
    }
}

pub const F32_256: F32 = F32::from_bits(0x4380_0000);
pub const F32_M500: F32 = F32::from_bits(0xC3FA_0000);

/// `isSkipPos`
pub fn is_skip_pos(f: &LegacyFrame) -> bool {
    f.mouse_x.eq(F32_256) && f.mouse_y.eq(F32_M500)
}

/// `Array.eraseIdx!`
pub fn erase_idx(fs: &[LegacyFrame], k: usize) -> Vec<LegacyFrame> {
    let mut out: Vec<LegacyFrame> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len() {
        if i != k {
            out.push(fs[i]);
        }
        i += 1;
    }
    out
}

/// the backwards-time filter of `fixupFrames`
pub fn drop_backwards(fs: &[LegacyFrame]) -> Vec<LegacyFrame> {
    let mut out: Vec<LegacyFrame> = Vec::new();
    let mut i: usize = 0;
    while i < fs.len() {
        let f = fs[i];
        let n = out.len();
        if n == 0 || !f.time.lt(out[n - 1].time) {
            out.push(f);
        }
        i += 1;
    }
    out
}

/// `fixupFrames`
pub fn fixup_frames(fs0: Vec<LegacyFrame>) -> Vec<LegacyFrame> {
    let mut fs = fs0;
    if fs.len() >= 2 && fs[1].time.lt(fs[0].time) {
        fs[1].time = fs[0].time;
        fs[0].time = F64::from_bits(0);
    }
    if fs.len() >= 3 && fs[2].time.lt(fs[0].time) {
        let t = fs[2].time;
        fs[0].time = t;
        fs[1].time = t;
    }
    if fs.len() >= 2 && is_skip_pos(&fs[1]) {
        fs = erase_idx(&fs, 1);
    }
    if fs.len() >= 1 && is_skip_pos(&fs[0]) {
        fs = erase_idx(&fs, 0);
    }
    drop_backwards(&fs)
}

/// bit `k` of the button state (part of `convertFrame`: `(b >>> k) &&& 1 == 1`). A separate fn so that the
/// Aeneas translation of `== 1` is typed `Bool` (inline, Lean elaborated `ok (x = 1)` as a `Prop`).
pub fn button_bit(b: u32, k: u32) -> bool {
    ((b >> k) & 1) == 1
}

/// `convertFrame` (`OsuReplayFrame.FromLegacy`)
pub fn convert_frame(f: &LegacyFrame) -> Frame {
    let b: u32 = f.buttons as u32;
    let left = button_bit(b, 0) || button_bit(b, 2);
    let right = button_bit(b, 1) || button_bit(b, 3);
    let smoke = button_bit(b, 4);
    let mut acts = ACTLIST_EMPTY;
    if left {
        acts = act_push(acts, Action::Left);
    }
    if right {
        acts = act_push(acts, Action::Right);
    }
    if smoke {
        acts = act_push(acts, Action::Smoke);
    }
    Frame { time: f.time, pos: Vec2 { x: f.mouse_x, y: f.mouse_y }, actions: acts }
}

/// `decode`
pub fn decode(text: &[u32], beatmap_version: i64) -> Result<Vec<Frame>, NetExn> {
    let offset: i64 = if beatmap_version < 5 { 24 } else { 0 };
    match parse_legacy_frames(text, offset) {
        Err(e) => Err(e),
        Ok(fs) => {
            let fixed = fixup_frames(fs);
            let mut out: Vec<Frame> = Vec::new();
            let mut i: usize = 0;
            while i < fixed.len() {
                out.push(convert_frame(&fixed[i]));
                i += 1;
            }
            Ok(out)
        }
    }
}
