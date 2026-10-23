//! `nettest_rs`: differential tester for the Rust `net` port, reading the same binary stream as the
//! Lean `nettest` (`model/NetTest/Main.lean`; generator `model/nettest`, C#, real .NET 10):
//! `dotnet model/nettest/bin/Release/net10.0/nettest.dll gen N SEED | nettest_rs`
//! (also `... lib N SEED`, `... lazer ...`). Floats compared bit-for-bit (any NaN = any NaN;
//! payload differences counted separately). The Lean-only checks (ops 151-160, 186, 196, 200,
//! 201: Lean's `Float.Model`/`ofScientific`) have no Rust counterpart and are not produced.
use osu_eval_core::float::{F32, F64};
use osu_eval_core::net::basic::NetExn;
use osu_eval_core::net::decimal::{self, NetDecimal};
use osu_eval_core::net::framework::{self as fw, Easing};
use osu_eval_core::net::libm::f64_log_base;
use osu_eval_core::net::mathops::*;
use osu_eval_core::net::osutk::{self as tk, Matrix3, Vector2, Vector3};
use osu_eval_core::net::parse;
use osu_eval_core::net::random;
use osu_eval_core::net::sysmisc;
use osu_eval_core::net::{max as f64_max, min as f64_min};
use std::io::Read;

#[derive(Default, Clone, Copy)]
struct Stat {
    pass: u64,
    fail: u64,
    nan_diff: u64,
    shown: u64,
    snan: u64,
}

fn rd8(b: &[u8], i: usize) -> u64 {
    b[i] as u64
}
fn rd16(b: &[u8], i: usize) -> usize {
    b[i] as usize | ((b[i + 1] as usize) << 8)
}
fn rd32(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]])
}
fn rd64(b: &[u8], i: usize) -> u64 {
    rd32(b, i) as u64 | ((rd32(b, i + 4) as u64) << 32)
}
fn nan64(x: u64) -> bool {
    (x & 0x7FF0000000000000) == 0x7FF0000000000000 && (x & 0x000FFFFFFFFFFFFF) != 0
}
fn nan32(x: u32) -> bool {
    (x & 0x7F800000) == 0x7F800000 && (x & 0x007FFFFF) != 0
}
fn snan64(x: u64) -> bool {
    nan64(x) && (x & 0x0008000000000000) == 0
}
fn snan32(x: u32) -> bool {
    nan32(x) && (x & 0x00400000) == 0
}
fn cmp64(e: u64, g: u64) -> (bool, bool) {
    if nan64(e) { (nan64(g), nan64(g) && e != g) } else { (e == g, false) }
}
fn cmp32(e: u32, g: u32) -> (bool, bool) {
    if nan32(e) { (nan32(g), nan32(g) && e != g) } else { (e == g, false) }
}
fn exn_code(e: NetExn) -> u64 {
    match e {
        NetExn::Format => 1,
        NetExn::Overflow => 2,
        NetExn::Argument => 3,
        NetExn::ArgumentOutOfRange => 4,
        NetExn::Arithmetic => 5,
    }
}
fn fd(x: u64) -> F64 {
    F64::from_bits(x)
}
fn ff(x: u32) -> F32 {
    F32::from_bits(x)
}
fn flags64(x: F64, y: F64) -> u64 {
    (x.lt(y) as u64) | ((x.le(y) as u64) << 1) | ((x.eq(y) as u64) << 2) | ((y.lt(x) as u64) << 3) | ((y.le(x) as u64) << 4) | (((!x.eq(y)) as u64) << 5)
}
fn flags32(x: F32, y: F32) -> u64 {
    (x.lt(y) as u64) | ((x.le(y) as u64) << 1) | ((x.eq(y) as u64) << 2) | ((y.lt(x) as u64) << 3) | ((y.le(x) as u64) << 4) | (((!x.eq(y)) as u64) << 5)
}

fn op_name(op: usize) -> String {
    let s = match op {
        1 => "f64 +", 2 => "f64 -", 3 => "f64 *", 4 => "f64 /", 5 => "f64 compare",
        6 => "f32 +", 7 => "f32 -", 8 => "f32 *", 9 => "f32 /", 10 => "f32 compare",
        11 => "(float)double", 12 => "(double)float", 13 => "(double)int", 14 => "(double)long",
        15 => "(double)ulong", 16 => "(float)int", 17 => "(float)long", 18 => "(float)ulong",
        19 => "(double)uint", 20 => "(float)uint",
        21 => "(int)double", 22 => "(long)double", 23 => "(uint)double", 24 => "(ulong)double",
        25 => "(int)float", 26 => "(long)float", 27 => "(uint)float", 28 => "(ulong)float",
        30 => "Math.Round", 31 => "Math.Round(Away)", 32 => "Math.Floor", 33 => "Math.Ceiling",
        34 => "Math.Truncate", 35 => "Math.Abs", 36 => "Math.Sqrt", 37 => "f64 neg",
        40 => "MathF.Round", 41 => "MathF.Round(Away)", 42 => "MathF.Floor", 43 => "MathF.Ceiling",
        44 => "MathF.Truncate", 45 => "MathF.Abs", 46 => "MathF.Sqrt", 47 => "f32 neg",
        50 => "Math.Max(double)", 51 => "Math.Min(double)", 52 => "MathF.Max", 53 => "MathF.Min",
        54 => "Math.Clamp(double)", 55 => "Math.Clamp(float)", 56 => "Math.Sign(double)", 57 => "Math.Sign(float)",
        58 => "Math.Round(double,digits)", 59 => "MathF.Round(float,digits)",
        60 => "Math.Sin", 61 => "Math.Cos", 62 => "Math.Tan", 63 => "Math.Asin", 64 => "Math.Acos",
        65 => "Math.Atan", 66 => "Math.Atan2", 67 => "Math.Exp", 68 => "Math.Log", 69 => "Math.Log10",
        70 => "Math.Pow", 71 => "Math.Cbrt", 73 => "Math.Log(a,base)",
        80 => "MathF.Sin", 81 => "MathF.Cos", 82 => "MathF.Tan", 83 => "MathF.Asin", 84 => "MathF.Acos",
        85 => "MathF.Atan", 86 => "MathF.Atan2", 87 => "MathF.Exp", 88 => "MathF.Log", 90 => "MathF.Pow",
        100 => "double.Parse", 101 => "float.Parse", 102 => "int.Parse",
        103 => "Parsing.ParseDouble", 104 => "Parsing.ParseFloat", 105 => "Parsing.ParseInt",
        110 => "System.Random(seed) sequences", 111 => "decimal.CreateTruncating(double)",
        112 => "(decimal)double", 113 => "decimal.CreateTruncating(float)", 114 => "(decimal)float",
        115 => "(double)decimal", 116 => "(float)decimal", 117 => "decimal / decimal",
        118 => "decimal * decimal", 119 => "Math.Round(decimal)",
        120 => "osuTK Vector2.Length", 121 => "osuTK Vector2.LengthSquared", 122 => "osuTK Vector2.LengthFast",
        123 => "osuTK Vector2.Distance", 124 => "osuTK Vector2.DistanceSquared", 125 => "osuTK Vector2.Normalized",
        126 => "osuTK Vector2.Dot", 127 => "osuTK Vector2.Lerp", 128 => "osuTK Vector2.Clamp",
        129 => "osuTK Vector2 neg/PerpRight/PerpLeft", 130 => "osuTK Vector2 + - *s s* *v /s Divide",
        131 => "osuTK MathHelper.InverseSqrtFast", 132 => "osuTK Vector2.NormalizeFast", 133 => "osuTK Vector2.PerpDot",
        134 => "osuTK Vector2.ComponentMin/Max", 135 => "osuTK Matrix3.Mult",
        136 => "osuTK MathHelper.Deg/Rad (float, double)", 138 => "osuTK MathHelper constants",
        140 => "fw Vector2Extensions.Transform", 141 => "fw Vector2Extensions.Distance(Squared)",
        142 => "fw MatrixExtensions (8 ops)", 143 => "fw DrawInfo.ApplyTransform",
        144 => "fw Precision (float)", 145 => "fw Precision (double)",
        146 => "fw BindableDouble.Value=", 147 => "fw BindableFloat.Value=",
        148 => "fw BindableDouble initialiser", 149 => "fw BindableFloat initialiser",
        210 => "fw Easing (DefaultEasingFunction)", 211 => "fw Interpolation.ValueAt(double)",
        212 => "fw Interpolation.ValueAt(float)", 213 => "fw Interpolation.ValueAt(Vector2)",
        214 => "fw Interpolation.ValueAt(int)", 215 => "fw Lerp/DampContinuously/Damp",
        220 => "float.DegreesToRadians/RadiansToDegrees", 221 => "double.DegreesToRadians/RadiansToDegrees",
        222 => "Enumerable.Average(List<double>)",
        230 => "lazer APIMod.ToMod double setting", 231 => "lazer APIMod.ToMod float setting",
        _ => return format!("op{}", op),
    };
    s.to_string()
}

#[derive(Clone, Copy, PartialEq)]
enum Ty {
    F,
    D,
    I,
}
use Ty::*;

fn sig(op: usize) -> Option<(Vec<Ty>, Vec<Ty>)> {
    let r = |n: usize, t: Ty| vec![t; n];
    Some(match op {
        111 | 112 => (vec![D], vec![I, I, I, I, I]),
        113 | 114 => (vec![F], vec![I, I, I, I, I]),
        115 => (vec![I, I, I, I], vec![D]),
        116 => (vec![I, I, I, I], vec![F]),
        117 | 118 => (r(8, I), vec![I, I, I, I, I]),
        119 => (vec![I, I, I, I], vec![I, I, I, I]),
        120 | 121 | 122 => (vec![F, F], vec![F]),
        131 => (vec![F], vec![F]),
        123 | 124 | 126 | 133 => (r(4, F), vec![F]),
        125 | 132 => (vec![F, F], vec![F, F]),
        127 => (r(5, F), vec![F, F]),
        128 => (r(6, F), vec![F, F]),
        129 => (vec![F, F], r(6, F)),
        130 => (r(5, F), r(14, F)),
        134 => (r(4, F), r(4, F)),
        135 => (r(18, F), r(9, F)),
        136 => (vec![F, D], vec![F, F, D, D]),
        138 => (vec![], { let mut v = r(6, F); v.push(D); v.push(D); v }),
        140 => (r(11, F), vec![F, F]),
        141 => (r(4, F), vec![F, F]),
        142 => (r(12, F), r(72, F)),
        143 => (r(27, F), r(18, F)),
        144 => (vec![F, F, F], vec![I]),
        145 => (vec![D, D, D], vec![I]),
        146 => (r(4, D), vec![I, D]),
        147 => (r(4, F), vec![I, F]),
        148 => (r(4, D), vec![I, D]),
        149 => (r(4, F), vec![I, F]),
        210 => (vec![I, D], vec![D]),
        211 => (vec![I, D, D, D, D, D], vec![D]),
        212 => (vec![I, D, F, F, D, D], vec![F]),
        213 => (vec![I, D, F, F, F, F, D, D], vec![F, F]),
        214 => (vec![I, D, I, I, D, D], vec![I]),
        215 => (r(4, D), vec![D, D, I, D]),
        220 => (vec![F], vec![F, F]),
        221 => (vec![D], vec![D, D]),
        230 => (r(5, D), vec![D]),
        231 => (vec![F, F, F, F, D], vec![F]),
        _ => return None,
    })
}

fn wf(x: F32) -> u64 {
    x.to_bits() as u64
}
fn wd(x: F64) -> u64 {
    x.to_bits()
}
fn wi(x: i32) -> u64 {
    x as u32 as u64
}
fn dec_words(d: NetDecimal) -> Vec<u64> {
    let (a, b, c, e) = decimal::get_bits(d);
    vec![a as u64, b as u64, c as u64, e as u64]
}
fn with_status(n: usize, r: Result<Vec<u64>, NetExn>) -> Vec<u64> {
    match r {
        Ok(mut ws) => {
            ws.insert(0, 0);
            ws
        }
        Err(e) => {
            let mut v = vec![exn_code(e)];
            v.extend(std::iter::repeat(0).take(n));
            v
        }
    }
}
fn vec_w(v: Vector2) -> Vec<u64> {
    vec![wf(v.x), wf(v.y)]
}
fn mat_w(m: Matrix3) -> Vec<u64> {
    [m.row0.x, m.row0.y, m.row0.z, m.row1.x, m.row1.y, m.row1.z, m.row2.x, m.row2.y, m.row2.z].iter().map(|x| wf(*x)).collect()
}
fn easing(n: i32) -> Easing {
    fw::easing_of_index(if n < 0 { 1000 } else { n as u64 })
}

fn eval(op: usize, a: &[u64]) -> Vec<u64> {
    let fv = |k: usize| ff(a[k] as u32);
    let dv = |k: usize| fd(a[k]);
    let iv = |k: usize| a[k] as u32 as i32;
    let uv = |k: usize| a[k] as u32;
    let vv = |k: usize| Vector2 { x: fv(k), y: fv(k + 1) };
    let v3 = |k: usize| Vector3 { x: fv(k), y: fv(k + 1), z: fv(k + 2) };
    let mm = |k: usize| Matrix3 { row0: v3(k), row1: v3(k + 3), row2: v3(k + 6) };
    let dec = |k: usize| decimal::of_bits(uv(k), uv(k + 1), uv(k + 2), uv(k + 3));
    let wb = |b: bool| b as u64;
    match op {
        111 => with_status(4, decimal::create_truncating_f64(dv(0)).map(dec_words)),
        112 => with_status(4, decimal::of_f64(dv(0)).map(dec_words)),
        113 => with_status(4, decimal::create_truncating_f32(fv(0)).map(dec_words)),
        114 => with_status(4, decimal::of_f32(fv(0)).map(dec_words)),
        115 => vec![wd(decimal::to_f64(dec(0)))],
        116 => vec![wf(decimal::to_f32(dec(0)))],
        117 => with_status(4, decimal::div(dec(0), dec(4)).map(dec_words)),
        118 => with_status(4, decimal::mul(dec(0), dec(4)).map(dec_words)),
        119 => dec_words(decimal::round(dec(0))),
        120 => vec![wf(tk::v2_length(vv(0)))],
        121 => vec![wf(tk::v2_length_squared(vv(0)))],
        122 => vec![wf(tk::length_fast(vv(0)))],
        123 => vec![wf(tk::v2_distance(vv(0), vv(2)))],
        124 => vec![wf(tk::v2_distance_squared(vv(0), vv(2)))],
        125 => vec_w(tk::v2_normalized(vv(0))),
        126 => vec![wf(tk::v2_dot(vv(0), vv(2)))],
        127 => vec_w(tk::v2_lerp(vv(0), vv(2), fv(4))),
        128 => vec_w(tk::v2_clamp(vv(0), vv(2), vv(4))),
        129 => [vec_w(tk::v2_neg(vv(0))), vec_w(tk::v2_perpendicular_right(vv(0))), vec_w(tk::v2_perpendicular_left(vv(0)))].concat(),
        130 => {
            let (x, y, s) = (vv(0), vv(2), fv(4));
            [
                vec_w(tk::v2_add(x, y)),
                vec_w(tk::v2_sub(x, y)),
                vec_w(tk::v2_scale(x, s)),
                vec_w(Vector2 { x: s.mul(x.x), y: s.mul(x.y) }),
                vec_w(tk::v2_mul(x, y)),
                vec_w(tk::v2_div_s(x, s)),
                vec_w(tk::v2_divide(x, y)),
            ]
            .concat()
        }
        131 => vec![wf(tk::inverse_sqrt_fast(fv(0)))],
        132 => vec_w(tk::normalize_fast(vv(0))),
        133 => vec![wf(tk::v2_perp_dot(vv(0), vv(2)))],
        134 => [vec_w(tk::v2_component_min(vv(0), vv(2))), vec_w(tk::v2_component_max(vv(0), vv(2)))].concat(),
        135 => mat_w(tk::m3_mult(mm(0), mm(9))),
        136 => vec![
            wf(tk::degrees_to_radians_f(fv(0))),
            wf(tk::radians_to_degrees_f(fv(0))),
            wd(tk::degrees_to_radians_d(dv(1))),
            wd(tk::radians_to_degrees_d(dv(1))),
        ],
        138 => vec![
            wf(tk::PI_F),
            wf(tk::TWO_PI_F),
            wf(tk::PI_OVER2_F),
            wf(tk::PI_OVER4_F),
            wf(tk::DEG_TO_RAD_F),
            wf(tk::RAD_TO_DEG_F),
            wd(tk::DEG_TO_RAD_D),
            wd(tk::RAD_TO_DEG_D),
        ],
        140 => vec_w(fw::transform(vv(0), mm(2))),
        141 => vec![wf(fw::distance(vv(0), vv(2))), wf(fw::distance_squared(vv(0), vv(2)))],
        142 => {
            let (m, v, r) = (mm(0), vv(9), fv(11));
            [
                mat_w(fw::translate_from_left(m, v)),
                mat_w(fw::translate_from_right(m, v)),
                mat_w(fw::rotate_from_left(m, r)),
                mat_w(fw::rotate_from_right(m, r)),
                mat_w(fw::scale_from_left(m, v)),
                mat_w(fw::scale_from_right(m, v)),
                mat_w(fw::shear_from_left(m, v)),
                mat_w(fw::shear_from_right(m, v)),
            ]
            .concat()
        }
        143 => {
            let di = fw::DrawInfo { matrix: mm(0), matrix_inverse: mm(9) };
            let r = fw::apply_transform(di, vv(18), vv(20), fv(22), vv(23), vv(25));
            [mat_w(r.matrix), mat_w(r.matrix_inverse)].concat()
        }
        144 => {
            let (x, y, e) = (fv(0), fv(1), fv(2));
            let eps = fw::FLOAT_EPSILON;
            vec![
                wb(fw::definitely_bigger_f(x, y, e))
                    | (wb(fw::almost_bigger_f(x, y, e)) << 1)
                    | (wb(fw::almost_equals_f(x, y, e)) << 2)
                    | (wb(fw::definitely_bigger_f(x, y, eps)) << 3)
                    | (wb(fw::almost_bigger_f(x, y, eps)) << 4)
                    | (wb(fw::almost_equals_f(x, y, eps)) << 5)
                    | (wb(fw::almost_equals_v(Vector2 { x, y }, Vector2 { x: y, y: x }, e)) << 6),
            ]
        }
        145 => {
            let (x, y, e) = (dv(0), dv(1), dv(2));
            let eps = fw::DOUBLE_EPSILON;
            vec![
                wb(fw::definitely_bigger_d(x, y, e))
                    | (wb(fw::almost_bigger_d(x, y, e)) << 1)
                    | (wb(fw::almost_equals_d(x, y, e)) << 2)
                    | (wb(fw::definitely_bigger_d(x, y, eps)) << 3)
                    | (wb(fw::almost_bigger_d(x, y, eps)) << 4)
                    | (wb(fw::almost_equals_d(x, y, eps)) << 5),
            ]
        }
        146 => with_status(1, fw::bd_init(F64::from_bits(0), dv(0), dv(1), dv(2)).and_then(|s| fw::bd_set_value(s, dv(3))).map(|s| vec![wd(s.value)])),
        147 => with_status(1, fw::bf_init(F32::from_bits(0), fv(0), fv(1), fv(2)).and_then(|s| fw::bf_set_value(s, fv(3))).map(|s| vec![wf(s.value)])),
        148 => with_status(1, fw::bd_init(dv(0), dv(1), dv(2), dv(3)).map(|s| vec![wd(s.value)])),
        149 => with_status(1, fw::bf_init(fv(0), fv(1), fv(2), fv(3)).map(|s| vec![wf(s.value)])),
        210 => vec![wd(fw::apply_easing(easing(iv(0)), dv(1)))],
        211 => vec![wd(fw::value_at_d(dv(1), dv(2), dv(3), dv(4), dv(5), easing(iv(0))))],
        212 => vec![wf(fw::value_at_f(dv(1), fv(2), fv(3), dv(4), dv(5), easing(iv(0))))],
        213 => vec_w(fw::value_at_v(dv(1), vv(2), vv(4), dv(6), dv(7), easing(iv(0)))),
        214 => vec![wi(fw::value_at_i(dv(1), iv(2), iv(3), dv(4), dv(5), easing(iv(0))))],
        215 => {
            let mut v = vec![wd(fw::lerp(dv(0), dv(1), dv(2))), wd(fw::damp_continuously(dv(0), dv(1), dv(2), dv(3)))];
            v.extend(with_status(1, fw::damp(dv(0), dv(1), dv(2), dv(3)).map(|x| vec![wd(x)])));
            v
        }
        220 => vec![wf(sysmisc::f32_degrees_to_radians(fv(0))), wf(sysmisc::f32_radians_to_degrees(fv(0)))],
        221 => vec![wd(sysmisc::f64_degrees_to_radians(dv(0))), wd(sysmisc::f64_radians_to_degrees(dv(0)))],
        230 => with_status(1, fw::bd_init(dv(0), dv(1), dv(2), dv(3)).and_then(|s| fw::bd_set_value(s, dv(4))).map(|s| vec![wd(s.value)]))[1..].to_vec(),
        231 => with_status(1, fw::bf_init(fv(0), fv(1), fv(2), fv(3)).and_then(|s| fw::bf_set_value(s, dv(4).to_f32())).map(|s| vec![wf(s.value)]))[1..].to_vec(),
        _ => vec![],
    }
}

struct T {
    st: Vec<Stat>,
}

impl T {
    fn record(&mut self, op: usize, ok: bool, nd: bool, msg: &dyn Fn() -> String, snan_in: bool) {
        let s = &mut self.st[op];
        if !ok && snan_in {
            s.snan += 1;
            return;
        }
        if ok {
            s.pass += 1;
            if nd {
                s.nan_diff += 1;
            }
        } else {
            s.fail += 1;
            if s.shown < 8 {
                s.shown += 1;
                eprintln!("FAIL {}: {}", op_name(op), msg());
            }
        }
    }

    fn step(&mut self, b: &[u8], i0: usize) -> usize {
        let op = b[i0] as usize;
        let i = i0 + 1;
        let h16 = |x: u64| format!("0x{:016x}", x);
        let h8 = |x: u64| format!("0x{:08x}", x);
        if [1, 2, 3, 4, 50, 51, 66, 70, 73].contains(&op) {
            let (a, c, r) = (rd64(b, i), rd64(b, i + 8), rd64(b, i + 16));
            let (x, y) = (fd(a), fd(c));
            let got = match op {
                1 => x.add(y),
                2 => x.sub(y),
                3 => x.mul(y),
                4 => x.div(y),
                50 => f64_max(x, y),
                51 => f64_min(x, y),
                66 => x.atan2(y),
                70 => x.pow(y),
                _ => f64_log_base(x, y),
            };
            let (ok, nd) = cmp64(r, got.to_bits());
            self.record(op, ok, nd, &|| format!("{} {} -> .NET {} Rust {}", h16(a), h16(c), h16(r), h16(got.to_bits())), op >= 60 && (snan64(a) || snan64(c)));
            i + 24
        } else if op == 5 {
            let (a, c, r) = (rd64(b, i), rd64(b, i + 8), rd8(b, i + 16));
            let g = flags64(fd(a), fd(c));
            self.record(op, g == r, false, &|| format!("{} {} .NET {} Rust {}", h16(a), h16(c), r, g), false);
            i + 17
        } else if [6, 7, 8, 9, 52, 53, 86, 90].contains(&op) {
            let (a, c, r) = (rd32(b, i), rd32(b, i + 4), rd32(b, i + 8));
            let (x, y) = (ff(a), ff(c));
            let got = match op {
                6 => x.add(y),
                7 => x.sub(y),
                8 => x.mul(y),
                9 => x.div(y),
                52 => f32_max(x, y),
                53 => f32_min(x, y),
                86 => x.atan2(y),
                _ => x.pow(y),
            };
            let (ok, nd) = cmp32(r, got.to_bits());
            self.record(op, ok, nd, &|| format!("{} {} -> .NET {} Rust {}", h8(a as u64), h8(c as u64), h8(r as u64), h8(got.to_bits() as u64)), op >= 60 && (snan32(a) || snan32(c)));
            i + 12
        } else if op == 10 {
            let (a, c, r) = (rd32(b, i), rd32(b, i + 4), rd8(b, i + 8));
            let g = flags32(ff(a), ff(c));
            self.record(op, g == r, false, &|| format!("{} {} .NET {} Rust {}", h8(a as u64), h8(c as u64), r, g), false);
            i + 9
        } else if (30..=37).contains(&op) || ((60..=71).contains(&op) && op != 66 && op != 70) {
            let (a, r) = (rd64(b, i), rd64(b, i + 8));
            let x = fd(a);
            let got = match op {
                30 => f64_round(x),
                31 => f64_round_mode(x, MidpointRounding::AwayFromZero),
                32 => x.floor(),
                33 => x.ceil(),
                34 => x.trunc(),
                35 => x.abs(),
                36 => x.sqrt(),
                37 => x.neg(),
                60 => x.sin(),
                61 => x.cos(),
                62 => x.tan(),
                63 => x.asin(),
                64 => x.acos(),
                65 => x.atan(),
                67 => x.exp(),
                68 => x.log(),
                69 => x.log10(),
                _ => x.cbrt(),
            };
            let (ok, nd) = cmp64(r, got.to_bits());
            self.record(op, ok, nd, &|| format!("{} -> .NET {} Rust {}", h16(a), h16(r), h16(got.to_bits())), op >= 60 && snan64(a));
            i + 16
        } else if (40..=47).contains(&op) || ((80..=88).contains(&op) && op != 86) {
            let (a, r) = (rd32(b, i), rd32(b, i + 4));
            let x = ff(a);
            let got = match op {
                40 => f32_round(x),
                41 => f32_round_mode(x, MidpointRounding::AwayFromZero),
                42 => x.floor(),
                43 => x.ceil(),
                44 => x.trunc(),
                45 => x.abs(),
                46 => x.sqrt(),
                47 => x.neg(),
                80 => x.sin(),
                81 => x.cos(),
                82 => x.tan(),
                83 => x.asin(),
                84 => x.acos(),
                85 => x.atan(),
                87 => x.exp(),
                _ => x.log(),
            };
            let (ok, nd) = cmp32(r, got.to_bits());
            self.record(op, ok, nd, &|| format!("{} -> .NET {} Rust {}", h8(a as u64), h8(r as u64), h8(got.to_bits() as u64)), op >= 60 && snan32(a));
            i + 8
        } else if (11..=28).contains(&op) {
            let in_w = if [12, 13, 16, 19, 20, 25, 26, 27, 28].contains(&op) { 4 } else { 8 };
            let a64: u64 = if in_w == 4 { rd32(b, i) as u64 } else { rd64(b, i) };
            let a32 = a64 as u32;
            let out_w = if [11, 16, 17, 18, 20].contains(&op) { 4 } else { 8 };
            let r64: u64 = if out_w == 4 { rd32(b, i + in_w) as u64 } else { rd64(b, i + in_w) };
            let (ok, nd, g): (bool, bool, u64) = match op {
                11 => {
                    let g = fd(a64).to_f32().to_bits();
                    let c = cmp32(r64 as u32, g);
                    (c.0, c.1, g as u64)
                }
                12 => {
                    let g = ff(a32).to_f64().to_bits();
                    let c = cmp64(r64, g);
                    (c.0, c.1, g)
                }
                13 => { let g = F64::from_i64(a32 as i32 as i64).to_bits(); (g == r64, false, g) }
                14 => { let g = F64::from_i64(a64 as i64).to_bits(); (g == r64, false, g) }
                15 => { let g = F64::from_u64(a64).to_bits(); (g == r64, false, g) }
                16 => { let g = F32::from_i64(a32 as i32 as i64).to_bits() as u64; (g == r64, false, g) }
                17 => { let g = F32::from_i64(a64 as i64).to_bits() as u64; (g == r64, false, g) }
                18 => { let g = F32::from_u64(a64).to_bits() as u64; (g == r64, false, g) }
                19 => { let g = F64::from_u64(a32 as u64).to_bits(); (g == r64, false, g) }
                20 => { let g = F32::from_u64(a32 as u64).to_bits() as u64; (g == r64, false, g) }
                21 => { let g = fd(a64).to_i32_sat() as u32 as u64; (g == r64, false, g) }
                22 => { let g = fd(a64).to_i64_sat() as u64; (g == r64, false, g) }
                23 => { let g = fd(a64).to_u32() as u64; (g == r64, false, g) }
                24 => { let g = fd(a64).to_u64(); (g == r64, false, g) }
                25 => { let g = ff(a32).to_i32_sat() as u32 as u64; (g == r64, false, g) }
                26 => { let g = ff(a32).to_i64_sat() as u64; (g == r64, false, g) }
                27 => { let g = ff(a32).to_u32() as u64; (g == r64, false, g) }
                _ => { let g = ff(a32).to_u64(); (g == r64, false, g) }
            };
            self.record(op, ok, nd, &|| format!("{} -> .NET {} Rust {}", h16(a64), h16(r64), h16(g)), false);
            i + in_w + out_w
        } else if op == 54 {
            let (vv, lo, hi, s, r) = (rd64(b, i), rd64(b, i + 8), rd64(b, i + 16), rd8(b, i + 24), rd64(b, i + 25));
            let (gs, g) = match f64_clamp(fd(vv), fd(lo), fd(hi)) {
                Ok(x) => (0, x.to_bits()),
                Err(e) => (exn_code(e), 0),
            };
            let ok = gs == s && (s != 0 || cmp64(r, g).0);
            self.record(op, ok, false, &|| format!("{} {} {} -> .NET {}/{} Rust {}/{}", h16(vv), h16(lo), h16(hi), s, h16(r), gs, h16(g)), false);
            i + 33
        } else if op == 55 {
            let (vv, lo, hi, s, r) = (rd32(b, i), rd32(b, i + 4), rd32(b, i + 8), rd8(b, i + 12), rd32(b, i + 13));
            let (gs, g) = match f32_clamp(ff(vv), ff(lo), ff(hi)) {
                Ok(x) => (0, x.to_bits() as u64),
                Err(e) => (exn_code(e), 0),
            };
            let ok = gs == s && (s != 0 || cmp32(r, g as u32).0);
            self.record(op, ok, false, &|| format!("{:x} {:x} {:x} -> .NET {}/{:x} Rust {}/{:x}", vv, lo, hi, s, r, gs, g), false);
            i + 17
        } else if op == 56 || op == 57 {
            let w = if op == 56 { 8 } else { 4 };
            let a = if w == 8 { rd64(b, i) } else { rd32(b, i) as u64 };
            let (s, r) = (rd8(b, i + w), rd32(b, i + w + 1));
            let res = if op == 56 { f64_sign(fd(a)) } else { f32_sign(ff(a as u32)) };
            let (gs, g) = match res {
                Ok(x) => (0, x as u32 as u64),
                Err(e) => (exn_code(e), 0),
            };
            let ok = gs == s && (s != 0 || g as u32 == r);
            self.record(op, ok, false, &|| format!("{} -> .NET {}/{} Rust {}/{}", h16(a), s, r, gs, g), false);
            i + w + 5
        } else if op == 58 {
            let (a, dg, s, r) = (rd64(b, i), rd8(b, i + 8), rd8(b, i + 9), rd64(b, i + 10));
            let (gs, g) = match f64_round_digits(fd(a), dg as i64) {
                Ok(x) => (0, x.to_bits()),
                Err(e) => (exn_code(e), 0),
            };
            let ok = gs == s && (s != 0 || cmp64(r, g).0);
            self.record(op, ok, false, &|| format!("{} digits {} -> .NET {}/{} Rust {}/{}", h16(a), dg, s, h16(r), gs, h16(g)), false);
            i + 18
        } else if op == 59 {
            let (a, dg, s, r) = (rd32(b, i), rd8(b, i + 4), rd8(b, i + 5), rd32(b, i + 6));
            let (gs, g) = match f32_round_digits(ff(a), dg as i64) {
                Ok(x) => (0, x.to_bits() as u64),
                Err(e) => (exn_code(e), 0),
            };
            let ok = gs == s && (s != 0 || cmp32(r, g as u32).0);
            self.record(op, ok, false, &|| format!("{:x} digits {} -> .NET {}/{:x} Rust {}/{:x}", a, dg, s, r, gs, g), false);
            i + 10
        } else if (100..=105).contains(&op) {
            let len = rd16(b, i);
            let bytes = &b[i + 2..i + 2 + len];
            let (s, r) = (rd8(b, i + 2 + len), rd64(b, i + 3 + len));
            let text: String = match std::str::from_utf8(bytes) {
                Ok(t) => t.to_string(),
                Err(_) => "<invalid utf8>".to_string(),
            };
            let cs: Vec<u32> = text.chars().map(|c| c as u32).collect();
            let res: Result<u64, NetExn> = match op {
                100 => parse::double_parse(&cs).map(|x| x.to_bits()),
                101 => parse::float_parse(&cs).map(|x| x.to_bits() as u64),
                102 => parse::int_parse(&cs).map(|x| x as u32 as u64),
                103 => parse::parse_double_default(&cs).map(|x| x.to_bits()),
                104 => parse::parse_float_default(&cs).map(|x| x.to_bits() as u64),
                _ => parse::parse_int_default(&cs).map(|x| x as u32 as u64),
            };
            let (gs, g) = match res {
                Ok(x) => (0, x),
                Err(e) => (exn_code(e), 0),
            };
            let is_f = op == 100 || op == 101 || op == 103 || op == 104;
            let is32 = op == 101 || op == 104;
            let val_ok = if !is_f { g == r } else if is32 { cmp32(r as u32, g as u32).0 } else { cmp64(r, g).0 };
            let nd = s == 0 && is_f && (if is32 { cmp32(r as u32, g as u32).1 } else { cmp64(r, g).1 });
            let ok = gs == s && (s != 0 || val_ok);
            self.record(op, ok, nd, &|| format!("{:?} -> .NET {}/{} Rust {}/{}", text, s, h16(r), gs, h16(g)), false);
            i + 11 + len
        } else if op == 110 {
            let seed = rd32(b, i) as i32;
            let n = rd16(b, i + 4);
            let mut j = i + 6;
            let mut rs = random::create(seed);
            for _ in 0..n {
                let kind = rd8(b, j);
                let x = rd32(b, j + 1) as i32;
                let y = rd32(b, j + 5) as i32;
                let r = rd64(b, j + 9);
                let (g, rs2, is_d, is_f): (u64, random::State, bool, bool) = match kind {
                    0 => { let (v, s) = random::next(rs); (v as u32 as u64, s, false, false) }
                    1 => match random::next_max(rs, x) { Ok((v, s)) => (v as u32 as u64, s, false, false), Err(_) => (0xFFFFFFFF, rs, false, false) },
                    2 => match random::next_range(rs, x, y) { Ok((v, s)) => (v as u32 as u64, s, false, false), Err(_) => (0xFFFFFFFF, rs, false, false) },
                    3 => { let (v, s) = random::next_double(rs); (v.to_bits(), s, true, false) }
                    _ => match random::next_single(64, rs) { Some((v, s)) => (v.to_bits() as u64, s, false, true), None => (0xFFFFFFFF, rs, false, false) },
                };
                rs = rs2;
                let ok = if is_d { cmp64(r, g).0 } else if is_f { cmp32(r as u32, g as u32).0 } else { r == g };
                self.record(110, ok, false, &|| format!("seed {} call kind {} ({},{}) -> .NET {} Rust {}", seed, kind, x, y, h16(r), h16(g)), false);
                j += 17;
            }
            j
        } else if op == 222 {
            let n = b[i] as usize;
            let xs: Vec<F64> = (0..n).map(|k| fd(rd64(b, i + 1 + 8 * k))).collect();
            let r = rd64(b, i + 1 + 8 * n);
            let g = match sysmisc::average_f64(&xs) {
                Ok(v) => v.to_bits(),
                Err(_) => 0,
            };
            self.record(222, cmp64(r, g).0, false, &|| format!("n={} -> .NET {} Rust {}", n, h16(r), h16(g)), false);
            i + 9 + 8 * n
        } else {
            match sig(op) {
                Some((ins, outs)) => {
                    let mut j = i;
                    let mut in_w: Vec<u64> = vec![];
                    for t in &ins {
                        in_w.push(if *t == D { rd64(b, j) } else { rd32(b, j) as u64 });
                        j += if *t == D { 8 } else { 4 };
                    }
                    let got = eval(op, &in_w);
                    let mut ok = got.len() == outs.len();
                    let mut nd = false;
                    let mut exp_w: Vec<u64> = vec![];
                    for (k, t) in outs.iter().enumerate() {
                        let e = if *t == D { rd64(b, j) } else { rd32(b, j) as u64 };
                        exp_w.push(e);
                        let g = got.get(k).copied().unwrap_or(0);
                        let (o, n2) = match t {
                            D => cmp64(e, g),
                            F => cmp32(e as u32, g as u32),
                            I => (e == g, false),
                        };
                        ok = ok && o;
                        nd = nd || n2;
                        j += if *t == D { 8 } else { 4 };
                    }
                    self.record(op, ok, nd, &|| format!("in {:x?} -> .NET {:x?} Rust {:x?}", in_w, exp_w, got), false);
                    j
                }
                None => {
                    eprintln!("unknown op {} at offset {}", op, i0);
                    std::process::exit(2);
                }
            }
        }
    }
}

fn main() {
    let mut t = T { st: vec![Stat::default(); 256] };
    let mut stdin = std::io::stdin().lock();
    loop {
        let mut hdr = [0u8; 4];
        if stdin.read_exact(&mut hdr).is_err() {
            break;
        }
        let len = u32::from_le_bytes(hdr) as usize;
        let mut body = vec![0u8; len];
        if stdin.read_exact(&mut body).is_err() {
            eprintln!("truncated frame");
            std::process::exit(2);
        }
        let mut i = 0;
        while i < body.len() {
            i = t.step(&body, i);
        }
    }
    let (mut total, mut fails) = (0u64, 0u64);
    println!("{:<40} {:<10} fail  nan-payload-diff  snan-input-diff", "op", "pass");
    for k in 0..256 {
        let s = t.st[k];
        if s.pass + s.fail + s.snan > 0 {
            println!("{:<42} {:<10} {}  {}  {}", op_name(k), s.pass, s.fail, s.nan_diff, s.snan);
            total += s.pass + s.fail;
            fails += s.fail;
        }
    }
    println!("TOTAL checks {}, failures {}", total, fails);
    std::process::exit(if fails == 0 { 0 } else { 1 });
}
