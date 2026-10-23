//! Port of `OsuModel/Beatmap/ModSettings.lean`: `APIMod.ToMod` (settings decode with
//! `Bindable<T>.Parse` semantics, setters, setting tables, `ValueChanged` cross-constraints).
use super::names::*;
use super::dotnet::{enum_try_parse, is_white_space, lit_str, str_eq, Str};
use crate::float::{F32, F64};
use crate::net::basic::{f64_is_inf, NetExn};
use crate::net::framework::{bd_create, bd_init, bd_set_max, bd_set_min, bd_set_precision, bd_set_value, bf_create, bf_init, bf_set_max, bf_set_min, bf_set_precision, bf_set_value, equals_d, equals_f, BD, BF};
use crate::net::mathops::f32_clamp;
use crate::net::mathops::{f32_max, f32_min};
use crate::net::parse::{ascii_lower, ascii_upper, double_parse, float_parse, int_parse};
use alloc::vec::Vec;

/// A Newtonsoft settings value; spec `JsonVal`
#[derive(Clone)]
pub enum JsonVal {
    Long(i64),
    Big,
    Double(F64),
    Bool(bool),
    Str(Str),
    Null,
}

/// The bindable types of osu! mod settings; spec `SettingType`
#[derive(Clone, Copy)]
pub enum SettingType {
    Bool(bool),
    Int(i32, i32),
    Double(F64, F64, F64),
    Float(F32, F32, F32),
    /// member names (value = index)
    Enum(u32),
    NullableInt,
    Difficulty(F32, F32, Option<F32>, Option<F32>),
}

/// A stored setting value; spec `SettingValue`
#[derive(Clone, Copy)]
pub enum SettingValue {
    Bool(bool),
    Int(i32),
    Double(F64),
    Float(F32),
    Enum(i32),
    OptInt(Option<i32>),
    OptFloat(Option<F32>),
}

/// derived `BEq SettingValue` (IEEE `==` on float fields)
pub fn setting_value_beq(a: SettingValue, b: SettingValue) -> bool {
    match (a, b) {
        (SettingValue::Bool(x), SettingValue::Bool(y)) => x == y,
        (SettingValue::Int(x), SettingValue::Int(y)) => x == y,
        (SettingValue::Double(x), SettingValue::Double(y)) => x.eq(y),
        (SettingValue::Float(x), SettingValue::Float(y)) => x.eq(y),
        (SettingValue::Enum(x), SettingValue::Enum(y)) => x == y,
        (SettingValue::OptInt(x), SettingValue::OptInt(y)) => match (x, y) {
            (None, None) => true,
            (Some(p), Some(q)) => p == q,
            _ => false,
        },
        (SettingValue::OptFloat(x), SettingValue::OptFloat(y)) => match (x, y) {
            (None, None) => true,
            (Some(p), Some(q)) => p.eq(q),
            _ => false,
        },
        _ => false,
    }
}

/// spec `SettingDef`
#[derive(Clone, Copy)]
pub struct SettingDef {
    pub key: u32,
    pub stype: SettingType,
    pub default: SettingValue,
}

/// A decoded mod; spec `ModConfig`
#[derive(Clone)]
pub struct ModConfig {
    pub acronym: Str,
    pub known: bool,
    pub settings: Vec<(u32, SettingValue)>,
}

/// byte-string equality
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        false
    } else {
        let mut i = 0;
        let mut ok = true;
        while i < a.len() {
            if a[i] != b[i] {
                ok = false;
            }
            i = i + 1;
        }
        ok
    }
}

/// spec `ModConfig.get?`
pub fn mc_get(m: &ModConfig, key: u32) -> Option<SettingValue> {
    vals_get(&m.settings, key)
}
pub fn vals_get(vals: &[(u32, SettingValue)], key: u32) -> Option<SettingValue> {
    let mut i = 0;
    let mut r: Option<SettingValue> = None;
    while r.is_none() && i < vals.len() {
        if vals[i].0 == key {
            r = Some(vals[i].1);
        }
        i = i + 1;
    }
    r
}
/// spec `ModConfig.getBool`
pub fn get_bool(m: &ModConfig, key: u32) -> bool {
    match mc_get(m, key) {
        Some(SettingValue::Bool(b)) => b,
        _ => false,
    }
}
/// spec `ModConfig.getInt`
pub fn get_int(m: &ModConfig, key: u32) -> i32 {
    match mc_get(m, key) {
        Some(SettingValue::Int(v)) => v,
        Some(SettingValue::Enum(v)) => v,
        _ => 0,
    }
}
/// spec `ModConfig.getDouble`
pub fn get_double(m: &ModConfig, key: u32) -> F64 {
    match mc_get(m, key) {
        Some(SettingValue::Double(v)) => v,
        _ => F64::from_bits(0),
    }
}
/// spec `ModConfig.getFloat`
pub fn get_float(m: &ModConfig, key: u32) -> F32 {
    match mc_get(m, key) {
        Some(SettingValue::Float(v)) => v,
        _ => F32::from_bits(0),
    }
}
/// spec `ModConfig.getOptInt`
pub fn get_opt_int(m: &ModConfig, key: u32) -> Option<i32> {
    match mc_get(m, key) {
        Some(SettingValue::OptInt(v)) => v,
        _ => None,
    }
}
/// spec `ModConfig.getOptFloat`
pub fn get_opt_float(m: &ModConfig, key: u32) -> Option<F32> {
    match mc_get(m, key) {
        Some(SettingValue::OptFloat(v)) => v,
        _ => None,
    }
}

// ----------------------------------------------------------------- Convert.ChangeType

const D0: F64 = F64::from_bits(0);
const D_HALF: F64 = F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */;
const D_MHALF: F64 = F64::from_bits(0xBFE0_0000_0000_0000) /* -0.5 */;
const D_I32_HI: F64 = F64::from_bits(0x41DF_FFFF_FFE0_0000) /* 2147483647.5 */;
const D_I32_LO: F64 = F64::from_bits(0xC1E0_0000_0010_0000) /* -2147483648.5 */;

/// `Convert.ToInt32(double)`; spec `Settings.convertToInt32`
pub fn convert_to_int32(v: F64) -> Result<i32, NetExn> {
    if D0.le(v) {
        if v.lt(D_I32_HI) {
            let r = v.to_i32_sat();
            let dif = v.sub(F64::from_i64(r as i64));
            Ok(if D_HALF.lt(dif) || (dif.eq(D_HALF) && (r & 1) != 0) { r.wrapping_add(1) } else { r })
        } else {
            Err(NetExn::Overflow)
        }
    } else if D_I32_LO.le(v) {
        let r = v.to_i32_sat();
        let dif = v.sub(F64::from_i64(r as i64));
        Ok(if dif.lt(D_MHALF) || (dif.eq(D_MHALF) && (r & 1) != 0) { r.wrapping_sub(1) } else { r })
    } else {
        Err(NetExn::Overflow)
    }
}

/// `Convert.ToInt32(long)`; spec `Settings.longToInt32`
pub fn long_to_int32(v: i64) -> Result<i32, NetExn> {
    if -2147483648 <= v && v <= 2147483647 { Ok(v as i32) } else { Err(NetExn::Overflow) }
}

fn is_trim(c: u32) -> bool {
    is_white_space(c) || c == 0
}

/// `bool.Parse(string)`; spec `Settings.boolParse`
pub fn bool_parse(s: &[u32]) -> Result<bool, NetExn> {
    let mut lo = 0;
    while lo < s.len() && is_trim(s[lo]) {
        lo = lo + 1;
    }
    let mut hi = s.len();
    while hi > lo && is_trim(s[hi - 1]) {
        hi = hi - 1;
    }
    let mut l: Str = Vec::new();
    let mut i = lo;
    while i < hi {
        l.push(ascii_lower(s[i]));
        i = i + 1;
    }
    if str_eq(&l, b"true") {
        Ok(true)
    } else if str_eq(&l, b"false") {
        Ok(false)
    } else {
        Err(NetExn::Format)
    }
}

/// spec `Settings.toInt32`
pub fn to_int32(j: &JsonVal) -> Result<i32, NetExn> {
    match j {
        JsonVal::Long(v) => long_to_int32(*v),
        JsonVal::Double(v) => convert_to_int32(*v),
        JsonVal::Bool(b) => Ok(if *b { 1 } else { 0 }),
        JsonVal::Str(s) => int_parse(s),
        JsonVal::Big | JsonVal::Null => Err(NetExn::Argument),
    }
}

/// spec `Settings.toF64`
pub fn to_f64(j: &JsonVal) -> Result<F64, NetExn> {
    match j {
        JsonVal::Long(v) => Ok(F64::from_i64(*v)),
        JsonVal::Double(v) => Ok(*v),
        JsonVal::Bool(b) => Ok(if *b { F64::from_bits(0x3FF0_0000_0000_0000) /* 1 */ } else { D0 }),
        JsonVal::Str(s) => double_parse(s),
        JsonVal::Big | JsonVal::Null => Err(NetExn::Argument),
    }
}

/// spec `Settings.toF32`
pub fn to_f32(j: &JsonVal) -> Result<F32, NetExn> {
    match j {
        JsonVal::Long(v) => Ok(F32::from_i64(*v)),
        JsonVal::Double(v) => Ok(v.to_f32()),
        JsonVal::Bool(b) => Ok(if *b { F32::from_bits(0x3F80_0000) /* 1f */ } else { F32::from_bits(0) }),
        JsonVal::Str(s) => float_parse(s),
        JsonVal::Big | JsonVal::Null => Err(NetExn::Argument),
    }
}

/// spec `Settings.toBool`
pub fn to_bool(bindable_bool: bool, j: &JsonVal) -> Result<bool, NetExn> {
    match j {
        JsonVal::Bool(b) => Ok(*b),
        JsonVal::Str(s) => {
            if str_eq(s, b"1") && bindable_bool {
                Ok(true)
            } else if str_eq(s, b"0") && bindable_bool {
                Ok(false)
            } else {
                bool_parse(s)
            }
        }
        JsonVal::Long(v) => Ok(*v != 0),
        JsonVal::Double(v) => Ok(!v.eq(D0)),
        JsonVal::Big | JsonVal::Null => Err(NetExn::Argument),
    }
}

/// `Int.toString` (decimal)
pub fn int_to_str(v: i64) -> Str {
    let neg = v < 0;
    let mut m: i128 = if neg { -(v as i128) } else { v as i128 };
    let mut digits: Str = Vec::new();
    if m == 0 {
        digits.push(0x30);
    }
    while m > 0 {
        digits.push(0x30 + (m % 10) as u32);
        m = m / 10;
    }
    let mut out: Str = Vec::new();
    if neg {
        out.push(0x2D);
    }
    let mut k = digits.len();
    while k > 0 {
        k = k - 1;
        out.push(digits[k]);
    }
    out
}

const D1E15: F64 = F64::from_bits(0x430C_6BF5_2634_0000) /* 1e15 */;

/// `input.ToString()` for the enum branch; spec `Settings.enumString`
pub fn enum_string(j: &JsonVal) -> Option<Str> {
    match j {
        JsonVal::Long(v) => Some(int_to_str(*v)),
        JsonVal::Double(v) => {
            if !v.is_nan() && !f64_is_inf(*v) && v.trunc().eq(*v) && v.abs().lt(D1E15) {
                let i = v.to_i64_sat();
                if i == 0 && (v.to_bits() >> 63) == 1 { Some(lit_str(b"-0")) } else { Some(int_to_str(i)) }
            } else {
                None
            }
        }
        JsonVal::Bool(b) => Some(if *b { lit_str(b"True") } else { lit_str(b"False") }),
        JsonVal::Str(s) => Some(s.clone()),
        JsonVal::Big | JsonVal::Null => None,
    }
}

// ----------------------------------------------------------------- setters

/// `BindableNumber<double>.Value = v` on a bindable holding `old`; spec `Settings.setDouble`
pub fn set_double(min: F64, max: F64, precision: F64, old: F64, v: F64) -> Option<F64> {
    match bd_set_value(BD { value: old, min_v: min, max_v: max, prec: precision }, v) {
        Ok(s) => Some(s.value),
        Err(_) => None,
    }
}

/// `BindableNumber<float>.Value = v`; spec `Settings.setFloat`
pub fn set_float(min: F32, max: F32, precision: F32, old: F32, v: F32) -> Option<F32> {
    match bf_set_value(BF { value: old, min_v: min, max_v: max, prec: precision }, v) {
        Ok(s) => Some(s.value),
        Err(_) => None,
    }
}

fn init_double_pf(d: F64, min: F64, max: F64, precision: F64) -> Result<BD, NetExn> {
    let s = tri!(bd_create(d));
    let s = tri!(bd_set_precision(s, precision));
    let s = tri!(bd_set_min(s, min));
    bd_set_max(s, max)
}

/// `new BindableDouble(d) { MinValue, MaxValue, Precision }`; spec `Settings.initDouble`
pub fn init_double(d: F64, min: F64, max: F64, precision: F64, precision_first: bool) -> F64 {
    let r = if precision_first { init_double_pf(d, min, max, precision) } else { bd_init(d, min, max, precision) };
    match r {
        Ok(s) => s.value,
        Err(_) => d,
    }
}

fn init_float_pf(d: F32, min: F32, max: F32, precision: F32) -> Result<BF, NetExn> {
    let s = tri!(bf_create(d));
    let s = tri!(bf_set_precision(s, precision));
    let s = tri!(bf_set_min(s, min));
    bf_set_max(s, max)
}

/// spec `Settings.initFloat`
pub fn init_float(d: F32, min: F32, max: F32, precision: F32, precision_first: bool) -> F32 {
    let r = if precision_first { init_float_pf(d, min, max, precision) } else { bf_init(d, min, max, precision) };
    match r {
        Ok(s) => s.value,
        Err(_) => d,
    }
}

/// `BindableInt` setter (clamp); spec `Settings.setInt`
pub fn set_int(min: i32, max: i32, v: i32) -> i32 {
    if v < min { min } else if max < v { max } else { v }
}

/// `DifficultyBindable.Value` setter (non-null); spec `Settings.setDifficulty`
pub fn set_difficulty(min: F32, max: F32, ext_min: Option<F32>, ext_max: Option<F32>, v: F32) -> F32 {
    let lo = match ext_min {
        Some(x) => x,
        None => min,
    };
    let hi = match ext_max {
        Some(x) => x,
        None => max,
    };
    let cn_min = f32_clamp(f32_min(min, v), lo, min);
    let cn_max = f32_clamp(f32_max(max, v), max, hi);
    match (cn_min, cn_max) {
        (Ok(a), Ok(b)) => match f32_clamp(v, a, b) {
            Ok(r) => r,
            Err(_) => v,
        },
        _ => v,
    }
}

fn is_null_or_empty(j: &JsonVal) -> bool {
    match j {
        JsonVal::Null => true,
        JsonVal::Str(s) => s.len() == 0,
        _ => false,
    }
}

/// `Bindable<T>.Parse(input)` + setter on a bindable holding `old` (`None` = exception);
/// spec `Settings.parse`
pub fn parse(t: SettingType, old: SettingValue, j: &JsonVal) -> Option<SettingValue> {
    match t {
        SettingType::Bool(bb) => match to_bool(bb, j) {
            Ok(b) => Some(SettingValue::Bool(b)),
            Err(_) => None,
        },
        SettingType::Int(mn, mx) => match to_int32(j) {
            Ok(v) => Some(SettingValue::Int(set_int(mn, mx, v))),
            Err(_) => None,
        },
        SettingType::Double(mn, mx, p) => {
            let o = match old {
                SettingValue::Double(x) => x,
                _ => D0,
            };
            match to_f64(j) {
                Ok(v) => match set_double(mn, mx, p, o, v) {
                    Some(x) => Some(SettingValue::Double(x)),
                    None => None,
                },
                Err(_) => None,
            }
        }
        SettingType::Float(mn, mx, p) => {
            let o = match old {
                SettingValue::Float(x) => x,
                _ => F32::from_bits(0),
            };
            match to_f32(j) {
                Ok(v) => match set_float(mn, mx, p, o, v) {
                    Some(x) => Some(SettingValue::Float(x)),
                    None => None,
                },
                Err(_) => None,
            }
        }
        SettingType::Enum(names) => match enum_string(j) {
            Some(s) => match enum_try_parse(names, &s) {
                Some(x) => Some(SettingValue::Enum(x)),
                None => None,
            },
            None => None,
        },
        SettingType::NullableInt => {
            if is_null_or_empty(j) {
                Some(SettingValue::OptInt(None))
            } else {
                match to_int32(j) {
                    Ok(v) => Some(SettingValue::OptInt(Some(v))),
                    Err(_) => None,
                }
            }
        }
        SettingType::Difficulty(mn, mx, emn, emx) => {
            if is_null_or_empty(j) {
                Some(SettingValue::OptFloat(None))
            } else {
                match to_f32(j) {
                    Ok(v) => Some(SettingValue::OptFloat(Some(set_difficulty(mn, mx, emn, emx, v)))),
                    Err(_) => None,
                }
            }
        }
    }
}

// ----------------------------------------------------------------- setting tables

pub fn s_bool(key: u32, d: bool) -> SettingDef {
    SettingDef { key, stype: SettingType::Bool(true), default: SettingValue::Bool(d) }
}
/// `sBool key d (bindableBool := false)` (plain `Bindable<bool>`)
pub fn s_bool_plain(key: u32, d: bool) -> SettingDef {
    SettingDef { key, stype: SettingType::Bool(false), default: SettingValue::Bool(d) }
}
pub fn s_int(key: u32, d: i32, mn: i32, mx: i32) -> SettingDef {
    SettingDef { key, stype: SettingType::Int(mn, mx), default: SettingValue::Int(set_int(mn, mx, d)) }
}
pub fn s_double(key: u32, d: F64, mn: F64, mx: F64, p: F64) -> SettingDef {
    SettingDef { key, stype: SettingType::Double(mn, mx, p), default: SettingValue::Double(init_double(d, mn, mx, p, false)) }
}
pub fn s_float(key: u32, d: F32, mn: F32, mx: F32, p: F32, precision_first: bool) -> SettingDef {
    SettingDef { key, stype: SettingType::Float(mn, mx, p), default: SettingValue::Float(init_float(d, mn, mx, p, precision_first)) }
}
pub fn s_enum(key: u32, names: u32, d: i32) -> SettingDef {
    SettingDef { key, stype: SettingType::Enum(names), default: SettingValue::Enum(d) }
}
pub fn s_seed() -> SettingDef {
    SettingDef { key: K_SEED, stype: SettingType::NullableInt, default: SettingValue::OptInt(None) }
}
pub fn s_diff(key: u32, ext_min: Option<F32>) -> SettingDef {
    SettingDef { key, stype: SettingType::Difficulty(F32::from_bits(0), F32::from_bits(0x4120_0000) /* 10f */, ext_min, Some(F32::from_bits(0x4130_0000) /* 11f */)), default: SettingValue::OptFloat(None) }
}


/// `(double)0.1f` etc. (`BindableDouble` initialisers with float literals); spec `f32d`
pub fn f32d(x: F32) -> F64 {
    x.to_f64()
}

/// The settings of every osu! mod, by (upper-case) acronym; spec `Settings.table`
pub fn table(acr: &[u32]) -> Option<Vec<SettingDef>> {
    // one fn per table entry + an index lookup with early returns: the original single
    // `else if` chain over a mutable `Vec` needed 1.6 GB in Aeneas (joins), impl/STYLE.md §5
    match table_index(acr) {
        0 => Some(table_ez()),
        1 => Some(Vec::new()),
        2 => Some(table_ht()),
        3 => Some(table_dc()),
        4 => Some(table_sd()),
        5 => Some(table_pf()),
        6 => Some(table_dt()),
        7 => Some(table_nc()),
        8 => Some(table_hd()),
        9 => Some(table_fl()),
        10 => Some(table_ac()),
        11 => Some(table_tp()),
        12 => Some(table_da()),
        13 => Some(table_cl()),
        14 => Some(table_rd()),
        15 => Some(table_mr()),
        16 => Some(table_wg()),
        17 => Some(table_gr()),
        18 => Some(table_df()),
        19 => Some(table_wu()),
        20 => Some(table_wd()),
        21 => Some(table_br()),
        22 => Some(table_ad()),
        23 => Some(table_mu()),
        24 => Some(table_ns()),
        25 => Some(table_mg()),
        26 => Some(table_rp()),
        27 => Some(table_as()),
        28 => Some(table_dp()),
        29 => Some(table_bm()),
        _ => None,
    }
}

/// part of spec `table`: position of `acr` in the table (first match; 1000 = unknown)
pub fn table_index(acr: &[u32]) -> u32 {
    if str_eq(acr, b"EZ") {
        return 0;
    }
    if has_no_settings(acr) {
        return 1;
    }
    if str_eq(acr, b"HT") {
        return 2;
    }
    if str_eq(acr, b"DC") {
        return 3;
    }
    if str_eq(acr, b"SD") {
        return 4;
    }
    if str_eq(acr, b"PF") {
        return 5;
    }
    if str_eq(acr, b"DT") {
        return 6;
    }
    if str_eq(acr, b"NC") {
        return 7;
    }
    if str_eq(acr, b"HD") {
        return 8;
    }
    if str_eq(acr, b"FL") {
        return 9;
    }
    if str_eq(acr, b"AC") {
        return 10;
    }
    if str_eq(acr, b"TP") {
        return 11;
    }
    if str_eq(acr, b"DA") {
        return 12;
    }
    if str_eq(acr, b"CL") {
        return 13;
    }
    if str_eq(acr, b"RD") {
        return 14;
    }
    if str_eq(acr, b"MR") {
        return 15;
    }
    if str_eq(acr, b"WG") {
        return 16;
    }
    if str_eq(acr, b"GR") {
        return 17;
    }
    if str_eq(acr, b"DF") {
        return 18;
    }
    if str_eq(acr, b"WU") {
        return 19;
    }
    if str_eq(acr, b"WD") {
        return 20;
    }
    if str_eq(acr, b"BR") {
        return 21;
    }
    if str_eq(acr, b"AD") {
        return 22;
    }
    if str_eq(acr, b"MU") {
        return 23;
    }
    if str_eq(acr, b"NS") {
        return 24;
    }
    if str_eq(acr, b"MG") {
        return 25;
    }
    if str_eq(acr, b"RP") {
        return 26;
    }
    if str_eq(acr, b"AS") {
        return 27;
    }
    if str_eq(acr, b"DP") {
        return 28;
    }
    if str_eq(acr, b"BM") {
        return 29;
    }
    1000
}

/// part of spec `table`: the entry of `EZ`
pub fn table_ez() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_int(K_RETRIES, 2, 0, 10));
    v
}

/// part of spec `table`: the entry of `HT`
pub fn table_ht() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_SPEED_CHANGE, F64::from_bits(0x3FE8_0000_0000_0000) /* 0.75 */, F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */, F64::from_bits(0x3FEF_AE14_7AE1_47AE) /* 0.99 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_bool(K_ADJUST_PITCH, false));
    v
}

/// part of spec `table`: the entry of `DC`
pub fn table_dc() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_SPEED_CHANGE, F64::from_bits(0x3FE8_0000_0000_0000) /* 0.75 */, F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */, F64::from_bits(0x3FEF_AE14_7AE1_47AE) /* 0.99 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v
}

/// part of spec `table`: the entry of `SD`
pub fn table_sd() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_bool(K_FAIL_ON_SLIDER_TAIL, false));
    v.push(s_bool(K_RESTART, false));
    v
}

/// part of spec `table`: the entry of `PF`
pub fn table_pf() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_bool(K_RESTART, true));
    v
}

/// part of spec `table`: the entry of `DT`
pub fn table_dt() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_SPEED_CHANGE, F64::from_bits(0x3FF8_0000_0000_0000) /* 1.5 */, F64::from_bits(0x3FF0_28F5_C28F_5C29) /* 1.01 */, F64::from_bits(0x4000_0000_0000_0000) /* 2 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_bool(K_ADJUST_PITCH, false));
    v
}

/// part of spec `table`: the entry of `NC`
pub fn table_nc() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_SPEED_CHANGE, F64::from_bits(0x3FF8_0000_0000_0000) /* 1.5 */, F64::from_bits(0x3FF0_28F5_C28F_5C29) /* 1.01 */, F64::from_bits(0x4000_0000_0000_0000) /* 2 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v
}

/// part of spec `table`: the entry of `HD`
pub fn table_hd() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_bool(K_ONLY_FADE_APPROACH_CIRCLES, false));
    v
}

/// part of spec `table`: the entry of `FL`
pub fn table_fl() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_FOLLOW_DELAY, F64::from_bits(0x405E_0000_0000_0000) /* 120 */, F64::from_bits(0x405E_0000_0000_0000) /* 120 */, F64::from_bits(0x4092_C000_0000_0000) /* 1200 */, F64::from_bits(0x405E_0000_0000_0000) /* 120 */));
    v.push(s_float(K_SIZE_MULTIPLIER, F32::from_bits(0x3F80_0000) /* 1f */, F32::from_bits(0x3F00_0000) /* 0.5f */, F32::from_bits(0x4000_0000) /* 2f */, F32::from_bits(0x3DCC_CCCD) /* 0.1f */, false));
    v.push(s_bool(K_COMBO_BASED_SIZE, true));
    v
}

/// part of spec `table`: the entry of `AC`
pub fn table_ac() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_MINIMUM_ACCURACY, F64::from_bits(0x3FEC_CCCC_CCCC_CCCD) /* 0.9 */, F64::from_bits(0x3FE3_3333_3333_3333) /* 0.6 */, F64::from_bits(0x3FEF_F7CE_D916_872B) /* 0.999 */, F64::from_bits(0x3F50_624D_D2F1_A9FC) /* 0.001 */));
    v.push(s_enum(K_ACCURACY_JUDGE_MODE, T_ACCURACY_JUDGE_MODE, 0));
    v.push(s_bool(K_RESTART, false));
    v
}

/// part of spec `table`: the entry of `TP`
pub fn table_tp() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_seed());
    v.push(s_bool(K_METRONOME, true));
    v
}

/// part of spec `table`: the entry of `DA`
pub fn table_da() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_diff(K_CIRCLE_SIZE, None));
    v.push(s_diff(K_APPROACH_RATE, Some(F32::from_bits(0xC120_0000) /* -10f */)));
    v.push(s_diff(K_DRAIN_RATE, None));
    v.push(s_diff(K_OVERALL_DIFFICULTY, None));
    v.push(s_bool(K_EXTENDED_LIMITS, false));
    v
}

/// part of spec `table`: the entry of `CL`
pub fn table_cl() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_bool(K_NO_SLIDER_HEAD_ACCURACY, true));
    v.push(s_bool(K_CLASSIC_NOTE_LOCK, true));
    v.push(s_bool(K_ALWAYS_PLAY_TAIL_SAMPLE, true));
    v.push(s_bool_plain(K_FADE_HIT_CIRCLE_EARLY, true));
    v.push(s_bool_plain(K_CLASSIC_HEALTH, true));
    v
}

/// part of spec `table`: the entry of `RD`
pub fn table_rd() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_ANGLE_SHARPNESS, F32::from_bits(0x40E0_0000) /* 7f */, F32::from_bits(0x3F80_0000) /* 1f */, F32::from_bits(0x4120_0000) /* 10f */, F32::from_bits(0x3DCC_CCCD) /* 0.1f */, false));
    v.push(s_seed());
    v
}

/// part of spec `table`: the entry of `MR`
pub fn table_mr() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_enum(K_REFLECTION, T_REFLECTION, 0));
    v
}

/// part of spec `table`: the entry of `WG`
pub fn table_wg() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_STRENGTH, F64::from_bits(0x3FF0_0000_0000_0000) /* 1 */, f32d(F32::from_bits(0x3DCC_CCCD) /* 0.1f */), f32d(F32::from_bits(0x4000_0000) /* 2f */), f32d(F32::from_bits(0x3DCC_CCCD) /* 0.1f */)));
    v
}

/// part of spec `table`: the entry of `GR`
pub fn table_gr() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_START_SCALE, F32::from_bits(0x3F00_0000) /* 0.5f */, F32::from_bits(0), F32::from_bits(0x3F7D_70A4) /* 0.99f */, F32::from_bits(0x3C23_D70A) /* 0.01f */, false));
    v
}

/// part of spec `table`: the entry of `DF`
pub fn table_df() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_START_SCALE, F32::from_bits(0x4000_0000) /* 2f */, F32::from_bits(0x3F80_0000) /* 1f */, F32::from_bits(0x41C8_0000) /* 25f */, F32::from_bits(0x3DCC_CCCD) /* 0.1f */, false));
    v
}

/// part of spec `table`: the entry of `WU`
pub fn table_wu() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_INITIAL_RATE, F64::from_bits(0x3FF0_0000_0000_0000) /* 1 */, F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */, F64::from_bits(0x3FFF_D70A_3D70_A3D7) /* 1.99 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_double(K_FINAL_RATE, F64::from_bits(0x3FF8_0000_0000_0000) /* 1.5 */, F64::from_bits(0x3FE0_51EB_851E_B852) /* 0.51 */, F64::from_bits(0x4000_0000_0000_0000) /* 2 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_bool(K_ADJUST_PITCH, true));
    v
}

/// part of spec `table`: the entry of `WD`
pub fn table_wd() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_INITIAL_RATE, F64::from_bits(0x3FF0_0000_0000_0000) /* 1 */, F64::from_bits(0x3FE0_51EB_851E_B852) /* 0.51 */, F64::from_bits(0x4000_0000_0000_0000) /* 2 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_double(K_FINAL_RATE, F64::from_bits(0x3FE8_0000_0000_0000) /* 0.75 */, F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */, F64::from_bits(0x3FFF_D70A_3D70_A3D7) /* 1.99 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_bool(K_ADJUST_PITCH, true));
    v
}

/// part of spec `table`: the entry of `BR`
pub fn table_br() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_SPIN_SPEED, F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */, F64::from_bits(0x3F94_7AE1_47AE_147B) /* 0.02 */, F64::from_bits(0x4028_0000_0000_0000) /* 12 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_enum(K_DIRECTION, T_SPIN_DIRECTION, 0));
    v
}

/// part of spec `table`: the entry of `AD`
pub fn table_ad() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_SCALE, F32::from_bits(0x4080_0000) /* 4f */, F32::from_bits(0x3FC0_0000) /* 1.5f */, F32::from_bits(0x4120_0000) /* 10f */, F32::from_bits(0x3DCC_CCCD) /* 0.1f */, true));
    v.push(s_enum(K_STYLE, T_AD_STYLE, 1));
    v
}

/// part of spec `table`: the entry of `MU`
pub fn table_mu() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_bool(K_INVERSE_MUTING, false));
    v.push(s_bool(K_ENABLE_METRONOME, true));
    v.push(s_int(K_MUTE_COMBO_COUNT, 100, 0, 500));
    v.push(s_bool(K_AFFECTS_HIT_SOUNDS, true));
    v
}

/// part of spec `table`: the entry of `NS`
pub fn table_ns() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_int(K_HIDDEN_COMBO_COUNT, 10, 0, 50));
    v
}

/// part of spec `table`: the entry of `MG`
pub fn table_mg() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_ATTRACTION_STRENGTH, F32::from_bits(0x3F00_0000) /* 0.5f */, F32::from_bits(0x3D4C_CCCD) /* 0.05f */, F32::from_bits(0x3F80_0000) /* 1f */, F32::from_bits(0x3D4C_CCCD) /* 0.05f */, true));
    v
}

/// part of spec `table`: the entry of `RP`
pub fn table_rp() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_REPULSION_STRENGTH, F32::from_bits(0x3F00_0000) /* 0.5f */, F32::from_bits(0x3D4C_CCCD) /* 0.05f */, F32::from_bits(0x3F80_0000) /* 1f */, F32::from_bits(0x3D4C_CCCD) /* 0.05f */, true));
    v
}

/// part of spec `table`: the entry of `AS`
pub fn table_as() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_double(K_INITIAL_RATE, F64::from_bits(0x3FF0_0000_0000_0000) /* 1 */, F64::from_bits(0x3FE0_0000_0000_0000) /* 0.5 */, F64::from_bits(0x4000_0000_0000_0000) /* 2 */, F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */));
    v.push(s_bool(K_ADJUST_PITCH, true));
    v
}

/// part of spec `table`: the entry of `DP`
pub fn table_dp() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_float(K_MAX_DEPTH, F32::from_bits(0x42C8_0000) /* 100f */, F32::from_bits(0x4248_0000) /* 50f */, F32::from_bits(0x4348_0000) /* 200f */, F32::from_bits(0x4120_0000) /* 10f */, true));
    v.push(s_bool(K_SHOW_APPROACH_CIRCLES, true));
    v
}

/// part of spec `table`: the entry of `BM`
pub fn table_bm() -> Vec<SettingDef> {
    let mut v: Vec<SettingDef> = Vec::new();
    v.push(s_int(K_MAX_SIZE_COMBO_COUNT, 50, 5, 100));
    v.push(s_float(K_MAX_CURSOR_SIZE, F32::from_bits(0x4120_0000) /* 10f */, F32::from_bits(0x40A0_0000) /* 5f */, F32::from_bits(0x4170_0000) /* 15f */, F32::from_bits(0x3F00_0000) /* 0.5f */, false));
    v
}

/// the setting-less acronyms of spec `table` (a separate fn: an `||` chain inside the
/// `else if` chain of `table` makes Charon/Aeneas duplicate the rest of the chain per operand)
pub fn has_no_settings(acr: &[u32]) -> bool {
    str_eq(acr, b"NF") || str_eq(acr, b"HR") || str_eq(acr, b"TC") || str_eq(acr, b"BL") || str_eq(acr, b"ST")
        || str_eq(acr, b"AL") || str_eq(acr, b"SG") || str_eq(acr, b"AT") || str_eq(acr, b"CN") || str_eq(acr, b"RX")
        || str_eq(acr, b"AP") || str_eq(acr, b"SO") || str_eq(acr, b"TR") || str_eq(acr, b"SI") || str_eq(acr, b"FR")
        || str_eq(acr, b"BU") || str_eq(acr, b"SY") || str_eq(acr, b"TD") || str_eq(acr, b"SV2")
}

/// spec `Settings.setValue`
pub fn set_value(vals: &mut Vec<(u32, SettingValue)>, key: u32, v: SettingValue) {
    let mut i = 0;
    while i < vals.len() {
        if vals[i].0 == key {
            vals[i].1 = v;
        }
        i = i + 1;
    }
}

fn type_of(defs: &[SettingDef], k: u32) -> Option<SettingType> {
    let mut i = 0;
    let mut r: Option<SettingType> = None;
    while r.is_none() && i < defs.len() {
        if defs[i].key == k {
            r = Some(defs[i].stype);
        }
        i = i + 1;
    }
    r
}

fn dbl(vals: &[(u32, SettingValue)], k: u32) -> F64 {
    match vals_get(vals, k) {
        Some(SettingValue::Double(x)) => x,
        _ => D0,
    }
}

/// spec `assignF.setD` (`fuel` = the fuel of the nested `assignF` call)
fn set_d(fuel: u32, acr: &[u32], defs: &[SettingDef], vals: &mut Vec<(u32, SettingValue)>, k: u32, x: F64) {
    match type_of(defs, k) {
        Some(SettingType::Double(mn, mx, p)) => match set_double(mn, mx, p, dbl(vals, k), x) {
            Some(y) => assign_f(fuel, acr, defs, vals, k, SettingValue::Double(y)),
            None => {}
        },
        _ => {}
    }
}

fn le(a: F64, b: F64) -> bool {
    a.lt(b) || a.eq(b)
}

/// spec `Settings.assignFuel`: nesting bound of the `ValueChanged` callback chain (at most 2 levels
/// are reachable, D27)
pub const ASSIGN_FUEL: u32 = 4;

/// `Bindable.Value = v` for setting `key` + the mod's `ValueChanged` callbacks; spec `Settings.assign`
pub fn assign(acr: &[u32], defs: &[SettingDef], vals: &mut Vec<(u32, SettingValue)>, key: u32, v: SettingValue) {
    assign_f(ASSIGN_FUEL, acr, defs, vals, key, v)
}

/// `Bindable.Value` assignment + the mod's `ValueChanged` callbacks with explicit nesting fuel; spec
/// `Settings.assignF` (fuel 0: `vals` unchanged; the nested call through `set_d` gets `fuel - 1`).
/// The change test and the callback selection are helpers so that no `&&` chain sits inside the
/// `else if` chain, impl/STYLE.md §5.
pub fn assign_f(fuel: u32, acr: &[u32], defs: &[SettingDef], vals: &mut Vec<(u32, SettingValue)>, key: u32,
                v: SettingValue) {
    if fuel == 0 {
        return;
    }
    let fuel1 = fuel - 1;
    let old = vals_get(vals, key);
    if !assign_changed(old, v) {
        return;
    }
    set_value(vals, key, v);
    let nv = match v {
        SettingValue::Double(x) => x,
        _ => D0,
    };
    let fin = dbl(vals, K_FINAL_RATE);
    let ini = dbl(vals, K_INITIAL_RATE);
    let step = F64::from_bits(0x3F84_7AE1_47AE_147B) /* 0.01 */;
    match assign_rule(acr, key) {
        1 => {
            if le(fin, nv) {
                set_d(fuel1, acr, defs, vals, K_FINAL_RATE, nv.add(step));
            }
        }
        2 => {
            if le(nv, ini) {
                set_d(fuel1, acr, defs, vals, K_INITIAL_RATE, nv.sub(step));
            }
        }
        3 => {
            if le(nv, fin) {
                set_d(fuel1, acr, defs, vals, K_FINAL_RATE, nv.sub(step));
            }
        }
        4 => {
            if le(ini, nv) {
                set_d(fuel1, acr, defs, vals, K_INITIAL_RATE, nv.add(step));
            }
        }
        5 => {
            let mn: i32 = if setting_value_beq(v, SettingValue::Bool(true)) { 1 } else { 0 };
            match vals_get(vals, K_MUTE_COMBO_COUNT) {
                Some(SettingValue::Int(c)) => set_value(vals, K_MUTE_COMBO_COUNT, SettingValue::Int(set_int(mn, 500, c))),
                _ => {}
            }
        }
        _ => {}
    }
}

/// part of spec `Settings.assign`: did the bindable value change (`Equals` semantics per type)
pub fn assign_changed(old: Option<SettingValue>, v: SettingValue) -> bool {
    match (old, v) {
        (Some(SettingValue::Double(a)), SettingValue::Double(b)) => !equals_d(a, b),
        (Some(SettingValue::Float(a)), SettingValue::Float(b)) => !equals_f(a, b),
        (Some(SettingValue::OptFloat(Some(a))), SettingValue::OptFloat(Some(b))) => !equals_f(a, b),
        (Some(a), b) => !setting_value_beq(a, b),
        (None, _) => true,
    }
}

/// part of spec `Settings.assign`: which `ValueChanged` callback fires (0 = none;
/// 1 WU initial, 2 WU final, 3 WD initial, 4 WD final, 5 MU inverse_muting), first match wins
pub fn assign_rule(acr: &[u32], key: u32) -> u32 {
    if str_eq(acr, b"WU") {
        if key == K_INITIAL_RATE { 1 } else if key == K_FINAL_RATE { 2 } else { 0 }
    } else if str_eq(acr, b"WD") {
        if key == K_INITIAL_RATE { 3 } else if key == K_FINAL_RATE { 4 } else { 0 }
    } else if str_eq(acr, b"MU") {
        if key == K_INVERSE_MUTING { 5 } else { 0 }
    } else {
        0
    }
}

/// `APIMod.ToMod(ruleset)` for the osu! ruleset (`settings` in document order); spec `Settings.toMod`
pub fn to_mod(acronym0: &[u32], settings: &[(Str, JsonVal)]) -> ModConfig {
    // split into helpers (loop bodies in callees, owned `Vec`s passed by value) for Aeneas:
    // the inline version failed with "Could not match the contexts" (impl/STYLE.md §5)
    let mut acronym: Str = Vec::new();
    let mut i = 0;
    while i < acronym0.len() {
        acronym.push(ascii_upper(acronym0[i]));
        i = i + 1;
    }
    match table(&acronym) {
        None => ModConfig { acronym: copy_str(acronym0), known: false, settings: Vec::new() },
        Some(defs) => to_mod_known(acronym, defs, settings),
    }
}

/// copy of a string (`acronym0` kept verbatim for unknown mods)
pub fn copy_str(s: &[u32]) -> Str {
    let mut a: Str = Vec::new();
    let mut k = 0;
    while k < s.len() {
        a.push(s[k]);
        k = k + 1;
    }
    a
}

/// part of spec `Settings.toMod`: a known acronym (`defs` = its settings table)
pub fn to_mod_known(acronym: Str, defs: Vec<SettingDef>, settings: &[(Str, JsonVal)]) -> ModConfig {
    let mut vals: Vec<(u32, SettingValue)> = Vec::new();
    let mut k = 0;
    while k < defs.len() {
        vals.push((defs[k].key, defs[k].default));
        k = k + 1;
    }
    if settings.len() == 0 {
        ModConfig { acronym, known: true, settings: vals }
    } else {
        let mut di = 0;
        while di < defs.len() {
            vals = to_mod_apply(&acronym, &defs, vals, defs[di], settings);
            di = di + 1;
        }
        ModConfig { acronym, known: true, settings: vals }
    }
}

/// part of spec `Settings.toMod`: last occurrence of a setting key (`settings.reverse.find?`)
pub fn last_key_index(key: u32, settings: &[(Str, JsonVal)]) -> Option<usize> {
    let mut found: Option<usize> = None;
    let mut s = settings.len();
    while found.is_none() && s > 0 {
        s = s - 1;
        if key_is(key, &settings[s].0) {
            found = Some(s);
        }
    }
    found
}

/// part of spec `Settings.toMod`: the setting type used for parsing (MU's dynamic int minimum)
pub fn to_mod_type(acronym: &[u32], vals: &[(u32, SettingValue)], d: SettingDef) -> SettingType {
    match d.stype {
        SettingType::Int(_, mx) => {
            if str_eq(acronym, b"MU") {
                let inv = match vals_get(vals, K_INVERSE_MUTING) {
                    Some(x) => setting_value_beq(x, SettingValue::Bool(true)),
                    None => false,
                };
                SettingType::Int(if inv { 1 } else { 0 }, mx)
            } else {
                d.stype
            }
        }
        t => t,
    }
}

/// part of spec `Settings.toMod`: apply the JSON value of setting `d` (if present)
pub fn to_mod_apply(acronym: &[u32], defs: &[SettingDef], vals0: Vec<(u32, SettingValue)>, d: SettingDef,
                    settings: &[(Str, JsonVal)]) -> Vec<(u32, SettingValue)> {
    let mut vals = vals0;
    match last_key_index(d.key, settings) {
        None => {}
        Some(si) => {
            let old = match vals_get(&vals, d.key) {
                Some(x) => x,
                None => d.default,
            };
            let ty = to_mod_type(acronym, &vals, d);
            match parse(ty, old, &settings[si].1) {
                Some(v) => assign(acronym, defs, &mut vals, d.key, v),
                None => {}
            }
        }
    }
    vals
}
