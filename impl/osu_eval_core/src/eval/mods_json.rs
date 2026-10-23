//! Port of `OsuModel/Sim/ModsJson.lean` (namespace `SimJson`): the strict JSON reader used for the
//! `--mods` option and the lazer score info of `.osr` files, the Newtonsoft-like classification of
//! setting values (`toSetting`) and `parseMods` (`List<APIMod>` -> `APIMod.ToMod`).
//! The spec's parser is `StateT (List Char) (Except String)`; here every parser takes the input as a
//! slice of Unicode scalar values plus a position and returns the new position (the remaining list
//! of the spec = `s[p..]`).
use crate::beatmap::dotnet::Str;
use crate::beatmap::mod_settings::{to_mod, JsonVal, ModConfig};
use crate::float::F64;
use crate::net::parse::double_parse;
use alloc::vec::Vec;

/// spec `SimJson.V` (no `derive(Clone)`: never cloned, and Aeneas translates the derived clone of this
/// recursive enum as a non-recursive definition)
pub enum V {
    /// `num text`
    Num(Str),
    /// `str s`
    VStr(Str),
    Bool(bool),
    Null,
    Arr(Vec<V>),
    Obj(Vec<(Str, V)>),
}

/// The parser's `throw` messages (spec strings in `text`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum JsonErr {
    /// `s!"expected {c}"`
    Expected(u32),
    /// `"bad \\u"`
    BadU,
    /// `"unterminated string"`
    Unterminated,
    /// `"bad array"`
    BadArray,
    /// `"bad object"`
    BadObject,
    /// `"bad value"`
    BadValue,
    /// `"internal: JSON nesting fuel exhausted"` (unreachable: `value` starts with fuel = remaining
    /// length + 1, D27)
    Fuel,
}

/// `ws`'s character test (also `decodeScoreInfo`'s trailing-content test)
pub fn is_ws(c: u32) -> bool {
    c == 0x20 || c == 0x0A || c == 0x09 || c == 0x0D
}

/// spec `ws` (= `modify wsL`): skip `' ' '\n' '\t' '\r'`
pub fn ws(s: &[u32], p0: usize) -> usize {
    let mut p = p0;
    while p < s.len() && is_ws(s[p]) {
        p = p + 1;
    }
    p
}

/// spec `expect c`
pub fn expect(s: &[u32], p0: usize, c: u32) -> Result<usize, JsonErr> {
    let p = ws(s, p0);
    if p < s.len() && s[p] == c {
        Ok(p + 1)
    } else {
        Err(JsonErr::Expected(c))
    }
}

/// `Char.isDigit`
pub fn is_digit(c: u32) -> bool {
    0x30 <= c && c <= 0x39
}

/// spec `hexVal` (`Nat` subtraction truncates: non-hex characters below `'A'` give 10)
pub fn hex_val(c: u32) -> u64 {
    if is_digit(c) {
        (c - 0x30) as u64
    } else if 0x61 <= c && c <= 0x66 {
        (c - 0x61 + 10) as u64
    } else if c >= 0x41 {
        (c - 0x41) as u64 + 10
    } else {
        10
    }
}

/// `Char.ofNat n` (invalid scalar values, i.e. surrogates and values >= 0x110000, give `'\0'`)
pub fn char_of_nat(n: u64) -> u32 {
    if n < 0xD800 || (0xDFFF < n && n < 0x110000) {
        n as u32
    } else {
        0
    }
}

/// spec `strBody`/`strBodyL` (after the opening quote): the string contents and the position after the
/// closing quote. The spec's recursion on the remaining list is a loop over `p`.
pub fn str_body(s: &[u32], p0: usize) -> Result<(Str, usize), JsonErr> {
    let n = s.len();
    let mut acc: Str = Vec::new();
    let mut p = p0;
    let mut done = false;
    let mut err: Option<JsonErr> = None;
    while !done && err.is_none() {
        if p >= n {
            err = Some(JsonErr::Unterminated);
        } else if s[p] == 0x22 {
            p = p + 1;
            done = true;
        } else if s[p] == 0x5C && p + 1 < n {
            let e = s[p + 1];
            p = p + 2;
            if e == 0x75 {
                // 'u': four more characters
                if p + 4 <= n {
                    let v = ((hex_val(s[p]) * 16 + hex_val(s[p + 1])) * 16 + hex_val(s[p + 2])) * 16 + hex_val(s[p + 3]);
                    acc.push(char_of_nat(v));
                    p = p + 4;
                } else {
                    err = Some(JsonErr::BadU);
                }
            } else {
                acc.push(escape_char(e));
            }
        } else {
            acc.push(s[p]);
            p = p + 1;
        }
    }
    match err {
        Some(e) => Err(e),
        None => Ok((acc, p)),
    }
}

/// part of spec `strBody`: the character of a one-character escape (`\n \t \r \b \f`; any other
/// character stands for itself)
pub fn escape_char(e: u32) -> u32 {
    match e {
        0x6E => 0x0A,
        0x74 => 0x09,
        0x72 => 0x0D,
        0x62 => 0x08,
        0x66 => 0x0C,
        _ => e,
    }
}

/// part of spec `value`: `isNumChar`
pub fn is_num_char(c: u32) -> bool {
    is_digit(c) || c == 0x2D || c == 0x2B || c == 0x2E || c == 0x65 || c == 0x45
}

/// `s[p..]` starts with the ASCII literal `lit`
pub fn has_lit(s: &[u32], p: usize, lit: &[u8]) -> bool {
    if p + lit.len() > s.len() {
        false
    } else {
        let mut k = 0;
        let mut ok_ = true;
        while k < lit.len() {
            if s[p + k] != lit[k] as u32 {
                ok_ = false;
            }
            k = k + 1;
        }
        ok_
    }
}

/// spec `value`: `valueF` with fuel = (remaining input).length + 1
pub fn value(s: &[u32], p0: usize) -> Result<(V, usize), JsonErr> {
    let rest = if p0 < s.len() { s.len() - p0 } else { 0 };
    value_f(s, p0, rest + 1)
}

/// spec `valueF` (explicit nesting fuel, D27): fuel 0 rejects; the nested values of an array or
/// object get `fuel - 1`
pub fn value_f(s: &[u32], p0: usize, fuel: usize) -> Result<(V, usize), JsonErr> {
    if fuel == 0 {
        return Err(JsonErr::Fuel);
    }
    let fuel1 = fuel - 1;
    let p = ws(s, p0);
    let n = s.len();
    if p < n && s[p] == 0x22 {
        let (t, q) = tri!(str_body(s, p + 1));
        Ok((V::VStr(t), q))
    } else if p < n && s[p] == 0x5B {
        array_value(s, p + 1, fuel1)
    } else if p < n && s[p] == 0x7B {
        object_value(s, p + 1, fuel1)
    } else if has_lit(s, p, b"true") {
        Ok((V::Bool(true), p + 4))
    } else if has_lit(s, p, b"false") {
        Ok((V::Bool(false), p + 5))
    } else if has_lit(s, p, b"null") {
        Ok((V::Null, p + 4))
    } else {
        number_value(s, p)
    }
}

/// part of spec `value`: the number branch (`takeWhile isNumChar`, non-empty)
pub fn number_value(s: &[u32], p: usize) -> Result<(V, usize), JsonErr> {
    let mut q = p;
    while q < s.len() && is_num_char(s[q]) {
        q = q + 1;
    }
    if q == p {
        Err(JsonErr::BadValue)
    } else {
        let mut t: Str = Vec::new();
        let mut k = p;
        while k < q {
            t.push(s[k]);
            k = k + 1;
        }
        Ok((V::Num(t), q))
    }
}

/// part of spec `value`: the array branch (after `[`)
pub fn array_value(s: &[u32], p0: usize, fuel: usize) -> Result<(V, usize), JsonErr> {
    let p = ws(s, p0);
    if p < s.len() && s[p] == 0x5D {
        Ok((V::Arr(Vec::new()), p + 1))
    } else {
        let (xs, q) = tri!(array_items(s, p, fuel));
        Ok((V::Arr(xs), q))
    }
}

/// part of spec `value`: the `repeat` loop of the array branch (elements: `valueF fuel`)
pub fn array_items(s: &[u32], p0: usize, fuel: usize) -> Result<(Vec<V>, usize), JsonErr> {
    array_items_rec(s, p0, fuel, Vec::new())
}

/// part of spec `value`: the `repeat` loop of the array branch as recursion, one iteration per call
/// (Aeneas: a `loop` inside the `value_f` recursion group is not provably monotone, D25)
pub fn array_items_rec(s: &[u32], p: usize, fuel: usize, xs0: Vec<V>) -> Result<(Vec<V>, usize), JsonErr> {
    let mut xs = xs0;
    match value_f(s, p, fuel) {
        Err(e) => Err(e),
        Ok((v, q)) => {
            xs.push(v);
            let r = ws(s, q);
            if r < s.len() && s[r] == 0x2C {
                array_items_rec(s, r + 1, fuel, xs)
            } else if r < s.len() && s[r] == 0x5D {
                Ok((xs, r + 1))
            } else {
                Err(JsonErr::BadArray)
            }
        }
    }
}

/// part of spec `value`: the object branch (after `{`)
pub fn object_value(s: &[u32], p0: usize, fuel: usize) -> Result<(V, usize), JsonErr> {
    let p = ws(s, p0);
    if p < s.len() && s[p] == 0x7D {
        Ok((V::Obj(Vec::new()), p + 1))
    } else {
        let (kvs, q) = tri!(object_items(s, p, fuel));
        Ok((V::Obj(kvs), q))
    }
}

/// part of spec `value`: one member of the object `repeat` loop (`expect '"'`, `strBody`,
/// `expect ':'`, `value`)
pub fn object_member(s: &[u32], p0: usize, fuel: usize) -> Result<((Str, V), usize), JsonErr> {
    let p1 = tri!(expect(s, p0, 0x22));
    let (k, p2) = tri!(str_body(s, p1));
    let p3 = tri!(expect(s, p2, 0x3A));
    let (v, p4) = tri!(value_f(s, p3, fuel));
    Ok(((k, v), p4))
}

/// part of spec `value`: the `repeat` loop of the object branch (values: `valueF fuel`)
pub fn object_items(s: &[u32], p0: usize, fuel: usize) -> Result<(Vec<(Str, V)>, usize), JsonErr> {
    object_items_rec(s, p0, fuel, Vec::new())
}

/// part of spec `value`: the `repeat` loop of the object branch as recursion, one iteration per call
/// (as `array_items_rec`)
pub fn object_items_rec(s: &[u32], p: usize, fuel: usize, kvs0: Vec<(Str, V)>) -> Result<(Vec<(Str, V)>, usize), JsonErr> {
    let mut kvs = kvs0;
    match object_member(s, p, fuel) {
        Err(e) => Err(e),
        Ok((kv, q)) => {
            kvs.push(kv);
            let r = ws(s, q);
            if r < s.len() && s[r] == 0x2C {
                object_items_rec(s, r + 1, fuel, kvs)
            } else if r < s.len() && s[r] == 0x7D {
                Ok((kvs, r + 1))
            } else {
                Err(JsonErr::BadObject)
            }
        }
    }
}

/// Saturation bound of `nat_sat` (> every |n| that `toSetting`/`jsonInt` accept: 2^64)
pub const NAT_CAP: u128 = 18446744073709551616;

/// `String.isNat` (Lean 4.35, `String.Slice.isNat`) on `s[lo..hi]`: non-empty, digits, `_` only
/// between digits
pub fn is_nat(s: &[u32], lo: usize, hi: usize) -> bool {
    let mut last_was_digit = false;
    let mut ok_ = true;
    let mut i = lo;
    while ok_ && i < hi {
        let c = s[i];
        if c == 0x5F {
            if !last_was_digit {
                ok_ = false;
            }
            last_was_digit = false;
        } else if is_digit(c) {
            last_was_digit = true;
        } else {
            ok_ = false;
        }
        i = i + 1;
    }
    ok_ && last_was_digit
}

/// `String.toNat!` on `s[lo..hi]`, saturated at `NAT_CAP` (only compared against 64-bit ranges);
/// not a natural number -> the `panic!` default 0
pub fn nat_sat(s: &[u32], lo: usize, hi: usize) -> u128 {
    if !is_nat(s, lo, hi) {
        0
    } else {
        let mut v: u128 = 0;
        let mut i = lo;
        while i < hi {
            let c = s[i];
            if c != 0x5F {
                let w = v * 10 + (c - 0x30) as u128;
                v = if w > NAT_CAP { NAT_CAP } else { w };
            }
            i = i + 1;
        }
        v
    }
}

/// `t.startsWith "-"`
pub fn starts_minus(t: &[u32]) -> bool {
    t.len() > 0 && t[0] == 0x2D
}

/// `t.any (fun c => c == '.' || c == 'e' || c == 'E')`
pub fn has_frac_or_exp(t: &[u32]) -> bool {
    let mut r = false;
    let mut i = 0;
    while i < t.len() {
        if t[i] == 0x2E || t[i] == 0x65 || t[i] == 0x45 {
            r = true;
        }
        i = i + 1;
    }
    r
}

/// The integer of a number literal without `.`/`e`/`E`, as in the spec:
/// `if t.startsWith "-" then -((t.drop 1).toNat!) else t.toNat!`, as (negative, |n| saturated)
pub fn int_of_text(t: &[u32]) -> (bool, u128) {
    if starts_minus(t) {
        (true, nat_sat(t, 1, t.len()))
    } else {
        (false, nat_sat(t, 0, t.len()))
    }
}

/// `lo <= n && n <= hi` for `n` from `int_of_text`, with `lo = -2^b`, `hi = 2^b - 1` given as
/// magnitudes (`lo_mag = 2^b`, `hi = 2^b - 1`)
pub fn in_range(neg: bool, m: u128, lo_mag: u128, hi: u128) -> bool {
    if neg {
        m <= lo_mag
    } else {
        m <= hi
    }
}

/// `9223372036854775808` (= -Int64.min)
pub const I64_LO_MAG: u128 = 9223372036854775808;
/// `9223372036854775807`
pub const I64_HI: u128 = 9223372036854775807;
/// `2147483648` (= -Int32.min)
pub const I32_LO_MAG: u128 = 2147483648;
/// `2147483647`
pub const I32_HI: u128 = 2147483647;

/// spec `toSetting`
pub fn to_setting(v: &V) -> JsonVal {
    match v {
        V::Num(t) => {
            if has_frac_or_exp(t) {
                match double_parse(t) {
                    Ok(d) => JsonVal::Double(d),
                    Err(_) => JsonVal::Null,
                }
            } else {
                let (neg, m) = int_of_text(t);
                if in_range(neg, m, I64_LO_MAG, I64_HI) {
                    JsonVal::Long(long_of(neg, m))
                } else {
                    JsonVal::Big
                }
            }
        }
        V::VStr(s) => JsonVal::Str(s.clone()),
        V::Bool(b) => JsonVal::Bool(*b),
        V::Null => JsonVal::Null,
        V::Arr(_) => JsonVal::Big,
        V::Obj(_) => JsonVal::Big,
    }
}

/// the `Int` `-m` / `m` (in the 64-bit range) as an `i64`
pub fn long_of(neg: bool, m: u128) -> i64 {
    if neg {
        if m == I64_LO_MAG {
            i64::MIN
        } else {
            -(m as i64)
        }
    } else {
        m as i64
    }
}

/// `parseMods` failures
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ModsJsonErr {
    Json(JsonErr),
    /// "mods is not an array"
    NotArray,
    /// "mod is not an object"
    NotObject,
}

/// spec `kvs.find? (·.1 == k)` (first occurrence): its index
pub fn find_first(kvs: &[(Str, V)], key: &[u8]) -> Option<usize> {
    // the loop state is updated unconditionally (Aeneas: "Could not match the contexts" otherwise)
    let mut r: Option<usize> = None;
    let mut i = 0;
    while r.is_none() && i < kvs.len() {
        r = first_match(key_is_at(kvs, i, key), i);
        i = i + 1;
    }
    r
}

/// `kvs[i].1 == key`
pub fn key_is_at(kvs: &[(Str, V)], i: usize, key: &[u8]) -> bool {
    crate::beatmap::dotnet::str_eq(&kvs[i].0, key)
}

/// `if m then some i else none`
pub fn first_match(m: bool, i: usize) -> Option<usize> {
    if m { Some(i) } else { None }
}

/// spec `kvs.reverse.find? (·.1 == k)` (last occurrence): its index
pub fn find_last(kvs: &[(Str, V)], key: &[u8]) -> Option<usize> {
    let mut r: Option<usize> = None;
    let mut i = kvs.len();
    while r.is_none() && i > 0 {
        i = i - 1;
        r = first_match(key_is_at(kvs, i, key), i);
    }
    r
}

/// `ss.map fun (k, x) => (k, toSetting x)`
pub fn settings_of(ss: &[(Str, V)]) -> Vec<(Str, JsonVal)> {
    let mut out: Vec<(Str, JsonVal)> = Vec::new();
    let mut i = 0;
    while i < ss.len() {
        out.push((ss[i].0.clone(), to_setting(&ss[i].1)));
        i = i + 1;
    }
    out
}

/// part of spec `parseMods`: one array element
pub fn parse_mod(x: &V) -> Result<ModConfig, ModsJsonErr> {
    match x {
        V::Obj(kvs) => {
            let acr: Str = match find_first(kvs, b"acronym") {
                Some(i) => acronym_str(&kvs[i].1),
                None => Vec::new(),
            };
            let settings: Vec<(Str, JsonVal)> = match find_first(kvs, b"settings") {
                Some(i) => settings_obj(&kvs[i].1),
                None => Vec::new(),
            };
            Ok(to_mod(&acr, &settings))
        }
        _ => Err(ModsJsonErr::NotObject),
    }
}

/// part of spec `parseMods`: `some (_, .str a) => a | _ => ""`
pub fn acronym_str(v: &V) -> Str {
    match v {
        V::VStr(a) => a.clone(),
        _ => Vec::new(),
    }
}

/// part of spec `parseMods`: `some (_, .obj ss) => ss.map … | _ => []`
pub fn settings_obj(v: &V) -> Vec<(Str, JsonVal)> {
    match v {
        V::Obj(ss) => settings_of(ss),
        _ => Vec::new(),
    }
}

/// part of spec `parseMods`: `xs.mapM …`
pub fn parse_mod_list(xs: &[V]) -> Result<Vec<ModConfig>, ModsJsonErr> {
    let mut out: Vec<ModConfig> = Vec::new();
    let mut err: Option<ModsJsonErr> = None;
    let mut i = 0;
    while err.is_none() && i < xs.len() {
        match parse_mod(&xs[i]) {
            Ok(m) => out.push(m),
            Err(e) => err = Some(e),
        }
        i = i + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(out),
    }
}

/// spec `parseMods`: `List<APIMod>` JSON -> decoded mod configs (`APIMod.ToMod`); trailing input
/// is ignored, as in the spec
pub fn parse_mods(s: &[u32]) -> Result<Vec<ModConfig>, ModsJsonErr> {
    match value(s, 0) {
        Err(e) => Err(ModsJsonErr::Json(e)),
        Ok((v, _)) => match v {
            V::Arr(xs) => parse_mod_list(&xs),
            _ => Err(ModsJsonErr::NotArray),
        },
    }
}

/// keeps `F64` in scope for the doc links of `toSetting` (`.double`)
pub type Double = F64;

/// Message texts (not translated; excluded from Charon).
pub mod text {
    use super::{JsonErr, ModsJsonErr};
    /// the spec's `throw` string of a `JsonErr`
    pub fn json_err(e: JsonErr) -> String {
        match e {
            JsonErr::Expected(c) => format!("expected {}", char::from_u32(c).unwrap_or('\u{0}')),
            JsonErr::BadU => "bad \\u".to_string(),
            JsonErr::Unterminated => "unterminated string".to_string(),
            JsonErr::BadArray => "bad array".to_string(),
            JsonErr::BadObject => "bad object".to_string(),
            JsonErr::BadValue => "bad value".to_string(),
            JsonErr::Fuel => "internal: JSON nesting fuel exhausted".to_string(),
        }
    }
    pub fn mods_json_err(e: ModsJsonErr) -> String {
        match e {
            ModsJsonErr::Json(j) => json_err(j),
            ModsJsonErr::NotArray => "mods is not an array".to_string(),
            ModsJsonErr::NotObject => "mod is not an object".to_string(),
        }
    }
}
