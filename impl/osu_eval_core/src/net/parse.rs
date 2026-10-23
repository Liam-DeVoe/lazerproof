//! Port of `OsuModel/Net/Parse.lean`: `double.Parse`, `float.Parse`, `int.Parse`
//! (InvariantCulture) and lazer's `Parsing.*`.
//!
//! Strings are slices of Unicode scalar values (`&[u32]`, = Lean `List Char`); the Lean
//! list-recursive helpers take a start index instead of a list suffix. The decimal mantissa is
//! kept as its digit string (the Lean model's `Nat`); the final correctly rounded
//! decimal -> binary step is the trusted primitive `F64/F32::parse_decimal` (= `decToBits`).
use super::basic::{NetExn, F32_NAN, F32_POS_INF, F64_NAN, F64_POS_INF};
use crate::float::{F32, F64};
use alloc::vec::Vec;

/// `Number.IsWhite`: U+0009–U+000D and U+0020; spec `Parse.isWhite`
pub fn is_white(c: u32) -> bool {
    c == 0x20 || (0x09 <= c && c <= 0x0D)
}

/// `char.IsWhiteSpace`; spec `Parse.isUnicodeWhiteSpace`
pub fn is_unicode_white_space(c: u32) -> bool {
    is_white(c)
        || c == 0x85
        || c == 0xA0
        || c == 0x1680
        || (0x2000 <= c && c <= 0x200A)
        || c == 0x2028
        || c == 0x2029
        || c == 0x202F
        || c == 0x205F
        || c == 0x3000
}

/// spec `Parse.isDigit`
pub fn is_digit(c: u32) -> bool {
    0x30 <= c && c <= 0x39
}

/// `dropWhile isWhite` from index `i`: first index `>= i` that is not white (or `len`)
pub fn skip_white(s: &[u32], i: usize) -> usize {
    let mut j = i;
    while j < s.len() && is_white(s[j]) {
        j = j + 1;
    }
    j
}

/// spec `Parse.allNul` on the suffix `s[i..]`
pub fn all_nul(s: &[u32], i: usize) -> bool {
    let mut j = i;
    let mut ok = true;
    while j < s.len() {
        if s[j] != 0 {
            ok = false;
        }
        j = j + 1;
    }
    ok
}

/// Lean `Char.toLower` (ASCII only)
pub fn ascii_lower(c: u32) -> u32 {
    if 0x41 <= c && c <= 0x5A { c + 32 } else { c }
}

/// Lean `Char.toUpper` (ASCII only)
pub fn ascii_upper(c: u32) -> u32 {
    if 0x61 <= c && c <= 0x7A { c - 32 } else { c }
}

/// spec `Parse.eqIgnoreCase` on `s[lo..hi]` against an ASCII literal
pub fn eq_ignore_case(s: &[u32], lo: usize, hi: usize, lit: &[u8]) -> bool {
    if hi < lo || hi - lo != lit.len() {
        false
    } else {
        let mut i = 0;
        let mut ok = true;
        while i < lit.len() {
            if ascii_lower(s[lo + i]) != ascii_lower(lit[i] as u32) {
                ok = false;
            }
            i = i + 1;
        }
        ok
    }
}

/// spec `Parse.Num`: `mant` is the digit string `digits` (leading zeros dropped),
/// value = `(-1)^neg * mant * 10^exp10`; `sat = Some(negExp)` = exponent saturation.
pub struct Num {
    pub neg: bool,
    pub digits: Vec<u8>,
    pub exp10: i64,
    pub sat: Option<bool>,
}

/// Result of `Parse.digitsLoop`: (mantissa digits, #fraction digits, seenDigit, rest index).
pub struct DigitsResult {
    pub digits: Vec<u8>,
    pub nf: i64,
    pub seen: bool,
    pub rest: usize,
}

/// spec `Parse.digitsLoop s 0 0 false inDec` (integer/fraction digits, `,` separators).
pub fn digits_loop(s: &[u32], start: usize, in_dec0: bool) -> DigitsResult {
    let mut digits: Vec<u8> = Vec::new();
    let mut nf: i64 = 0;
    let mut seen = false;
    let mut in_dec = in_dec0;
    let mut i = start;
    let mut go = true;
    while go && i < s.len() {
        let c = s[i];
        if is_digit(c) {
            // `m * 10 + digitVal c`: leading zeros do not change `m`
            if !(digits.len() == 0 && c == 0x30) {
                digits.push((c - 0x30) as u8);
            }
            if in_dec {
                nf = nf + 1;
            }
            seen = true;
            i = i + 1;
        } else if c == 0x2E && !in_dec {
            in_dec = true;
            i = i + 1;
        } else if c == 0x2C && seen && !in_dec {
            i = i + 1;
        } else {
            go = false;
        }
    }
    DigitsResult { digits, nf, seen, rest: i }
}

/// spec `Parse.expLoop s 0 false`: exponent digits with the `>= 100_000_000` saturation rule.
/// Returns (exponent, saturated, rest index).
pub fn exp_loop(s: &[u32], start: usize) -> (i64, bool, usize) {
    let mut e: i64 = 0;
    let mut sat = false;
    let mut i = start;
    while i < s.len() && is_digit(s[i]) {
        if sat || e >= 100_000_000 {
            sat = true;
        } else {
            e = e * 10 + (s[i] - 0x30) as i64;
            sat = false;
        }
        i = i + 1;
    }
    (e, sat, i)
}

/// spec `Parse.parseExp`: (exponent, saturated?, rest index); `(0, None, i)` if absent.
pub fn parse_exp(s: &[u32], i: usize) -> (i64, Option<bool>, usize) {
    if i < s.len() && (s[i] == 0x65 || s[i] == 0x45) {
        let mut r = i + 1;
        let mut neg_e = false;
        if r < s.len() && s[r] == 0x2B {
            r = r + 1;
        } else if r < s.len() && s[r] == 0x2D {
            neg_e = true;
            r = r + 1;
        }
        if r < s.len() && is_digit(s[r]) {
            let (e, sat, r2) = exp_loop(s, r);
            if sat {
                (0, Some(neg_e), r2)
            } else {
                (if neg_e { -e } else { e }, None, r2)
            }
        } else {
            (0, None, i)
        }
    } else {
        (0, None, i)
    }
}

/// `TryStringToNumber` (`NumberStyles.Float | AllowThousands`); spec `Parse.parseNumber`
pub fn parse_number(s: &[u32]) -> Option<Num> {
    let mut i = skip_white(s, 0);
    let mut neg = false;
    if i < s.len() && s[i] == 0x2B {
        i = i + 1;
    } else if i < s.len() && s[i] == 0x2D {
        neg = true;
        i = i + 1;
    }
    let d = digits_loop(s, i, false);
    if !d.seen {
        None
    } else {
        let (e, sat, j) = parse_exp(s, d.rest);
        let k = skip_white(s, j);
        if !all_nul(s, k) {
            None
        } else {
            Some(Num { neg, digits: d.digits, exp10: e - d.nf, sat })
        }
    }
}

/// spec `Parse.numToBits Fmt.f64`
pub fn num_to_f64(n: &Num) -> F64 {
    match n.sat {
        Some(neg_exp) => {
            if n.digits.len() == 0 || neg_exp {
                F64::parse_decimal(n.neg, &[], 0)
            } else {
                if n.neg { F64_POS_INF.neg() } else { F64_POS_INF }
            }
        }
        None => F64::parse_decimal(n.neg, &n.digits, n.exp10),
    }
}

/// spec `Parse.numToBits Fmt.f32`
pub fn num_to_f32(n: &Num) -> F32 {
    match n.sat {
        Some(neg_exp) => {
            if n.digits.len() == 0 || neg_exp {
                F32::parse_decimal(n.neg, &[], 0)
            } else {
                if n.neg { F32_POS_INF.neg() } else { F32_POS_INF }
            }
        }
        None => F32::parse_decimal(n.neg, &n.digits, n.exp10),
    }
}

/// Infinity/NaN fallback; spec `Parse.parseSymbol`: `Some(Some(neg))` = ±∞, `Some(None)` = NaN.
pub fn parse_symbol(s: &[u32]) -> Option<Option<bool>> {
    let mut lo = 0;
    while lo < s.len() && is_unicode_white_space(s[lo]) {
        lo = lo + 1;
    }
    let mut hi = s.len();
    while hi > lo && is_unicode_white_space(s[hi - 1]) {
        hi = hi - 1;
    }
    if eq_ignore_case(s, lo, hi, b"Infinity") {
        Some(Some(false))
    } else if eq_ignore_case(s, lo, hi, b"-Infinity") {
        Some(Some(true))
    } else if eq_ignore_case(s, lo, hi, b"NaN") {
        Some(None)
    } else if lo < hi && s[lo] == 0x2B {
        if eq_ignore_case(s, lo + 1, hi, b"Infinity") {
            Some(Some(false))
        } else if eq_ignore_case(s, lo + 1, hi, b"NaN") {
            Some(None)
        } else {
            None
        }
    } else if lo < hi && s[lo] == 0x2D {
        if eq_ignore_case(s, lo + 1, hi, b"NaN") { Some(None) } else { None }
    } else {
        None
    }
}

/// `double.Parse(s, InvariantCulture)`; spec `OsuModel.Net.doubleParseChars` (via `parseFloatBits`)
pub fn double_parse(s: &[u32]) -> Result<F64, NetExn> {
    match parse_number(s) {
        Some(n) => Ok(num_to_f64(&n)),
        None => match parse_symbol(s) {
            Some(Some(neg)) => Ok(if neg { F64_POS_INF.neg() } else { F64_POS_INF }),
            Some(None) => Ok(F64_NAN),
            None => Err(NetExn::Format),
        },
    }
}

/// `float.Parse(s, InvariantCulture)`; spec `OsuModel.Net.floatParseChars`
pub fn float_parse(s: &[u32]) -> Result<F32, NetExn> {
    match parse_number(s) {
        Some(n) => Ok(num_to_f32(&n)),
        None => match parse_symbol(s) {
            Some(Some(neg)) => Ok(if neg { F32_POS_INF.neg() } else { F32_POS_INF }),
            Some(None) => Ok(F32_NAN),
            None => Err(NetExn::Format),
        },
    }
}

/// Saturation cap for the integer value of `int.Parse` digits: any value above `2^31` is out
/// of range, so the exact `Nat` of the spec can be replaced by `min(value, CAP)`.
const INT_CAP: i64 = 1 << 40;

/// `int.Parse` grammar; spec `Parse.parseIntegerValue` (value saturated at `±INT_CAP`).
pub fn parse_integer_value(s: &[u32]) -> Option<i64> {
    let mut i = skip_white(s, 0);
    let mut neg = false;
    if i < s.len() && s[i] == 0x2B {
        i = i + 1;
    } else if i < s.len() && s[i] == 0x2D {
        neg = true;
        i = i + 1;
    }
    if i < s.len() && is_digit(s[i]) {
        // `digitsLoop s 0 0 false true`: digits only
        let mut m: i64 = 0;
        while i < s.len() && is_digit(s[i]) {
            m = m * 10 + (s[i] - 0x30) as i64;
            if m > INT_CAP {
                m = INT_CAP;
            }
            i = i + 1;
        }
        let k = skip_white(s, i);
        if !all_nul(s, k) {
            None
        } else {
            Some(if neg { -m } else { m })
        }
    } else {
        None
    }
}

/// `int.Parse(s, InvariantCulture)`; spec `OsuModel.Net.intParseChars`
pub fn int_parse(s: &[u32]) -> Result<i32, NetExn> {
    match parse_integer_value(s) {
        None => Err(NetExn::Format),
        Some(v) => {
            if v < -2147483648 || v > 2147483647 {
                Err(NetExn::Overflow)
            } else {
                Ok(v as i32)
            }
        }
    }
}

/// `Parsing.MAX_COORDINATE_VALUE`
pub const MAX_COORDINATE_VALUE: i32 = 131072;
/// `Parsing.MAX_PARSE_VALUE = int.MaxValue` as double
pub const MAX_PARSE_VALUE: F64 = F64::from_bits(0x41DF_FFFF_FFC0_0000);
/// `(float)MAX_PARSE_VALUE = 2147483648f`
pub const MAX_PARSE_VALUE_F32: F32 = F32::from_bits(0x4F00_0000);

/// `Parsing.ParseDouble(input, parseLimit, allowNaN)`; spec `Parsing.parseDouble`
pub fn parsing_parse_double(input: &[u32], parse_limit: F64, allow_nan: bool) -> Result<F64, NetExn> {
    let output = tri!(double_parse(input));
    if output.lt(parse_limit.neg()) {
        Err(NetExn::Overflow)
    } else if parse_limit.lt(output) {
        Err(NetExn::Overflow)
    } else if !allow_nan && output.is_nan() {
        Err(NetExn::Format)
    } else {
        Ok(output)
    }
}

/// `Parsing.ParseFloat(input, parseLimit, allowNaN)`; spec `Parsing.parseFloat`
pub fn parsing_parse_float(input: &[u32], parse_limit: F32, allow_nan: bool) -> Result<F32, NetExn> {
    let output = tri!(float_parse(input));
    if output.lt(parse_limit.neg()) {
        Err(NetExn::Overflow)
    } else if parse_limit.lt(output) {
        Err(NetExn::Overflow)
    } else if !allow_nan && output.is_nan() {
        Err(NetExn::Format)
    } else {
        Ok(output)
    }
}

/// `Parsing.ParseInt(input, parseLimit)`; spec `Parsing.parseInt`. (`-parseLimit` is Int32
/// negation in the spec; callers pass positive limits.)
pub fn parsing_parse_int(input: &[u32], parse_limit: i32) -> Result<i32, NetExn> {
    let output = tri!(int_parse(input));
    if output < 0i32.wrapping_sub(parse_limit) {
        Err(NetExn::Overflow)
    } else if output > parse_limit {
        Err(NetExn::Overflow)
    } else {
        Ok(output)
    }
}

/// `Parsing.ParseDouble(input)` with the defaults
pub fn parse_double_default(input: &[u32]) -> Result<F64, NetExn> {
    parsing_parse_double(input, MAX_PARSE_VALUE, false)
}

/// `Parsing.ParseFloat(input)` with the defaults
pub fn parse_float_default(input: &[u32]) -> Result<F32, NetExn> {
    parsing_parse_float(input, MAX_PARSE_VALUE_F32, false)
}

/// `Parsing.ParseInt(input)` with the default limit `int.MaxValue`
pub fn parse_int_default(input: &[u32]) -> Result<i32, NetExn> {
    parsing_parse_int(input, 2147483647)
}
