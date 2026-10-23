//! Port of `OsuModel/Replay/Osr.lean`: `.osr` container decoding (`LegacyScoreDecoder.Parse`,
//! lazer 2026.1005.0 `osu.Game/Scoring/Legacy/LegacyScoreDecoder.cs:37-193`), the lazer score info
//! JSON (`LegacyReplaySoloScoreInfo`) and the decoded score. The LZMA payloads go through the trusted
//! `crate::lzma` (spec: the opaque `lzmaAloneDecode`).
//!
//! The spec's reader monad `RdM = ReaderT ByteArray (StateT Nat (Except String))` becomes
//! `(b: &[u8], p: usize) -> Result<(T, usize), OsrErr>`; the spec's `String` messages are `OsrErr`
//! ids (rendered byte-identically by `text::osr_err`).
use super::mods_json::{self, find_last, int_of_text, has_frac_or_exp, in_range, is_nat, settings_of, starts_minus, JsonErr, V};
use super::mods_json::{I32_HI, I32_LO_MAG, I64_HI, I64_LO_MAG};
use crate::beatmap::dotnet::{lit_str, Str};
use crate::beatmap::mod_settings::{to_mod, JsonVal, ModConfig};
use crate::beatmap::text::{decode_utf8, stream_reader_decode};
use crate::lzma::{lzma_alone_decode, LzmaErr};
use crate::net::parse::eq_ignore_case;
use alloc::vec::Vec;

/// Member keys named in `checkScoreInfo` messages.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum InfoKey {
    Statistics,
    MaximumStatistics,
    OnlineId,
    UserId,
    TotalScoreWithoutMods,
    ClientVersion,
    Rank,
    Pauses,
}

/// The spec's `throw` messages (texts in `text::osr_err`).
#[derive(Clone, Copy)]
pub enum OsrErr {
    /// `EndOfStreamException: Unable to read beyond the end of the stream.`
    Eos,
    /// `FormatException: Too many bytes in what should have been a 7-bit encoded integer.`
    Bad7Bit,
    /// `IOException: Invalid string length`
    InvalidStringLength,
    /// `IOException: Bad ticks count read!`
    BadTicks,
    /// `ArgumentOutOfRangeException: Ticks must be between …`
    TicksRange,
    /// `InvalidOperationException: only the osu! ruleset is supported (replay ruleset id {r})`
    Ruleset(u8),
    /// `IOException: input .lzma is too short`
    LzmaTooShort,
    /// `IOException: Can't Read 1`
    LzmaRead1,
    /// `lzma (trusted boundary): {e}`
    Lzma(LzmaErr),
    /// `unsupported text encoding in compressed payload (UTF-32/invalid UTF-16; not modelled)`
    Encoding,
    /// `JsonReaderException: {e}`
    JsonReader(JsonErr),
    /// `JsonReaderException: Additional text encountered after finished reading JSON content.`
    JsonTrailing,
    /// `JsonSerializationException: bad value for '{k}' in lazer score info`
    BadValue(InfoKey),
    /// `NullReferenceException: '{k}' is null`
    NullMember(InfoKey),
    /// `ArgumentNullException: pauses is null`
    PausesNull,
    /// `JsonSerializationException: bad acronym`
    BadAcronym,
    /// `NullReferenceException: mod settings are null`
    SettingsNull,
    /// `JsonSerializationException: bad mod settings`
    BadSettings,
    /// `JsonSerializationException: mod is not an object`
    ModNotObject,
    /// `NullReferenceException: mods is null`
    ModsNull,
    /// `JsonSerializationException: mods is not an array`
    ModsNotArray,
    /// `NullReferenceException: lazer score info is null`
    InfoNull,
    /// `JsonSerializationException: lazer score info is not an object`
    InfoNotObject,
}

/// spec `maxPayload` (256 MiB)
pub const MAX_PAYLOAD: usize = 268435456;

// ---------------------------------------------------------------------------------------------
// `SerializationReader` / `BinaryReader` over a byte array
// ---------------------------------------------------------------------------------------------

/// spec `readByte`
pub fn read_byte(b: &[u8], p: usize) -> Result<(u8, usize), OsrErr> {
    if p < b.len() {
        Ok((b[p], p + 1))
    } else {
        Err(OsrErr::Eos)
    }
}

/// spec `readLE n` (little-endian unsigned, `n <= 8`)
pub fn read_le(b: &[u8], p: usize, n: usize) -> Result<(u64, usize), OsrErr> {
    if p + n <= b.len() {
        let mut v: u64 = 0;
        let mut i = 0;
        while i < n {
            v = v | ((b[p + i] as u64) << (8 * i));
            i = i + 1;
        }
        Ok((v, p + n))
    } else {
        Err(OsrErr::Eos)
    }
}

/// spec `readUInt16`
pub fn read_uint16(b: &[u8], p: usize) -> Result<(u64, usize), OsrErr> {
    read_le(b, p, 2)
}

/// spec `readInt32` (`Int32.ofNat`: two's complement wrap)
pub fn read_int32(b: &[u8], p: usize) -> Result<(i32, usize), OsrErr> {
    let (v, q) = tri!(read_le(b, p, 4));
    Ok(((v as u32) as i32, q))
}

/// spec `readInt64`
pub fn read_int64(b: &[u8], p: usize) -> Result<(i64, usize), OsrErr> {
    let (v, q) = tri!(read_le(b, p, 8));
    Ok((v as i64, q))
}

/// spec `readBoolean` (`ReadByte() != 0`)
pub fn read_boolean(b: &[u8], p: usize) -> Result<(bool, usize), OsrErr> {
    let (x, q) = tri!(read_byte(b, p));
    Ok((x != 0, q))
}

/// spec `readBytes count`: fewer bytes at the end of the stream (no exception)
pub fn read_bytes(b: &[u8], p: usize, count: usize) -> (Vec<u8>, usize) {
    let avail = if p <= b.len() { b.len() - p } else { 0 };
    let n = if count < avail { count } else { avail };
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        out.push(b[p + i]);
        i = i + 1;
    }
    (out, p + n)
}

/// part of spec `read7BitEncodedInt`: the `for i in [0:4]` loop; returns (result, finished early,
/// position). Rejections only from `readByte`.
pub fn read7bit_loop(b: &[u8], p0: usize) -> Result<(u32, bool, usize), OsrErr> {
    let mut result: u32 = 0;
    let mut p = p0;
    let mut i: u32 = 0;
    let mut done = false;
    let mut err: Option<OsrErr> = None;
    while err.is_none() && !done && i < 4 {
        if p < b.len() {
            let x = b[p];
            p = p + 1;
            result = result | (((x as u32) & 0x7F) << (7 * i));
            if x <= 0x7F {
                done = true;
            }
            i = i + 1;
        } else {
            err = Some(OsrErr::Eos);
        }
    }
    match err {
        Some(e) => Err(e),
        None => Ok((result, done, p)),
    }
}

/// spec `read7BitEncodedInt` (.NET: at most 5 bytes, the 5th must be <= 0b1111)
pub fn read7bit_encoded_int(b: &[u8], p0: usize) -> Result<(i32, usize), OsrErr> {
    let (result, done, p) = tri!(read7bit_loop(b, p0));
    if done {
        Ok((result as i32, p))
    } else {
        let (x, q) = tri!(read_byte(b, p));
        if x > 0b1111 {
            Err(OsrErr::Bad7Bit)
        } else {
            Ok(((result | ((x as u32) << 28)) as i32, q))
        }
    }
}

/// spec `readString`: a zero byte = `null`; otherwise 7-bit length + UTF-8 (`decodeUtf8`)
pub fn read_string(b: &[u8], p0: usize) -> Result<(Option<Str>, usize), OsrErr> {
    let (x, p1) = tri!(read_byte(b, p0));
    if x == 0 {
        Ok((None, p1))
    } else {
        let (len, p2) = tri!(read7bit_encoded_int(b, p1));
        if len < 0 {
            Err(OsrErr::InvalidStringLength)
        } else if len == 0 {
            Ok((Some(Vec::new()), p2))
        } else {
            let (bs, p3) = read_bytes(b, p2, len as usize);
            if bs.len() < len as usize {
                Err(OsrErr::Eos)
            } else {
                Ok((Some(decode_utf8(&bs, 0)), p3))
            }
        }
    }
}

/// `DateTime.MaxValue.Ticks`
pub const MAX_TICKS: i64 = 3155378975999999999;

/// spec `readDateTime`
pub fn read_date_time(b: &[u8], p: usize) -> Result<(i64, usize), OsrErr> {
    let (t, q) = tri!(read_int64(b, p));
    if t < 0 {
        Err(OsrErr::BadTicks)
    } else if t > MAX_TICKS {
        Err(OsrErr::TicksRange)
    } else {
        Ok((t, q))
    }
}

/// spec `readByteArray`: length > 0 -> bytes (short at EOF), < 0 -> `null`, 0 -> empty
pub fn read_byte_array(b: &[u8], p: usize) -> Result<(Option<Vec<u8>>, usize), OsrErr> {
    let (len, q) = tri!(read_int32(b, p));
    if len > 0 {
        let (bs, r) = read_bytes(b, q, len as usize);
        Ok((Some(bs), r))
    } else if len < 0 {
        Ok((None, q))
    } else {
        Ok((Some(Vec::new()), q))
    }
}

// ---------------------------------------------------------------------------------------------
// Legacy mods
// ---------------------------------------------------------------------------------------------

/// `(m >>> bit) &&& 1 == 1`
pub fn has_bit(m: u32, bit: u32) -> bool {
    (m >> bit) & 1 == 1
}

/// spec `convertFromLegacyMods` (`OsuRuleset.ConvertFromLegacyMods`, `OsuRuleset.cs:96-148`):
/// acronyms in yield order, each `Settings.toMod · []`
pub fn convert_from_legacy_mods(mods: i32) -> Vec<ModConfig> {
    let m = mods as u32;
    let none: Vec<(Str, JsonVal)> = Vec::new();
    let mut out: Vec<ModConfig> = Vec::new();
    if has_bit(m, 9) {
        out.push(to_mod(&lit_str(b"NC"), &none));
    } else if has_bit(m, 6) {
        out.push(to_mod(&lit_str(b"DT"), &none));
    }
    if has_bit(m, 14) {
        out.push(to_mod(&lit_str(b"PF"), &none));
    } else if has_bit(m, 5) {
        out.push(to_mod(&lit_str(b"SD"), &none));
    }
    if has_bit(m, 13) {
        out.push(to_mod(&lit_str(b"AP"), &none));
    }
    if has_bit(m, 22) {
        out.push(to_mod(&lit_str(b"CN"), &none));
    } else if has_bit(m, 11) {
        out.push(to_mod(&lit_str(b"AT"), &none));
    }
    if has_bit(m, 1) {
        out.push(to_mod(&lit_str(b"EZ"), &none));
    }
    if has_bit(m, 10) {
        out.push(to_mod(&lit_str(b"FL"), &none));
    }
    if has_bit(m, 8) {
        out.push(to_mod(&lit_str(b"HT"), &none));
    }
    if has_bit(m, 4) {
        out.push(to_mod(&lit_str(b"HR"), &none));
    }
    if has_bit(m, 3) {
        out.push(to_mod(&lit_str(b"HD"), &none));
    }
    if has_bit(m, 0) {
        out.push(to_mod(&lit_str(b"NF"), &none));
    }
    if has_bit(m, 7) {
        out.push(to_mod(&lit_str(b"RX"), &none));
    }
    if has_bit(m, 12) {
        out.push(to_mod(&lit_str(b"SO"), &none));
    }
    if has_bit(m, 23) {
        out.push(to_mod(&lit_str(b"TP"), &none));
    }
    if has_bit(m, 2) {
        out.push(to_mod(&lit_str(b"TD"), &none));
    }
    if has_bit(m, 29) {
        out.push(to_mod(&lit_str(b"SV2"), &none));
    }
    out
}

/// spec `FIRST_LAZER_VERSION` (`LegacyScoreEncoder.FIRST_LAZER_VERSION`)
pub const FIRST_LAZER_VERSION: i32 = 30000000;

// ---------------------------------------------------------------------------------------------
// Container
// ---------------------------------------------------------------------------------------------

/// spec `Container`
#[derive(Clone)]
pub struct Container {
    pub ruleset_id: u8,
    pub version: i32,
    pub beatmap_hash: Option<Str>,
    pub legacy_mods: i32,
    pub compressed_replay: Option<Vec<u8>>,
    pub compressed_score_info: Option<Vec<u8>>,
}

/// part of spec `readContainer`: version, beatmap hash, player name, replay hash, the six counts,
/// total score, max combo, perfect flag (after the ruleset byte)
pub fn read_header(b: &[u8], p0: usize) -> Result<(i32, Option<Str>, usize), OsrErr> {
    let (version, p1) = tri!(read_int32(b, p0));
    let (beatmap_hash, p2) = tri!(read_string(b, p1));
    let (_player, p3) = tri!(read_string(b, p2));
    let (_md5, p4) = tri!(read_string(b, p3));
    // `for _ in [0:6] do let _ ← readUInt16`
    let (_c0, p5) = tri!(read_uint16(b, p4));
    let (_c1, p6) = tri!(read_uint16(b, p5));
    let (_c2, p7) = tri!(read_uint16(b, p6));
    let (_c3, p8) = tri!(read_uint16(b, p7));
    let (_c4, p9) = tri!(read_uint16(b, p8));
    let (_c5, p10) = tri!(read_uint16(b, p9));
    let (_total_score, p11) = tri!(read_int32(b, p10));
    let (_max_combo, p12) = tri!(read_uint16(b, p11));
    let (_perfect, p13) = tri!(read_boolean(b, p12));
    Ok((version, beatmap_hash, p13))
}

/// part of spec `readContainer`: legacy mods, HP graph, date, compressed replay, online id,
/// compressed score info
pub fn read_body(b: &[u8], p0: usize, version: i32) -> Result<(i32, Option<Vec<u8>>, Option<Vec<u8>>), OsrErr> {
    let (legacy_mods, p1) = tri!(read_int32(b, p0));
    let (_hp_graph, p2) = tri!(read_string(b, p1));
    let (_date, p3) = tri!(read_date_time(b, p2));
    let (compressed_replay, p4) = tri!(read_byte_array(b, p3));
    let p5 = tri!(skip_online_id(b, p4, version));
    if version >= 30000001 {
        let (info, _p6) = tri!(read_byte_array(b, p5));
        Ok((legacy_mods, compressed_replay, info))
    } else {
        Ok((legacy_mods, compressed_replay, None))
    }
}

/// part of spec `readContainer`: the online id (`Int64` from 20140721, `Int32` from 20121008)
pub fn skip_online_id(b: &[u8], p: usize, version: i32) -> Result<usize, OsrErr> {
    if version >= 20140721 {
        let (_x, q) = tri!(read_int64(b, p));
        Ok(q)
    } else if version >= 20121008 {
        let (_x, q) = tri!(read_int32(b, p));
        Ok(q)
    } else {
        Ok(p)
    }
}

/// spec `readContainer` (`LegacyScoreDecoder.Parse` up to the end of the stream reads, `:47-118`)
pub fn read_container(b: &[u8]) -> Result<Container, OsrErr> {
    let (ruleset_id, p1) = tri!(read_byte(b, 0));
    if ruleset_id != 0 {
        Err(OsrErr::Ruleset(ruleset_id))
    } else {
        let (version, beatmap_hash, p2) = tri!(read_header(b, p1));
        let (legacy_mods, compressed_replay, compressed_score_info) = tri!(read_body(b, p2, version));
        Ok(Container { ruleset_id, version, beatmap_hash, legacy_mods, compressed_replay, compressed_score_info })
    }
}

/// spec `parseContainer`
pub fn parse_container(bytes: &[u8]) -> Result<Container, OsrErr> {
    read_container(bytes)
}

/// `String.fromUTF8?` validity (well-formed UTF-8: no overlongs, surrogates or values > U+10FFFF)
pub fn utf8_valid(b: &[u8]) -> bool {
    let n = b.len();
    let mut i = 0;
    let mut ok_ = true;
    while ok_ && i < n {
        let k = utf8_seq_len(b, i);
        if k == 0 {
            ok_ = false;
        } else {
            i = i + k;
        }
    }
    ok_
}

/// part of `utf8_valid`: length of the well-formed sequence at `i` (0 = ill-formed)
pub fn utf8_seq_len(b: &[u8], i: usize) -> usize {
    let n = b.len();
    let c0 = b[i];
    if c0 < 0x80 {
        1
    } else if c0 < 0xC2 {
        0
    } else if c0 < 0xE0 {
        if i + 1 < n && utf8_cont(b[i + 1]) { 2 } else { 0 }
    } else if c0 < 0xF0 {
        let lo: u8 = if c0 == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if c0 == 0xED { 0x9F } else { 0xBF };
        if i + 2 < n && lo <= b[i + 1] && b[i + 1] <= hi && utf8_cont(b[i + 2]) { 3 } else { 0 }
    } else if c0 < 0xF5 {
        let lo: u8 = if c0 == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if c0 == 0xF4 { 0x8F } else { 0xBF };
        if i + 3 < n && lo <= b[i + 1] && b[i + 1] <= hi && utf8_cont(b[i + 2]) && utf8_cont(b[i + 3]) { 4 } else { 0 }
    } else {
        0
    }
}

/// UTF-8 continuation byte
pub fn utf8_cont(x: u8) -> bool {
    (x & 0xC0) == 0x80
}

/// part of spec `readCompressedText`: `hasBom` (first two bytes EF BB, FE FF or FF FE)
pub fn has_bom(raw: &[u8]) -> bool {
    if raw.len() >= 2 {
        let b0 = raw[0];
        let b1 = raw[1];
        (b0 == 0xEF && b1 == 0xBB) || (b0 == 0xFE && b1 == 0xFF) || (b0 == 0xFF && b1 == 0xFE)
    } else {
        false
    }
}

/// spec `readCompressedText` (`readCompressedData`, `:168-193`, + `StreamReader.ReadToEnd`): at least
/// 13 header bytes, LZMA (trusted), then `StreamReader` decoding (fast path: valid UTF-8 without a BOM
/// decodes as itself, `decode_utf8` = identity on well-formed input)
pub fn read_compressed_text(data: &[u8]) -> Result<Str, OsrErr> {
    if data.len() < 5 {
        Err(OsrErr::LzmaTooShort)
    } else if data.len() < 13 {
        Err(OsrErr::LzmaRead1)
    } else {
        match lzma_alone_decode(data, MAX_PAYLOAD) {
            Err(e) => Err(OsrErr::Lzma(e)),
            Ok(raw) => decode_payload_text(&raw),
        }
    }
}

/// part of spec `readCompressedText`: bytes -> text
pub fn decode_payload_text(raw: &[u8]) -> Result<Str, OsrErr> {
    if !has_bom(raw) && utf8_valid(raw) {
        Ok(decode_utf8(raw, 0))
    } else {
        match stream_reader_decode(raw) {
            Some(cs) => Ok(cs),
            None => Err(OsrErr::Encoding),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Lazer score info JSON (`LegacyReplaySoloScoreInfo`)
// ---------------------------------------------------------------------------------------------

/// spec `jsonInt v lo hi` (Newtonsoft `ReadAsInt32`/`Int64` of an integer literal in range;
/// `lo = -lo_mag`)
pub fn json_int(v: &V, lo_mag: u128, hi: u128) -> bool {
    match v {
        V::Num(t) => {
            if has_frac_or_exp(t) {
                false
            } else {
                let (neg, m) = int_of_text(t);
                in_range(neg, m, lo_mag, hi)
            }
        }
        _ => false,
    }
}

/// `s.toInt?.isSome` (Lean 4.35 `String.toInt?`: optional `-`, then `isNat`)
pub fn is_int(s: &[u32]) -> bool {
    if starts_minus(s) {
        is_nat(s, 1, s.len())
    } else {
        is_nat(s, 0, s.len())
    }
}

/// `n.map Char.toLower == s.map Char.toLower`
pub fn eq_ci(s: &[u32], lit: &[u8]) -> bool {
    eq_ignore_case(s, 0, s.len(), lit)
}

/// `hitResultKeys` membership, case-insensitive: the `HitResult` names (`HitResult.all`) and their
/// `snakeCase` (the `[EnumMember]` values of `osu.Game/Rulesets/Scoring/HitResult.cs`)
pub fn is_hit_result_key(s: &[u32]) -> bool {
    // split in four (Aeneas: one 36-deep `||` chain is printed too deeply nested for Lean's parser)
    hr_names_a(s) || hr_names_b(s) || hr_snake_a(s) || hr_snake_b(s)
}

/// part of `is_hit_result_key`: the first 9 `HitResult` names
pub fn hr_names_a(s: &[u32]) -> bool {
    eq_ci(s, b"None") || eq_ci(s, b"Miss") || eq_ci(s, b"Meh") || eq_ci(s, b"Ok") || eq_ci(s, b"Good")
        || eq_ci(s, b"Great") || eq_ci(s, b"Perfect") || eq_ci(s, b"SmallTickMiss") || eq_ci(s, b"SmallTickHit")
}

/// part of `is_hit_result_key`: the last 9 `HitResult` names
pub fn hr_names_b(s: &[u32]) -> bool {
    eq_ci(s, b"LargeTickMiss") || eq_ci(s, b"LargeTickHit") || eq_ci(s, b"SmallBonus") || eq_ci(s, b"LargeBonus")
        || eq_ci(s, b"IgnoreMiss") || eq_ci(s, b"IgnoreHit") || eq_ci(s, b"ComboBreak") || eq_ci(s, b"SliderTailHit")
        || eq_ci(s, b"LegacyComboIncrease")
}

/// part of `is_hit_result_key`: the first 9 `snakeCase` names
pub fn hr_snake_a(s: &[u32]) -> bool {
    eq_ci(s, b"none") || eq_ci(s, b"miss") || eq_ci(s, b"meh") || eq_ci(s, b"ok") || eq_ci(s, b"good")
        || eq_ci(s, b"great") || eq_ci(s, b"perfect") || eq_ci(s, b"small_tick_miss") || eq_ci(s, b"small_tick_hit")
}

/// part of `is_hit_result_key`: the last 9 `snakeCase` names
pub fn hr_snake_b(s: &[u32]) -> bool {
    eq_ci(s, b"large_tick_miss") || eq_ci(s, b"large_tick_hit") || eq_ci(s, b"small_bonus")
        || eq_ci(s, b"large_bonus") || eq_ci(s, b"ignore_miss") || eq_ci(s, b"ignore_hit") || eq_ci(s, b"combo_break")
        || eq_ci(s, b"slider_tail_hit") || eq_ci(s, b"legacy_combo_increase")
}

/// spec `enumName hitResultKeys s`
pub fn enum_name_hit_result(s: &[u32]) -> bool {
    is_hit_result_key(s) || is_int(s)
}

/// spec `enumName scoreRankNames s` (`F D C B A S SH X XH`)
pub fn enum_name_rank(s: &[u32]) -> bool {
    eq_ci(s, b"F") || eq_ci(s, b"D") || eq_ci(s, b"C") || eq_ci(s, b"B") || eq_ci(s, b"A") || eq_ci(s, b"S")
        || eq_ci(s, b"SH") || eq_ci(s, b"X") || eq_ci(s, b"XH") || is_int(s)
}

/// part of spec `checkScoreInfo`: the entries of `statistics` / `maximum_statistics`
pub fn stats_entries_ok(es: &[(Str, V)]) -> bool {
    let mut ok_ = true;
    let mut i = 0;
    while ok_ && i < es.len() {
        ok_ = stats_entry_ok(es, i);
        i = i + 1;
    }
    ok_
}

/// part of spec `checkScoreInfo`: one `statistics` entry (`enumName hitResultKeys rk && jsonInt rv`)
pub fn stats_entry_ok(es: &[(Str, V)], i: usize) -> bool {
    enum_name_hit_result(&es[i].0) && json_int(&es[i].1, I32_LO_MAG, I32_HI)
}

/// part of spec `checkScoreInfo`: the elements of `pauses`
pub fn pauses_ok(xs: &[V]) -> bool {
    let mut ok_ = true;
    let mut i = 0;
    while ok_ && i < xs.len() {
        if !json_int(&xs[i], I32_LO_MAG, I32_HI) {
            ok_ = false;
        }
        i = i + 1;
    }
    ok_
}

/// part of spec `checkScoreInfo`: `statistics` / `maximum_statistics`
pub fn check_stats(k: InfoKey, v: &V) -> Result<(), OsrErr> {
    match v {
        V::Obj(es) => {
            if stats_entries_ok(es) {
                Ok(())
            } else {
                Err(OsrErr::BadValue(k))
            }
        }
        V::Null => Err(OsrErr::NullMember(k)),
        _ => Err(OsrErr::BadValue(k)),
    }
}

/// part of spec `checkScoreInfo`: `bad` unless `c`
pub fn bad_unless(c: bool, k: InfoKey) -> Result<(), OsrErr> {
    if c {
        Ok(())
    } else {
        Err(OsrErr::BadValue(k))
    }
}

/// part of spec `checkScoreInfo`: `rank`
pub fn check_rank(v: &V) -> Result<(), OsrErr> {
    match v {
        V::Null => Ok(()),
        V::VStr(s) => bad_unless(enum_name_rank(s), InfoKey::Rank),
        _ => bad_unless(json_int(v, I32_LO_MAG, I32_HI), InfoKey::Rank),
    }
}

/// part of spec `checkScoreInfo`: `pauses`
pub fn check_pauses(v: &V) -> Result<(), OsrErr> {
    match v {
        V::Arr(xs) => bad_unless(pauses_ok(xs), InfoKey::Pauses),
        V::Null => Err(OsrErr::PausesNull),
        _ => Err(OsrErr::BadValue(InfoKey::Pauses)),
    }
}

/// part of spec `checkScoreInfo`: `total_score_without_mods`
pub fn check_total_without_mods(v: &V) -> Result<(), OsrErr> {
    match v {
        V::Null => Ok(()),
        _ => bad_unless(json_int(v, I64_LO_MAG, I64_HI), InfoKey::TotalScoreWithoutMods),
    }
}

/// part of spec `checkScoreInfo`: `client_version`
pub fn check_client_version(v: &V) -> Result<(), OsrErr> {
    match v {
        V::VStr(_) => Ok(()),
        V::Null => Ok(()),
        _ => Err(OsrErr::BadValue(InfoKey::ClientVersion)),
    }
}

/// part of spec `checkScoreInfo`: one member (`match k with …`)
pub fn check_member(k: &[u32], v: &V) -> Result<(), OsrErr> {
    if crate::beatmap::dotnet::str_eq(k, b"statistics") {
        check_stats(InfoKey::Statistics, v)
    } else if crate::beatmap::dotnet::str_eq(k, b"maximum_statistics") {
        check_stats(InfoKey::MaximumStatistics, v)
    } else if crate::beatmap::dotnet::str_eq(k, b"online_id") {
        bad_unless(json_int(v, I64_LO_MAG, I64_HI), InfoKey::OnlineId)
    } else if crate::beatmap::dotnet::str_eq(k, b"user_id") {
        bad_unless(json_int(v, I32_LO_MAG, I32_HI), InfoKey::UserId)
    } else if crate::beatmap::dotnet::str_eq(k, b"total_score_without_mods") {
        check_total_without_mods(v)
    } else if crate::beatmap::dotnet::str_eq(k, b"client_version") {
        check_client_version(v)
    } else if crate::beatmap::dotnet::str_eq(k, b"rank") {
        check_rank(v)
    } else if crate::beatmap::dotnet::str_eq(k, b"pauses") {
        check_pauses(v)
    } else {
        Ok(())
    }
}

/// spec `checkScoreInfo` (type checks of the non-mod members, in document order)
pub fn check_score_info(kvs: &[(Str, V)]) -> Result<(), OsrErr> {
    let mut err: Option<OsrErr> = None;
    let mut i = 0;
    while err.is_none() && i < kvs.len() {
        match check_member(&kvs[i].0, &kvs[i].1) {
            Ok(_) => {}
            Err(e) => err = Some(e),
        }
        i = i + 1;
    }
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// part of spec `apiModToMod`: the acronym (`none` = absent or `null`)
pub fn api_acronym(v: &V) -> Result<Option<Str>, OsrErr> {
    match v {
        V::VStr(s) => Ok(Some(s.clone())),
        V::Num(t) => Ok(Some(t.clone())),
        V::Bool(b) => {
            if *b {
                Ok(Some(lit_str(b"True")))
            } else {
                Ok(Some(lit_str(b"False")))
            }
        }
        V::Null => Ok(None),
        _ => Err(OsrErr::BadAcronym),
    }
}

/// part of spec `apiModToMod`: the settings
pub fn api_settings(v: &V) -> Result<Vec<(Str, JsonVal)>, OsrErr> {
    match v {
        V::Obj(ss) => Ok(settings_of(ss)),
        V::Null => Err(OsrErr::SettingsNull),
        _ => Err(OsrErr::BadSettings),
    }
}

/// spec `apiModToMod` (one `APIMod` -> `APIMod.ToMod(ruleset)`, `APIMod.cs:43-70`; members: last occurrence)
pub fn api_mod_to_mod(v: &V) -> Result<ModConfig, OsrErr> {
    match v {
        V::Obj(kvs) => {
            let acronym: Option<Str> = match find_last(kvs, b"acronym") {
                Some(i) => tri!(api_acronym(&kvs[i].1)),
                None => None,
            };
            let settings: Vec<(Str, JsonVal)> = match find_last(kvs, b"settings") {
                Some(i) => tri!(api_settings(&kvs[i].1)),
                None => Vec::new(),
            };
            match acronym {
                Some(a) => Ok(to_mod(&a, &settings)),
                None => Ok(ModConfig { acronym: Vec::new(), known: false, settings: Vec::new() }),
            }
        }
        _ => Err(OsrErr::ModNotObject),
    }
}

/// part of spec `decodeScoreInfo`: `xs.mapM apiModToMod`
pub fn api_mods(xs: &[V]) -> Result<Vec<ModConfig>, OsrErr> {
    let mut out: Vec<ModConfig> = Vec::new();
    let mut err: Option<OsrErr> = None;
    let mut i = 0;
    while err.is_none() && i < xs.len() {
        match api_mod_to_mod(&xs[i]) {
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

/// part of spec `decodeScoreInfo`: additional non-whitespace content after the value
pub fn has_trailing(s: &[u32], p: usize) -> bool {
    let mut r = false;
    let mut i = p;
    while i < s.len() {
        if !mods_json::is_ws(s[i]) {
            r = true;
        }
        i = i + 1;
    }
    r
}

/// part of spec `decodeScoreInfo`: the object case
pub fn score_info_mods(kvs: &[(Str, V)]) -> Result<Vec<ModConfig>, OsrErr> {
    tri!(check_score_info(kvs));
    match find_last(kvs, b"mods") {
        None => Ok(Vec::new()),
        Some(i) => match &kvs[i].1 {
            V::Arr(xs) => api_mods(xs),
            V::Null => Err(OsrErr::ModsNull),
            _ => Err(OsrErr::ModsNotArray),
        },
    }
}

/// spec `decodeScoreInfo` (`:123-146`): JSON text -> mods (replacing the decoded bitfield mods)
pub fn decode_score_info(text: &[u32]) -> Result<Vec<ModConfig>, OsrErr> {
    match mods_json::value(text, 0) {
        Err(e) => Err(OsrErr::JsonReader(e)),
        Ok((v, rest)) => {
            if has_trailing(text, rest) {
                Err(OsrErr::JsonTrailing)
            } else {
                match v {
                    V::Obj(kvs) => score_info_mods(&kvs),
                    V::Null => Err(OsrErr::InfoNull),
                    _ => Err(OsrErr::InfoNotObject),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Decoded score
// ---------------------------------------------------------------------------------------------

/// spec `DecodedScore`
#[derive(Clone)]
pub struct DecodedScore {
    pub container: Container,
    /// `ScoreInfo.IsLegacyScore` (`version < 30000000`)
    pub is_legacy_score: bool,
    /// mods before the lazer JSON (bitfield + automatic Classic)
    pub bitfield_mods: Vec<ModConfig>,
    /// `ScoreInfo.Mods` after `Parse`
    pub mods: Vec<ModConfig>,
    /// decompressed frame text (`None`: no / empty replay payload)
    pub frame_text: Option<Str>,
}

/// part of spec `decode`: the frame text
pub fn frame_text_of(c: &Container) -> Result<Option<Str>, OsrErr> {
    match &c.compressed_replay {
        Some(d) => {
            if d.len() > 0 {
                let t = tri!(read_compressed_text(d));
                Ok(Some(t))
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// part of spec `decode`: the score mods
pub fn mods_of(c: &Container, bitfield_mods: &[ModConfig]) -> Result<Vec<ModConfig>, OsrErr> {
    match &c.compressed_score_info {
        Some(d) => {
            if d.len() > 0 {
                let t = tri!(read_compressed_text(d));
                decode_score_info(&t)
            } else {
                Ok(bitfield_mods.to_vec())
            }
        }
        None => Ok(bitfield_mods.to_vec()),
    }
}

/// spec `decode`: everything except the frames' dependency on the beatmap
pub fn decode(bytes: &[u8]) -> Result<DecodedScore, OsrErr> {
    let c = tri!(parse_container(bytes));
    let is_legacy_score = c.version < FIRST_LAZER_VERSION;
    let mut bitfield_mods = convert_from_legacy_mods(c.legacy_mods);
    if is_legacy_score {
        let none: Vec<(Str, JsonVal)> = Vec::new();
        bitfield_mods.push(to_mod(&lit_str(b"CL"), &none));
    }
    let frame_text = tri!(frame_text_of(&c));
    let mods = tri!(mods_of(&c, &bitfield_mods));
    Ok(DecodedScore { container: c, is_legacy_score, bitfield_mods, mods, frame_text })
}

/// Message texts (not translated; excluded from Charon).
pub mod text {
    use super::{InfoKey, OsrErr};
    pub fn info_key(k: InfoKey) -> &'static str {
        match k {
            InfoKey::Statistics => "statistics",
            InfoKey::MaximumStatistics => "maximum_statistics",
            InfoKey::OnlineId => "online_id",
            InfoKey::UserId => "user_id",
            InfoKey::TotalScoreWithoutMods => "total_score_without_mods",
            InfoKey::ClientVersion => "client_version",
            InfoKey::Rank => "rank",
            InfoKey::Pauses => "pauses",
        }
    }
    /// the spec's `throw` string of an `OsrErr`
    pub fn osr_err(e: OsrErr) -> String {
        match e {
            OsrErr::Eos => "EndOfStreamException: Unable to read beyond the end of the stream.".into(),
            OsrErr::Bad7Bit => "FormatException: Too many bytes in what should have been a 7-bit encoded integer.".into(),
            OsrErr::InvalidStringLength => "IOException: Invalid string length".into(),
            OsrErr::BadTicks => "IOException: Bad ticks count read!".into(),
            OsrErr::TicksRange => {
                "ArgumentOutOfRangeException: Ticks must be between DateTime.MinValue.Ticks and DateTime.MaxValue.Ticks.".into()
            }
            OsrErr::Ruleset(r) => {
                format!("InvalidOperationException: only the osu! ruleset is supported (replay ruleset id {})", r)
            }
            OsrErr::LzmaTooShort => "IOException: input .lzma is too short".into(),
            OsrErr::LzmaRead1 => "IOException: Can't Read 1".into(),
            OsrErr::Lzma(x) => format!("lzma (trusted boundary): {}", crate::lzma::message(x)),
            OsrErr::Encoding => {
                "unsupported text encoding in compressed payload (UTF-32/invalid UTF-16; not modelled)".into()
            }
            OsrErr::JsonReader(j) => format!("JsonReaderException: {}", super::mods_json::text::json_err(j)),
            OsrErr::JsonTrailing => {
                "JsonReaderException: Additional text encountered after finished reading JSON content.".into()
            }
            OsrErr::BadValue(k) => format!("JsonSerializationException: bad value for '{}' in lazer score info", info_key(k)),
            OsrErr::NullMember(k) => format!("NullReferenceException: '{}' is null", info_key(k)),
            OsrErr::PausesNull => "ArgumentNullException: pauses is null".into(),
            OsrErr::BadAcronym => "JsonSerializationException: bad acronym".into(),
            OsrErr::SettingsNull => "NullReferenceException: mod settings are null".into(),
            OsrErr::BadSettings => "JsonSerializationException: bad mod settings".into(),
            OsrErr::ModNotObject => "JsonSerializationException: mod is not an object".into(),
            OsrErr::ModsNull => "NullReferenceException: mods is null".into(),
            OsrErr::ModsNotArray => "JsonSerializationException: mods is not an array".into(),
            OsrErr::InfoNull => "NullReferenceException: lazer score info is null".into(),
            OsrErr::InfoNotObject => "JsonSerializationException: lazer score info is not an object".into(),
        }
    }
}
