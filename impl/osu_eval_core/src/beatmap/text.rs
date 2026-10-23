//! Port of `OsuModel/Beatmap/Text.lean`: `StreamReader(UTF8, detectBOM)` decoding and `ReadLine`.
use super::dotnet::Str;
use alloc::vec::Vec;

const REPL: u32 = 0xFFFD;

fn is_cont(x: u8) -> bool {
    (x & 0xC0) == 0x80
}

/// UTF-8 with maximal-subpart U+FFFD replacement; spec `decodeUtf8`
pub fn decode_utf8(b: &[u8], start: usize) -> Str {
    let n = b.len();
    let mut out: Str = Vec::with_capacity(n);
    let mut i = start;
    while i < n {
        let c0 = b[i];
        if c0 < 0x80 {
            out.push(c0 as u32);
            i = i + 1;
        } else if c0 < 0xC2 {
            out.push(REPL);
            i = i + 1;
        } else if c0 < 0xE0 {
            if i + 1 < n && is_cont(b[i + 1]) {
                out.push((((c0 as u32) & 0x1F) << 6) | ((b[i + 1] as u32) & 0x3F));
                i = i + 2;
            } else {
                out.push(REPL);
                i = i + 1;
            }
        } else if c0 < 0xF0 {
            let lo: u8 = if c0 == 0xE0 { 0xA0 } else { 0x80 };
            let hi: u8 = if c0 == 0xED { 0x9F } else { 0xBF };
            if i + 1 < n && lo <= b[i + 1] && b[i + 1] <= hi {
                if i + 2 < n && is_cont(b[i + 2]) {
                    out.push((((c0 as u32) & 0x0F) << 12) | (((b[i + 1] as u32) & 0x3F) << 6) | ((b[i + 2] as u32) & 0x3F));
                    i = i + 3;
                } else {
                    out.push(REPL);
                    i = i + 2;
                }
            } else {
                out.push(REPL);
                i = i + 1;
            }
        } else if c0 < 0xF5 {
            let lo: u8 = if c0 == 0xF0 { 0x90 } else { 0x80 };
            let hi: u8 = if c0 == 0xF4 { 0x8F } else { 0xBF };
            if i + 1 < n && lo <= b[i + 1] && b[i + 1] <= hi {
                if i + 2 < n && is_cont(b[i + 2]) {
                    if i + 3 < n && is_cont(b[i + 3]) {
                        out.push(
                            (((c0 as u32) & 0x07) << 18)
                                | (((b[i + 1] as u32) & 0x3F) << 12)
                                | (((b[i + 2] as u32) & 0x3F) << 6)
                                | ((b[i + 3] as u32) & 0x3F),
                        );
                        i = i + 4;
                    } else {
                        out.push(REPL);
                        i = i + 3;
                    }
                } else {
                    out.push(REPL);
                    i = i + 2;
                }
            } else {
                out.push(REPL);
                i = i + 1;
            }
        } else {
            out.push(REPL);
            i = i + 1;
        }
    }
    out
}

fn unit16(b: &[u8], i: usize, big_endian: bool) -> u32 {
    if big_endian { (b[i] as u32) * 256 + (b[i + 1] as u32) } else { (b[i + 1] as u32) * 256 + (b[i] as u32) }
}

/// UTF-16 (BE/LE); `None` on an unpaired surrogate; spec `decodeUtf16`
pub fn decode_utf16(b: &[u8], start: usize, big_endian: bool) -> Option<Str> {
    let n = b.len();
    let mut out: Str = Vec::new();
    let mut i = start;
    let mut bad = false;
    while !bad && i < n {
        if i + 1 < n {
            let u = unit16(b, i, big_endian);
            if u < 0xD800 || u > 0xDFFF {
                out.push(u);
                i = i + 2;
            } else if u <= 0xDBFF && i + 3 < n && 0xDC00 <= unit16(b, i + 2, big_endian) && unit16(b, i + 2, big_endian) <= 0xDFFF {
                out.push(0x10000 + ((u - 0xD800) << 10) + (unit16(b, i + 2, big_endian) - 0xDC00));
                i = i + 4;
            } else {
                bad = true;
            }
        } else {
            out.push(REPL);
            i = i + 1;
        }
    }
    if bad { None } else { Some(out) }
}

/// The characters `StreamReader` produces, `None` if unsupported; spec `streamReaderDecode`
pub fn stream_reader_decode(b: &[u8]) -> Option<Str> {
    // BOM tests via `has_prefix` (no `&&` chains inside the `else if` chain: Charon would
    // duplicate the remaining chain once per conjunct, impl/STYLE.md §5)
    if has_prefix(b, b"\xFF\xFE\x00\x00") {
        None
    } else if has_prefix(b, b"\x00\x00\xFE\xFF") {
        None
    } else if has_prefix(b, b"\xFE\xFF") {
        decode_utf16(b, 2, true)
    } else if has_prefix(b, b"\xFF\xFE") {
        decode_utf16(b, 2, false)
    } else if has_prefix(b, b"\xEF\xBB\xBF") {
        Some(decode_utf8(b, 3))
    } else {
        Some(decode_utf8(b, 0))
    }
}

/// `b.size ≥ p.size && b[0] == p[0] && ...` (the BOM tests of spec `streamReaderDecode`)
pub fn has_prefix(b: &[u8], p: &[u8]) -> bool {
    if b.len() < p.len() {
        false
    } else {
        let mut i = 0;
        let mut ok_ = true;
        while i < p.len() {
            if b[i] != p[i] {
                ok_ = false;
            }
            i = i + 1;
        }
        ok_
    }
}

/// Successive `StreamReader.ReadLine()` results; spec `readLines`
pub fn read_lines(cs: &[u32]) -> Vec<Str> {
    let mut lines: Vec<Str> = Vec::new();
    let mut cur: Str = Vec::new();
    let mut i = 0;
    let n = cs.len();
    let mut pending = false;
    while i < n {
        let c = cs[i];
        if c == 0x0A {
            lines.push(cur);
            cur = Vec::new();
            pending = false;
            i = i + 1;
        } else if c == 0x0D {
            lines.push(cur);
            cur = Vec::new();
            pending = false;
            i = if i + 1 < n && cs[i + 1] == 0x0A { i + 2 } else { i + 1 };
        } else {
            cur.push(c);
            pending = true;
            i = i + 1;
        }
    }
    if pending {
        lines.push(cur);
    }
    lines
}
