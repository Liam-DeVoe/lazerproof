//! `bmdump_rs`: the Rust side of the beatmap differential test; same CLI and output as the Lean
//! `bmdump` (`model/BmDump/Main.lean`):
//! * `bmdump_rs FILE.osu [MODS_JSON]` — dump of the playable beatmap
//! * `bmdump_rs batch LIST OUTDIR` — LIST lines `<osu path>\t<out name>[\t<mods json>]`
//! * `bmdump_rs sorttest` — check `list_sort` against `bmtest sorttest` output on stdin
use osu_eval_core::beatmap::dotnet::{list_sort, SortCmp, Str};
use osu_eval_core::beatmap::dump::dump_load;
use osu_eval_core::beatmap::mod_settings::{to_mod, JsonVal, ModConfig};
use osu_eval_core::beatmap::playable::load;
use osu_eval_core::net::parse::double_parse;
use std::io::{BufRead, Write};

/// Minimal JSON reader classifying numbers like Newtonsoft (spec: `BmDump/Main.lean` `Json`).
enum V {
    Num(String),
    Str(Vec<u32>),
    Bool(bool),
    Null,
    Arr(Vec<V>),
    Obj(Vec<(Vec<u32>, V)>),
}

struct P<'a> {
    s: &'a [char],
    i: usize,
}

impl<'a> P<'a> {
    fn ws(&mut self) {
        while self.i < self.s.len() && matches!(self.s[self.i], ' ' | '\n' | '\t' | '\r') {
            self.i += 1;
        }
    }
    fn peek(&self) -> Option<char> {
        self.s.get(self.i).copied()
    }
    fn expect(&mut self, c: char) -> Result<(), String> {
        self.ws();
        if self.peek() == Some(c) {
            self.i += 1;
            Ok(())
        } else {
            Err(format!("expected {}", c))
        }
    }
    fn hex_val(c: char) -> u32 {
        if c.is_ascii_digit() {
            c as u32 - '0' as u32
        } else if ('a'..='f').contains(&c) {
            c as u32 - 'a' as u32 + 10
        } else {
            (c as u32).wrapping_sub('A' as u32).wrapping_add(10)
        }
    }
    fn str_body(&mut self) -> Result<Vec<u32>, String> {
        let mut acc = Vec::new();
        loop {
            match self.peek() {
                None => return Err("unterminated string".into()),
                Some('"') => {
                    self.i += 1;
                    return Ok(acc);
                }
                Some('\\') if self.i + 1 < self.s.len() => {
                    let e = self.s[self.i + 1];
                    self.i += 2;
                    match e {
                        'n' => acc.push(10),
                        't' => acc.push(9),
                        'r' => acc.push(13),
                        'b' => acc.push(8),
                        'f' => acc.push(12),
                        'u' => {
                            if self.i + 4 > self.s.len() {
                                return Err("bad \\u".into());
                            }
                            let (a, b, c, d) = (self.s[self.i], self.s[self.i + 1], self.s[self.i + 2], self.s[self.i + 3]);
                            self.i += 4;
                            let n = ((Self::hex_val(a).wrapping_mul(16).wrapping_add(Self::hex_val(b))).wrapping_mul(16).wrapping_add(Self::hex_val(c)))
                                .wrapping_mul(16)
                                .wrapping_add(Self::hex_val(d));
                            // Lean `Char.ofNat`: invalid scalar values become '\0'
                            acc.push(if char::from_u32(n).is_some() { n } else { 0 });
                        }
                        c => acc.push(c as u32),
                    }
                }
                Some(c) => {
                    self.i += 1;
                    acc.push(c as u32);
                }
            }
        }
    }
    fn starts(&self, lit: &str) -> bool {
        let l: Vec<char> = lit.chars().collect();
        self.s.len() >= self.i + l.len() && self.s[self.i..self.i + l.len()] == l[..]
    }
    fn value(&mut self) -> Result<V, String> {
        self.ws();
        match self.peek() {
            Some('"') => {
                self.i += 1;
                Ok(V::Str(self.str_body()?))
            }
            Some('[') => {
                self.i += 1;
                self.ws();
                if self.peek() == Some(']') {
                    self.i += 1;
                    return Ok(V::Arr(vec![]));
                }
                let mut xs = vec![];
                loop {
                    xs.push(self.value()?);
                    self.ws();
                    match self.peek() {
                        Some(',') => self.i += 1,
                        Some(']') => {
                            self.i += 1;
                            break;
                        }
                        _ => return Err("bad array".into()),
                    }
                }
                Ok(V::Arr(xs))
            }
            Some('{') => {
                self.i += 1;
                self.ws();
                if self.peek() == Some('}') {
                    self.i += 1;
                    return Ok(V::Obj(vec![]));
                }
                let mut kvs = vec![];
                loop {
                    self.expect('"')?;
                    let k = self.str_body()?;
                    self.expect(':')?;
                    let v = self.value()?;
                    kvs.push((k, v));
                    self.ws();
                    match self.peek() {
                        Some(',') => self.i += 1,
                        Some('}') => {
                            self.i += 1;
                            break;
                        }
                        _ => return Err("bad object".into()),
                    }
                }
                Ok(V::Obj(kvs))
            }
            _ if self.starts("true") => {
                self.i += 4;
                Ok(V::Bool(true))
            }
            _ if self.starts("false") => {
                self.i += 5;
                Ok(V::Bool(false))
            }
            _ if self.starts("null") => {
                self.i += 4;
                Ok(V::Null)
            }
            _ => {
                let st = self.i;
                while self.i < self.s.len() && matches!(self.s[self.i], '0'..='9' | '-' | '+' | '.' | 'e' | 'E') {
                    self.i += 1;
                }
                if self.i == st {
                    return Err("bad value".into());
                }
                Ok(V::Num(self.s[st..self.i].iter().collect()))
            }
        }
    }
}

/// Lean `String.toNat!` (non-digits -> panic default 0)
fn to_nat(t: &str) -> Option<u128> {
    if t.is_empty() || !t.chars().all(|c| c.is_ascii_digit()) {
        return Some(0);
    }
    let mut v: u128 = 0;
    for c in t.chars() {
        v = v.checked_mul(10)?.checked_add(c as u128 - '0' as u128)?;
    }
    Some(v)
}

fn to_setting(v: &V) -> JsonVal {
    match v {
        V::Num(t) => {
            if t.chars().any(|c| c == '.' || c == 'e' || c == 'E') {
                let cs: Vec<u32> = t.chars().map(|c| c as u32).collect();
                match double_parse(&cs) {
                    Ok(d) => JsonVal::Double(d),
                    Err(_) => JsonVal::Null,
                }
            } else {
                let (neg, digits) = if let Some(r) = t.strip_prefix('-') { (true, r) } else { (false, t.as_str()) };
                match to_nat(digits) {
                    None => JsonVal::Big,
                    Some(m) => {
                        let n: i128 = if neg { -(m as i128) } else { m as i128 };
                        if m > (1u128 << 64) || n < i64::MIN as i128 || n > i64::MAX as i128 {
                            JsonVal::Big
                        } else {
                            JsonVal::Long(n as i64)
                        }
                    }
                }
            }
        }
        V::Str(s) => JsonVal::Str(s.clone()),
        V::Bool(b) => JsonVal::Bool(*b),
        V::Null => JsonVal::Null,
        _ => JsonVal::Big,
    }
}

fn s32(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

fn parse_mods(s: &str) -> Result<Vec<ModConfig>, String> {
    let cs: Vec<char> = s.chars().collect();
    let mut p = P { s: &cs, i: 0 };
    let v = p.value()?;
    match v {
        V::Arr(xs) => {
            let mut out = vec![];
            for x in &xs {
                match x {
                    V::Obj(kvs) => {
                        let acr: Str = match kvs.iter().find(|(k, _)| *k == s32("acronym")) {
                            Some((_, V::Str(a))) => a.clone(),
                            _ => vec![],
                        };
                        let settings: Vec<(Str, JsonVal)> = match kvs.iter().find(|(k, _)| *k == s32("settings")) {
                            Some((_, V::Obj(ss))) => ss.iter().map(|(k, v)| (k.clone(), to_setting(v))).collect(),
                            _ => vec![],
                        };
                        out.push(to_mod(&acr, &settings));
                    }
                    _ => return Err("mod is not an object".into()),
                }
            }
            Ok(out)
        }
        _ => Err("mods is not an array".into()),
    }
}

fn dump_file(path: &str, mods_json: Option<&str>) -> Result<String, String> {
    let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
    let mods = match mods_json {
        None => vec![],
        Some(j) => parse_mods(j).map_err(|e| format!("bad mods json: {}", e))?,
    };
    Ok(dump_load(&load(&bytes, &mods), &mods))
}

#[derive(Clone)]
struct KI(u64, u64);
impl SortCmp for KI {
    fn cmp3(&self, o: &KI) -> i32 {
        if self.0 < o.0 {
            -1
        } else if self.0 > o.0 {
            1
        } else {
            0
        }
    }
}

fn sort_test() -> i32 {
    let stdin = std::io::stdin();
    let (mut n, mut bad) = (0, 0);
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        let parts: Vec<&str> = line.split(' ').collect();
        if parts.len() == 2 {
            let (ks, perm) = (parts[0], parts[1]);
            let keys: Vec<u64> = if ks.is_empty() { vec![] } else { ks.split(',').map(|x| x.parse().unwrap_or(0)).collect() };
            let mut arr: Vec<KI> = keys.iter().enumerate().map(|(i, k)| KI(*k, i as u64)).collect();
            list_sort(&mut arr);
            let got: Vec<String> = arr.iter().map(|x| x.1.to_string()).collect();
            let got = got.join(",");
            n += 1;
            if got != perm {
                bad += 1;
                if bad <= 5 {
                    println!("MISMATCH keys={}\n  .NET {}\n  Rust {}", ks, perm, got);
                }
            }
        } else if parts.len() == 1 {
            n += 1;
            if !parts[0].is_empty() {
                bad += 1;
            }
        }
    }
    println!("sorttest: {} arrays, {} mismatches", n, bad);
    if bad == 0 { 0 } else { 1 }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    let code = match a.as_slice() {
        ["sorttest"] => sort_test(),
        ["bench", list] => {
            // pipeline only (decode + playable + mods), no dump formatting
            let f = std::fs::File::open(list).unwrap();
            let mut jobs = vec![];
            for l in std::io::BufReader::new(f).lines() {
                let l = l.unwrap();
                let parts: Vec<&str> = l.split('\t').collect();
                let mods = match parts.get(2) {
                    Some(j) => parse_mods(j).unwrap_or_default(),
                    None => vec![],
                };
                jobs.push((std::fs::read(parts[0]).unwrap(), mods));
            }
            let t0 = std::time::Instant::now();
            let mut n_ok = 0;
            for (b, m) in &jobs {
                if let osu_eval_core::beatmap::playable::LoadResult::Ok(_) = load(b, m) {
                    n_ok += 1;
                }
            }
            let dt = t0.elapsed().as_secs_f64();
            println!("{} maps ({} playable) in {:.3}s = {:.1} maps/s (load only, files preread)", jobs.len(), n_ok, dt, jobs.len() as f64 / dt);
            0
        }
        ["batch", list, out_dir] => {
            std::fs::create_dir_all(out_dir).unwrap();
            let f = std::fs::File::open(list).unwrap();
            for l in std::io::BufReader::new(f).lines() {
                let l = l.unwrap();
                let parts: Vec<&str> = l.split('\t').collect();
                if parts.len() >= 2 {
                    match dump_file(parts[0], parts.get(2).copied()) {
                        Ok(out) => std::fs::write(format!("{}/{}", out_dir, parts[1]), out).unwrap(),
                        Err(e) => {
                            eprintln!("{}: {}", parts[0], e);
                            std::process::exit(1);
                        }
                    }
                }
            }
            0
        }
        [file] => match dump_file(file, None) {
            Ok(out) => {
                std::io::stdout().write_all(out.as_bytes()).unwrap();
                0
            }
            Err(e) => {
                eprintln!("{}", e);
                1
            }
        },
        [file, mods] => match dump_file(file, Some(mods)) {
            Ok(out) => {
                std::io::stdout().write_all(out.as_bytes()).unwrap();
                0
            }
            Err(e) => {
                eprintln!("{}", e);
                1
            }
        },
        _ => {
            eprintln!("usage: bmdump_rs FILE.osu [MODS] | bmdump_rs batch LIST OUTDIR | bmdump_rs sorttest");
            2
        }
    };
    std::process::exit(code);
}
