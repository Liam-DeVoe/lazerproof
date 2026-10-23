//! Minimal JSON reader (enough for the oracle's dumps, env files and APIMod lists). Numbers keep their text.

#[derive(Clone, Debug)]
pub enum J {
    Null,
    Bool(bool),
    Num(String),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

pub fn parse(s: &str) -> Result<J, String> {
    let b = s.as_bytes();
    let mut i = 0usize;
    let v = value(b, &mut i)?;
    ws(b, &mut i);
    if i != b.len() {
        return Err(format!("trailing data at {}", i));
    }
    Ok(v)
}

fn ws(b: &[u8], i: &mut usize) {
    while *i < b.len() && matches!(b[*i], b' ' | b'\n' | b'\t' | b'\r') {
        *i += 1;
    }
}

fn value(b: &[u8], i: &mut usize) -> Result<J, String> {
    ws(b, i);
    if *i >= b.len() {
        return Err("unexpected end".into());
    }
    match b[*i] {
        b'{' => {
            *i += 1;
            let mut kv = Vec::new();
            ws(b, i);
            if *i < b.len() && b[*i] == b'}' {
                *i += 1;
                return Ok(J::Obj(kv));
            }
            loop {
                ws(b, i);
                let k = match value(b, i)? {
                    J::Str(s) => s,
                    _ => return Err("object key".into()),
                };
                ws(b, i);
                if *i >= b.len() || b[*i] != b':' {
                    return Err("expected :".into());
                }
                *i += 1;
                let v = value(b, i)?;
                kv.push((k, v));
                ws(b, i);
                if *i < b.len() && b[*i] == b',' {
                    *i += 1;
                } else if *i < b.len() && b[*i] == b'}' {
                    *i += 1;
                    return Ok(J::Obj(kv));
                } else {
                    return Err("bad object".into());
                }
            }
        }
        b'[' => {
            *i += 1;
            let mut xs = Vec::new();
            ws(b, i);
            if *i < b.len() && b[*i] == b']' {
                *i += 1;
                return Ok(J::Arr(xs));
            }
            loop {
                xs.push(value(b, i)?);
                ws(b, i);
                if *i < b.len() && b[*i] == b',' {
                    *i += 1;
                } else if *i < b.len() && b[*i] == b']' {
                    *i += 1;
                    return Ok(J::Arr(xs));
                } else {
                    return Err("bad array".into());
                }
            }
        }
        b'"' => {
            *i += 1;
            let mut out: Vec<u8> = Vec::new();
            loop {
                if *i >= b.len() {
                    return Err("unterminated string".into());
                }
                let c = b[*i];
                *i += 1;
                match c {
                    b'"' => break,
                    b'\\' => {
                        if *i >= b.len() {
                            return Err("bad escape".into());
                        }
                        let e = b[*i];
                        *i += 1;
                        match e {
                            b'n' => out.push(b'\n'),
                            b't' => out.push(b'\t'),
                            b'r' => out.push(b'\r'),
                            b'b' => out.push(8),
                            b'f' => out.push(12),
                            b'u' => {
                                if *i + 4 > b.len() {
                                    return Err("bad \\u".into());
                                }
                                let h = std::str::from_utf8(&b[*i..*i + 4]).map_err(|_| "bad \\u")?;
                                let cp = u32::from_str_radix(h, 16).map_err(|_| "bad \\u")?;
                                *i += 4;
                                let ch = char::from_u32(cp).unwrap_or('\u{FFFD}');
                                let mut buf = [0u8; 4];
                                out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                            }
                            x => out.push(x),
                        }
                    }
                    x => out.push(x),
                }
            }
            Ok(J::Str(String::from_utf8(out).map_err(|_| "bad utf8")?))
        }
        b't' if b[*i..].starts_with(b"true") => {
            *i += 4;
            Ok(J::Bool(true))
        }
        b'f' if b[*i..].starts_with(b"false") => {
            *i += 5;
            Ok(J::Bool(false))
        }
        b'n' if b[*i..].starts_with(b"null") => {
            *i += 4;
            Ok(J::Null)
        }
        _ => {
            let st = *i;
            while *i < b.len() && matches!(b[*i], b'0'..=b'9' | b'-' | b'+' | b'.' | b'e' | b'E') {
                *i += 1;
            }
            if st == *i {
                return Err(format!("bad value at {}", st));
            }
            Ok(J::Num(String::from_utf8_lossy(&b[st..*i]).into_owned()))
        }
    }
}

impl J {
    pub fn get(&self, k: &str) -> Option<&J> {
        match self {
            // last occurrence wins (as a map would keep)
            J::Obj(kv) => kv.iter().rev().find(|(a, _)| a == k).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn field(&self, k: &str) -> Result<&J, String> {
        self.get(k).ok_or_else(|| format!("property not found: {}", k))
    }
    pub fn arr(&self) -> Result<&Vec<J>, String> {
        match self {
            J::Arr(x) => Ok(x),
            _ => Err("array expected".into()),
        }
    }
    pub fn str(&self) -> Result<&str, String> {
        match self {
            J::Str(x) => Ok(x),
            _ => Err("string expected".into()),
        }
    }
    pub fn bool(&self) -> Result<bool, String> {
        match self {
            J::Bool(x) => Ok(*x),
            _ => Err("bool expected".into()),
        }
    }
    pub fn int(&self) -> Result<i64, String> {
        match self {
            J::Num(t) => t.parse::<i64>().map_err(|_| format!("integer expected: {}", t)),
            _ => Err("number expected".into()),
        }
    }
    pub fn nat(&self) -> Result<u64, String> {
        match self {
            J::Num(t) => t.parse::<u64>().map_err(|_| format!("natural expected: {}", t)),
            _ => Err("number expected".into()),
        }
    }
}
