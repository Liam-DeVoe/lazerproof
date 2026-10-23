//! IEEE-754 primitives (trusted base).
//!
//! `F64`/`F32` are thin wrappers over the raw bit patterns. This whole module is **opaque to
//! Charon** (`--opaque crate::float`, see `impl/charon.sh`): Aeneas sees only the type names and
//! signatures, and `proofs/OsuProofs/Generated/{TypesExternal,FunsExternal}.lean` defines each
//! item as *exactly* the corresponding `OsuModel.Net` spec function (`F64 := Float`,
//! `F64.add a b := ok (a + b)`, ...). The trust is therefore one identification per primitive:
//! "this Rust function computes the same IEEE value as that spec function"
//! (table in `docs/proof-poc.md`).
//!
//! Rules: every primitive is a single IEEE operation (or bit manipulation) with no branching
//! on NaN payloads; everything with .NET-specific semantics (Math.Max/Min/Clamp, ...) is written
//! *outside* this module on top of these primitives and proven against the spec.
//!
//! At runtime `#[inline(always)]` + `repr(transparent)` make each op a single SSE instruction
//! (`from_bits`/`to_bits` are no-ops on registers).

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct F64(u64);

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct F32(u32);

impl F64 {
    #[inline(always)]
    pub const fn from_bits(b: u64) -> F64 {
        F64(b)
    }
    #[inline(always)]
    pub fn to_bits(self) -> u64 {
        self.0
    }
    #[inline(always)]
    fn v(self) -> f64 {
        f64::from_bits(self.0)
    }
    #[inline(always)]
    fn w(x: f64) -> F64 {
        F64(x.to_bits())
    }
    #[inline(always)]
    pub fn native(self) -> f64 {
        self.v()
    }
    #[inline(always)]
    pub fn of_native(x: f64) -> F64 {
        F64::w(x)
    }
    #[inline(always)]
    pub fn add(self, o: F64) -> F64 {
        F64::w(self.v() + o.v())
    }
    #[inline(always)]
    pub fn sub(self, o: F64) -> F64 {
        F64::w(self.v() - o.v())
    }
    #[inline(always)]
    pub fn mul(self, o: F64) -> F64 {
        F64::w(self.v() * o.v())
    }
    #[inline(always)]
    pub fn div(self, o: F64) -> F64 {
        F64::w(self.v() / o.v())
    }
    /// sign flip (.NET unary minus)
    #[inline(always)]
    pub fn neg(self) -> F64 {
        F64::w(-self.v())
    }
    /// IEEE `<` (false on NaN)
    #[inline(always)]
    pub fn lt(self, o: F64) -> bool {
        self.v() < o.v()
    }
    /// IEEE `<=`
    #[inline(always)]
    pub fn le(self, o: F64) -> bool {
        self.v() <= o.v()
    }
    /// IEEE `==` (`+0 == -0`, NaN != NaN)
    #[inline(always)]
    pub fn eq(self, o: F64) -> bool {
        self.v() == o.v()
    }
    #[inline(always)]
    pub fn is_nan(self) -> bool {
        self.v().is_nan()
    }
    /// sign bit set
    #[inline(always)]
    pub fn is_negative(self) -> bool {
        (self.0 >> 63) == 1
    }
    /// `Math.Abs`: clear the sign bit
    #[inline(always)]
    pub fn abs(self) -> F64 {
        F64(self.0 & 0x7FFF_FFFF_FFFF_FFFF)
    }
    /// `Math.Floor` (`roundsd` mode 9)
    #[inline(always)]
    pub fn floor(self) -> F64 {
        F64::w(self.v().floor())
    }
    /// `Math.Sqrt` (`sqrtsd`)
    #[inline(always)]
    pub fn sqrt(self) -> F64 {
        F64::w(self.v().sqrt())
    }
    /// `(float)double` (`cvtsd2ss`, RNE)
    #[inline(always)]
    pub fn to_f32(self) -> F32 {
        F32((self.v() as f32).to_bits())
    }
    // ---- additions for the Sim/Replay port (each one trusted primitive = one OsuModel.Net fn) ----
    /// `Math.Truncate` (`roundsd` mode 11 / libm `trunc`); spec `F64.truncate`
    #[inline(always)]
    pub fn trunc(self) -> F64 {
        F64::w(self.v().trunc())
    }
    /// `Math.Pow` → glibc `pow`; spec `F64.pow` (extern `pow`)
    #[inline(always)]
    pub fn pow(self, y: F64) -> F64 {
        F64::w(unsafe { pow(self.v(), y.v()) })
    }
    /// `(double)long` (RNE); spec `F64.ofInt` / `F64.ofInt64`
    #[inline(always)]
    pub fn from_i64(n: i64) -> F64 {
        F64::w(n as f64)
    }
    /// `(double)ulong`-free helper for counts: `(double)n` (RNE); spec `F64.ofInt n`
    #[inline(always)]
    pub fn from_u64(n: u64) -> F64 {
        F64::w(n as f64)
    }
    /// `(int)double` with .NET 9+ saturating semantics (NaN → 0); spec `F64.toInt32`
    #[inline(always)]
    pub fn to_i32_sat(self) -> i32 {
        self.v() as i32
    }
    /// `(long)double` saturating (NaN → 0); spec `F64.toInt64`
    #[inline(always)]
    pub fn to_i64_sat(self) -> i64 {
        self.v() as i64
    }
    /// Correctly rounded decimal → binary64: `(-1)^neg * digits * 10^exp10` where `digits` are decimal digit
    /// values (0..=9, most significant first, may be empty = 0). Spec `F64.ofBitsN (Parse.decToBits Fmt.f64 neg m exp10)`
    /// (Rust's `dec2flt` is correctly rounded for any input length).
    pub fn parse_decimal(neg: bool, digits: &[u8], exp10: i64) -> F64 {
        F64::w(decimal_string(neg, digits, exp10).parse::<f64>().unwrap_or(0.0))
    }

}

impl F32 {
    #[inline(always)]
    pub const fn from_bits(b: u32) -> F32 {
        F32(b)
    }
    #[inline(always)]
    pub fn to_bits(self) -> u32 {
        self.0
    }
    #[inline(always)]
    fn v(self) -> f32 {
        f32::from_bits(self.0)
    }
    #[inline(always)]
    fn w(x: f32) -> F32 {
        F32(x.to_bits())
    }
    #[inline(always)]
    pub fn native(self) -> f32 {
        self.v()
    }
    #[inline(always)]
    pub fn of_native(x: f32) -> F32 {
        F32::w(x)
    }
    #[inline(always)]
    pub fn add(self, o: F32) -> F32 {
        F32::w(self.v() + o.v())
    }
    #[inline(always)]
    pub fn sub(self, o: F32) -> F32 {
        F32::w(self.v() - o.v())
    }
    #[inline(always)]
    pub fn mul(self, o: F32) -> F32 {
        F32::w(self.v() * o.v())
    }
    #[inline(always)]
    pub fn div(self, o: F32) -> F32 {
        F32::w(self.v() / o.v())
    }
    #[inline(always)]
    pub fn lt(self, o: F32) -> bool {
        self.v() < o.v()
    }
    #[inline(always)]
    pub fn eq(self, o: F32) -> bool {
        self.v() == o.v()
    }
    /// `(double)float` (exact)
    #[inline(always)]
    pub fn to_f64(self) -> F64 {
        F64::w(self.v() as f64)
    }
    // ---- additions for the Sim/Replay port ----
    /// sign flip (unary minus)
    #[inline(always)]
    pub fn neg(self) -> F32 {
        F32::w(-self.v())
    }
    /// IEEE `<=`
    #[inline(always)]
    pub fn le(self, o: F32) -> bool {
        self.v() <= o.v()
    }
    #[inline(always)]
    pub fn is_nan(self) -> bool {
        self.v().is_nan()
    }
    /// sign bit set
    #[inline(always)]
    pub fn is_negative(self) -> bool {
        (self.0 >> 31) == 1
    }
    /// `MathF.Abs`: clear the sign bit
    #[inline(always)]
    pub fn abs(self) -> F32 {
        F32(self.0 & 0x7FFF_FFFF)
    }
    /// `MathF.Pow` → glibc `powf`; spec `F32.pow`
    #[inline(always)]
    pub fn pow(self, y: F32) -> F32 {
        F32::w(unsafe { powf(self.v(), y.v()) })
    }
    /// `MathF.Atan2(y = self, x)` → glibc `atan2f`; spec `F32.atan2`
    #[inline(always)]
    pub fn atan2(self, x: F32) -> F32 {
        F32::w(unsafe { atan2f(self.v(), x.v()) })
    }
    /// `(float)long` (RNE); spec `F32.ofInt`
    #[inline(always)]
    pub fn from_i64(n: i64) -> F32 {
        F32::w(n as f32)
    }
    /// `(int)float` saturating (NaN → 0); spec `F32.toInt32`
    #[inline(always)]
    pub fn to_i32_sat(self) -> i32 {
        self.v() as i32
    }
    /// Correctly rounded decimal → binary32 (directly, no double rounding); spec
    /// `F32.ofBitsN (Parse.decToBits Fmt.f32 neg m exp10)`.
    pub fn parse_decimal(neg: bool, digits: &[u8], exp10: i64) -> F32 {
        F32::w(decimal_string(neg, digits, exp10).parse::<f32>().unwrap_or(0.0))
    }
}

/// `[-]D...De<exp>` for the decimal parse primitives (not translated: part of the opaque module).
fn decimal_string(neg: bool, digits: &[u8], exp10: i64) -> alloc::string::String {
    let mut s = alloc::string::String::with_capacity(digits.len() + 24);
    if neg {
        s.push('-');
    }
    if digits.is_empty() {
        s.push('0');
    }
    for &d in digits {
        s.push((b'0' + d) as char);
    }
    s.push('e');
    s.push_str(&alloc::format!("{}", exp10));
    s
}

// ---------------------------------------------------------------------------------------------
// Additional primitives (beatmap/net port, impl/STYLE.md). Same rules as above: each is one IEEE
// operation / conversion / libm call, identified with the `OsuModel.Net` function named in its
// doc comment. Add new ones *additively* (never rename); shared with the sim port.
// ---------------------------------------------------------------------------------------------

/// glibc libm entry points, resolved at run time with `dlopen("libm.so.6")`/`dlsym` (or, D86, the vendored
/// static build of the same glibc 2.39 sources: see `LIBM_VENDORED`).
/// Calling through these pointers (a) guarantees the *glibc* implementation is used (Rust's
/// `compiler_builtins` ships its own weak `cbrt`, `pow`, ... symbols that can win at link time) and
/// (b) stops LLVM's libcall simplifier from rewriting calls (e.g. `pow(2.0, x)` -> `exp2(x)`, which
/// is not bit-identical). Found by `nettest_rs` (Math.Cbrt, Easing/Damp with `pow(2, x)`).
struct Libm {
    sin: extern "C" fn(f64) -> f64,
    cos: extern "C" fn(f64) -> f64,
    tan: extern "C" fn(f64) -> f64,
    asin: extern "C" fn(f64) -> f64,
    acos: extern "C" fn(f64) -> f64,
    atan: extern "C" fn(f64) -> f64,
    exp: extern "C" fn(f64) -> f64,
    log: extern "C" fn(f64) -> f64,
    log10: extern "C" fn(f64) -> f64,
    cbrt: extern "C" fn(f64) -> f64,
    atan2: extern "C" fn(f64, f64) -> f64,
    pow: extern "C" fn(f64, f64) -> f64,
    fmod: extern "C" fn(f64, f64) -> f64,
    sinf: extern "C" fn(f32) -> f32,
    cosf: extern "C" fn(f32) -> f32,
    tanf: extern "C" fn(f32) -> f32,
    asinf: extern "C" fn(f32) -> f32,
    acosf: extern "C" fn(f32) -> f32,
    atanf: extern "C" fn(f32) -> f32,
    expf: extern "C" fn(f32) -> f32,
    logf: extern "C" fn(f32) -> f32,
    atan2f: extern "C" fn(f32, f32) -> f32,
    powf: extern "C" fn(f32, f32) -> f32,
}

// Default on Linux: glibc's own libm.so.6, dlopen'd (the trusted row "glibc 2.39 x86-64 libm").
#[cfg(any(not(lp_vendored_libm), feature = "verify-libm"))]
extern "C" {
    fn dlopen(filename: *const u8, flag: i32) -> *mut u8;
    fn dlsym(handle: *mut u8, symbol: *const u8) -> *mut u8;
}

#[cfg(any(not(lp_vendored_libm), feature = "verify-libm"))]
unsafe fn sym(h: *mut u8, name: &[u8]) -> *mut u8 {
    let p = dlsym(h, name.as_ptr());
    if p.is_null() {
        panic!("libm symbol missing");
    }
    p
}

#[cfg(any(not(lp_vendored_libm), feature = "verify-libm"))]
static LIBM: std::sync::OnceLock<Libm> = std::sync::OnceLock::new();

#[cfg(any(not(lp_vendored_libm), feature = "verify-libm"))]
#[inline(always)]
fn glibc_libm() -> &'static Libm {
    LIBM.get_or_init(|| unsafe {
        let h = dlopen(b"libm.so.6\0".as_ptr(), 2 /* RTLD_NOW */);
        if h.is_null() {
            panic!("cannot dlopen libm.so.6 (non-glibc platform: build with --features vendored-libm)");
        }
        Libm {
            sin: core::mem::transmute(sym(h, b"sin\0")),
            cos: core::mem::transmute(sym(h, b"cos\0")),
            tan: core::mem::transmute(sym(h, b"tan\0")),
            asin: core::mem::transmute(sym(h, b"asin\0")),
            acos: core::mem::transmute(sym(h, b"acos\0")),
            atan: core::mem::transmute(sym(h, b"atan\0")),
            exp: core::mem::transmute(sym(h, b"exp\0")),
            log: core::mem::transmute(sym(h, b"log\0")),
            log10: core::mem::transmute(sym(h, b"log10\0")),
            cbrt: core::mem::transmute(sym(h, b"cbrt\0")),
            atan2: core::mem::transmute(sym(h, b"atan2\0")),
            pow: core::mem::transmute(sym(h, b"pow\0")),
            fmod: core::mem::transmute(sym(h, b"fmod\0")),
            sinf: core::mem::transmute(sym(h, b"sinf\0")),
            cosf: core::mem::transmute(sym(h, b"cosf\0")),
            tanf: core::mem::transmute(sym(h, b"tanf\0")),
            asinf: core::mem::transmute(sym(h, b"asinf\0")),
            acosf: core::mem::transmute(sym(h, b"acosf\0")),
            atanf: core::mem::transmute(sym(h, b"atanf\0")),
            expf: core::mem::transmute(sym(h, b"expf\0")),
            logf: core::mem::transmute(sym(h, b"logf\0")),
            atan2f: core::mem::transmute(sym(h, b"atan2f\0")),
            powf: core::mem::transmute(sym(h, b"powf\0")),
        }
    })
}

// D86, vendored build (always on non-Linux targets; `--features vendored-libm` on Linux; build.rs): the glibc 2.39
// sources of these 23 functions (vendor/glibc-libm), with glibc x86-64's FMA contractions written as explicit
// `fma` and compiled with `-ffp-contract=off`, statically linked under `lp_` names. The calls still go through the
// function-pointer table (read through `black_box`, so LLVM cannot see the targets): the libcall simplifier can then
// never rewrite them (comment on `Libm` above), whatever names the vendored symbols have.
#[cfg(lp_vendored_libm)]
unsafe extern "C" {
    safe fn lp_sin(x: f64) -> f64;
    safe fn lp_cos(x: f64) -> f64;
    safe fn lp_tan(x: f64) -> f64;
    safe fn lp_asin(x: f64) -> f64;
    safe fn lp_acos(x: f64) -> f64;
    safe fn lp_atan(x: f64) -> f64;
    safe fn lp_exp(x: f64) -> f64;
    safe fn lp_log(x: f64) -> f64;
    safe fn lp_log10(x: f64) -> f64;
    safe fn lp_cbrt(x: f64) -> f64;
    safe fn lp_atan2(x: f64, y: f64) -> f64;
    safe fn lp_pow(x: f64, y: f64) -> f64;
    safe fn lp_fmod(x: f64, y: f64) -> f64;
    safe fn lp_sinf(x: f32) -> f32;
    safe fn lp_cosf(x: f32) -> f32;
    safe fn lp_tanf(x: f32) -> f32;
    safe fn lp_asinf(x: f32) -> f32;
    safe fn lp_acosf(x: f32) -> f32;
    safe fn lp_atanf(x: f32) -> f32;
    safe fn lp_expf(x: f32) -> f32;
    safe fn lp_logf(x: f32) -> f32;
    safe fn lp_atan2f(x: f32, y: f32) -> f32;
    safe fn lp_powf(x: f32, y: f32) -> f32;
}

#[cfg(lp_vendored_libm)]
static LIBM_VENDORED: Libm = Libm {
    sin: lp_sin,
    cos: lp_cos,
    tan: lp_tan,
    asin: lp_asin,
    acos: lp_acos,
    atan: lp_atan,
    exp: lp_exp,
    log: lp_log,
    log10: lp_log10,
    cbrt: lp_cbrt,
    atan2: lp_atan2,
    pow: lp_pow,
    fmod: lp_fmod,
    sinf: lp_sinf,
    cosf: lp_cosf,
    tanf: lp_tanf,
    asinf: lp_asinf,
    acosf: lp_acosf,
    atanf: lp_atanf,
    expf: lp_expf,
    logf: lp_logf,
    atan2f: lp_atan2f,
    powf: lp_powf,
};

#[cfg(lp_vendored_libm)]
#[inline(always)]
fn libm() -> &'static Libm {
    core::hint::black_box(&LIBM_VENDORED)
}

#[cfg(not(lp_vendored_libm))]
#[inline(always)]
fn libm() -> &'static Libm {
    glibc_libm()
}

/// D86 validation only (`--features verify-libm`, implies the vendored build; never in a release build): every libm
/// call is also made on the dlopen'd glibc and the result bits compared. Mismatches go to stderr at once; at exit one
/// summary line per process (`verify-libm calls=<23 counts> mismatches=<23 counts>`) is appended to
/// `$LP_VERIFY_LIBM` (if set).
#[cfg(feature = "verify-libm")]
mod verify {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
    static CALLS: [AtomicU64; 23] = [const { AtomicU64::new(0) }; 23];
    static BAD: [AtomicU64; 23] = [const { AtomicU64::new(0) }; 23];
    static REG: std::sync::Once = std::sync::Once::new();
    extern "C" {
        fn atexit(cb: extern "C" fn()) -> i32;
    }
    extern "C" fn summary() {
        let c: Vec<String> = CALLS.iter().map(|a| a.load(Relaxed).to_string()).collect();
        let b: Vec<String> = BAD.iter().map(|a| a.load(Relaxed).to_string()).collect();
        let line = format!("verify-libm calls={} mismatches={}\n", c.join(","), b.join(","));
        if let Some(p) = std::env::var_os("LP_VERIFY_LIBM") {
            use std::io::Write;
            if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(p) {
                let _ = f.write_all(line.as_bytes());
            }
        }
    }
    pub fn chk(f: usize, x: u64, y: u64, vendored: u64, glibc: u64) {
        REG.call_once(|| unsafe {
            atexit(summary);
        });
        CALLS[f].fetch_add(1, Relaxed);
        if vendored != glibc {
            BAD[f].fetch_add(1, Relaxed);
            eprintln!("verify-libm MISMATCH fn#{} x={:#x} y={:#x} vendored={:#x} glibc={:#x}", f, x, y, vendored, glibc);
        }
    }
}

#[inline(always)]
unsafe fn sin(x: f64) -> f64 {
    let r = (libm().sin)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(0, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().sin)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn cos(x: f64) -> f64 {
    let r = (libm().cos)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(1, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().cos)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn tan(x: f64) -> f64 {
    let r = (libm().tan)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(2, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().tan)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn asin(x: f64) -> f64 {
    let r = (libm().asin)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(3, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().asin)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn acos(x: f64) -> f64 {
    let r = (libm().acos)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(4, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().acos)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn atan(x: f64) -> f64 {
    let r = (libm().atan)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(5, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().atan)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn exp(x: f64) -> f64 {
    let r = (libm().exp)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(6, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().exp)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn log(x: f64) -> f64 {
    let r = (libm().log)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(7, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().log)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn log10(x: f64) -> f64 {
    let r = (libm().log10)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(8, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().log10)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn cbrt(x: f64) -> f64 {
    let r = (libm().cbrt)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(9, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().cbrt)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn atan2(x: f64, y: f64) -> f64 {
    let r = (libm().atan2)(x, y);
    #[cfg(feature = "verify-libm")]
    verify::chk(10, x.to_bits() as u64, y.to_bits() as u64, r.to_bits() as u64, (glibc_libm().atan2)(x, y).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn pow(x: f64, y: f64) -> f64 {
    let r = (libm().pow)(x, y);
    #[cfg(feature = "verify-libm")]
    verify::chk(11, x.to_bits() as u64, y.to_bits() as u64, r.to_bits() as u64, (glibc_libm().pow)(x, y).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn fmod(x: f64, y: f64) -> f64 {
    let r = (libm().fmod)(x, y);
    #[cfg(feature = "verify-libm")]
    verify::chk(12, x.to_bits() as u64, y.to_bits() as u64, r.to_bits() as u64, (glibc_libm().fmod)(x, y).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn sinf(x: f32) -> f32 {
    let r = (libm().sinf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(13, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().sinf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn cosf(x: f32) -> f32 {
    let r = (libm().cosf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(14, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().cosf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn tanf(x: f32) -> f32 {
    let r = (libm().tanf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(15, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().tanf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn asinf(x: f32) -> f32 {
    let r = (libm().asinf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(16, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().asinf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn acosf(x: f32) -> f32 {
    let r = (libm().acosf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(17, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().acosf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn atanf(x: f32) -> f32 {
    let r = (libm().atanf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(18, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().atanf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn expf(x: f32) -> f32 {
    let r = (libm().expf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(19, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().expf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn logf(x: f32) -> f32 {
    let r = (libm().logf)(x);
    #[cfg(feature = "verify-libm")]
    verify::chk(20, x.to_bits() as u64, 0, r.to_bits() as u64, (glibc_libm().logf)(x).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn atan2f(x: f32, y: f32) -> f32 {
    let r = (libm().atan2f)(x, y);
    #[cfg(feature = "verify-libm")]
    verify::chk(21, x.to_bits() as u64, y.to_bits() as u64, r.to_bits() as u64, (glibc_libm().atan2f)(x, y).to_bits() as u64);
    r
}
#[inline(always)]
unsafe fn powf(x: f32, y: f32) -> f32 {
    let r = (libm().powf)(x, y);
    #[cfg(feature = "verify-libm")]
    verify::chk(22, x.to_bits() as u64, y.to_bits() as u64, r.to_bits() as u64, (glibc_libm().powf)(x, y).to_bits() as u64);
    r
}

impl F64 {
    /// `Math.Ceiling` (`roundsd` mode 10); spec `OsuModel.Net.F64.ceiling`
    #[inline(always)]
    pub fn ceil(self) -> F64 {
        F64::w(self.v().ceil())
    }
    /// C# `(uint)x`, saturating; spec `OsuModel.Net.F64.toUInt32`
    #[inline(always)]
    pub fn to_u32(self) -> u32 {
        self.v() as u32
    }
    /// C# `(ulong)x`, saturating; spec `OsuModel.Net.F64.toUInt64`
    #[inline(always)]
    pub fn to_u64(self) -> u64 {
        self.v() as u64
    }
    /// `Math.Sin` -> glibc `sin`; spec `OsuModel.Net.F64.sin` (trusted extern)
    #[inline(always)]
    pub fn sin(self) -> F64 {
        F64::w(unsafe { sin(self.v()) })
    }
    /// `Math.Cos` -> glibc `cos`; spec `OsuModel.Net.F64.cos`
    #[inline(always)]
    pub fn cos(self) -> F64 {
        F64::w(unsafe { cos(self.v()) })
    }
    /// `Math.Tan` -> glibc `tan`; spec `OsuModel.Net.F64.tan`
    #[inline(always)]
    pub fn tan(self) -> F64 {
        F64::w(unsafe { tan(self.v()) })
    }
    /// `Math.Asin` -> glibc `asin`; spec `OsuModel.Net.F64.asin`
    #[inline(always)]
    pub fn asin(self) -> F64 {
        F64::w(unsafe { asin(self.v()) })
    }
    /// `Math.Acos` -> glibc `acos`; spec `OsuModel.Net.F64.acos`
    #[inline(always)]
    pub fn acos(self) -> F64 {
        F64::w(unsafe { acos(self.v()) })
    }
    /// `Math.Atan` -> glibc `atan`; spec `OsuModel.Net.F64.atan`
    #[inline(always)]
    pub fn atan(self) -> F64 {
        F64::w(unsafe { atan(self.v()) })
    }
    /// `Math.Atan2(y, x)` -> glibc `atan2`; spec `OsuModel.Net.F64.atan2` (self = y)
    #[inline(always)]
    pub fn atan2(self, x: F64) -> F64 {
        F64::w(unsafe { atan2(self.v(), x.v()) })
    }
    /// `Math.Exp` -> glibc `exp`; spec `OsuModel.Net.F64.exp`
    #[inline(always)]
    pub fn exp(self) -> F64 {
        F64::w(unsafe { exp(self.v()) })
    }
    /// `Math.Log` -> glibc `log`; spec `OsuModel.Net.F64.log`
    #[inline(always)]
    pub fn log(self) -> F64 {
        F64::w(unsafe { log(self.v()) })
    }
    /// `Math.Log10` -> glibc `log10`; spec `OsuModel.Net.F64.log10`
    #[inline(always)]
    pub fn log10(self) -> F64 {
        F64::w(unsafe { log10(self.v()) })
    }
    /// `Math.Cbrt` -> glibc `cbrt`; spec `OsuModel.Net.F64.cbrt`
    #[inline(always)]
    pub fn cbrt(self) -> F64 {
        F64::w(unsafe { cbrt(self.v()) })
    }
    /// C# `a % b` on doubles = IEEE `fmod` (exact); spec `OsuModel.Beatmap.fmodF64`
    #[inline(always)]
    pub fn fmod(self, b: F64) -> F64 {
        F64::w(unsafe { fmod(self.v(), b.v()) })
    }
}

impl F32 {
    /// `MathF.Floor`; spec `OsuModel.Net.F32.floor`
    #[inline(always)]
    pub fn floor(self) -> F32 {
        F32::w(self.v().floor())
    }
    /// `MathF.Ceiling`; spec `OsuModel.Net.F32.ceiling`
    #[inline(always)]
    pub fn ceil(self) -> F32 {
        F32::w(self.v().ceil())
    }
    /// `MathF.Truncate`; spec `OsuModel.Net.F32.truncate`
    #[inline(always)]
    pub fn trunc(self) -> F32 {
        F32::w(self.v().trunc())
    }
    /// `MathF.Sqrt` (`sqrtss`); spec `OsuModel.Net.F32.sqrt`
    #[inline(always)]
    pub fn sqrt(self) -> F32 {
        F32::w(self.v().sqrt())
    }
    /// C# `(uint)x` (saturating); spec `OsuModel.Net.F32.toUInt32`
    #[inline(always)]
    pub fn to_u32(self) -> u32 {
        self.v() as u32
    }
    /// C# `(ulong)x` (saturating); spec `OsuModel.Net.F32.toUInt64`
    #[inline(always)]
    pub fn to_u64(self) -> u64 {
        self.v() as u64
    }
    /// `MathF.Sin` -> `sinf`; spec `OsuModel.Net.F32.sin`
    #[inline(always)]
    pub fn sin(self) -> F32 {
        F32::w(unsafe { sinf(self.v()) })
    }
    /// `MathF.Cos` -> `cosf`
    #[inline(always)]
    pub fn cos(self) -> F32 {
        F32::w(unsafe { cosf(self.v()) })
    }
    /// `MathF.Tan` -> `tanf`
    #[inline(always)]
    pub fn tan(self) -> F32 {
        F32::w(unsafe { tanf(self.v()) })
    }
    /// `MathF.Asin` -> `asinf`
    #[inline(always)]
    pub fn asin(self) -> F32 {
        F32::w(unsafe { asinf(self.v()) })
    }
    /// `MathF.Acos` -> `acosf`
    #[inline(always)]
    pub fn acos(self) -> F32 {
        F32::w(unsafe { acosf(self.v()) })
    }
    /// `MathF.Atan` -> `atanf`
    #[inline(always)]
    pub fn atan(self) -> F32 {
        F32::w(unsafe { atanf(self.v()) })
    }
    /// `MathF.Exp` -> `expf`
    #[inline(always)]
    pub fn exp(self) -> F32 {
        F32::w(unsafe { expf(self.v()) })
    }
    /// `MathF.Log` -> `logf`
    #[inline(always)]
    pub fn log(self) -> F32 {
        F32::w(unsafe { logf(self.v()) })
    }
    /// C# `(long)x` for float (saturating); spec `OsuModel.Net.F32.toInt64`
    #[inline(always)]
    pub fn to_i64_sat(self) -> i64 {
        self.v() as i64
    }
    /// C# `(float)u` for ulong (one RNE rounding); spec `OsuModel.Net.F32.ofUInt64`
    #[inline(always)]
    pub fn from_u64(n: u64) -> F32 {
        F32::w(n as f32)
    }
}
