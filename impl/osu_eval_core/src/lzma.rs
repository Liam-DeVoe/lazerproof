//! TRUSTED BOUNDARY (docs/model-eval.md "Trust boundary: LZMA", docs/proof-pipeline.md trusted base):
//! LZMA "alone" (`.lzma`: 5 property bytes, 8-byte size, stream) decompression of the `.osr` payloads.
//! Spec: the opaque `OsuModel.Replay.Osr.lzmaAloneDecode` (`@[extern "osu_lzma_alone_decode"]`,
//! `model/c/lzma_shim.c`). This module is a line-by-line port of that C shim onto the *same* system
//! liblzma (xz-utils 5.4.5, `liblzma.so.5`; the Lean binary links the static `liblzma.a` of the same
//! package), resolved at run time with `dlopen`/`dlsym` (as `float.rs` does for libm), so no build
//! script and no link-time dependency is added to the other binaries of the workspace.
//! Opaque to Charon (`impl/charon_check.sh --opaque crate::lzma`): the translated code sees only
//! `lzma_alone_decode : &[u8] -> usize -> Result<Vec<u8>, LzmaErr>`.
use alloc::vec::Vec;

/// The shim's error messages (`mk_except_error` call sites), as ids.
/// (no `PartialEq` derive: it would be one more opaque item in the trusted base)
#[derive(Clone, Copy)]
pub enum LzmaErr {
    /// "lzma: decoder init failed"
    InitFailed,
    /// "lzma: out of memory" (`LZMA_MEM_ERROR`; allocation failures abort the Rust process instead)
    OutOfMemory,
    /// "lzma: output too large"
    OutputTooLarge,
    /// "lzma: format error"
    Format,
    /// "lzma: data error"
    Data,
    /// "lzma: truncated input" (`LZMA_BUF_ERROR` under `LZMA_FINISH`)
    Truncated,
    /// "lzma: decode error" (any other `lzma_ret`)
    Other,
}

/// The shim's message text of an `LzmaErr` (spec: the `String` in the `Except`).
pub fn message(e: LzmaErr) -> &'static str {
    match e {
        LzmaErr::InitFailed => "lzma: decoder init failed",
        LzmaErr::OutOfMemory => "lzma: out of memory",
        LzmaErr::OutputTooLarge => "lzma: output too large",
        LzmaErr::Format => "lzma: format error",
        LzmaErr::Data => "lzma: data error",
        LzmaErr::Truncated => "lzma: truncated input",
        LzmaErr::Other => "lzma: decode error",
    }
}

/// `lzma_stream` (`<lzma/base.h>`, liblzma 5.4); `LZMA_STREAM_INIT` = all zero.
#[repr(C)]
struct LzmaStream {
    next_in: *const u8,
    avail_in: usize,
    total_in: u64,
    next_out: *mut u8,
    avail_out: usize,
    total_out: u64,
    allocator: *const u8,
    internal: *mut u8,
    reserved_ptr1: *mut u8,
    reserved_ptr2: *mut u8,
    reserved_ptr3: *mut u8,
    reserved_ptr4: *mut u8,
    seek_pos: u64,
    reserved_int2: u64,
    reserved_int3: usize,
    reserved_int4: usize,
    reserved_enum1: i32,
    reserved_enum2: i32,
}

struct Liblzma {
    alone_decoder: unsafe extern "C" fn(*mut LzmaStream, u64) -> i32,
    code: unsafe extern "C" fn(*mut LzmaStream, i32) -> i32,
    end: unsafe extern "C" fn(*mut LzmaStream),
}

#[cfg(not(lp_vendored_lzma))]
extern "C" {
    fn dlopen(filename: *const u8, flag: i32) -> *mut u8;
    fn dlsym(handle: *mut u8, symbol: *const u8) -> *mut u8;
}

#[cfg(not(lp_vendored_lzma))]
unsafe fn sym(h: *mut u8, name: &[u8]) -> *mut u8 {
    let p = dlsym(h, name.as_ptr());
    if p.is_null() {
        panic!("liblzma symbol missing");
    }
    p
}

#[cfg(not(lp_vendored_lzma))]
static LIBLZMA: std::sync::OnceLock<Liblzma> = std::sync::OnceLock::new();

#[cfg(not(lp_vendored_lzma))]
fn liblzma() -> &'static Liblzma {
    LIBLZMA.get_or_init(|| unsafe {
        let h = dlopen(b"liblzma.so.5\0".as_ptr(), 2 /* RTLD_NOW */);
        if h.is_null() {
            panic!("cannot dlopen liblzma.so.5 (build with --features vendored-lzma)");
        }
        Liblzma {
            alone_decoder: core::mem::transmute(sym(h, b"lzma_alone_decoder\0")),
            code: core::mem::transmute(sym(h, b"lzma_code\0")),
            end: core::mem::transmute(sym(h, b"lzma_end\0")),
        }
    })
}

// D86, vendored build (always on non-Linux targets; `--features vendored-lzma` on Linux; build.rs): the decoder
// subset of the same xz 5.4.5 liblzma sources (vendor/xz), statically linked under `lp_` names. Integer-only code,
// so it computes the same bytes on every platform.
#[cfg(lp_vendored_lzma)]
extern "C" {
    fn lp_lzma_alone_decoder(strm: *mut LzmaStream, memlimit: u64) -> i32;
    fn lp_lzma_code(strm: *mut LzmaStream, action: i32) -> i32;
    fn lp_lzma_end(strm: *mut LzmaStream);
}

#[cfg(lp_vendored_lzma)]
static LIBLZMA_VENDORED: Liblzma = Liblzma { alone_decoder: lp_lzma_alone_decoder, code: lp_lzma_code, end: lp_lzma_end };

#[cfg(lp_vendored_lzma)]
fn liblzma() -> &'static Liblzma {
    &LIBLZMA_VENDORED
}

const LZMA_OK: i32 = 0;
const LZMA_STREAM_END: i32 = 1;
const LZMA_MEM_ERROR: i32 = 5;
const LZMA_FORMAT_ERROR: i32 = 7;
const LZMA_DATA_ERROR: i32 = 9;
const LZMA_BUF_ERROR: i32 = 10;
const LZMA_FINISH: i32 = 3;

/// `.lzma` bytes -> decompressed bytes, at most `max_out` (spec `Osr.lzmaAloneDecode`; the C shim
/// `osu_lzma_alone_decode`, same buffer growth and error mapping).
pub fn lzma_alone_decode(input: &[u8], max_out: usize) -> Result<Vec<u8>, LzmaErr> {
    let lib = liblzma();
    let mut strm = LzmaStream {
        next_in: core::ptr::null(),
        avail_in: 0,
        total_in: 0,
        next_out: core::ptr::null_mut(),
        avail_out: 0,
        total_out: 0,
        allocator: core::ptr::null(),
        internal: core::ptr::null_mut(),
        reserved_ptr1: core::ptr::null_mut(),
        reserved_ptr2: core::ptr::null_mut(),
        reserved_ptr3: core::ptr::null_mut(),
        reserved_ptr4: core::ptr::null_mut(),
        seek_pos: 0,
        reserved_int2: 0,
        reserved_int3: 0,
        reserved_int4: 0,
        reserved_enum1: 0,
        reserved_enum2: 0,
    };
    unsafe {
        if (lib.alone_decoder)(&mut strm, u64::MAX) != LZMA_OK {
            return Err(LzmaErr::InitFailed);
        }
        let mut cap = input.len().saturating_mul(4).saturating_add(4096);
        if cap > max_out {
            cap = max_out + 1;
        }
        let mut out: Vec<u8> = vec![0u8; cap];
        let mut len: usize = 0;
        strm.next_in = input.as_ptr();
        strm.avail_in = input.len();
        loop {
            if len == cap {
                if cap > max_out {
                    (lib.end)(&mut strm);
                    return Err(LzmaErr::OutputTooLarge);
                }
                let mut ncap = cap.saturating_mul(2);
                if ncap > max_out + 1 {
                    ncap = max_out + 1;
                }
                out.resize(ncap, 0);
                cap = ncap;
            }
            strm.next_out = out.as_mut_ptr().add(len);
            strm.avail_out = cap - len;
            let ret = (lib.code)(&mut strm, LZMA_FINISH);
            len = cap - strm.avail_out;
            if ret == LZMA_STREAM_END {
                break;
            }
            if ret != LZMA_OK {
                (lib.end)(&mut strm);
                return Err(match ret {
                    LZMA_FORMAT_ERROR => LzmaErr::Format,
                    LZMA_DATA_ERROR => LzmaErr::Data,
                    LZMA_BUF_ERROR => LzmaErr::Truncated,
                    LZMA_MEM_ERROR => LzmaErr::OutOfMemory,
                    _ => LzmaErr::Other,
                });
            }
        }
        (lib.end)(&mut strm);
        if len > max_out {
            return Err(LzmaErr::OutputTooLarge);
        }
        out.truncate(len);
        Ok(out)
    }
}
