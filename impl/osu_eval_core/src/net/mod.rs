//! .NET numeric helpers on top of the `float` primitives (translated by Aeneas and proven equal
//! to `OsuModel.Net` — they are *not* part of the trusted base).
//!
//! Port of `model/OsuModel/Net/*` (see impl/STYLE.md). Submodules mirror the Lean files:
//! `basic` (Basic.lean), `mathops` (MathOps.lean), `libm` (Libm.lean), `parse` (Parse.lean),
//! `random` (Random.lean), `decimal` (Decimal.lean), `osutk` (OsuTK.lean), `sysmisc`
//! (SysMisc.lean), `framework` (Framework.lean). Conversions (Convert.lean) and the
//! `Fmt`-level bit algorithms (Fmt.lean) are trusted primitives in `crate::float`.

/// Early return on `Err` (Aeneas-friendly expansion of `?`: an explicit `match` + `return`).
/// Do not use inside loops (STYLE.md).
macro_rules! tri {
    ($e:expr) => {
        match $e {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
}

pub mod basic;
pub mod mathops;
pub mod libm;
pub mod parse;
pub mod random;
pub mod decimal;
pub mod osutk;
pub mod sysmisc;
pub mod framework;

pub use basic::NetExn;
use crate::float::F64;

/// `Math.Max(double, double)` (IEEE 754:2019 maximum); spec `OsuModel.Net.F64.max`.
pub fn max(val1: F64, val2: F64) -> F64 {
    if !val1.eq(val2) {
        if !val1.is_nan() {
            if val2.lt(val1) { val1 } else { val2 }
        } else {
            val1
        }
    } else if val2.is_negative() {
        val1
    } else {
        val2
    }
}

/// `Math.Min(double, double)`; spec `OsuModel.Net.F64.min`.
pub fn min(val1: F64, val2: F64) -> F64 {
    if !val1.eq(val2) {
        if !val1.is_nan() {
            if val1.lt(val2) { val1 } else { val2 }
        } else {
            val1
        }
    } else if val1.is_negative() {
        val1
    } else {
        val2
    }
}

/// `Math.Clamp(value, lo, hi)`; `None` = ArgumentException. Spec `OsuModel.Net.F64.clamp`.
pub fn clamp(value: F64, lo: F64, hi: F64) -> Option<F64> {
    if hi.lt(lo) {
        None
    } else if value.lt(lo) {
        Some(lo)
    } else if hi.lt(value) {
        Some(hi)
    } else {
        Some(value)
    }
}
