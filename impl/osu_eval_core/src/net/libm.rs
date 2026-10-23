//! Port of `OsuModel/Net/Libm.lean`. The transcendentals themselves are trusted primitives
//! (`F64::sin` ... in `crate::float`, glibc 2.39); only the managed `Math.Log(a, newBase)` is here.
use super::basic::{F64_NAN, F64_POS_INF};
use crate::float::F64;

const ONE: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const ZERO: F64 = F64::from_bits(0);

/// `Math.Log(a, newBase)`; spec `OsuModel.Net.F64.logBase`
pub fn f64_log_base(a: F64, new_base: F64) -> F64 {
    if a.is_nan() {
        a
    } else if new_base.is_nan() {
        new_base
    } else if new_base.eq(ONE) {
        F64_NAN
    } else if !a.eq(ONE) && (new_base.eq(ZERO) || new_base.eq(F64_POS_INF)) {
        F64_NAN
    } else {
        a.log().div(new_base.log())
    }
}
