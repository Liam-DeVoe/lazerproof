//! Port of `OsuModel/Beatmap/DotNet.lean`: BCL behaviour used by the beatmap pipeline (string
//! trimming/splitting, `Enum.TryParse`, `double.CompareTo`, `%`, `List<double>.BinarySearch`,
//! `List<T>.Sort` introsort (unstable), LINQ `OrderBy` (stable)).
//!
//! Strings are `Vec<u32>` / `&[u32]` of Unicode scalar values (= Lean `String`).
use crate::float::{F32, F64};
use crate::net::basic::{f64_copy_sign, f64_is_inf, F64_NAN};
use crate::net::parse::{int_parse, is_digit, is_unicode_white_space};
use super::names::{table_len, table_name_is};
use alloc::vec::Vec;

/// A .NET string as Unicode scalar values (spec: Lean `String`).
pub type Str = Vec<u32>;

/// Lean `Nat` subtraction (truncated at 0).
pub fn nat_sub(a: usize, b: usize) -> usize {
    if a >= b { a - b } else { 0 }
}

/// `char.IsWhiteSpace`; spec `isWhiteSpace`
pub fn is_white_space(c: u32) -> bool {
    is_unicode_white_space(c)
}

/// Copy of `s[lo..hi]`.
pub fn sub_str(s: &[u32], lo: usize, hi: usize) -> Str {
    let mut out: Str = Vec::new();
    let mut i = lo;
    while i < hi {
        out.push(s[i]);
        i = i + 1;
    }
    out
}

/// Bounds `[lo, hi)` of `s` with leading/trailing white space removed.
pub fn trim_bounds(s: &[u32], start: bool, end: bool) -> (usize, usize) {
    let mut lo = 0;
    if start {
        while lo < s.len() && is_white_space(s[lo]) {
            lo = lo + 1;
        }
    }
    let mut hi = s.len();
    if end {
        while hi > lo && is_white_space(s[hi - 1]) {
            hi = hi - 1;
        }
    }
    (lo, hi)
}

/// `string.TrimStart()`; spec `trimStart`
pub fn trim_start(s: &[u32]) -> Str {
    let (lo, hi) = trim_bounds(s, true, false);
    sub_str(s, lo, hi)
}

/// `string.TrimEnd()`; spec `trimEnd`
pub fn trim_end(s: &[u32]) -> Str {
    let (lo, hi) = trim_bounds(s, false, true);
    sub_str(s, lo, hi)
}

/// `string.Trim()`; spec `trim`
pub fn trim(s: &[u32]) -> Str {
    let (lo, hi) = trim_bounds(s, true, true);
    sub_str(s, lo, hi)
}

/// `string.IsNullOrWhiteSpace(s)`; spec `isNullOrWhiteSpace`
pub fn is_null_or_white_space(s: &[u32]) -> bool {
    let mut i = 0;
    let mut all = true;
    while i < s.len() {
        if !is_white_space(s[i]) {
            all = false;
        }
        i = i + 1;
    }
    all
}

/// `s.Split(c)` (keeps empty entries); spec `split`
pub fn split(s: &[u32], c: u32) -> Vec<Str> {
    let mut out: Vec<Str> = Vec::new();
    let mut cur: Str = Vec::new();
    let mut i = 0;
    while i < s.len() {
        if s[i] == c {
            out.push(cur);
            cur = Vec::new();
        } else {
            cur.push(s[i]);
        }
        i = i + 1;
    }
    out.push(cur);
    out
}

/// `LegacyDecoder.SplitKeyVal(line, sep)`: key and value (everything after the first `sep`),
/// both trimmed; spec `splitKeyVal`
pub fn split_key_val(line: &[u32], sep: u32) -> (Str, Str) {
    let mut i = 0;
    let mut found = false;
    while !found && i < line.len() {
        if line[i] == sep {
            found = true;
        } else {
            i = i + 1;
        }
    }
    if found {
        let k = sub_str(line, 0, i);
        let v = sub_str(line, i + 1, line.len());
        (trim(&k), trim(&v))
    } else {
        (trim(line), Vec::new())
    }
}

/// ordinal equality with an ASCII literal
pub fn str_eq(s: &[u32], lit: &[u8]) -> bool {
    if s.len() != lit.len() {
        false
    } else {
        let mut i = 0;
        let mut ok = true;
        while i < lit.len() {
            if s[i] != lit[i] as u32 {
                ok = false;
            }
            i = i + 1;
        }
        ok
    }
}

/// ordinal equality of two strings
pub fn str_eq2(a: &[u32], b: &[u32]) -> bool {
    if a.len() != b.len() {
        false
    } else {
        let mut i = 0;
        let mut ok = true;
        while i < a.len() {
            if a[i] != b[i] {
                ok = false;
            }
            i = i + 1;
        }
        ok
    }
}

/// `string.StartsWith(prefix)` (ordinal, ASCII literal); spec `startsWith`
pub fn starts_with(s: &[u32], lit: &[u8]) -> bool {
    if s.len() < lit.len() {
        false
    } else {
        let mut i = 0;
        let mut ok = true;
        while i < lit.len() {
            if s[i] != lit[i] as u32 {
                ok = false;
            }
            i = i + 1;
        }
        ok
    }
}

/// `string.EndsWith` (ordinal, ASCII literal)
pub fn ends_with(s: &[u32], lit: &[u8]) -> bool {
    if s.len() < lit.len() {
        false
    } else {
        let off = s.len() - lit.len();
        let mut i = 0;
        let mut ok = true;
        while i < lit.len() {
            if s[off + i] != lit[i] as u32 {
                ok = false;
            }
            i = i + 1;
        }
        ok
    }
}

/// An ASCII literal as a string.
pub fn lit_str(lit: &[u8]) -> Str {
    let mut out: Str = Vec::new();
    let mut i = 0;
    while i < lit.len() {
        out.push(lit[i] as u32);
        i = i + 1;
    }
    out
}

/// `double.CompareTo(double)` (NaN smallest, `-0 = +0`); spec `compareF64`
pub fn compare_f64(a: F64, b: F64) -> i32 {
    if a.lt(b) {
        -1
    } else if b.lt(a) {
        1
    } else if a.eq(b) {
        0
    } else if a.is_nan() {
        if b.is_nan() { 0 } else { -1 }
    } else {
        1
    }
}

const F64_ONE: F64 = F64::from_bits(0x3FF0_0000_0000_0000);
const F64_ZERO: F64 = F64::from_bits(0);

/// C# `x % 1.0`; spec `fmod1`
pub fn fmod1(x: F64) -> F64 {
    if x.is_nan() || f64_is_inf(x) {
        F64_NAN
    } else if x.abs().lt(F64_ONE) {
        x
    } else {
        let r = x.sub(x.trunc());
        if r.eq(F64_ZERO) { f64_copy_sign(F64_ZERO, x) } else { r }
    }
}

/// C# `a % b` on doubles = IEEE `fmod` (exact); spec `fmodF64` (trusted primitive `F64::fmod`)
pub fn fmod_f64(a: F64, b: F64) -> F64 {
    a.fmod(b)
}

/// C# `a % b` on floats; spec `fmodF32`
pub fn fmod_f32(a: F32, b: F32) -> F32 {
    fmod_f64(a.to_f64(), b.to_f64()).to_f32()
}

/// `List<double>.BinarySearch(value)`; spec `binarySearchF64`
pub fn binary_search_f64(a: &[F64], v: F64) -> i64 {
    let mut lo: i64 = 0;
    let mut hi: i64 = (a.len() as i64) - 1;
    let mut res: Option<i64> = None;
    let mut it: usize = 0;
    while res.is_none() && it < a.len() + 1 {
        if lo <= hi {
            let i = lo + (hi - lo) / 2;
            let c = compare_f64(a[i as usize], v);
            if c == 0 {
                res = Some(i);
            } else if c < 0 {
                lo = i + 1;
            } else {
                hi = i - 1;
            }
        }
        it = it + 1;
    }
    match res {
        Some(i) => i,
        None => -lo - 1,
    }
}

// ------------------------------------------------------------------ IntroSort (`List<T>.Sort`)

/// The comparison of `List<T>.Sort(Comparison<T>)` (spec: the `cmp` argument).
pub trait SortCmp {
    fn cmp3(&self, other: &Self) -> i32;
}

/// spec `IntroSort.swap`
pub fn swap<T: Clone>(a: &mut Vec<T>, i: usize, j: usize) {
    let t = a[i].clone();
    let aj = a[j].clone();
    a[i] = aj;
    a[j] = t;
}

/// spec `IntroSort.swapIfGreater`
pub fn swap_if_greater<T: Clone + SortCmp>(a: &mut Vec<T>, i: usize, j: usize) {
    if a[i].cmp3(&a[j]) > 0 {
        swap(a, i, j);
    }
}

/// spec `IntroSort.insertionSort`
pub fn insertion_sort<T: Clone + SortCmp>(a: &mut Vec<T>, lo: usize, len: usize) {
    let mut i = 0;
    while i < nat_sub(len, 1) {
        let t = a[lo + i + 1].clone();
        let mut j: i64 = i as i64;
        let mut go = true;
        let mut k = 0;
        while k < i + 1 {
            if go {
                if j >= 0 && t.cmp3(&a[lo + (j as usize)]) < 0 {
                    let v = a[lo + (j as usize)].clone();
                    a[lo + (j as usize) + 1] = v;
                    j = j - 1;
                } else {
                    go = false;
                }
            }
            k = k + 1;
        }
        a[lo + ((j + 1) as usize)] = t;
        i = i + 1;
    }
}

/// spec `IntroSort.downHeap`
pub fn down_heap<T: Clone + SortCmp>(a: &mut Vec<T>, lo: usize, i0: usize, n: usize) {
    let d = a[lo + i0 - 1].clone();
    let mut i = i0;
    let mut go = true;
    let mut k = 0;
    while k < n + 1 {
        if go && i <= n / 2 {
            let mut child = 2 * i;
            if child < n && a[lo + child - 1].cmp3(&a[lo + child]) < 0 {
                child = child + 1;
            }
            if !(d.cmp3(&a[lo + child - 1]) < 0) {
                go = false;
            } else {
                let v = a[lo + child - 1].clone();
                a[lo + i - 1] = v;
                i = child;
            }
        }
        k = k + 1;
    }
    a[lo + i - 1] = d;
}

/// spec `IntroSort.heapSort`
pub fn heap_sort<T: Clone + SortCmp>(a: &mut Vec<T>, lo: usize, n: usize) {
    let mut i = n / 2;
    let mut k0 = 0;
    while k0 < n / 2 {
        down_heap(a, lo, i, n);
        i = nat_sub(i, 1);
        k0 = k0 + 1;
    }
    let mut k = n;
    let mut k1 = 0;
    while k1 < nat_sub(n, 1) {
        swap(a, lo, lo + k - 1);
        down_heap(a, lo, 1, k - 1);
        k = k - 1;
        k1 = k1 + 1;
    }
}

/// spec `IntroSort.pickPivotAndPartition`: returns the pivot position (relative to `lo`).
pub fn pick_pivot_and_partition<T: Clone + SortCmp>(a: &mut Vec<T>, lo: usize, len: usize) -> usize {
    let hi = nat_sub(len, 1);
    let middle = hi / 2;
    swap_if_greater(a, lo, lo + middle);
    swap_if_greater(a, lo, lo + hi);
    swap_if_greater(a, lo + middle, lo + hi);
    let pivot = a[lo + middle].clone();
    swap(a, lo + middle, nat_sub(lo + hi, 1));
    let mut left: usize = 0;
    let mut right: usize = nat_sub(hi, 1);
    let mut k = 0;
    while k < len + 1 {
        if left < right {
            left = left + 1;
            let mut go = true;
            let mut k2 = 0;
            while k2 < len {
                if go {
                    if a[lo + left].cmp3(&pivot) < 0 {
                        left = left + 1;
                    } else {
                        go = false;
                    }
                }
                k2 = k2 + 1;
            }
            right = nat_sub(right, 1);
            go = true;
            let mut k3 = 0;
            while k3 < len {
                if go {
                    if pivot.cmp3(&a[lo + right]) < 0 {
                        right = nat_sub(right, 1);
                    } else {
                        go = false;
                    }
                }
                k3 = k3 + 1;
            }
            if left < right {
                swap(a, lo + left, lo + right);
            }
        }
        k = k + 1;
    }
    if left != nat_sub(hi, 1) {
        swap(a, lo + left, nat_sub(lo + hi, 1));
    }
    left
}

/// `IntroSort(keys[lo..lo+len), depthLimit)` with recursion fuel; spec `IntroSort.introSort`
pub fn intro_sort<T: Clone + SortCmp>(a: &mut Vec<T>, lo: usize, len: usize, depth_limit: usize, fuel: usize) {
    if fuel == 0 {
        return;
    }
    intro_sort_iter(a, lo, len, depth_limit, len + 1, fuel);
}

/// The `while partitionSize > 1` loop of spec `IntroSort.introSort`, as recursion (`steps` =
/// remaining iterations of the spec's bounded loop). A Rust `while` here would put the recursive
/// `intro_sort` call inside an Aeneas `loop`, which Lean cannot prove monotone. Iterations after
/// the loop finished (or once `partition_size <= 1`) change nothing, so they are skipped.
/// Recursion depth <= depth_limit + 1 (each continuing iteration decrements `depth`).
pub fn intro_sort_iter<T: Clone + SortCmp>(a: &mut Vec<T>, lo: usize, partition_size: usize, depth: usize, steps: usize,
                                           fuel: usize) {
    if steps == 0 || partition_size <= 1 {
        return;
    }
    if partition_size <= 16 {
        if partition_size == 2 {
            swap_if_greater(a, lo, lo + 1);
        } else if partition_size == 3 {
            swap_if_greater(a, lo, lo + 1);
            swap_if_greater(a, lo, lo + 2);
            swap_if_greater(a, lo + 1, lo + 2);
        } else {
            insertion_sort(a, lo, partition_size);
        }
    } else if depth == 0 {
        heap_sort(a, lo, partition_size);
    } else {
        let p = pick_pivot_and_partition(a, lo, partition_size);
        intro_sort(a, lo + p + 1, nat_sub(partition_size, p + 1), depth - 1, fuel - 1);
        intro_sort_iter(a, lo, p, depth - 1, steps - 1, fuel);
    }
}

/// `BitOperations.Log2(n)` = `Nat.log2 n` (`n >= 1`); spec `IntroSort.log2`
pub fn log2(n: usize) -> usize {
    let mut r = 0;
    let mut m = n;
    while m > 1 {
        m = m / 2;
        r = r + 1;
    }
    r
}

/// `List<T>.Sort(Comparison<T>)` (introspective sort, unstable); spec `listSort`
pub fn list_sort<T: Clone + SortCmp>(a: &mut Vec<T>) {
    if a.len() > 1 {
        let n = a.len();
        intro_sort(a, 0, n, 2 * (log2(n) + 1), n + 1);
    }
}

// ------------------------------------------------------------------ stable sort (LINQ `OrderBy`)

/// The key of `stableSortBy` (compared with `double.CompareTo`).
pub trait SortKey {
    fn sort_key(&self) -> F64;
}

/// merge of two sorted runs `a[lo..mid)`, `a[mid..hi)` (spec `stableSortBy.merge`: the right
/// element is taken only when strictly smaller)
pub fn merge_runs<T: Clone + SortKey>(a: &Vec<T>, lo: usize, mid: usize, hi: usize, out: &mut Vec<T>) {
    let mut i = lo;
    let mut j = mid;
    while i < mid || j < hi {
        if i < mid && j < hi {
            if compare_f64(a[j].sort_key(), a[i].sort_key()) < 0 {
                out.push(a[j].clone());
                j = j + 1;
            } else {
                out.push(a[i].clone());
                i = i + 1;
            }
        } else if i < mid {
            out.push(a[i].clone());
            i = i + 1;
        } else {
            out.push(a[j].clone());
            j = j + 1;
        }
    }
}

/// top-down merge sort of `a[lo..hi)` (split at `len / 2`, as spec `stableSortBy.sort`)
pub fn merge_sort_range<T: Clone + SortKey>(a: &mut Vec<T>, lo: usize, hi: usize) {
    let n = hi - lo;
    if n > 1 {
        let mid = lo + n / 2;
        merge_sort_range(a, lo, mid);
        merge_sort_range(a, mid, hi);
        let mut out: Vec<T> = Vec::with_capacity(n);
        merge_runs(a, lo, mid, hi, &mut out);
        let mut k = 0;
        while k < n {
            a[lo + k] = out[k].clone();
            k = k + 1;
        }
    }
}

/// Stable sort by key (LINQ `OrderBy`, `double.CompareTo`); spec `stableSortBy`
pub fn stable_sort_by<T: Clone + SortKey>(a: &mut Vec<T>) {
    let n = a.len();
    merge_sort_range(a, 0, n);
}

impl SortKey for F64 {
    fn sort_key(&self) -> F64 {
        *self
    }
}

// ------------------------------------------------------------------ Enum.TryParse

/// `Enum.TryParse<TEnum>(s)` for an int-backed enum (`names`: a `beatmap::names` table) whose member `i` has value `i`;
/// spec `enumTryParse` (whose name tables are all of that shape).
pub fn enum_try_parse(names: u32, s: &[u32]) -> Option<i32> {
    let t = trim_start(s);
    if t.len() == 0 {
        None
    } else if is_digit(t[0]) || t[0] == 0x2B || t[0] == 0x2D {
        match int_parse(&t) {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    } else {
        let parts = split(&t, 0x2C);
        let mut acc: Option<i32> = Some(0);
        let mut i = 0;
        while i < parts.len() {
            match acc {
                None => {}
                Some(v) => {
                    let p = trim(&parts[i]);
                    let mut found: Option<i32> = None;
                    let mut k = 0;
                    while found.is_none() && k < table_len(names) {
                        if table_name_is(names, k, &p) {
                            found = Some(k as i32);
                        }
                        k = k + 1;
                    }
                    acc = match found {
                        Some(x) => Some(v | x),
                        None => None,
                    };
                }
            }
            i = i + 1;
        }
        acc
    }
}

/// `List<T>.Insert(k, x)` (spec: `Array.insertIdx!`), written with `push` + shifts.
pub fn insert_at<T: Clone>(v: &mut Vec<T>, k: usize, x: T) {
    v.push(x.clone());
    let mut i = v.len() - 1;
    while i > k {
        let prev = v[i - 1].clone();
        v[i] = prev;
        i = i - 1;
    }
    v[k] = x;
}
