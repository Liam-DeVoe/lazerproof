//! Build script: compiles the vendored C sources (D86) when they are used, and nothing otherwise.
//!
//! * `vendor/glibc-libm/*`: the glibc 2.39 sources of the 23 libm functions `float.rs` calls, rewritten so that every
//!   multiply-add glibc's x86-64 FMA build contracts is an explicit `__builtin_fma` and compiled with
//!   `-ffp-contract=off`, so GCC and clang on x86-64 and aarch64 produce the same bits as the
//!   `glibc 2.39 x86-64 libm.so.6` of the trusted float row (docs/proof-pipeline.md §4/§5).
//! * `vendor/xz`: the liblzma 5.4.5 decoder subset `lzma.rs` calls (integer code, platform-independent).
//!
//! Used when the target OS is not Linux (no glibc `libm.so.6` / `liblzma.so.5` to dlopen), or on Linux with the
//! cargo features `vendored-libm` / `vendored-lzma`. A plain Linux build (and Charon/Aeneas) compiles no C at all.
//!
//! No `cc` crate (the workspace has no crates.io dependencies): the C compiler is `$CC_<target>`, `$CC`, or `cc`
//! (Xcode command-line tools on macOS), the archiver `$AR_<target>`, `$AR`, or `ar`. The compile flags are pinned
//! below and do not depend on the cargo profile.
//!
//! Each vendor directory has `SOURCES.txt`: one `.c` file per line (relative to the directory); lines starting with
//! `-I` (path relative to the directory) or `-D` are extra flags for that directory; `#` starts a comment.
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Pinned C flags (D86). `-ffp-contract=off`: no implicit FMA contraction (GCC's default in GNU C mode is `fast`,
/// clang's is `on`; the FMAs of glibc's x86-64 `-mfma` build are explicit `__builtin_fma` calls in the vendored
/// sources). `-fno-fast-math` is the default but stated. No `-march`: the code must not depend on the CPU.
const CFLAGS: &[&str] = &[
    "-O2",
    "-std=gnu11",
    "-ffp-contract=off",
    "-fno-fast-math",
    "-fno-builtin",
    "-fno-strict-aliasing",
    "-fvisibility=hidden",
    "-w",
];

const LIBM_DIRS: &[&str] = &["glibc-libm/dbl-trig", "glibc-libm/dbl-invtrig", "glibc-libm/dbl-explog", "glibc-libm/flt"];
const LZMA_DIRS: &[&str] = &["xz"];

fn tool(var: &str, target: &str, default: &str) -> String {
    let t = target.replace('-', "_");
    for k in [format!("{}_{}", var, target), format!("{}_{}", var, t), var.to_string()] {
        println!("cargo:rerun-if-env-changed={}", k);
        if let Ok(v) = env::var(&k) {
            if !v.trim().is_empty() {
                return v;
            }
        }
    }
    default.to_string()
}

fn build_lib(name: &str, dirs: &[&str], vendor: &Path, out: &Path, cc: &str, ar: &str, target: &str) {
    let objdir = out.join(format!("obj-{}", name));
    fs::create_dir_all(&objdir).unwrap();
    let common = vendor.join("glibc-libm").join("common");
    let mut objs: Vec<PathBuf> = Vec::new();
    for d in dirs {
        let dir = vendor.join(d);
        let list = dir.join("SOURCES.txt");
        println!("cargo:rerun-if-changed={}", dir.display());
        let text = fs::read_to_string(&list).unwrap_or_else(|e| {
            panic!("vendored build: cannot read {} ({}); the vendor tree is incomplete", list.display(), e)
        });
        let mut flags: Vec<String> = vec![format!("-I{}", dir.display())];
        if common.is_dir() {
            flags.push(format!("-I{}", common.display()));
        }
        let mut srcs: Vec<String> = Vec::new();
        for line in text.lines() {
            let l = line.split('#').next().unwrap().trim();
            if l.is_empty() {
                continue;
            }
            if let Some(p) = l.strip_prefix("-I") {
                flags.push(format!("-I{}", dir.join(p.trim()).display()));
            } else if l.starts_with("-D") {
                flags.push(l.to_string());
            } else {
                srcs.push(l.to_string());
            }
        }
        for s in srcs {
            let src = dir.join(&s);
            let obj = objdir.join(format!("{}__{}.o", d.replace('/', "_"), s.replace('/', "_").trim_end_matches(".c")));
            let mut cmd = Command::new(cc);
            cmd.args(CFLAGS).args(&flags);
            if !target.contains("windows") {
                cmd.arg("-fPIC");
            }
            cmd.arg("-c").arg(&src).arg("-o").arg(&obj);
            let st = cmd.status().unwrap_or_else(|e| panic!("vendored build: cannot run C compiler `{}`: {}", cc, e));
            if !st.success() {
                panic!("vendored build: `{:?}` failed", cmd);
            }
            objs.push(obj);
        }
    }
    let lib = out.join(format!("lib{}.a", name));
    let _ = fs::remove_file(&lib);
    let st = Command::new(ar).arg("crs").arg(&lib).args(&objs).status()
        .unwrap_or_else(|e| panic!("vendored build: cannot run archiver `{}`: {}", ar, e));
    if !st.success() {
        panic!("vendored build: `{} crs {}` failed", ar, lib.display());
    }
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static={}", name);
}

fn main() {
    println!("cargo::rustc-check-cfg=cfg(lp_vendored_libm)");
    println!("cargo::rustc-check-cfg=cfg(lp_vendored_lzma)");
    println!("cargo:rerun-if-changed=build.rs");
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target = env::var("TARGET").unwrap_or_default();
    let linux = target_os == "linux";
    let libm = !linux || env::var_os("CARGO_FEATURE_VENDORED_LIBM").is_some();
    let lzma = !linux || env::var_os("CARGO_FEATURE_VENDORED_LZMA").is_some();
    if !libm && !lzma {
        return;
    }
    // LP_VENDOR_DIR: another vendor tree (testing only)
    println!("cargo:rerun-if-env-changed=LP_VENDOR_DIR");
    let vendor = match env::var("LP_VENDOR_DIR") {
        Ok(v) if !v.is_empty() => PathBuf::from(v),
        _ => PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("vendor"),
    };
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let cc = tool("CC", &target, "cc");
    let ar = tool("AR", &target, "ar");
    if libm {
        build_lib("lp_libm", LIBM_DIRS, &vendor, &out, &cc, &ar, &target);
        println!("cargo:rustc-cfg=lp_vendored_libm");
    }
    if lzma {
        build_lib("lp_lzma", LZMA_DIRS, &vendor, &out, &cc, &ar, &target);
        println!("cargo:rustc-cfg=lp_vendored_lzma");
    }
}
