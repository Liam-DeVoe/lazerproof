//! Differential-test generator and micro-benchmark for `osu_eval_core` (not translated by Charon).
//!
//! `osu_eval_bench gen <count> <seed>`: prints test cases with the Rust results, one per line,
//! all floats as hex bits; `proofs/.lake/build/bin/pocspec` recomputes them with the Lean spec.
//! `osu_eval_bench bench`: timing of the ported functions.
use osu_eval_core::float::{F32, F64};
use osu_eval_core::hit_windows::{self, HitResult};
use osu_eval_core::schedule::{self, Step};
use osu_eval_core::slider::{self, Vec2};
use std::fmt::Write as _;
use std::io::Write as _;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
    /// interesting doubles: specials, small integers/halves, human ranges, raw bits
    fn f64(&mut self, scale: f64) -> f64 {
        match self.below(16) {
            0 => [0.0, -0.0, f64::INFINITY, f64::NEG_INFINITY, f64::NAN, 5.0, 10.0, -5.0][self.below(8) as usize],
            1 => f64::from_bits(self.next()),
            2 => (self.below(41) as f64) * 0.25 - 0.0,
            3 => (self.below(200) as f64) - 100.0,
            4 => f64::from_bits((5.0f64).to_bits().wrapping_add(self.below(5)).wrapping_sub(2)),
            _ => (self.unit() * 2.0 - 1.0) * scale,
        }
    }
    fn f32(&mut self, scale: f32) -> f32 {
        match self.below(16) {
            0 => [0.0, -0.0, f32::INFINITY, f32::NEG_INFINITY, f32::NAN, 1.0][self.below(6) as usize],
            1 => f32::from_bits(self.next() as u32),
            2 => (self.below(64) as f32) - 32.0,
            _ => ((self.unit() * 2.0 - 1.0) as f32) * scale,
        }
    }
}

fn h64(s: &mut String, x: F64) {
    write!(s, " {:x}", x.to_bits()).unwrap();
}
fn h32(s: &mut String, x: F32) {
    write!(s, " {:x}", x.to_bits()).unwrap();
}
fn hr(r: HitResult) -> u8 {
    match r {
        HitResult::None => 0,
        HitResult::Miss => 1,
        HitResult::Meh => 2,
        HitResult::Ok => 3,
        HitResult::Great => 4,
    }
}

fn gen(count: usize, seed: u64) {
    let mut rng = Rng(seed);
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());
    for k in 0..count {
        let mut s = String::new();
        match k % 4 {
            0 => {
                // difficulty_range + osu_hit_windows + result_for
                let od = F64::of_native(if rng.below(2) == 0 { rng.below(111) as f64 / 10.0 } else { rng.f64(20.0) });
                let t = F64::of_native(rng.f64(500.0));
                let hw = hit_windows::osu_hit_windows(od);
                let r = hit_windows::result_for(&hw, t);
                s.push_str("hw");
                h64(&mut s, od);
                h64(&mut s, t);
                h64(&mut s, hw.great);
                h64(&mut s, hw.ok_);
                h64(&mut s, hw.meh);
                h64(&mut s, hw.miss);
                write!(s, " {}", hr(r)).unwrap();
            }
            1 => {
                let a = [rng.f64(20.0), rng.f64(300.0), rng.f64(300.0), rng.f64(300.0)].map(F64::of_native);
                let r = hit_windows::difficulty_range(a[0], a[1], a[2], a[3]);
                s.push_str("dr");
                for x in a {
                    h64(&mut s, x);
                }
                h64(&mut s, r);
            }
            2 => {
                let n = rng.below(12) as usize;
                let mut path = Vec::with_capacity(n);
                for _ in 0..n {
                    path.push(Vec2 { x: F32::of_native(rng.f32(512.0)), y: F32::of_native(rng.f32(384.0)) });
                }
                let opt = F64::of_native(if rng.below(3) == 0 { rng.f64(100.0) } else { 0.0 });
                let (cum, calc) = slider::cumulative_lengths(&path, opt);
                write!(s, "cum {}", n).unwrap();
                for p in &path {
                    h32(&mut s, p.x);
                    h32(&mut s, p.y);
                }
                h64(&mut s, opt);
                write!(s, " {}", cum.len()).unwrap();
                for c in &cum {
                    h64(&mut s, *c);
                }
                h64(&mut s, calc);
            }
            _ => {
                // step schedule: sorted-ish replay frame times, catchup/perframe-like references
                let nf = rng.below(30) as usize;
                let mut t = rng.unit() * 3000.0 - 2500.0;
                let mut frames = Vec::with_capacity(nf);
                for _ in 0..nf {
                    t += match rng.below(8) {
                        0 => 0.0,
                        1 => -(rng.below(30) as f64), // out-of-order frames
                        2 => rng.unit() * 400.0,
                        3 => (rng.below(4) as f64) * (1000.0 / 60.0),
                        _ => rng.unit() * 20.0,
                    };
                    frames.push(if rng.below(200) == 0 { rng.unit() * 2e4 - 1e4 } else { t });
                }
                let gst = rng.unit() * -3000.0;
                let r0 = gst.min(0.0);
                let mut refs = vec![r0];
                if rng.below(2) == 0 {
                    refs.push(r0.max(t + rng.unit() * 2000.0));
                } else {
                    for f in &frames {
                        if *refs.last().unwrap() < *f {
                            refs.push(*f);
                        }
                    }
                    refs.push(t + 1000.0);
                }
                if rng.below(50) == 0 {
                    // finite only: a NaN/inf reference makes both spec and impl run the full 10^8-step fuel
                    refs.push(rng.unit() * 2e4 - 1e4);
                }
                let refs: Vec<F64> = refs.into_iter().map(F64::of_native).collect();
                let frames: Vec<F64> = frames.into_iter().map(F64::of_native).collect();
                let gst = F64::of_native(gst);
                let steps: Vec<Step> = schedule::simulate_steps(&refs, &frames, gst);
                write!(s, "sim {}", refs.len()).unwrap();
                for r in &refs {
                    h64(&mut s, *r);
                }
                write!(s, " {}", frames.len()).unwrap();
                for f in &frames {
                    h64(&mut s, *f);
                }
                h64(&mut s, gst);
                write!(s, " {}", steps.len()).unwrap();
                for st in &steps {
                    h64(&mut s, st.time);
                    write!(s, " {}", st.frame_index).unwrap();
                }
            }
        }
        writeln!(out, "{}", s).unwrap();
    }
}

fn bench() {
    let mut rng = Rng(1);
    // 1M result_for
    let hws: Vec<_> = (0..16).map(|i| hit_windows::osu_hit_windows(F64::of_native(i as f64 * 0.7))).collect();
    let offs: Vec<F64> = (0..1_000_000).map(|_| F64::of_native(rng.unit() * 400.0 - 200.0)).collect();
    let t0 = std::time::Instant::now();
    let mut acc = 0u64;
    for (i, o) in offs.iter().enumerate() {
        acc += hr(hit_windows::result_for(&hws[i & 15], *o)) as u64;
    }
    let d = t0.elapsed();
    println!("result_for: 1M calls in {:?} ({:.2} ns/call) [acc {}]", d, d.as_nanos() as f64 / 1e6, acc);
    // 10M-point path length
    let path: Vec<Vec2> = (0..10_000_000)
        .map(|_| Vec2 { x: F32::of_native(rng.unit() as f32 * 512.0), y: F32::of_native(rng.unit() as f32 * 384.0) })
        .collect();
    let t0 = std::time::Instant::now();
    let (cum, calc) = slider::cumulative_lengths(&path, F64::of_native(0.0));
    let d = t0.elapsed();
    println!("cumulative_lengths: 10M points in {:?} ({:.2} ns/pt) [{} {}]", d, d.as_nanos() as f64 / 1e7, cum.len(), calc.native());
    // native f32/f64 reference loop (same arithmetic)
    let t0 = std::time::Instant::now();
    let mut c = 0.0f64;
    let mut v = Vec::with_capacity(path.len());
    v.push(0.0f64);
    for w in path.windows(2) {
        let dx = w[1].x.native() - w[0].x.native();
        let dy = w[1].y.native() - w[0].y.native();
        c += (((dx * dx + dy * dy) as f64).sqrt() as f32) as f64;
        v.push(c);
    }
    let d = t0.elapsed();
    println!("native reference loop: 10M points in {:?} ({:.2} ns/pt) [{}]", d, d.as_nanos() as f64 / 1e7, c);
    // schedule: 100k frames, perframe refs
    let mut t = 0.0;
    let frames: Vec<F64> = (0..100_000)
        .map(|_| {
            t += rng.unit() * 20.0;
            F64::of_native(t)
        })
        .collect();
    let mut refs = vec![F64::of_native(-2000.0)];
    refs.extend(frames.iter().copied());
    let t0 = std::time::Instant::now();
    let steps = schedule::simulate_steps(&refs, &frames, F64::of_native(-1500.0));
    let d = t0.elapsed();
    println!("simulate_steps: {} refs -> {} steps in {:?} ({:.2} ns/step)", refs.len(), steps.len(), d, d.as_nanos() as f64 / steps.len() as f64);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("gen") => gen(args[2].parse().unwrap(), args[3].parse().unwrap()),
        Some("bench") => bench(),
        _ => {
            eprintln!("usage: osu_eval_bench gen <count> <seed> | bench");
            std::process::exit(2)
        }
    }
    let _ = std::io::stdout().flush();
}
