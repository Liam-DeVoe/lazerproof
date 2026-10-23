/-
Differential checker: reads `osu_eval_bench gen` lines (inputs + Rust results, floats as hex bits)
and recomputes them with the compiled Lean *spec* (OsuModel only; no Aeneas/Mathlib here).
NaNs compare equal to any NaN (the model has a single NaN, docs/net-float.md).
-/
import OsuModel.Beatmap.Objects
import OsuModel.Beatmap.SliderPath
import OsuModel.Sim.Schedule

open OsuModel.Net OsuModel

def hexNat (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def f64 (s : String) : F64 := Float.ofBits (UInt64.ofNat (hexNat s))
def f32 (s : String) : F32 := Float32.ofBits (UInt32.ofNat (hexNat s))
def same64 (a b : F64) : Bool := (a.isNaN && b.isNaN) || a.toBits == b.toBits

def hrCode : Sim.HitResult → Nat
  | .none => 0 | .miss => 1 | .meh => 2 | .ok => 3 | .great => 4 | _ => 99

/-- returns true if the Rust results equal the spec results -/
def check (ws : Array String) : Bool := Id.run do
  match ws[0]! with
  | "hw" =>
    let od := f64 ws[1]!; let t := f64 ws[2]!
    match Beatmap.osuHitWindows od with
    | .osu g o m =>
      let hw : Sim.HitWindows := { great := g, ok := o, meh := m, miss := Beatmap.MISS_WINDOW }
      return same64 g (f64 ws[3]!) && same64 o (f64 ws[4]!) && same64 m (f64 ws[5]!)
        && same64 hw.miss (f64 ws[6]!) && hrCode (hw.resultFor t) == ws[7]!.toNat!
    | .empty => return false
  | "dr" =>
    return same64 (Beatmap.difficultyRange (f64 ws[1]!) (f64 ws[2]!) (f64 ws[3]!) (f64 ws[4]!)) (f64 ws[5]!)
  | "cum" =>
    let n := ws[1]!.toNat!
    let path : Array Beatmap.Vec2 := (Array.range n).map fun i => ⟨f32 ws[2 + 2*i]!, f32 ws[3 + 2*i]!⟩
    let opt := f64 ws[2 + 2*n]!
    let sp : Beatmap.SliderPathSpec := { controlPoints := #[], expectedDistance := none, optimiseCatmull := false }
    let r := Beatmap.SliderPath.calculateLength sp path opt
    let m := ws[3 + 2*n]!.toNat!
    if m != r.cumulativeLength.size then return false
    let mut ok := true
    for i in [0:m] do
      ok := ok && same64 r.cumulativeLength[i]! (f64 ws[4 + 2*n + i]!)
    return ok && same64 r.calculatedLength (f64 ws[4 + 2*n + m]!)
  | "sim" =>
    let nr := ws[1]!.toNat!
    let refs := (Array.range nr).map fun i => f64 ws[2 + i]!
    let nf := ws[2 + nr]!.toNat!
    let frames := (Array.range nf).map fun i => f64 ws[3 + nr + i]!
    let gst := f64 ws[3 + nr + nf]!
    let steps := Sim.simulateSteps refs frames gst
    let k := 4 + nr + nf
    let ns := ws[k]!.toNat!
    if ns != steps.size then return false
    let mut ok := true
    for i in [0:ns] do
      ok := ok && same64 steps[i]!.time (f64 ws[k + 1 + 2*i]!) && steps[i]!.frameIndex == ws[k + 2 + 2*i]!.toInt!
    return ok
  | _ => return false

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut n := 0
  let mut fails := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let ws := ((line.replace "\n" "").splitOn " ").toArray
    n := n + 1
    if !check ws then
      fails := fails + 1
      if fails ≤ 10 then IO.eprintln s!"MISMATCH: {(line.replace "\n" "").take 300}"
  IO.println s!"pocspec: {n} cases, {fails} mismatches"
  return if fails == 0 then 0 else 1
