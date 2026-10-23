import OsuModel.Eval

/-!
# rbcheck: corpus acceptance test for RunBudgetS (audit M1; DECISIONS D67, D70)

Spec-side copy of `runBudgetOkE` / `runBudgetNeed` from proofs/OsuProofs/Sim/StepInv.lean (the proofs package
imports Aeneas, so it cannot be compiled cheaply). The four definitions between `BEGIN VERBATIM` and `END VERBATIM`
are copied textually; tools/runbudget/check_defs.py checks that they are identical to StepInv.lean.
`unitsLoop` is the same fold as `sc2UnitsRun`, written as a loop (`sc2UnitsRun` is not tail-recursive and
overflows the stack on 10^6-step schedules); `rbcheck selftest` compares the two on small inputs.

```
rbcheck bound LIST              LIST lines: BEATMAP<TAB>OSR -> per schedule: steps, objects, unj, n (cheap: mkCtx only)
rbcheck exact BM OSR SCHED [MODS_JSON]     exact U (MODS_JSON is appended like evaltest --mods)
rbcheck synth BM SCHED MODS_JSON DT        exact U for a synthetic replay: a no-button frame every DT ms from r0-1000
                                           to end+1000 at the playfield centre (mods = MODS_JSON, lazer replay)
rbcheck selftest BM OSR SCHED [MODS_JSON]  recursive sc2UnitsRun == unitsLoop
```
-/

open OsuModel.Net OsuModel.Sim OsuModel.Eval OsuModel.Replay
open OsuModel.Beatmap (ModConfig)

namespace RB

-- BEGIN VERBATIM (proofs/OsuProofs/Sim/StepInv.lean)
/-- the step prefix before the per-object updates -/
def sc2PreDho : OsuModel.Sim.SimM Unit := do
  OsuModel.Sim.Sim.processorsPhase
  OsuModel.Sim.Sim.inputPhase
  OsuModel.Sim.Sim.playfieldUpdate
  OsuModel.Sim.Sim.lifetimeUpdate

/-- updates needed by the steps `ks` from spec state `S` (the active-list size after each lifetime phase) -/
def sc2UnitsRun (C : OsuModel.Sim.Ctx) : List (Nat × OsuModel.Sim.Step) → OsuModel.Sim.St → Nat
  | [], _ => 0
  | (k, stp) :: rest, S =>
    let S1 := { S with k := k, t := stp.time }
    match sc2PreDho C S1 with
    | .error _ => 0
    | .ok (_, SL) => SL.active.size +
      match OsuModel.Sim.Sim.stepOnce C S1 with
      | .ok (_, S2) => sc2UnitsRun C rest S2
      | .error _ => 0

/-- the number of per-object updates of the whole spec run from `S0` -/
def runBudgetNeed (C : OsuModel.Sim.Ctx) (S0 : OsuModel.Sim.St) : Nat :=
  sc2UnitsRun C ((List.range C.steps.size).zip C.steps.toList) S0

/-- spec-side custom-state cost of the visibility mods (= `s3b_csCostFrom vis_mods 0` under `abs`) -/
def sc2VmCostS : OsuModel.Sim.VisMod → Nat
  | .classicEarlyFade => 1 | .scaleTween _ => 2 | .spinIn => 5 | .targetPractice => 2 | .hidden _ => 1
  | .transform => 2 | .wiggle _ => 2 ^ 31 + 2 ^ 25 | .inert => 0

def sc2CsCostS (cfg : OsuModel.Sim.Config) : Nat := (cfg.visMods.toList.map sc2VmCostS).sum
-- END VERBATIM

/-- `sc2UnitsRun C ((List.range C.steps.size).zip C.steps.toList) S0` as a loop; also the max active size,
the number of steps actually run and whether the run stopped on a rejection -/
def unitsLoop (C : Ctx) (S0 : St) : Nat × Nat × Nat × Bool := Id.run do
  let mut S := S0
  let mut acc := 0
  let mut mx := 0
  for k in [0:C.steps.size] do
    let stp := C.steps[k]!
    let S1 := { S with k := k, t := stp.time }
    match sc2PreDho C S1 with
    | .error _ => return (acc, mx, k, true)
    | .ok (_, SL) =>
      acc := acc + SL.active.size
      mx := max mx SL.active.size
      match Sim.stepOnce C S1 with
      | .ok (_, S2) => S := S2
      | .error _ => return (acc, mx, k + 1, true)
  return (acc, mx, C.steps.size, false)

/-- the rest of `Sim.stepOnce` after its first four phases (= `sc2PreDho`) -/
def updatesPart : SimM Unit := do
  for i in ← Sim.updateOrder do
    if (← Sim.ostate i).life == .alive then Sim.updateDho i

/-- `unitsLoop` in one pass: `stepOnce C S1` is computed as `updatesPart C SL` from `sc2PreDho`'s result SL
(`stepOnce` = the four phases of `sc2PreDho`, then `updatesPart`); half the cost. `rbcheck exact2` compares the
two loops (U and the final state's judgement count) on an input. -/
def unitsLoop1 (C : Ctx) (S0 : St) : Nat × Nat × Nat × Bool × St := Id.run do
  let mut S := S0
  let mut acc := 0
  let mut mx := 0
  for k in [0:C.steps.size] do
    let stp := C.steps[k]!
    let S1 := { S with k := k, t := stp.time }
    match sc2PreDho C S1 with
    | .error _ => return (acc, mx, k, true, S)
    | .ok (_, SL) =>
      acc := acc + SL.active.size
      mx := max mx SL.active.size
      match updatesPart C SL with
      | .ok (_, S2) => S := S2
      | .error _ => return (acc, mx, k + 1, true, S)
  return (acc, mx, C.steps.size, false, S)

def unj (pb : Playable) : Nat := (pb.objects.toList.map (fun o => o.nested.size + 1)).sum

/-- the `RunBudgetS` / `runBudgetOkE` inequality for a given U -/
def budgetOk (U n objs unj : Nat) : Bool :=
  decide ((2 * U + unj + 1) * (n + n + 4) + objs * (4 * n + 8) + 1 < 2 ^ 64 - 1 ∧ (U + 1) * 2000000 ≤ 2 ^ 54)

def hasWG (cfg : Config) : Bool := cfg.visMods.any fun v => match v with | .wiggle _ => true | _ => false

def jstr (s : String) : String := Lean.Json.compress (Lean.Json.str s)

/-- `evaluate` up to the simulation inputs (decode, ResolveMods, playable, frames, Config) -/
def lift {α ε} [ToString ε] : Except ε α → Except String α
  | .ok v => .ok v | .error e => .error (toString e)

def inputs (bm osr : ByteArray) (ov : Option (List ModConfig)) :
    Except String (Config × Playable × Array Frame × List ModConfig) := do
  let d ← lift (OsuModel.Beatmap.LegacyBeatmapDecoder.decode bm)
  if d.rulesetId != 0 then throw "non-osu ruleset"
  let sc ← lift (Osr.decode osr)
  let mods ← match resolveMods sc.mods { modsOverride := ov } with
    | .ok m => pure m | .error e => throw s!"{e.stage}: {e.reason}"
  if let some m := mods.find? unseededRandom then throw s!"{m.acronym} without a seed"
  let pb ← lift (playableOf d mods)
  let spb := toSimPlayable pb
  let frames ← match sc.frameText with
    | some t => lift (OsuModel.Replay.decode t spb.beatmapVersion)
    | none => pure #[]
  let cfg := { Config.ofMods mods spb with lazerReplay := !sc.isLegacyScore }
  return (cfg, spb, frames, mods)

def acr (ms : List ModConfig) : String := "[" ++ ",".intercalate (ms.map (jstr ·.acronym)) ++ "]"

def exactJson (env : Env) (cfg : Config) (pb : Playable) (frames : Array Frame) (k : ScheduleKind) (fast : Bool := false) :
    Except String String := do
  let C ← mkCtx env cfg pb frames k
  let S0 ← initState cfg pb
  let (U, mx, ran, rej) := if fast then (let (a, b, c, d, _) := unitsLoop1 C S0; (a, b, c, d)) else unitsLoop C S0
  let n := sc2CsCostS C.cfg
  let objs := C.pb.objects.size
  let u := unj C.pb
  let lhs := (2 * U + u + 1) * (n + n + 4) + objs * (4 * n + 8) + 1
  return s!"\"steps\":{C.steps.size},\"ran\":{ran},\"stopped_on_rejection\":{rej},\"objects\":{objs},\"unj\":{u},\"n\":{n}," ++
    s!"\"wg\":{hasWG cfg},\"frames\":{frames.size},\"U\":{U},\"max_active\":{mx},\"lhs64\":{lhs},\"lhs54\":{(U + 1) * 2000000}," ++
    s!"\"ok\":{budgetOk U n objs u},\"one_pass\":{fast}"

def schedOf (s : String) : IO ScheduleKind := match ScheduleKind.ofString? s with
  | some k => pure k | none => throw (IO.userError s!"unknown schedule {s}")

def parseOv (a : Option String) : IO (Option (List ModConfig)) := match a with
  | none => pure none
  | some m => match SimJson.parseMods m with
    | .ok ms => pure (some ms) | .error e => throw (IO.userError s!"mods JSON: {e}")

end RB

open RB in
def main (args : List String) : IO UInt32 := do
  let env := defaultEnv
  match args with
  | ["bound", list] =>
    let out ← IO.getStdout
    for line in (← IO.FS.readFile list).splitOn "\n" do
      let line := line.trimAscii.toString
      if line.isEmpty then continue
      let ps := line.splitOn "\t"
      if ps.length < 2 then continue
      let bmP := ps[0]!; let osrP := ps[1]!
      let hd := s!"\{\"beatmap\":{jstr bmP},\"replay\":{jstr osrP}"
      let r ← (do
        let bm ← IO.FS.readBinFile bmP
        let osr ← IO.FS.readBinFile osrP
        pure (inputs bm osr none) : IO _)
      match r with
      | .error e => out.putStrLn s!"{hd},\"error\":{jstr e}}"
      | .ok (cfg, pb, frames, mods) =>
        let objs := pb.objects.size
        let n := sc2CsCostS cfg
        let mut parts : Array String := #[]
        for k in [ScheduleKind.catchup, .perframe, .dense1ms] do
          match mkCtx env cfg pb frames k with
          | .ok C => parts := parts.push s!"{jstr (Schedule.kind k).name}:{C.steps.size}"
          | .error e => parts := parts.push s!"{jstr (Schedule.kind k).name}:{jstr e}"
        out.putStrLn (s!"{hd},\"mods\":{acr mods},\"objects\":{objs},\"unj\":{unj pb},\"n\":{n},\"wg\":{hasWG cfg}," ++
          s!"\"frames\":{frames.size},\"steps\":\{{",".intercalate parts.toList}}}")
      out.flush
    return 0
  | ["mapbound", list] =>
    -- per beatmap (NoMod playable): objects, unj, r0, end, dense1ms reference count (no simulation)
    let out ← IO.getStdout
    for line in (← IO.FS.readFile list).splitOn "\n" do
      let bmP := line.trimAscii.toString
      if bmP.isEmpty then continue
      let hd := s!"\{\"beatmap\":{jstr bmP}"
      match OsuModel.Beatmap.LegacyBeatmapDecoder.decode (← IO.FS.readBinFile bmP) with
      | .error e => out.putStrLn s!"{hd},\"error\":{jstr (toString e)}}"
      | .ok d =>
        if d.rulesetId != 0 then out.putStrLn s!"{hd},\"error\":\"non-osu ruleset\"}" else
        match playableOf d [] with
        | .error e => out.putStrLn s!"{hd},\"error\":{jstr e}}"
        | .ok pb0 =>
          let pb := toSimPlayable pb0
          let r0 := referenceStart pb
          let e := referenceEnd pb
          let refs := match references .dense1ms r0 e #[] with | .ok l => toString l.size | .error x => jstr x
          out.putStrLn s!"{hd},\"objects\":{pb.objects.size},\"unj\":{unj pb},\"r0\":{r0},\"end\":{e},\"dense_refs\":{refs}}"
      out.flush
    return 0
  | "exact2" :: bmP :: osrP :: sch :: rest =>
    -- unitsLoop (two-pass, as sc2UnitsRun) vs unitsLoop1 (one-pass) on one input
    let k ← schedOf sch
    let ov ← parseOv rest.head?
    match inputs (← IO.FS.readBinFile bmP) (← IO.FS.readBinFile osrP) ov with
    | .error e => IO.println s!"\{\"error\":{jstr e}}"; return 1
    | .ok (cfg, pb, frames, _) =>
      match mkCtx env cfg pb frames k, initState cfg pb with
      | .ok C, .ok S0 =>
        let (a, _, _, _) := unitsLoop C S0
        let (b, _, _, _, S) := unitsLoop1 C S0
        let full := match Sim.run C S0 with | .ok (_, S') => S'.out.size | .error _ => 0
        IO.println s!"\{\"exact2\":{a == b && full == S.out.size},\"two_pass\":{a},\"one_pass\":{b},\"judgements_run\":{full},\"judgements_one_pass\":{S.out.size}}"
        return (if a == b then 0 else 1)
      | _, _ => IO.println "{\"error\":\"ctx/init\"}"; return 1
  | "exact" :: bmP :: osrP :: sch :: rest | "exact1" :: bmP :: osrP :: sch :: rest =>
    let fast := args.head? == some "exact1"
    let k ← schedOf sch
    let ov ← parseOv rest.head?
    match inputs (← IO.FS.readBinFile bmP) (← IO.FS.readBinFile osrP) ov with
    | .error e => IO.println s!"\{\"error\":{jstr e}}"; return 1
    | .ok (cfg, pb, frames, mods) =>
      match exactJson env cfg pb frames k fast with
      | .error e => IO.println s!"\{\"error\":{jstr e}}"; return 1
      | .ok j => IO.println s!"\{\"beatmap\":{jstr bmP},\"replay\":{jstr osrP},\"schedule\":{jstr sch},\"mods\":{acr mods},{j}}"; return 0
  | ["synth", bmP, sch, modsJ, dtS] =>
    let k ← schedOf sch
    let some ms ← parseOv (some modsJ) | return 2
    let dt : Float := match OsuModel.Net.doubleParse dtS with | .ok v => v | .error _ => 1.0
    let d ← match OsuModel.Beatmap.LegacyBeatmapDecoder.decode (← IO.FS.readBinFile bmP) with
      | .ok d => pure d | .error e => IO.println s!"\{\"error\":{jstr (toString e)}}"; return 1
    match playableOf d ms with
    | .error e => IO.println s!"\{\"error\":{jstr e}}"; return 1
    | .ok pb0 =>
      let pb := toSimPlayable pb0
      let r0 := referenceStart pb - 1000
      let e := referenceEnd pb + 1000
      let nF := ((e - r0) / dt).ceil.toUInt64.toNat
      let frames : Array Frame := (Array.range nF).map fun i =>
        { time := r0 + dt * i.toFloat, pos := ⟨(256 : Float).toFloat32, (192 : Float).toFloat32⟩, actions := [] }
      let cfg := { Config.ofMods ms pb with lazerReplay := true }
      match exactJson env cfg pb frames k true with
      | .error e => IO.println s!"\{\"error\":{jstr e}}"; return 1
      | .ok j => IO.println s!"\{\"beatmap\":{jstr bmP},\"synthetic_dt\":{jstr dtS},\"schedule\":{jstr sch},\"mods\":{acr ms},{j}}"; return 0
  | "selftest" :: bmP :: osrP :: sch :: rest =>
    let k ← schedOf sch
    let ov ← parseOv rest.head?
    match inputs (← IO.FS.readBinFile bmP) (← IO.FS.readBinFile osrP) ov with
    | .error e => IO.println s!"\{\"error\":{jstr e}}"; return 1
    | .ok (cfg, pb, frames, _) =>
      match mkCtx env cfg pb frames k, initState cfg pb with
      | .ok C, .ok S0 =>
        let a := runBudgetNeed C S0
        let (b, _, _, _) := unitsLoop C S0
        IO.println s!"\{\"selftest\":{a == b},\"recursive\":{a},\"loop\":{b},\"steps\":{C.steps.size}}"
        return (if a == b then 0 else 1)
      | _, _ => IO.println "{\"error\":\"ctx/init\"}"; return 1
  | _ => IO.eprintln "usage: see tools/runbudget/RunBudget.lean"; return 2
