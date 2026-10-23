import OsuModel.Sim.Step
import OsuModel.Sim.ModsJson
import Std.Data.HashSet

/-!
# simtest: run the Lean simulation model on (playable dump, decompressed frame text, env, mods, schedule)

```
simtest --playable P.json --frames F.txt --env ENV.json [--schedule catchup|perframe|dense1ms]
        [--mods CL,NF,...] [--steps]
```
Prints one JSON object (oracle-like schema; times as raw IEEE bits in hex).
-/

open OsuModel.Net OsuModel.Sim OsuModel.Replay
open Lean (Json)

def loadMat (v : Json) : Except String Mat3 := do
  match ← v.getArr? with
  | #[a0, a1, a2, a3, a4, a5, a6, a7, a8] =>
    let f := Load.f32
    return ⟨← f a0, ← f a1, ← f a2, ← f a3, ← f a4, ← f a5, ← f a6, ← f a7, ← f a8⟩
  | _ => throw "matrix: expected 9 entries"

def loadEnv (s : String) : Except String Env := do
  let j ← Json.parse s
  let mat (v : Json) : Except String Mat3 := loadMat v
  let hoc : DrawInfo := ⟨← mat (← j.getObjVal? "hit_object_container_matrix"),
    ← mat (← j.getObjVal? "hit_object_container_inverse")⟩
  let hist ← (← j.getObjVal? "hit_object_container_history").getArr?
  let hocFirst ← if h : 0 < hist.size then do
      pure (⟨← mat (← hist[0].getObjVal? "matrix"), ← mat (← hist[0].getObjVal? "inverse")⟩ : DrawInfo)
    else pure hoc
  let argonPathRadius ← Load.f32 (← j.getObjVal? "argon_path_radius")
  let hocSize ← Load.vec2 (← j.getObjVal? "hit_object_container_draw_size")
  let node (v : Json) : Except String ChainNode := do
    return { typeName := ← (← v.getObjVal? "type").getStr?, pos := ← Load.vec2 (← v.getObjVal? "pos")
             scale := ← Load.vec2 (← v.getObjVal? "scale"), rot := ← Load.f32 (← v.getObjVal? "rotation")
             origin := ← Load.vec2 (← v.getObjVal? "origin") }
  let chainOf (k : String) : Except String (Array ChainNode) :=
    match j.getObjVal? k with
    | .ok v => do (← v.getArr?).mapM node
    | .error _ => pure #[]
  return { hoc, hocFirst, argonPathRadius, hocSize, chainFirst := ← chainOf "hoc_chain_first", chain := ← chainOf "hoc_chain" }


def jsonStr (s : String) : String := "\"" ++ s ++ "\""

open OsuModel.Sim.Sim in
/-- `--trace-tracking FILE` (debugging, difftest/tracking_trace.py): the loop of `Sim.run` (same `k`/`t` update and
`stepOnce`; the `traceObj` debug push is omitted, it never changes the state) plus, after every frame-stable step, one
line per alive slider whose tracking-relevant state changed:
`i t_bits tracking mouseInR mouseIn2.4R anyValidTrackingAction pressedMask(1=L,2=R) hitAction(0/1/2) acceptAnyAfter_bits|- life`.
Only reads the state (`mouseInFollowArea` and `isValidTrackingAction` are pure queries). -/
def trackingTraceRun : SimM (Array String) := do
  let steps := (← ctx).steps
  let objs := (← ctx).pb.objects
  let mut out : Array String := #[]
  let mut last : Std.HashMap Nat String := {}
  for stp in steps, k in [0:steps.size] do
    let t := stp.time
    modify fun s => { s with k, t }
    stepOnce
    for o in objs, i in [0:objs.size] do
      let isSlider := match o.h.kind with | Kind.slider => true | _ => false
      if !isSlider then continue
      let os ← ostate i
      if os.life != .alive && !(last.contains i) then continue
      let s ← st
      let inR ← mouseInFollowArea i false
      let inB ← mouseInFollowArea i true
      let valid := s.pressed.any (isValidTrackingAction os t)
      let pm := (if s.pressed.contains .left then 1 else 0) + (if s.pressed.contains .right then 2 else 0)
      let ha := match os.hitAction with | some .left => 1 | some .right => 2 | some _ => 3 | none => 0
      let aaa := match os.acceptAnyAfter with | some x => toString x.toBits | none => "-"
      let life := match os.life with | .future => "F" | .alive => "A" | .past => "P"
      let key := s!"{os.tracking} {inR} {inB} {valid} {pm} {ha} {aaa} {life}"
      if last[i]? != some key then out := out.push s!"{i} {t.toBits} {key}"
      last := if os.life == .past then last.erase i else last.insert i key
  return out

def main (args : List String) : IO UInt32 := do
  let mut playableP := ""
  let mut framesP := ""
  let mut envP := ""
  let mut sched := ScheduleKind.catchup
  let mut mods : List String := []
  let mut modsJson : Option String := none
  let mut lazerReplay := false
  let mut printGeom := false
  let mut traceObj : Option Nat := none
  let mut dbgNoPresence := false
  let mut printSteps := false
  let mut checkEnv := ""
  let mut traceTracking := ""
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--playable" :: v :: r => playableP := v; rest := r
    | "--frames" :: v :: r => framesP := v; rest := r
    | "--env" :: v :: r => envP := v; rest := r
    | "--schedule" :: v :: r =>
      match ScheduleKind.ofString? v with
      | some k => sched := k
      | none => IO.eprintln s!"unknown schedule {v}"; return 2
      rest := r
    | "--mods" :: v :: r => mods := (v.splitOn ",").filter (· != ""); rest := r
    | "--mods-json" :: v :: r => modsJson := some v; rest := r
    | "--lazer-replay" :: r => lazerReplay := true; rest := r
    | "--print-geom" :: r => printGeom := true; rest := r
    | "--trace-obj" :: v :: r => traceObj := v.toNat?; rest := r
    | "--dbg-no-presence" :: r => dbgNoPresence := true; rest := r
    | "--steps" :: r => printSteps := true; rest := r
    | "--check-env" :: v :: r => checkEnv := v; rest := r
    | "--trace-tracking" :: v :: r => traceTracking := v; rest := r
    | a :: _ => IO.eprintln s!"unknown argument {a}"; return 2
    | [] => rest := []
  let pb ← match Load.playableOfString (← IO.FS.readFile playableP) with
    | .ok p => pure p
    | .error e => IO.eprintln s!"playable: {e}"; return 1
  let env ← match loadEnv (← IO.FS.readFile envP) with
    | .ok e => pure e
    | .error e => IO.eprintln s!"env: {e}"; return 1
  let text ← IO.FS.readFile framesP
  let frames ← match OsuModel.Replay.decode text pb.beatmapVersion with
    | .ok f => pure f
    | .error e => IO.println s!"\{\"error\": \"frame decode: {repr e}\"}"; return 1
  if printGeom then
    -- static slider body geometry (Size, OriginPosition) per slider: [i, sx, sy, ox, oy]
    let mut first := true
    IO.print "["
    for o in pb.objects, i in [0:pb.objects.size] do
      if let some sd := o.slider then
        let g ← match sliderGeom env o.h sd with
          | .ok g => pure g
          | .error e => IO.println s!"\{\"error\": \"sim: {e}\"}"; return 1
        IO.print s!"{if first then "" else ","}[{i},\"{OsuModel.Sim.F32.hex g.size.x}\",\"{OsuModel.Sim.F32.hex g.size.y}\",\"{OsuModel.Sim.F32.hex g.origin.x}\",\"{OsuModel.Sim.F32.hex g.origin.y}\"]"
        first := false
    IO.println "]"
    return 0
  if !env.chain.isEmpty then
    -- the recomposed ancestor chain must reproduce the dumped HitObjectContainer matrices bit-exactly
    let a := composeChain env.chain
    let b := composeChain env.chainFirst
    if !(a.matrix.bitEq env.hoc.matrix && a.inverse.bitEq env.hoc.inverse && b.matrix.bitEq env.hocFirst.matrix && b.inverse.bitEq env.hocFirst.inverse) then
      IO.eprintln s!"env: hoc_chain does not reproduce the HitObjectContainer DrawInfo: {repr a} vs {repr env.hoc}"
      return 1
  if checkEnv != "" then
    -- compare the model's DrawInfo chains with the oracle's --dump-env probes (`oracle/Dump.cs` EnvProbe)
    let j ← match Json.parse (← IO.FS.readFile checkEnv) with
      | .ok j => pure j
      | .error e => IO.eprintln e; return 1
    let objs := (j.getObjValD "objects").getArr?.toOption.getD #[]
    let mat (v : Json) : Mat3 := match loadMat v with
      | .ok m => m | .error _ => Mat3.identity
    let mut ok := 0
    let mut bad := 0
    let mut seen : Std.HashSet Nat := {}
    let mut badLater := 0
    for o in objs do
      let i := (o.getObjValD "i").getNat?.toOption.getD 0
      let kind := (o.getObjValD "kind").getStr?.toOption.getD ""
      let some obj := pb.objects[i]? | IO.eprintln s!"check-env: object {i} out of range"; return 1
      let h := obj.h
      let gs : Option SliderGeom := match obj.slider with
        | some sd => (sliderGeom env h sd).toOption
        | none => none
      let checks : List (String × Mat3 × Mat3) := match kind with
        | "circle" => let d := circleReceptor env h
          [("receptor_matrix", d.matrix, mat (o.getObjValD "receptor_matrix")), ("receptor_inverse", d.inverse, mat (o.getObjValD "receptor_inverse"))]
        | "slider" => match gs with
          | none => []   -- reported below
          | some g => [("matrix", g.drawInfo.matrix, mat (o.getObjValD "matrix")), ("inverse", g.drawInfo.inverse, mat (o.getObjValD "inverse")),
           ("head_receptor_matrix", g.headReceptor.matrix, mat (o.getObjValD "head_receptor_matrix")),
           ("head_receptor_inverse", g.headReceptor.inverse, mat (o.getObjValD "head_receptor_inverse"))]
        | _ => []
      let isFirst := !seen.contains i
      seen := seen.insert i
      for (nm, a, b) in checks do
        if a.bitEq b then ok := ok + 1 else
          bad := bad + 1
          if !isFirst then badLater := badLater + 1
          if bad ≤ 5 then IO.eprintln s!"env mismatch obj {i} {kind} {nm}: model {repr a} oracle {repr b}"
      if kind == "slider" then
        let some g := gs | IO.eprintln s!"check-env: object {i}: no slider geometry"; return 1
        let v ← match Load.vec2 (o.getObjValD "origin"), Load.vec2 (o.getObjValD "draw_size") with
          | .ok a, .ok b => pure (a, b) | _, _ => pure (Vec2.zero, Vec2.zero)
        if g.origin.eq v.1 && g.size.eq v.2 then ok := ok + 1 else
          bad := bad + 1
          if !isFirst then badLater := badLater + 1
          if bad ≤ 5 then IO.eprintln s!"env mismatch obj {i} slider origin/size"
    IO.println s!"\{\"env_checks_ok\":{ok},\"env_checks_bad\":{bad},\"bad_not_first_record\":{badLater}}"
    return (if bad == 0 then 0 else 1)
  let modList ← match modsJson with
    | some j => match SimJson.parseMods j with
      | .ok ms => pure ms
      | .error e => IO.eprintln s!"mods json: {e}"; return 2
    | none => pure (mods.map fun a => OsuModel.Beatmap.Settings.toMod a [])
  let cfg := { Config.ofMods modList pb with lazerReplay, traceObj, dbgNoPresence }
  let res : Except String (Ctx × St × Array String) :=
    if traceTracking == "" then do
      let (c, s) ← simulate env cfg pb frames sched
      return (c, s, #[])
    else do
      let c ← mkCtx env cfg pb frames sched
      let (lines, s) ← (trackingTraceRun.run c).run (← initState cfg pb c.smax.initWithoutMods)
      return (c, s, lines)
  let (c, s) ← match res with
    | .ok (c, s, lines) =>
      if traceTracking != "" then IO.FS.writeFile traceTracking ("\n".intercalate lines.toList ++ "\n")
      pure (c, s)
    | .error e =>
      -- rejection (malformed input or a lazer exception): reported, never a silent default result
      IO.println (Json.compress (Json.mkObj [("error", Json.str s!"sim: {e}")])); return 1
  for d in s.dbg do IO.eprintln d
  let out ← IO.getStdout
  out.putStr "{"
  out.putStr s!"\"model\":\"OsuModel.Sim\",\"schedule\":{jsonStr (repr sched).pretty},\"frames\":{frames.size},\"steps\":{c.steps.size},"
  if printSteps then
    out.putStr "\"step_times\":["
    let mut first := true
    for st in c.steps do
      if !first then out.putStr ","
      first := false
      out.putStr (jsonStr (OsuModel.Sim.F64.hex st.time))
    out.putStr "],"
  let statsJson (a : Array Nat) : String := Id.run do
    let mut parts : Array String := #[]
    for r in HitResult.all do
      let n := a[r.toNat]?.getD 0   -- printing only; the arrays have `nStats` entries
      if n != 0 then parts := parts.push s!"{jsonStr r.name}:{n}"
    return "{" ++ ",".intercalate parts.toList ++ "}"
  let result (sc : ScoreSt) (h : HealthSt) (sem : String) : String :=
    let rank := if h.failed then Rank.f else sc.rank
    let ft := match h.failTime with | some t => jsonStr (OsuModel.Sim.F64.hex t) | none => "null"
    s!"\{\"semantics\":{jsonStr sem},\"failed\":{h.failed},\"fail_time\":{ft},\"fail_trigger_count\":{h.failTriggers}," ++
    s!"\"rank\":{jsonStr rank.name},\"total_score\":{sc.totalScore},\"total_score_without_mods\":{sc.totalScoreWithoutMods}," ++
    s!"\"accuracy\":{jsonStr (OsuModel.Sim.F64.hex sc.accuracy)},\"max_combo\":{sc.highestCombo},\"final_combo\":{sc.combo}," ++
    s!"\"final_health\":{jsonStr (OsuModel.Sim.F64.hex h.health)},\"completed\":{sc.hasCompleted}," ++
    s!"\"statistics\":{statsJson sc.stats},\"maximum_statistics\":{statsJson c.smax.maxStats}," ++
    s!"\"legacy_counts\":\{\"300\":{sc.stat .great},\"100\":{sc.stat .ok},\"50\":{sc.stat .meh},\"miss\":{sc.stat .miss}}}"
  out.putStr s!"\"score_multiplier\":{jsonStr (OsuModel.Sim.F64.hex cfg.scoreMultiplier)},"
  out.putStr s!"\"drain_rate\":{jsonStr (OsuModel.Sim.F64.hex c.hcfg.drainRate)},\"hp_multiplier\":{jsonStr (OsuModel.Sim.F64.hex c.hcfg.hpMultiplierNormal)},"
  out.putStr s!"\"live\":{result s.score s.health "live"},\"replay_player\":{result s.scoreRP s.healthRP "replay_player"},"
  out.putStr s!"\"max_combo\":{s.score.highestCombo},\"final_combo\":{s.score.combo},\"judgement_count\":{s.out.size},"
  out.putStr s!"\"statistics\":{statsJson s.score.stats},\"judgements\":["
  let mut first := true
  for j in s.out do
    if !first then out.putStr ","
    first := false
    out.putStr s!"\{\"i\":{j.top},\"n\":{j.nested},\"type\":{jsonStr (if j.typeName == "" then j.kind.typeName else j.typeName)},\"result\":{jsonStr j.result.name},\"time\":{jsonStr (OsuModel.Sim.F64.hex j.time)},\"combo\":{j.combo},\"health\":{jsonStr (OsuModel.Sim.F64.hex j.health)},\"failed\":{j.failed},\"rp_combo\":{j.comboRP},\"rp_health\":{jsonStr (OsuModel.Sim.F64.hex j.healthRP)},\"rp_failed\":{j.failedRP}}"
  out.putStr "]}\n"
  return 0
