import OsuModel.Eval

/-!
# evaltest: the end-to-end model on (.osu, .osr) with oracle-like options

```
evaltest BEATMAP.osu REPLAY.osr [--schedule catchup|perframe|dense1ms|explicit:FILE] [--mods JSON]
         [--replace-mods] [--no-classic] [--no-judgements] [--steps] [--timing] [--dump-playable PATH]
```
Prints one JSON object in the oracle's schema (`oracle/README.md` "Output schema"), with every double as its raw
IEEE bits (`"0x…"`, as simtest) and mods as acronym lists (`decoded_mods_acronyms`, `mods_acronyms`) plus the decoded
settings. A rejected input prints `{"rejected": "...", "stage": "..."}` and exits with 1.
`--dump-playable PATH` writes the adapter output in the oracle's `--dump-playable` format (no simulation).
`--sim-playable PATH` (localisation only) simulates on a playable dump (e.g. the oracle's) instead of the adapter output.
-/

open OsuModel.Net OsuModel.Sim OsuModel.Eval
open OsuModel.Beatmap (ModConfig)

def jstr (s : String) : String := Lean.Json.compress (Lean.Json.str s)
def hexD (x : F64) : String := jstr (F64.hex x)

def settingJson : OsuModel.Beatmap.SettingValue → String
  | .bool b => toString b
  | .int v | .enum v => toString v.toInt
  | .double v => hexD v
  | .float v => jstr (F32.hex v)
  | .optInt none | .optFloat none => "null"
  | .optInt (some v) => toString v.toInt
  | .optFloat (some v) => jstr (F32.hex v)

def modsJson (ms : List ModConfig) : String :=
  "[" ++ ",".intercalate (ms.map fun m =>
    "{\"acronym\":" ++ jstr m.acronym ++ (if m.known then "" else ",\"unknown\":true") ++ ",\"settings\":{" ++
      ",".intercalate (m.settings.toList.map fun (k, v) => jstr k ++ ":" ++ settingJson v) ++ "}}") ++ "]"

def acrJson (ms : List ModConfig) : String := "[" ++ ",".intercalate (ms.map (jstr ·.acronym)) ++ "]"

def statsJson (a : Array Nat) : String := Id.run do
  let mut parts : Array String := #[]
  for r in HitResult.all do
    let n := a[r.toNat]!
    if n != 0 then parts := parts.push s!"{jstr r.name}:{n}"
  return "{" ++ ",".intercalate parts.toList ++ "}"

def semJson (r : Result) (sem : SemResult) (name : String) (withJ : Bool) (live : Bool) : String := Id.run do
  let sc := sem.score
  let h := sem.health
  let rank := if h.failed then Rank.f else sc.rank
  let ft := match h.failTime with | some t => hexD t | none => "null"
  let mut s := s!"\{\"semantics\":{jstr name},\"failed\":{h.failed},\"fail_time\":{ft},\"fail_trigger_count\":{h.failTriggers}," ++
    s!"\"rank\":{jstr rank.name},\"total_score\":{sc.totalScore},\"total_score_without_mods\":{sc.totalScoreWithoutMods}," ++
    s!"\"accuracy\":{hexD sc.accuracy},\"max_combo\":{sc.highestCombo},\"final_combo\":{sc.combo}," ++
    s!"\"final_health\":{hexD h.health},\"completed\":{sc.hasCompleted}," ++
    s!"\"statistics\":{statsJson sc.stats},\"maximum_statistics\":{statsJson r.maxStats}," ++
    s!"\"legacy_counts\":\{\"300\":{sc.stats[HitResult.great.toNat]!},\"100\":{sc.stats[HitResult.ok.toNat]!},\"50\":{sc.stats[HitResult.meh.toNat]!},\"miss\":{sc.stats[HitResult.miss.toNat]!}}," ++
    s!"\"judgement_count\":{r.judgements.size}"
  if withJ then
    let parts := r.judgements.toList.map fun j =>
      let ty := if j.typeName == "" then j.kind.typeName else j.typeName
      -- per-judgement combo/health/failed per semantics (Sim JRec: live fields / *RP fields)
      if live then
        s!"\{\"i\":{j.top},\"n\":{j.nested},\"type\":{jstr ty},\"result\":{jstr j.result.name},\"time\":{hexD j.time},\"combo\":{j.combo},\"health\":{hexD j.health},\"failed\":{j.failed}}"
      else
        s!"\{\"i\":{j.top},\"n\":{j.nested},\"type\":{jstr ty},\"result\":{jstr j.result.name},\"time\":{hexD j.time},\"combo\":{j.comboRP},\"health\":{hexD j.healthRP},\"failed\":{j.failedRP}}"
    s := s ++ ",\"judgements\":[" ++ ",".intercalate parts ++ "]"
  return s ++ "}"

def parseExplicit (path : String) : IO (Except String (Array F64)) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for l in txt.splitOn "\n" do
    let l := l.trimAscii.toString
    if l.isEmpty then continue
    match doubleParse l with
    | .ok v => out := out.push v
    | .error _ => return .error s!"bad reference time {l}"
  return .ok out

def main (args : List String) : IO UInt32 := do
  let mut pos : Array String := #[]
  let mut schedS := "catchup"
  let mut modsArg : Option String := none
  let mut opts : Options := {}
  let mut withJ := true
  let mut withSteps := false
  let mut timing := false
  let mut dumpPlayable : Option String := none
  let mut simPlayable : Option String := none
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--schedule" :: v :: r => schedS := v; rest := r
    | "--mods" :: v :: r => modsArg := some v; rest := r
    | "--replace-mods" :: r => opts := { opts with replaceMods := true }; rest := r
    | "--no-classic" :: r => opts := { opts with noClassic := true }; rest := r
    | "--no-judgements" :: r => withJ := false; rest := r
    | "--steps" :: r => withSteps := true; rest := r
    | "--timing" :: r => timing := true; rest := r
    | "--dump-playable" :: v :: r => dumpPlayable := some v; rest := r
    | "--sim-playable" :: v :: r => simPlayable := some v; rest := r
    | a :: r =>
      if a.startsWith "--" then IO.eprintln s!"unknown option {a}"; return 2
      pos := pos.push a; rest := r
    | [] => rest := []
  if pos.size != 2 then
    IO.eprintln "usage: evaltest BEATMAP.osu REPLAY.osr [options]"; return 2
  let t0 ← IO.monoNanosNow
  if let some m := modsArg then
    match SimJson.parseMods m with
    | .ok ms => opts := { opts with modsOverride := some ms }
    | .error e => IO.println s!"\{\"rejected\":{jstr ("mods JSON: " ++ e)},\"stage\":\"mods\"}"; return 1
  let sched ← if schedS.startsWith "explicit:" then
      match ← parseExplicit (schedS.drop 9).toString with
      | .ok refs => pure (Schedule.explicit refs)
      | .error e => IO.eprintln e; return 2
    else match ScheduleKind.ofString? schedS with
      | some k => pure (Schedule.kind k)
      | none => IO.eprintln s!"unknown schedule {schedS}"; return 2
  let bm ← IO.FS.readBinFile pos[0]!
  let osr ← IO.FS.readBinFile pos[1]!
  let rejected (e : Rejection) : IO UInt32 := do
    IO.println s!"\{\"rejected\":{jstr e.reason},\"stage\":{jstr e.stage},\"input\":\{\"beatmap\":{jstr pos[0]!},\"replay\":{jstr pos[1]!}}}"
    return 1
  if let some p := dumpPlayable then
    match playableFor bm osr opts with
    | .ok spb => IO.FS.writeFile p (playableJson spb); IO.println "{\"dumped\":true}"; return 0
    | .error e => rejected e
  else
  let override ← match simPlayable with
    | some p => match Load.playableOfString (← IO.FS.readFile p) with
      | .ok pb => pure (some pb)
      | .error e => IO.eprintln s!"--sim-playable: {e}"; return 2
    | none => pure none
  match evaluate defaultEnv bm osr opts sched override with
  | .error e => rejected e
  | .ok r =>
    let out ← IO.getStdout
    let lf := match r.lastFrameTime with | some t => s!",\"last_frame_time\":{hexD t}" | none => ""
    let modsArgJ := match modsArg with | some m => s!",\"mods_arg\":{jstr m}" | none => ""
    out.putStr ("{\"model\":\"OsuModel.Eval\",\"input\":{" ++
      s!"\"beatmap\":{jstr pos[0]!},\"replay\":{jstr pos[1]!},\"replay_beatmap_md5\":{match r.replayBeatmapHash with | some h => jstr h | none => "null"}," ++
      s!"\"replay_version\":{r.replayVersion.toInt},\"is_legacy_score\":{r.isLegacyScore}{modsArgJ},\"no_classic\":{opts.noClassic},\"replace_mods\":{opts.replaceMods}," ++
      s!"\"decoded_mods_acronyms\":{acrJson r.decodedMods},\"mods_acronyms\":{acrJson r.mods}," ++
      s!"\"decoded_mods\":{modsJson r.decodedMods},\"mods\":{modsJson r.mods}," ++
      s!"\"true_gameplay_rate\":{hexD r.trueGameplayRate},\"hit_objects\":{r.hitObjects},\"frames\":{r.frames}}," ++
      s!"\"schedule\":\{\"kind\":{jstr r.scheduleName},\"r0\":{hexD r.r0},\"end\":{hexD r.endTime},\"gameplay_start_time\":{hexD r.gameplayStartTime}{lf}," ++
      s!"\"references\":{r.references},\"steps\":{r.steps}}," ++
      s!"\"score_multiplier\":{hexD r.scoreMultiplier}," ++
      s!"\"live\":{semJson r r.live "live" withJ true}," ++
      s!"\"replay_player\":" ++ (match r.replayPlayer with
        | some rp => semJson r rp "replay_player" withJ false
        | none => "\"same_as_live\""))
    if withSteps then
      out.putStr (",\"step_times\":[" ++ ",".intercalate (r.stepTimes.toList.map hexD) ++ "]")
    if timing then
      let t1 ← IO.monoNanosNow
      out.putStr s!",\"wall_ms\":{(t1 - t0) / 1000000}"
    out.putStr "}\n"
    return 0
