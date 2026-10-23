/-
File-driven, multi-client Lean REPL for proof iteration: pays the slow `import Aeneas`
(~2.3 GB private memory, 20 s to 12 min depending on page cache) once, then elaborates request
files against the imported environment. Several proof agents can share one process.

Usage: `lake env lean --run scripts/Repl.lean <dir>`. `<dir>/header` lists the modules to import
(one per line). Clients: `<dir>` itself and every subdirectory `<dir>/c_<name>/` (created at any
time; picked up within a second). Each client has its own environment and processes its
requests in name order; different clients run in parallel (one thread each).
For each new request `<client>/<name>.lean` the REPL writes `<client>/<name>.out` (messages,
then a line `%%DONE%%`). A request whose first line is `--commit` keeps its declarations for
that client's later requests; others are checked against the client's environment and dropped.
`maxHeartbeats` is 400000 per request unless the request sets it.
Memory watchdog (D38/D40): when the process RSS exceeds `REPL_MEM_MB` (default 3900; anonymous memory, RssAnon) one running request is
cancelled (its `.out` says so; logged with all running requests to `<dir>/watchdog.log`): the longest-running one
if it has run >= 10 s, else the most recently started. Freed memory often stays in the process, so after a
cancellation the next soft one needs `REPL_MEM_STEP_MB` (300) of new growth; above `REPL_MEM_HARD_MB` (4500;
scope cap 5000M) every running request is cancelled. Repeat offenders: a client whose requests are the culprit
`REPL_OFFENDER_N` (2) times within `REPL_OFFENDER_MIN` (60) minutes gets its environment dropped
(file `<client>/watchdog_dropped.*`; re-commit).
Commit chains survive restarts (D41): each successful `--commit` request is copied to
`<client>/committed/NNNNN_<name>.lean`; when a client is (re)started (server restart, idle drop) the chain is
replayed in order before new requests are served; failing ones are renamed `.failed` and logged in
`<client>/replay.log`. An explicit drop (file `drop`, or the watchdog's repeat-offender drop) discards the chain.
Release a client's environment (memory): create `<client>/drop` (renamed to `dropped.*` when done;
the next request in that dir starts a fresh environment). A client idle for `REPL_IDLE_MIN` minutes
(default 30) is dropped automatically (file `<client>/dropped.idle.*`). At most `REPL_MAX_CLIENTS`
(default 8) clients are served at once; a further `c_*` dir gets a file `waiting` until a slot frees.
A `c_*` dir is only picked up when it has an unanswered request (idle dirs take no slot). Exit: create `<dir>/stop`. Not part of the proof check (check_all.sh / lake build are).
-/
import Lean
open Lean Elab

/-- requests being elaborated: (client dir, request file, start time ms, cancel token) -/
abbrev Running := IO.Ref (Array (String × String × Nat × IO.CancelToken))

/-- anonymous resident memory of this process in bytes (`RssAnon` in `/proc/self/status`). Not VmRSS: that also
counts the mmapped .olean pages (2.7 GB after replays, file-backed and reclaimable), which made the v2 watchdog
cancel every request at 13:14 although only 2.3 GB were anonymous. -/
def rssBytes : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for l in s.splitOn "\n" do
    if l.startsWith "RssAnon:" then
      let ws := (l.splitOn " ").filter (· ≠ "")
      if let some kb := ws[1]?.bind String.toNat? then return kb * 1024
  return 0

/-- elaborate `src` command by command (as `Lean.Elab.process`, but non-incremental and with a
cancellation token that the watchdog can set; the elaborator's `checkSystem` honours it) -/
def elabCancellable (src : String) (env : Environment) (opts : Options) (fileName : String)
    (tk : IO.CancelToken) : IO (Environment × MessageLog) := do
  let inputCtx := Parser.mkInputContext src fileName
  -- synchronous elaboration: proof bodies are not deferred to snapshot tasks whose messages we would miss
  let opts := Elab.async.set opts false
  let mut cmdState := Command.mkState env {} opts
  let mut pstate : Parser.ModuleParserState := {}
  let mut acc : MessageLog := {}
  repeat
    let scope := cmdState.scopes.head!
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
                   openDecls := scope.openDecls }
    let pos := pstate.pos
    let (cmd, ps, pmsgs) := Parser.parseCommand inputCtx pmctx pstate {}
    pstate := ps
    acc := acc ++ pmsgs
    let cmdCtx : Command.Context := { cmdPos := pos, fileName := fileName, fileMap := inputCtx.fileMap,
                                      snap? := none, cancelTk? := some tk }
    match ← (EIO.toIO' (((Command.elabCommandTopLevel cmd #[]) cmdCtx).run cmdState)) with
    | .ok ((), s') =>
      cmdState := s'
      acc := acc ++ s'.messages
    | .error e =>
      let es ← e.toMessageData.toString
      let msg : Message := { fileName := fileName, pos := inputCtx.fileMap.toPosition pos, severity := .error,
                             data := m!"internal error: {es}" }
      acc := acc.add msg
    if Parser.isTerminalCommand cmd then break
    if ← tk.isSet then break
  return (cmdState.env, acc)

/-- an explicit drop also forgets the client's persisted commit chain (it is not replayed) -/
def clearCommitted (dir : String) : IO Unit := do
  let c := dir ++ "/committed"
  if ← System.FilePath.pathExists c then
    IO.FS.rename c (dir ++ s!"/committed.dropped.{← IO.monoMsNow}")

unsafe def serveClient (running : Running) (dir : String) (env0 : Environment) (stopFile : String) : IO Unit := do
  let mut env := env0
  let mut done : Std.HashSet String := {}
  let opts : Options := maxHeartbeats.set {} 400000
  let idleMs : Nat := 60000 * ((← IO.getEnv "REPL_IDLE_MIN").bind String.toNat? |>.getD 30)
  -- persisted commit chain (D41): every successful --commit request is copied to committed/NNNNN_<name>.lean;
  -- a fresh serveClient (server restart, idle drop) replays it in order before serving new requests
  let cdir := dir ++ "/committed"
  let mut seq : Nat := 0
  if ← System.FilePath.pathExists cdir then
    let fs := (← System.FilePath.readDir cdir).filter (·.fileName.endsWith ".lean") |>.map (·.fileName) |>.qsort (· < ·)
    let t0 ← IO.monoMsNow
    let mut nok := 0
    let mut log := s!"replay started (monoMs {t0}): {fs.size} committed requests\n"
    for f in fs do
      seq := max seq (((f.splitOn "_")[0]?.bind String.toNat?).getD 0)
      if ← System.FilePath.pathExists stopFile then break
      let src ← IO.FS.readFile (cdir ++ "/" ++ f)
      let tk ← IO.CancelToken.new
      let t1 ← IO.monoMsNow
      running.modify (·.push (dir, "replay:" ++ f, t1, tk))
      let (env', msgs) ← elabCancellable src env opts f tk
      running.modify (·.filter (fun e => e.2.1 != "replay:" ++ f || e.1 != dir))
      if ← tk.isSet then
        -- the watchdog cancelled the replay: keep the chain on disk (no .failed), serve with what replayed so far
        log := log ++ s!"replay stopped at {f} (cancelled by the memory watchdog); the rest stays for the next replay\n"
        break
      if !msgs.hasErrors then
        env := env'; nok := nok + 1
      else
        -- skip it from now on (later requests depending on it fail too and are skipped as well)
        IO.FS.rename (cdir ++ "/" ++ f) (cdir ++ "/" ++ f ++ ".failed")
        let firstErr := (msgs.toList.filter (·.severity == .error)).head?
        let e ← match firstErr with | some m => m.toString | none => pure "cancelled by the memory watchdog\n"
        log := log ++ s!"FAILED (skipped, renamed .failed): {f}: {(e.take 400).toString}"
    log := log ++ s!"replay done: {nok}/{fs.size} ok in {(← IO.monoMsNow) - t0} ms\n"
    IO.FS.withFile (dir ++ "/replay.log") .append fun h => h.putStr log
  let mut last ← IO.monoMsNow
  repeat
    if ← System.FilePath.pathExists stopFile then break
    if ← System.FilePath.pathExists (dir ++ "/drop") then
      -- release this client's environment (memory); the client dir can be reused afterwards
      clearCommitted dir
      IO.FS.rename (dir ++ "/drop") (dir ++ s!"/dropped.{← IO.monoMsNow}")
      break
    let entries ← System.FilePath.readDir dir
    let reqs := entries.filter (fun e => e.fileName.endsWith ".lean") |>.map (·.fileName) |>.qsort (· < ·)
    let mut any := false
    for r in reqs do
      if done.contains r then continue
      let base := r.dropEnd 5 |>.toString
      if ← System.FilePath.pathExists (dir ++ "/" ++ base ++ ".out") then
        done := done.insert r; continue
      any := true
      let src ← IO.FS.readFile (dir ++ "/" ++ r)
      let t1 ← IO.monoMsNow
      let tk ← IO.CancelToken.new
      running.modify (·.push (dir, r, t1, tk))
      -- markers in server.log, so that a Lean-internal PANIC message printed to stderr can be attributed
      IO.eprintln s!"[req] {t1} start {dir}/{r}"
      let (env', msgs) ← elabCancellable src env opts r tk
      IO.eprintln s!"[req] {← IO.monoMsNow} end {dir}/{r}"
      running.modify (·.filter (fun e => e.2.1 != r || e.1 != dir))
      let cancelled ← tk.isSet
      let mut out := ""
      if cancelled then
        out := s!"{r}:1:0: error: cancelled by the memory watchdog: server RSS above the limit; split the goal (smaller simp/omega contexts, no full `abs` unfolding of big records)\n"
        if ← System.FilePath.pathExists (dir ++ "/drop") then
          out := out ++ s!"{r}:1:0: error: repeat offender: this client's committed environment is dropped (re-run your --commit requests)\n"
      for m in msgs.toList do
        out := out ++ (← m.toString (includeEndPos := true))
      let ms := (← IO.monoMsNow) - t1
      if src.startsWith "--commit" && !msgs.hasErrors && !cancelled then
        env := env'
        seq := seq + 1
        IO.FS.createDirAll cdir
        IO.FS.writeFile (cdir ++ "/" ++ ((toString (100000 + seq)).drop 1).toString ++ "_" ++ r) src
      out := out ++ s!"%%TIME {ms} ms errors={msgs.hasErrors || cancelled}\n%%DONE%%\n"
      IO.FS.writeFile (dir ++ "/" ++ base ++ ".tmp") out
      IO.FS.rename (dir ++ "/" ++ base ++ ".tmp") (dir ++ "/" ++ base ++ ".out")
      done := done.insert r
    if any then last ← IO.monoMsNow
    else
      if (← IO.monoMsNow) - last > idleMs && dir ++ "/stop" != stopFile then
        IO.FS.writeFile (dir ++ s!"/dropped.idle.{← IO.monoMsNow}") "idle\n"
        break
      IO.sleep 300

/-- a client dir is served only while it has a request without answer (idle dirs take no slot) -/
def hasPending (dir : String) : IO Bool := do
  for e in ← System.FilePath.readDir dir do
    if e.fileName.endsWith ".lean" then
      let base := e.fileName.dropEnd 5 |>.toString
      if !(← System.FilePath.pathExists (dir ++ "/" ++ base ++ ".out")) then return true
  return false

unsafe def main (args : List String) : IO Unit := do
  let dir := args.head!
  let header ← IO.FS.readFile (dir ++ "/header")
  let mods := (header.splitOn "\n").filter (· ≠ "") |>.map (fun s => ({ module := s.toName } : Import))
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env0 ← importModules mods.toArray {} (loadExts := true)
  let stopFile := dir ++ "/stop"
  let running : Running ← IO.mkRef #[]
  let maxClients : Nat := (← IO.getEnv "REPL_MAX_CLIENTS").bind String.toNat? |>.getD 8
  let mut clients : Std.HashSet String := {}
  let mut tasks : Array (String × Task (Except IO.Error Unit)) := #[]
  tasks := tasks.push (dir, ← IO.asTask (serveClient running dir env0 stopFile) (prio := .dedicated))
  clients := clients.insert dir
  IO.FS.writeFile (dir ++ "/ready") s!"imported in {(← IO.monoMsNow) - t0} ms\n"
  -- memory watchdog (see the header comment): soft limit REPL_MEM_MB, hard limit REPL_MEM_HARD_MB
  let mb : Nat := 1024 * 1024
  let envNat (k : String) (d : Nat) : IO Nat := return ((← IO.getEnv k).bind String.toNat?).getD d
  let limit : Nat := mb * (← envNat "REPL_MEM_MB" 3900)
  let hard : Nat := mb * (← envNat "REPL_MEM_HARD_MB" 4500)
  let step : Nat := mb * (← envNat "REPL_MEM_STEP_MB" 300)
  let offN : Nat := ← envNat "REPL_OFFENDER_N" 2
  let offMs : Nat := 60000 * (← envNat "REPL_OFFENDER_MIN" 60)
  let wlog (line : String) : IO Unit := do
    IO.eprintln s!"[watchdog] {line}"
    IO.FS.withFile (dir ++ "/watchdog.log") .append fun h => h.putStrLn line
  let _ ← IO.asTask (prio := .dedicated) do
    -- RSS right after the last cancellation finished (Lean's allocator keeps freed pages, so RSS may stay
    -- above the limit afterwards; the next soft cancellation then needs `step` MB of new growth)
    let mut base : Nat := 0
    let mut offenses : Std.HashMap String (List Nat) := {}
    repeat
      if ← System.FilePath.pathExists stopFile then break
      IO.sleep 500
      let rss ← rssBytes
      if rss ≤ limit then
        base := 0
        continue
      let isHard := rss > hard
      if !isHard && rss ≤ base + step then continue
      let rs ← running.get
      let mut live := #[]
      for e in rs do
        if !(← e.2.2.2.isSet) then live := live.push e
      let some e0 := live[0]? | continue
      let now ← IO.monoMsNow
      -- culprit: the longest-running request that has run >= 10 s (runaway simp/omega/whnf grow over time),
      -- else the most recently started one
      let oldest := live.foldl (fun (a : (String × String × Nat × IO.CancelToken)) e =>
        if e.2.2.1 < a.2.2.1 then e else a) e0
      let newest := live.foldl (fun (a : (String × String × Nat × IO.CancelToken)) e =>
        if e.2.2.1 > a.2.2.1 then e else a) e0
      let culprit := if now - oldest.2.2.1 ≥ 10000 then oldest else newest
      let victims := if isHard then live else #[culprit]
      let desc := live.toList.map (fun e => s!"{e.1}/{e.2.1}({(now - e.2.2.1) / 1000}s)")
      -- repeat offenders: the culprit's client loses its committed environment
      let d := culprit.1
      let ts := (offenses.getD d []).filter (fun t => now - t < offMs) |>.cons now
      offenses := offenses.insert d ts
      if ts.length ≥ offN && d != dir && !culprit.2.1.startsWith "replay:" then
        IO.FS.writeFile (d ++ "/drop") "watchdog: repeat offender\n"
        IO.FS.writeFile (d ++ s!"/watchdog_dropped.{now}") s!"{ts.length} watchdog cancellations within {offMs / 60000} min: environment dropped; re-commit (smaller goals)\n"
        wlog s!"{now} auto-dropped the environment of {d} ({ts.length} cancellations within {offMs / 60000} min)"
        offenses := offenses.insert d []
      for v in victims do v.2.2.2.set
      wlog s!"{now} rss={rss / mb}MB {if isHard then "HARD" else "soft"} cancelled {culprit.1}/{culprit.2.1}{if isHard then s!" (+all {victims.size} running)" else ""}; running: {desc}"
      -- wait (<= 60 s) for the cancelled requests to stop, then take the new baseline
      for _ in [0:120] do
        let rs2 ← running.get
        if victims.all (fun v => !rs2.any (fun e => e.1 == v.1 && e.2.1 == v.2.1)) then break
        IO.sleep 500
      base ← rssBytes
      wlog s!"{← IO.monoMsNow} after cancel: rss={base / mb}MB"
  repeat
    if ← System.FilePath.pathExists stopFile then break
    -- forget finished (dropped) clients so their directory can be served again
    let mut live := #[]
    for (d, t) in tasks do
      if ← IO.hasFinished t then clients := clients.erase d else live := live.push (d, t)
    tasks := live
    try
      for e in ← System.FilePath.readDir dir do
        -- note: `(← x)` inside `&&` is evaluated eagerly, so test the cheap conditions first
        if !(e.fileName.startsWith "c_") || clients.contains e.path.toString then continue
        if !(← e.path.isDir) then continue
        if ← System.FilePath.pathExists (e.path.toString ++ "/drop") then
          -- not served: nothing to release; consume the request so the dir can be served again
          clearCommitted e.path.toString
          IO.FS.rename (e.path.toString ++ "/drop") (e.path.toString ++ s!"/dropped.{← IO.monoMsNow}")
        if !(← hasPending e.path.toString) then continue
        if tasks.size > maxClients then
          -- the root client is task 0; c_* clients beyond the cap wait
          IO.FS.writeFile (e.path.toString ++ "/waiting") s!"server at {maxClients} clients; drop one\n"
          continue
        if ← System.FilePath.pathExists (e.path.toString ++ "/waiting") then
          IO.FS.rename (e.path.toString ++ "/waiting") (e.path.toString ++ s!"/waited.{← IO.monoMsNow}")
        clients := clients.insert e.path.toString
        tasks := tasks.push (e.path.toString, ← IO.asTask (serveClient running e.path.toString env0 stopFile) (prio := .dedicated))
    catch e => IO.eprintln s!"client scan: {e}"
    IO.sleep 1000
  for (_, t) in tasks do
    let _ ← IO.wait t
