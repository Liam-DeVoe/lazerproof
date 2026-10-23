# Model architecture (owner: main agent)

## Top-level shape (implemented: `OsuModel.Eval.evaluate`, docs/model-eval.md)
```
evaluate : Env → (beatmap : ByteArray) → (osr : ByteArray) → Options → Schedule → Except Rejection Result
  = let d     := Beatmap.LegacyBeatmapDecoder.decode beatmap          -- OsuModel/Beatmap
    let sc    := Replay.Osr.decode osr                                -- container, LZMA (trusted), lazer JSON mods, auto-Classic
    check  getPlayableBeatmap d sc.bitfieldMods                       -- decode-time playable (LegacyScoreDecoder.cs:94): may only throw
    let mods  := resolveMods sc.mods opts                             -- oracle --mods/--replace-mods/--no-classic; Autoplay rejected
    let pb    := Eval.toSimPlayable (getPlayableBeatmap d mods)       -- OsuModel/Eval/Adapter (lossless vs oracle --dump-playable)
    let fr    := Replay.decode sc.frameText pb.beatmapVersion         -- OsuModel/Replay/Frames
    let steps := Sim.steps schedule fr pb                             -- FSC + SetFrameFromTime (mirrors oracle/Schedule.cs)
    Sim.run env (Config.ofMods mods pb) pb fr steps                   -- OsuModel/Sim
```
Executable `evaltest` (oracle-like CLI and JSON schema); harness `difftest/eval_diff.py`.
- **Schedule is an input (D9).** Equivalence claims are ∀ schedules. "Canonical" result uses `catchup`.
- **Env (D10)** fixed to 1024x768/default config, but represented explicitly (the screen-space matrices are data).
- **Rejections (ISSUES G12):** every input on which lazer throws (where modelled) yields `Rejection {stage, reason}`.
- **Trust boundary:** LZMA decompression of .osr payloads (`model/c/lzma_shim.c` → system liblzma, linked into
  `evaltest` only; lazer: SharpCompress);
  glibc transcendentals (opaque, pinned 2.39). Everything else is modelled.

## Interfaces (so pieces are testable independently)
- `PlayableBeatmap` = list of hit objects with all nested objects + per-object derived fields, exactly what
  `GetPlayableBeatmap` yields. The oracle can dump it (`--dump-playable`), the beatmap model produces it; the sim model
  consumes it. Hence: sim model is diff-tested using the *oracle's* playable dump first, beatmap model is diff-tested
  against the same dump; composition then follows.
- `Frames` = decoded `OsuReplayFrame` list (time: double, position: float32×2, actions).
- `Result` = ordered judgement list (object/nested id, HitResult, RawTime, combo/health after) + final stats, score,
  accuracy, rank, fail info (both semantics). Same schema as oracle JSON.

## Sim model structure (mirrors §3.1 of lazer-map)
State: FSC time, replay frame index, input state (pressed actions, last cursor pos, hover set), per-DHO state
(alive, judged, result, head/tail/tick states, slider tracking + `SliderInputManager` state, spinner rotation tracker &
spin history), hit policy state, score/health processor state, mod state.
`step : State → StepTime → State` runs phases: processors(drain) → input(pos/hover/mousemove/releases/presses) →
playfield mod updates → lifetime → DHO updates in container order (nested before parent).
Results emitted in exactly the processor-visible order.

## Ratchet (milestones; each must pass 100% diff vs oracle before the next)
- M0: circles only, NoMod (`--no-classic`), StartTimeOrdered policy; synthetic + real circle-only maps.
- M1: + Classic (LegacyHitPolicy, Classic head behaviour) — all real stable replays have Classic.
- M2: + sliders (head/ticks/repeats/tail, tracking, classic slider behaviour), M3: + spinners,
- M4: health/fail (both semantics), score/accuracy/rank exact, M5: difficulty mods (EZ/HR/DA/DT/HT/NC/DC etc.),
- M6: input mods (Relax/Autopilot/Alternate/SingleTap/…), M7: object-transform mods (Grow/Deflate/…/Magnetised/…), M8: rest.
- Then: Rust impl mirroring the Lean function-by-function; proof of refinement.
