# lazerproof: evaluate an osu! score with the verified evaluator

lazerproof is a community project, not affiliated with ppy.

`tools/lazerproof` (stdlib-only Python, run as `python3 -I`) resolves a score and evaluates it with `osu_eval`
(impl/osu_eval, the Rust evaluator proved against the Lean model), then compares the result with the osu! server.

```
lazerproof https://osu.ppy.sh/scores/7737706899        # lazer score URL
lazerproof https://osu.ppy.sh/scores/osu/4900932197    # legacy (stable) score URL
lazerproof 7737706899                                  # bare score id
lazerproof replay.osr --beatmap map.osu                # offline: no credentials, no network
lazerproof replay.osr                                  # beatmap looked up by the replay's md5
lazerproof 7737706899 --json                           # raw osu_eval JSON + "server_comparison" block
```

Other options: `--mods JSON` (merged with the replay's mods; `--replace-mods` replaces them), `--schedule
catchup|perframe|dense1ms` (default catchup, as the server-agreement pipeline), `--offline`.

- **Output**: player, map, mods, total score, accuracy, rank, max combo, hit counts; for score ids "matches osu!
  server" or a field-by-field difference (ours vs server). Exit status 0 = match (or no server score), 1 = differs,
  2 = error. pp is not computed; the server's pp is shown as "(server, not verified)".
- **Comparison** (same rules as `difftest/oracle_vs_server_v2.py`): lazer scores compare every statistic,
  maximum_statistics, max_combo, accuracy (server float32, 6 dp), total_score, rank and passed. Stable scores compare
  300/100/50/miss, max combo and stable accuracy (as the v1 corpus check); the server's total_score for them is a
  conversion of the stable score and is not compared. Small slider-tail/tick differences are expected on some replays
  (live play vs integer-ms replay; docs/server-agreement.md).
- **Mods**: like the pipeline, osu_eval uses the replay's own mods (lazer .osr JSON, or the legacy bitmask + CL);
  the server's mods are checked against them and any difference is printed as a note.
- **Data**: `/api/v2/scores/{id}` (or `/scores/osu/{legacy_id}`), `/api/v2/scores/{id}/download` (>= 6.5 s between
  downloads, back-off on 429), `https://osu.ppy.sh/osu/{beatmap_id}` with an md5 check against the replay, and
  `/api/v2/beatmaps/lookup?checksum=` for a bare .osr. Cached under `~/.cache/lazerproof/{scores,replays,beatmaps}`;
  inside this repo the corpus (`data/beatmaps`, `data/replays*`, `data/index_v2.sqlite` when offline) is also read.
- **Credentials**: `OSU_CLIENT_ID` / `OSU_CLIENT_SECRET`, or `~/.config/lazerproof/config` (`client_id = ...`,
  `client_secret = ...`). Register an OAuth application at https://osu.ppy.sh/home/account/edit.
- **osu_eval**: `$OSU_EVAL`, else `impl/target/release/osu_eval` (built with `cargo build --release -p osu_eval`
  via tools/heavy when missing).

Tested 2026-10-23 (all "matches osu! server", as the corpus): 7737708734 (HT 0.85 + DA cs/ar settings),
7737706899 (HR+DT+PF+FL; fresh API download into an empty cache), https://osu.ppy.sh/scores/osu/4900932197 (stable
HD+HR), plus `data/replays_v2/7737721400.osr --beatmap ...` offline without credentials. 7737721523 (HR+DT) reports
IgnoreMiss/LargeBonus differences, which the corpus classifies as `sched` (spinner bonus).

## Platforms (D86)

The evaluator's floating-point results must be bit-identical to glibc 2.39's x86-64 `libm` (the trusted float row,
docs/proof-pipeline.md §4/§5). A platform's own libm (macOS, musl, Windows) gives different bits for sin/cos/pow/...,
so it is never used.

- **x86-64 Linux (glibc)**: the default build dlopens the system `libm.so.6` and `liblzma.so.5` (the setup the proofs
  and corpus runs use).
- **macOS (Apple Silicon and Intel) and other non-Linux targets**: `cargo build --release -p osu_eval` (or just running
  `tools/lazerproof`, which builds it when missing) automatically uses the *vendored* build: the glibc 2.39 sources
  of the 23 libm functions osu_eval calls (`impl/osu_eval_core/vendor/glibc-libm`, with glibc x86-64's FMA
  contractions written as explicit `fma` calls and compiled with `-ffp-contract=off`, so any compiler and CPU gives the
  same bits) and the xz 5.4.5 `.lzma` decoder (`vendor/xz`), compiled by `impl/osu_eval_core/build.rs` and linked
  statically. Needs only rustup (stable) and a C compiler: on macOS the Xcode command-line tools
  (`xcode-select --install`).
  ```
  git pull && cd impl && cargo build --release -p osu_eval && cd .. && tools/lazerproof 7737706899
  ```
- **Linux, vendored**: `cargo build --release -p osu_eval --features vendored` (both), or `vendored-libm` /
  `vendored-lzma` separately (`CC=clang` works as well as gcc).
- Status: validated bit-identical to the VM's glibc 2.39 (every f32 input, >= 2.5e9 inputs per f64 function, every
  libm call on the 20,476-run corpus regression; also on aarch64 under qemu), docs/proof-pipeline.md §5.2.
- Linux on an x86-64 CPU without FMA/AVX2 (pre-Haswell Intel, pre-Zen AMD): glibc picks different (SSE2) variants
  there, so use `--features vendored`.
- Windows: not supported (MSVC has no `__builtin_fma`); use WSL2 (x86-64 Linux).

> **Since D97:** `tools/lazerproof` always builds and uses the vendored build (in `impl/target/lazerproof/`) on every platform, including Linux, so its results never depend on the CPU. It rebuilds automatically after a `git pull` changes the Rust sources. The proof pipeline keeps the default (dlopen) build in `impl/target/`.
