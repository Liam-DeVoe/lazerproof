# RESUME after reboot (machine upgrade 2 vCPU/3.8 GB → 4 vCPU/8 GB, 2026-10-21)

Read this file, then STATE.md (rules + progress log), DECISIONS.md, ISSUES.md. Each section below was written by the
agent that owned the area at checkpoint time; relaunch one agent per section with that section + the standard
rules preamble (STATE.md SAFETY/MODELLING/HEAVY/MEMORY/DISK rules).

**Git rules for every agent (put them in every agent prompt):** D75: agents share ONE git index, so commit only with
explicit paths: `git commit -m "..." -- <your paths>` (a plain `git commit` also commits whatever other agents have
staged). D56: no history rewriting on main (no amend, rebase, reset, cherry-pick-then-reset); fix mistakes with a
follow-up commit. Never push; never commit secrets (~/.osu_credentials).

## Main (orchestrator) checklist after boot
1. Sanity: `nproc` (4), `free -m` (8 GB), `df -h /`, `systemctl status osu-status earlyoom cron`, status page
   https://osu-judgments.exe.xyz/ renders (cron render.py every 5 min).
2. Re-tune for the bigger machine (then record in STATE.md):
   - tools/heavy: HEAVY_SLOTS default 2 → 3 (keep 1 vCPU headroom for agents/builds); HEAVY_EXCLUSIVE min mem 3000 → 6000.
   - MEMORY BUDGET: single process ≤ ~1 GB → ≤ ~2 GB; Aeneas sim+replay (OOMed at ~2.3 GB) should now fit under HEAVY_EXCLUSIVE.
   - Swap: 2 GB is fine; disk is the tighter resource (~3 GB free at checkpoint).
3. Background services that do NOT auto-restart: `difftest/oracle_v2_loop.sh` (+ triage hook) — see server section.
   Crawlers are restarted by cron watchdogs (crawl_watchdog.sh, crawl_v2_watchdog.sh) automatically.
4. /tmp is preserved across boot (/etc/tmpfiles.d override), but anything needed for resume was also copied to
   data/wip/<area>/. Stale lock files in /tmp/osu-heavy are harmless (flock locks die with processes).
5. Relaunch agents for: server agreement/triage, Lean sim totality (G17), end-to-end eval re-run, Rust sim port (M7
   verification + M8), refinement proofs. Then NEXT items in STATE.md (coverage measurement, continuous difftest).


## Lean sim mods / totality (G17)

**DONE, commit e0e8215:** G17 is closed (ISSUES), and all M5–M8 sim mods are bit-exact.
- The totality refactor landed (`data/wip/sim-totality.patch` is now obsolete):
  - No panicking or defaulting accessors remain.
  - `SimM` is over `Except String`.
  - Fuel exhaustion and lazer-throwing computations reject.
- Build fixes needed after applying the patch:
  - Structure-instance fields after `return {` must start on their own line (column rule).
  - Osr `readLE` uses a positive `if hb : … ≤ …` (the negated branch hypothesis is not in scope after `if … then throw`).
  - `raw : ByteArray` annotation in Osr.
  - **Bug:** `classicHead` used `&&` with a nested `(← sliderData …)`, which is hoisted and so evaluated for circles too.
- Regression: 35 corpora 1451/1451, 0 PANIC, 0 rejections; eval 40/40.
  - Rerun with `data/wip/sim-totality/reg.sh` on the `w_*` dirs in `/tmp/claude-1000/-home-exedev/0a1445fc-4537-4d02-8a4a-bd6503e72f8c/scratchpad/simmods`. It makes one `tools/heavy` call per corpus, with `NAME:LIST:POOL:SEED:SCHED` arguments as listed in docs/model-sim.md / results.jsonl there.
- Perf fix (2026-10-22): the G17 slowdown came from copying arrays in `modifyObj`/`modifyInst` and from Except
  allocations in accessors that were not inlined. Now `checkIdx` + `modify`, plus `@[inline]` accessors. evaltest is back to
  pre-G17 speed (commit 1b0a176; pinned simtest data/wip/rust-sim/simtest_lean_1b0a176; Rust f3cc2a1 output is identical: 4092/4092
  runs, 1680 of them identical rejections, so the Rust port does not need to follow). Regression via `data/wip/sim-totality/reg.sh` args, all 35 corpora 1451/1451. See docs/model-sim.md "Totality".
- Open items in this area:
  - Optionally, prove the remaining `getA` sites in bounds, so that `internal:` errors are provably unreachable.
  - (done, D27) `Sim/ModsJson.lean` is total now.

**Gotchas:**
- Perf: never `let s ← st; … set { s with xs := ← setA s.xs … }` on a large array (it copies the array); check the index, then `modify`. Keep the small `SimM` accessors `@[inline]`.
- Lean `do`: a `return` inside `← match … | _ => do return x` exits the whole function, so use `pure`.
- Never put a nested `(← e)` inside `&&`/`||`/a condition when `e` may reject. It is hoisted and evaluated unconditionally.
- Structure-instance fields must align with the column of the first field.
- `omega` needs `have hu : i < n := h.upper`, and `if h :` is needed for branch conditions.

## Rust sim port
Owner area: impl/osu_eval_core/src/{sim,replay}/*, impl/simtest_rs, difftest/rust_sim_diff.py, impl/tools/{run_chunks.py,mk_pairs.sh,bench_sim.py,rsconst.py}, docs/rust-sim-port.md.

**Done (all committed; current pin = Lean `e0e8215`, Rust f3cc2a1):**
- M0-M4 + NF/CL (`3f88501`): 15,600/15,600. M5/M6 (`3f88501`, c949ed3): 5,920/5,920. M7 (`7cffd29`, f0f6889): 6,540/6,540 (e38d0c2).
- `171dd71` (AP MouseMove -> cursorPos, 5afe1a5): 2,980/2,980.
- `e0e8215` G17 total sim (f3cc2a1): `Result<_, SimErr>` (sim/err.rs; D16), `simtest_rs` prints the spec's exact
  `{"error":"sim: …"}`. 10,492/10,492 (1,680 identical rejections), 0 Lean PANIC, 1.91M judgements.
- Aeneas on sim+replay (`HEAVY_EXCLUSIVE=1 OUT=<scratch> tools/heavy impl/charon_check.sh --start-from crate::sim --start-from crate::replay`):
  0 errors, 0 sorry, 2.6 GB peak, ~6 min. Generated Lean not type-checked yet. Loop/early-exit rules in docs/rust-sim-port.md "Translatability".

**Pinned binaries / corpora (data/wip/rust-sim):** simtest_lean_{7cffd29,171dd71,e0e8215}, simtest_rs7.bin, simtest_rs_171dd71.bin,
simtest_rs_e0e8215c.bin (= f3cc2a1). Corpora: synA-D, real40, `simmods/w_*` (18 oracle job-mod corpora, copied out of the old
scratch; paths rewritten), `apmg_*.txt` (AP+MG/RP job mods, impl/tools/mk_apmg.py), `rej/` + `rej_pairs.txt` (mutated playables hitting the rejections;
generator impl/tools/mk_rej.py: mutations notail/nohead/emptypath/shortcum/breakafter/badperiod/drainflip/hpnan x 8 mod lists).
Plans: plan_m7{,a,b}.json, plan_171.json, plan_e0{a,b,c}.json; results_*.jsonl (dedupe by label when aggregating).

**How to pin and verify a new Lean Sim commit X:**
1. `git worktree add --detach <scratch>/lp X && cp -a model/.lake <scratch>/lp/model/ && (cd <scratch>/lp/model && LEAN_NUM_THREADS=1 tools/heavy lake build simtest)`;
   copy `.lake/build/bin/simtest` to data/wip/rust-sim/simtest_lean_X; `git worktree remove --force <literal path>`.
2. Port `git diff e0e8215 X -- model/OsuModel/Sim model/OsuModel/Replay model/SimTest`; `tools/heavy cargo build --release -p simtest_rs`; copy the binary.
3. Copy a plan (e.g. plan_e0a.json) with new labels/env; `python3 -I impl/tools/run_chunks.py PLAN` (2 in parallel max); require mismatch 0, lean_panics 0.
4. Re-run Aeneas (exclusive, above) after structural changes.

**Next steps:** none open in this area except: port later Lean Sim diffs (none after e0e8215 as of 2026-10-22); type-check the
generated sim Lean in proofs/ (refinement-proofs agent); exercise the unexercised rejection classes (fuel, NaN signs) if a cheap
input is found.

**Gotchas:**
- Never wrap a multi-step script in one `tools/heavy`; use run_chunks.py. A queued HEAVY_EXCLUSIVE job holds the gate and blocks
  every new heavy job until memory frees (the proofs REPL holds ~2 GB): only queue it when MemAvailable is already > 3.5 GB.
- `pgrep -f` / `pkill -f` patterns match the shell running them: do not put the pattern in the same command line you wait in.
- Compare against a Lean simtest built from the pinned commit. The working-tree binary may contain other agents' WIP.
- Lean prints a `PANIC` to stderr while its stdout still looks valid. rust_sim_diff counts these as `lean_panics`, and they must be 0.
- Float constants in the Rust code use `c64!(lit)` markers expanded by `impl/tools/rsconst.py` (run it after editing).
- `crate::schedule` is the proof-POC copy of the pre-G17 simulateSteps; the sim uses `sim::schedule::simulate_steps`.

## server agreement / triage (lazer scores vs live server stats; D13, docs/server-agreement.md)

**PAUSED 2026-10-22 04:20 UTC** (orchestrator: machine time goes to the refinement proofs). Nothing of mine is
running. `data/oracle_v2/STOP` exists, so oracle_v2_loop.sh is not running. The crawler cron
(`difftest/crawl_v2_watchdog.sh`, bound 8000, stops below 10 GB free) is untouched and light (network only).

**State.**
- Catchup has been evaluated on 5113 scores: 63.1% exact, 35.2% sched.
- 959 of 1886 mismatches are triaged: demonstrated 570, heuristic-sched 360, suspicious 27, old perturbation 2.
- 927 mismatches are untriaged.
- Suspicious headline: 46/5113 (0.90%).
- Report: `data/oracle_v2/report.md`; metrics: `status/metrics.json`.
- Mechanisms: note-lock 397, spinner-alias 86, schedule 34, same-frame-split 32 (new: RX release+press in one Update), regain-rounding 1, replay-gap 6, and others.
- Open cases are listed in docs/server-agreement.md "Open suspicious cases" and ISSUES G16/G18. AL G18 is localised; HTNF, GR×4, AP, HDHR 7738056594, DA 7738080249, DANF 7737892997 are open.

**Restart (from ~/lazerproof).** Kill only these PIDs; never use `pkill -f`.
```
mv data/oracle_v2/STOP data/oracle_v2/STOP.old    # (or rm that literal path)
setsid nohup sh difftest/oracle_v2_loop.sh >> data/oracle_v2/loop.log 2>&1 < /dev/null &
setsid nohup nice -n 15 python3 -I difftest/triage_v2.py --new --max-shift-runs 150 >> data/oracle_v2/triage.log 2>&1 < /dev/null &
```
- Triage uses the pinned binaries in `data/oracle_v2/pinned/{simtest_rs,simtest,evaltest}` (D13a). Refresh them with `cp -p` when the sims gain features. Env `TRIAGE_{EVALTEST,SIMTEST_RS,SIMTEST_LEAN}` overrides them.
- Budgets: `TRIAGE_SHIFT_BUDGET_S` (default 300 s) for note-lock singles and the press-shift search. Maps with a playable dump over 6 MB get a reduced search.
- The backlog rate is about 3 scores/min on the loaded VM, and the loop keeps adding mismatches.
- After the restart, retriage the entries made with the old perturb or the old heuristic. Use `--retriage --ids` on the source=triage_v2 entries with triaged_at < 2026-10-21T22:27Z, except schedule/spinner-alias/replay-gap. This matters mainly for the CL classic-slider Great/Ok cases 7737759694 and 7737822303, which are now heuristic-sched.
- The 2 "perturbation" entries are old manual ones and need a geometric threshold check.

**Tools.**
- `triage_v2.py` steps: replay-gap → note-lock (single shifts under catchup and dense1ms, then all) → schedules → same-frame merge → de-alias → press-shift.
- Every run is gated against the oracle's catchup result. `score_exact` = max_combo and total_score also match.
- Scratch analysis scripts (force-miss search by score, relabel, AP fps sweep via `oracle_vs_server_v2.py run --schedule fineN --ids F --out-tag _ap`) are described in docs/server-agreement.md.

**Gotchas.**
- Never use `pkill -f` or `pgrep -f`: the pattern matches your own shell. This includes `crawl_v2_watchdog.sh` run from a shell whose command line contains "fetch_v2.py crawl".
- The loop script must be replaced with `mv`, not edited in place.
- Server accuracy is f32, served rounded to 6 dp. Normalise mod values before comparing.
- RX does nothing in playback of lazer replays. AP is frame-rate dependent: it advances one autoplay frame per Update.
- `perturb` keeps frame order now. Old results from before 2026-10-21 22:00 that used it may be artefacts.
- `oracle.sh` runs under tools/heavy and keeps a result cache.

## end-to-end eval

**Done** (docs/model-eval.md; code: model/OsuModel/Eval.lean, Eval/Adapter.lean, Eval/Env.lean, Replay/Osr.lean, model/c/lzma_shim.c, EvalTest/Main.lean, difftest/eval_diff.py):
- `evaltest BEATMAP OSR [--schedule S|explicit:F] [--mods JSON] [--replace-mods] [--no-classic] [--sim-playable ORACLE_DUMP] [--dump-playable P]` = oracle schema, doubles as hex bits.
- 95499c3: `Eval.defaultEnv` has the HOC ancestor chains (was empty -> every BR mismatch; eval-side, not sim). Sim BR geometry
  verified per step vs an ORACLE_DHO_STATES dump.
- G17 (e0e8215) regression, evaltest built at 5c15cfb: 1673/1673 (stable per-M7 165, M5/M6/M7 60 each, ALL 80, BR stress 60;
  lazer own catchup 800, perframe 388). Lists: data/wip/end-to-end-eval/h_*.txt, v2c_cu.txt, v2c_pf.txt; results g17_*.
- Lazer coverage: 2962/2962 of the 5141 v2 scores (catchup, 3.05M judgements) at 2026-10-22 ~00:40.

**Running (detached)**: `data/wip/end-to-end-eval/cov/loop.sh` (EVALTEST = data/wip/end-to-end-eval/bin/evaltest, a copy of
the 5c15cfb build). Each round: pick.py lists every oracle-cached v2 catchup job not yet evaluated, plus 50 uncached from
the highest ids when fewer than 50 are cached (the oracle_v2 loop walks ids upwards and then hits our cache entries).
Results cov/r_catchup_NNN; totals: `python3 -I data/wip/end-to-end-eval/cov/agg.py`. Stop: `touch .../cov/STOP`; restart:
`nohup data/wip/end-to-end-eval/cov/loop.sh > data/wip/end-to-end-eval/cov/loopN.log 2>&1 &` (resumes).

**Re-run** (cached oracle results; build evaltest in a HEAD worktree: `git worktree add --detach W HEAD`, copy
model/.lake/build/{lib,ir}, `tools/heavy lake build evaltest`, `export EVALTEST=W/model/.lake/build/bin/evaltest`):
`python3 -I difftest/eval_diff.py run [--replace-mods] [--schedule S] --list LIST --work DIR --tag T`.
**Localising a mismatch**: `ORACLE_DHO_STATES=1 oracle.sh run ... --dump-env E --dump-playable P`, then `simtest --playable P
--env difftest/env-1024x768.json` (simtest matches but evaltest not -> eval-side: adapter/env/mods). Per-step comparison
scripts data/wip/end-to-end-eval/br/cmp_{hoc,sl,mouse}.py (ENV_DUMP TRACE; oracle probe k = model state after step k-1;
TRACE lines `H k t brRot hocM hocInv` / `S k i sliderM sliderInv tracking mouse` from a throwaway `simtest --trace-hoc` patch: loop of `Sim.run`, print `curHoc`/`curSliderGeom` after each `stepOnce`).
**Next**: let the coverage loop finish the corpus, then update docs/model-eval.md + metrics "A."; perframe coverage of the
oracle-cached perframe jobs (pick.py takes the schedule as argv[1]; loop.sh is catchup-only); rebuild data/wip/end-to-end-eval/bin/evaltest at the sim
perf-fix commit, which runs about 2x faster on long maps (byte-identical).
**Gotchas**: the oracle cache key includes the oracle dll hashes — any oracle rebuild/swap invalidates all cached results.
Cache-hit runs bypass tools/heavy. `pgrep -f PATTERN` inside a shell loop matches the loop's own command line — wait on a
PID or a file instead. Error lines are never cached. Editing a running bash script with sed -i is safe (new inode).

## refinement proofs (net+beatmap Rust -> Lean spec, Charon/Aeneas)

**Status (2026-10-22 ~08:00)**: **223/558** net+beatmap fns proved (docs/proof-status.md; proofs/audit.txt:
234 theorems, axioms propext/choice/Quot.sound only; `tools/heavy proofs/scripts/check_all.sh` passes).
All of `net::*` is done except `net.osutk.m3_row` (trivial, missed). Beatmap done: chartable, control_points (all 18),
dotnet leaves (compare_f64, fmod*, is_white_space, nat_sub, log2, insert_at).

Files (proofs/OsuProofs/, all imported by OsuProofs.lean): Prims, Repr, Spec/FloatFacts, Loops, SpecLoops (forIn ->
`iterId`/`iterEx`), Net/{OsuTK,Basic,MathOps,SysMisc,FrameworkA,Random,Parse,Parse2,Decimal..Decimal9,DecimalValid,
FrameworkB,FrameworkC}, Beatmap/{Vector2,CharTable,DotNet,ControlPoints}.
Decimal4-9: 192-bit helpers, ScaleResult (Rust loop in lockstep with the spec loop; a potential `it+ceil(num/9)+2sc<=119`
shows the 120-iteration budget is never exhausted), VarDecMul, VarDecDiv (40-step loop lockstep; `searchScale_le` keeps
scale <= 28). DecimalValid: spec-level validity (mant < 2^96, scale <= 28) of CreateTruncating, /, *, Round results,
used to discharge the guards when chaining (FrameworkC: BindableNumber snapping, BD/BF create/init/setValue/Precision).

**Automation (2026-10-22, orchestrator priority)**: OsuProofs.lean = `OsuProofs.Manual` (hand proofs; add new
hand files there) + `OsuProofs.Auto.Gen`. Pipeline (all in proofs/scripts):
`repl_server.sh start` (shared multi-client REPL, header OsuProofs.Manual) ->
`auto_setup.sh $PROOF_REPL/c_auto <workdir>` (commits Auto/Abs.lean, generated AbsTo instances, constant lemmas,
@[step] wrappers of hand theorems; checked block by block) -> `REPL_DIR=$PROOF_REPL/c_auto auto_prove.py <workdir>/gen.lean`
-> assemble Auto/Base.lean (abs_ok + consts_ok + steps_ok) and Auto/Gen.lean (gen) exactly as in commit c23fcf8
-> check_all. Auto statements: `∃ r, f args = ok r ∧ spec (abs a..) = abs r`. First pass: 17/208 closed; blockers are
loops (60 direct, most of the 107 "missing callee") and "—"-helpers without spec def.
Other agents: one client dir each via `req.sh <agent> <name> file`; never a separate REPL (2.6 GB each). Server anon
memory grows with every client's committed env: drop idle clients (`touch $PROOF_REPL/c_<x>/drop`), keep commit chains
short; the lead restarts the server when anon > ~4 GB (announced in STATE Requests; clients must re-commit).

**Loop templates (LoopsR.lean, 2026-10-22)**: `loop_iterR` (Rust index loop vs spec `for j in [lo:hi]`/`for x in l`
/`Array.any`/`findIdx?`/`foldl`/`map`, via `forIn_range_iterR`, `forIn_list_iterR`, `any_iterR`, `findIdx_iterR`,
`foldl_iterR`, `map_iterR`; a spec `done` may take one extra Rust iteration (flag loops)); `loop_whileR` (Rust loop vs
Id `while`, i.e. `forIn Lean.Loop.mk`, with a decreasing measure); `loop_push_map` (Vec::push loops = `List.map`).
Worked examples: Beatmap/ModsLoops.lean (linq_max_f64: while + for), Post/TargetPractice.lean (inside_break: nested
any + find?), Beatmap/ModRandomBase.lean (modify_slider loop). Pattern: pass the spec loop body explicitly (copy it
from `unfold spec; simp only [Id.run]` output) with `hF : ∀ s, F () s = … := fun s => rfl`; in step obligations use
`rw [if_pos hc] at hs'; cases hs'` (not simp: it rewrites `l[j]!` to `getD`). `OsuProofs/Post/*` = hand proofs that
use Auto lemmas (imported after Auto.Gen in OsuProofs.lean; gen_steps skips them; write their @[step] by hand).
Index-fold automation: `loop_fold_gen' body ix n hn Inv rep G out (by loop_step [f_loop.body, callee lemmas..])
(by loop_end [f_loop.body]) t0 hInv0 hle` (body in projection style `fun x => f_loop.body args x.1 x.2`; spec side
`iterR (fun k s => .yield (G k s))`; push loops: `vec_push_ok`/`vpush_val`, Inv must carry `len = ix` and the source
length ≤ Usize.max; in-place loops: `vec_index_mut_usize_ok`, `vec_set_val'`, `list_modify_set`, then
`iterR_modify_map`). Example: Post/Processor.lean `set_stack_height_refines`. auto_prove.py closes few fns now (4/93 at
08:10, all already hand-proved): the agents' hand proofs + these tactics are the throughput path.
Regen policy: only on a "regenerate Generated for <commit>" request in STATE Requests, batched, in a window.
Infra lead (2026-10-22 16:20, D39-D45, D52): window = announce in STATE ~15 min ahead, then
`tools/heavy proofs/scripts/check_all.sh` (it stops the shared REPL, holds /tmp/osu-heavy/check_all.lock, restarts the
REPL at exit; rc 3 = PARTIAL: failed/sorry modules excluded and listed) + `python3 -I proofs/scripts/proof_status.py`
(proved / CONDITIONAL / FRAGMENT, D44) + commit audit.txt/proof-status/metrics + STATE note listing failing files and
owners. Commit chains replay by themselves (c_*/committed/, D41). Watch $PROOF_REPL/watchdog.log, c_*/replay.log,
server.log ([req] markers; rotated server.log.<ts>).
Server rules (Repl.lean): memory watchdog (RssAnon > 3900 MB: the longest-running (>=10 s) request is cancelled; > 4500 MB all;
repeat offenders lose their env; logged in $PROOF_REPL/watchdog.log); clients idle 30 min auto-dropped, max 8 clients (extra dirs get `waiting`), a c_* dir takes a
slot only while it has an unanswered request; check_all
every ~2 h by the infra lead, announced in STATE Requests (server stopped meanwhile).

**How to work** (REPL loop, ~1-20 s per check):
- REPL: `S=<scratch>; $S/repl_start.sh` runs `lake env lean --run scripts/Repl.lean $S/repl` niced, inside
  `systemd-run --user --scope -p MemoryMax=2800M` (a runaway request then kills only the REPL; it happened 4x: see
  gotchas). `$S/repl/header` lists modules to import: use *built* modules (e.g. `OsuProofs.Net.Decimal7` +
  `OsuProofs`; build new ones first with `tools/heavy lake build OsuProofs.Net.X`) - import is 2-12 min depending on
  load; then `$S/mkreq.sh NAME [--commit] FILE..` (request names are processed in name order: use lowercase names
  after a reload's z001.. commits). `$S/repl_reload.sh FILES..` restarts and commits files in order.
  Scripts live in the scratchpad; recreate from this description if lost.
- Safer for risky proofs: standalone `systemd-run --user --scope -q -p MemoryMax=2600M lake env lean file.lean` with
  `import OsuProofs.Net.X` (5-8 min per run, never kills the REPL).
- Build/audit: `tools/heavy proofs/scripts/check_all.sh` then `python3 -I proofs/scripts/proof_status.py`.
  Stop the REPL during check_all (both ~2.5 GB).

**Proof patterns / gotchas** (in addition to the ones in the files' headers)
- `omega` inside a big context (many hyps with `/`, `%`, casts, 2^192) can blow memory (heartbeats do not stop it):
  prove arithmetic facts as standalone lemmas or use `clear * - h1 h2; omega`. Never put `(by omega)` where the goal
  still has a metavariable (e.g. `rw [lemma _ (by omega)]`) - pass the fact explicitly.
- `split at h` picks inner ifs: `generalize` the inner subterm first, or `by_cases` + `rw [if_pos c] at h`.
- `rw [if_pos (by simp ..)]` with an unspecified condition rewrites the first ite found: state the condition (`show`).
- `simp only [decS]` on goals with `if` breaks Decidable instances (motive errors): rewrite conditions with `show`
  facts in decS form first, unfold decS only once no ite depends on it.
- Theorem statements `P (match st with ..)` where `h : f = .ok st` is in scope elaborate as `match st, h`: use a
  helper projection function (`fisS`, `fisR`).
- `revert a b` then `intro`: order varies with dependencies - prefer `cases h : e` + `rw [h] at ..`.
- Result `bind` does not reduce by `rfl`: `simp only [bind_ok]` / `except_bind_ok`; tuple let-patterns need full `simp`.
- Lockstep loop proofs: a relation predicate (`srRel`, `dRel`/`dB`) + a one-step lemma whose conclusion is a
  `match spec_step with | yield | done | error` (`DStepRel`), then `loop_ok`.

**Infra status 2026-10-23 04:52 (FINAL check_all OK, 4e55ea4)**: windows 13:20, 16:20, 18:38, 20:00, 22:00, 00:00, 02:00,
04:00, FINAL 04:49. 1178 audited, std axioms; headline `osu_eval_refines` (scripts/headline_theorem.txt) signature + the
proof-local definitions behind it pinned in scripts/headline_signature.txt (re-record only deliberately, own commit);
0 sorry tokens. net+beatmap 559/559; sim+replay 364 + 49 COVERED (only sim.step.simulate CONDITIONAL, no Rust caller);
eval 138 + 1 COVERED. Status machinery: check_all audits all transitively imported modules, `_refines_<suffix>` variants,
scripts/refines_aliases.txt, `@[attr] theorem`, discharge lemmas `theorem t .. : X :=|where`; proof_status: D44 classes,
D63 COVERED (call graph of Generated/*Funs), D67 scripts/class_overrides.txt (proved / fragment), TRUSTED_HYPS,
PROP_COND/DISCHARGED. Freshness: proofs/scripts/translation_fresh.sh (all three sets current 02:39). tools/heavy:
D74 + bounded exclusive gate hold. Window: `git checkout -- docs/proof-status.md status/metrics.json`,
`tools/heavy proofs/scripts/check_all.sh` (rc 0 ok / 3 partial / 4 headline or sorry check / 1 fatal), proof_status,
commit with explicit paths (D75).
**Playable slice (infra lead, 13:45)**: Post/Playable2.lean has all 5 get_playable_beatmap loop lemmas
(gpb_loop0..4), the spec normal form `gpb_spec`/`gpb_spec'` and `gpb_main` = the full refinement given callee
obligations as hypotheses (hAC apply_after_conversion, hAD apply_defaults, Q/hHO/hQ apply_to_hit_object (ReflOk),
hS stacking preconditions, P/hA/hP apply_to_beatmap). To finish: once mods/objects agents prove
`beatmap.mods.apply_after_conversion_refines`, `beatmap.objects.apply_defaults_refines` (+ mod_random.apply,
mod_target_practice.apply for ModsApply's hRD/hTP), state `beatmap.playable.get_playable_beatmap_refines` with
spec-level size hypotheses and discharge gpb_main's hypotheses; then `load_refines` (decoder.decode_refines + match).
Client `infra` chain: Auto/Abs,Base,Gen, Post/Processor, Beatmap/Objects, Post/Stacking, Post/Playable, Post/Mods,
Post/TargetPractice, Post/ModsB + Playable2 pieces (persisted, D41).
**Next steps (old)**: net.osutk.m3_row; beatmap.dotnet strings (str_eq, starts_with, trim*, split, split_key_val,
enum_try_parse) + sorts (intro/heap/insertion/merge); beatmap.names (key/enum tables as Lean string lists generated
from the Rust literals) -> beatmap.mod_settings (84: tables, s_*, init_double/float via FrameworkC, parse, to_*);
then text, types, slider_path, path_approximator, objects, hit_object_parser, decoder, mods, mod_random,
mod_target_practice, processor, playable. Checkpoint STATE/RESUME every ~50 fns.

## sim refinement proofs (sim core: sim/{basic,netx,scoring,state,step}.rs; D25)
Status 2026-10-22 09:50: 65/414 sim+replay fns audited (docs/proof-status.md "Sim + replay"; more stated since:
update_rank/update_score/score_apply, health_apply). Split: sim2 agent owns schedule/geometry/playable/transforms/mods/
autogen + replay/frames (proofs/OsuProofs/Sim2/), eval agent owns src/eval.
- Translation: `HEAVY_EXCLUSIVE=1 OUT=data/wip/sim-proofs/gen tools/heavy impl/charon_check.sh --start-from crate::sim
  --start-from crate::replay` (2 min) then `python3 -I proofs/scripts/install_sim_generated.py data/wip/sim-proofs/gen/lean/Gen`
  (drops items shared with Generated/Funs after checking identity) and `tools/heavy lake build OsuProofs.Generated.SimFuns`
  (~6 min, 2.8 GB). Manual imports SimFuns + OsuModel.Sim.Step, so the REPL header has them after a server restart.
- Files (root OsuProofs.lean imports each, after Auto): Sim/{Abs, NetX, Basic, Consts (generated: gen_sim_consts.py),
  Eqs, Scoring, Health, Processors, Fail, ScoringEq, HealthApply, ScoreApply, ScoreApply2}. Client setup:
  `TMPDIR=<scratch> proofs/scripts/sim_client_setup.sh simN` (commits Auto/Abs + files in Sim/ORDER; ~3 min). Use a new
  client name after each server restart (sim7 is current); drop old ones. Never --commit Generated files into a client.
- Patterns: ∃-statements as Auto (`∃ r, f a = ok r ∧ spec (abs a) = abs r`); turn them into equation lemmas for simp
  (`sim_clamp01_eq`, `Classical.choose` wrappers like `simUpdI`) when callers need rewriting; `cases` Bool conditions
  instead of `split_ifs` on float-heavy goals; avoid `congr`/whnf on float terms (timeouts) - use `Prod.mk.injEq` +
  `congrArg`; `uncurry_apply_pair` reduces Aeneas tuple binds; enum `==`: Eqs.lean; loops: LoopsR `loop_fold_gen'`
  (any_fail_condition), or a recursive model + induction with `loop_unfold` (trigger_failure: Rust loop and spec forIn
  both related to `simTFR`/`simTFS`).
- Rust edits for elaboration must be regression-verified BEFORE committing (orchestrator rule): plans
  data/wip/sim-proofs/plan_{reg1,ereg1}.json (impl/tools/run_chunks.py / run_eval_chunks.py, binaries from a clean
  worktree + own CARGO_TARGET_DIR). Last: 4092/4092 sim, 985/985 eval (STATE 09:20).
- Status 2026-10-22 ~13:30: Sim/ORDER chain (lake-builds through Sim/Periods; root imports each): ... AbsState SimM
  StepBasic AliveSort Enum Hit AccChallenge Emit InputOrder InputPhase LegacyHit Maxima Periods. Done since 09:50:
  acc_challenge, emit_one/emit, step accessors, alive_objects/stable sort, enumerate_up_to, check_hittable (both
  policies: Hit.lean STO, LegacyHit.lean legacy + combined `check_hittable_refines`), idx_of, input_lt/order,
  update_order, interpolate, replay_position, receptor_can_be_hit, sim_jinfo/push_simulated/simulated_judgements/
  score_maxima (Maxima.lean, counter guards via `sim_apply_bounds`), period_is_in_any/drain_clamp/drain/
  insert_period_sorted (Periods.lean; `simRel` = Result<_,SimErr> vs Except String).
- REPL: my client chain is now big (~27 files); committing all of it tripped the D38 memory watchdog at 13:1x. Prefer
  lake-building the file under work (`tools/heavy lake build OsuProofs.Sim.Periods`, ~3-5 min incremental) or a client
  with only the needed prefix (`sim_client_setup.sh simN <UPTO>`). Lake builds catch import gaps the REPL hides
  (Maxima needed `import OsuProofs.Sim.ScoreApply2`).
- Tricks: Aeneas `let (a, b) := (x, y)` matches are NOT reduced by dsimp/simp only (only full `simp`); `rw [show body
  .. = ok (.cont ..) by simp [..]]` after `loop_unfold; dsimp only` keeps loop bodies folded; shared-tail macros with
  `set_option hygiene false in macro ...` (LegacyHit `sim_leg_tail`); multi-line `{ .. }` record literals mis-parse in
  REPL requests: use anonymous constructors.
- Done ~15:00: HealthCfg, InitCtx, ProcPhase (lake-only: imports Sim2.Mods; not in Sim/ORDER), DrainRate, LegacyDrain,
  MkHealthCfg, IdxKind. Spec-loop pattern: Except `forIn` lemmas `sim_exc_forIn_map/_constF/_filter_push/'_range`,
  `sim_exc_loop_unfold` (Lean `while`), fuel models `simCDRrun`/`simLRun`; matcher mismatch (spec `match` vs mine):
  never restate spec match/lambda text, rewrite with `?h` side goals instead, close by `cases` on the scrutinee.
- Done ~20:00: EmitProps (emit postconditions), ApplyResult.lean: apply_result/handle_hit(_sto,_sto_from)/hit/miss_forcefully/
  max_fuel. Design: strong induction on fuel (`sim_ar_all`), invariant `SimARInv tn fo P b0 n c s e ut us` whose
  budgets are charged to `simUnj s` (# unjudged result slots; apply_result requires `res_of s r = ok none`): transform
  budget P (b0 + (U+ut)*(2n+4)), emit counters (`simEmitBud`, U+e), as_seen (U+us), enumerate size (`enum`). Ctx facts
  `SimARCtx`. Only remaining hypothesis `simCSH` (custom_state; `sim_ar_cs` from sim3b's s3b_csOk_of, CONDITIONAL hnw =
  no Wiggle, sim3c). Tail of apply_result shared by macros `sim_ar_tail`/`sim_ar_cont`.
- REPL: client sim13 = sim11's first 92 committed + Sim2 Transforms/TrEngine + Sim3 SB_* (SB_Basic patched copy in
  scratch: `try (refine ⟨..⟩)`) + ProcPhase rest + ApplyResult. A failed --commit is not stored; the memory watchdog
  drops the env after 2 cancellations: restore `committed.dropped.N` -> `committed`, `touch drop`, restore again, send a
  probe: the chain replays (~7 min for 100).
- Next: judgement (circle_check_for_result/update_result, try_judge_nested, slider_check_for_result, on_killed,
  spinner), bridges for sim3a (post_process_head_judgement s3aAllInF; update_bonus_score: s3aHF needs an extra premise
  `nested[j] = none` + a cfs-frame of hit_forcefully on spinner ticks), lifetime (needs SimARInv preservation: pool_get
  pushes insts, dict_slots: replace `enum` by Nodup alive + total-slot bound), input phase, step_once/run/run_with,
  mk_ctx (preceding_end_times now same algorithm, 7ec6d6a; SimFuns regen pending D29). EvalAssumptions runWith/mkCtx
  shapes: STATE Requests ~19:30 (ev_ctxWF).

- Done ~20:30: Judge.lean (last_tick_index, try_judge_nested, count_nested_hits, slider_result,
  slider_check_for_result), CtxWF.lean (`ev_ctxWF`, steps-independent), ApplyFrame.lean (apply_result fuel induction
  generalised: preserved predicate `Q` with `SimQOk` (writes: set top/nested, update_state usFrame, tick ito, AS, emit) and
  target predicate `A` (circle-like closure); frames `simARFr` (simKeepS/simKeepO projections) and `simTopRes`;
  `*_frame` corollaries), PostHead.lean (sim_jsn_loop, post_process_head_judgement), Circle.lean (circle_check/update_
  result). simCSH is now discharged unconditionally (sim_ar_cs, sim3c c069f00). mk_ctx handed to json (STATE 19:4x).
- REPL client sim13 after the 20:02 restart: committed chain rebuilt by hand (SB_US2 split in 3 parts r2_us2a-c,
  SC_WA/SC_Wiggle/SB_CS, ApplyResult, MkCtx, SA_*, Judge, CtxWF, ApplyFrame, jsn, pph, pph2 (= generalized
  post_process under the name `_refines2`), cc, cu). Old pre-restart tail in c_sim13/hold (ignore).
- Done ~21:50: OnKilled.lean (on_killed_refines CONDITIONAL on completed_spins*360<2^63 only; miss_unjudged_nested
  (FRAGMENT), spinner_result, judge_started_nested (FRAGMENT), try_judge_nested_frame/slider_check_for_result_frame),
  Bindings.lean (apply_bindings_refines, frame `simABFr`: loaded/armed/body_tf/body_loaded kept, tf only pos changes
  `simPosFr`). REPL names: circle_update_result_refines3 / spinner_result_refines2 in the chain = file names without suffix.
- Ownership (STATE 20:40/21:05/21:15): sim keeps step_once, run, run_with, simulate, init_state, mk_ctx_wf, input_phase,
  lifetime_* / became_alive (+spinner_ticks_get) / became_dead, update_dho, apply_bindings. sim4 = per-object updates,
  sim6 = press chain (result shape posted STATE 21:15). sort_by_lifetime_start_refines by sim5 (use in lifetime_first_update).
- Next: spinner_ticks_get loops, became_alive (needs update_state_from_result premises: SimInv, s3b_TfInv budget, CSOk;
  free_list entries < dict_slots len; push capacities), became_dead (dict free list + on_killed), lifetime_update,
  global step invariant (SimARInv e=0 + simLP + spin bound + ev_ctxWF facts), input_phase, update_dho, step_once/run.

- Checkpoint 23:25 (sim core): DONE since 21:50: became_alive_refines (Sim/BecameAlive.lean: split lemmas
  sim_ba_split/sim_ba_splitS copy the generated/spec body tails into defs proved `= … := rfl` to cut goal size; per-kind
  tails + `ba_top` macro; spinner_ticks_get gives TfInv), update_dho_refines (Sim/UpdateDho.lean, same split technique).
  REPL: verified chain c_sim13d/committed (replay it into a fresh client by copying files as a00001_… request names);
  REPL names `circle_update_result_refines3`/`spinner_result_refines2` = git names without suffix; Sim3/SC_Misc lemmas
  must be submitted to the client first (pp_001 did part_present). OPEN (sim core): input_phase (frame requests posted
  23:2x), step_once/run/run_with/simulate (need the step invariant: see STATE DESIGN NOTE 22:5x on the transform
  budget and sim8's simLifeInv; SimARInv.ik/tk must be restricted to life ≠ Future), mk_ctx_wf/initial-state invariant.
  Lifetime chain + became_alive/on_killed frame extensions: sim8.

## Rust end-to-end eval (osu_eval)

Owner area: impl/osu_eval_core/src/{eval/*,lzma.rs}, impl/osu_eval, difftest/rust_eval_diff.py,
impl/tools/{run_eval_chunks.py,mk_osr_fuzz.py,bench_eval.py}, docs/rust-eval-port.md, data/wip/rust-eval.

**Done (all committed):** 20,268/20,268 Lean-vs-Rust runs identical (full v2 corpus catchup, 3 schedules, stable, job-mod
lists, 7k fuzz runs); Aeneas 0 errors/0 sorry. Port of Eval.lean / Eval/Adapter / Eval/Env / Replay/Osr / Sim/ModsJson (spec 1b0a176) + trusted lzma +
`osu_eval` CLI (= evaltest; `--batch LIST` extra; `--sim-playable` not ported). Verified byte-identical stdout vs the
pinned Lean evaltest `data/wip/rust-eval/evaltest_lean_1b0a176` (see docs/rust-eval-port.md "Results"; aggregate:
`python3 data/wip/rust-eval/agg.py data/wip/rust-eval/results_*.jsonl`; metrics key via `python3 -I data/wip/rust-eval/metrics.py`).
Aeneas: `OUT=<scratch> HEAVY_MIN_MEM_MB=3000 tools/heavy impl/charon_check.sh --start-from crate::eval --opaque crate::lzma
--exclude crate::eval::text --exclude crate::eval::osr::text --exclude crate::eval::mods_json::text --exclude crate::eval::adapter::text`
(normal slot, 2.8 GB, ~5 min): 0 errors, 0 sorry.

**How to re-verify after a Lean change X:** build evaltest at X in a worktree (RESUME "end-to-end eval"), copy to
data/wip/rust-eval/evaltest_lean_X, port the diff of model/OsuModel/{Eval*,Replay/Osr.lean,Sim/ModsJson.lean}, build
(`tools/heavy cargo build --release -p osu_eval`), copy the binary to data/wip/rust-eval/osu_eval_<tag>.bin, write a plan like
plan_a2.json (env LEAN_EVALTEST/RUST_EVAL) and run `python3 -I impl/tools/run_eval_chunks.py PLAN` (detached; 2 in parallel max).
Rust-vs-Rust regressions (no Lean, fast): set LEAN_EVALTEST to the old Rust binary (plan_ab.json).

**Next steps:** type-check the generated eval Lean in proofs/ (refinement agent); rest of stable catchup (2/3 not run vs
Lean; Rust a==b on all) and h_* dense1ms (100/485) if slots are idle; port later Lean changes to Eval*/Osr/ModsJson.

**Gotchas:** Lean's `Float.toBits` canonicalises NaN -> print NaNs canonically. `String.toNat!` panics (stderr PANIC, default 0)
on non-digit number tokens — counted as lean_panics, stdout still compared. Don't use HEAVY_EXCLUSIVE for crate::eval Aeneas
(fits a normal slot). `pgrep -f` with the pattern in your own command line matches itself.

## lazer code coverage (docs/lazer-coverage.md, D21)

**Done (2026-10-22).** Coverage of the 2675-job corpus is measured and triaged. The 5 reachable judgement gaps are all
modelled and are now hit by `difftest/covfuzz.py`, with 1200/1200 model=oracle matches.

- Tools: `difftest/lazer_cov.py` (run/merge/report/branches) and `difftest/covfuzz.py` (scenarios ppmiss, onejudgement,
  floatdelta, oldversion, tpbreaks; `--gen-mods POOL`).
- Data: `data/wip/lazer-coverage/`:
  - `covbin` (instrumented build target);
  - `lists/`, `runs/<name>/cKKK.*`, `merged_corpus.json.gz`, `merged.json.gz`, `report_{corpus,all}.json`;
  - `covfuzz/` (the 400 targeted jobs);
  - `runall.sh` (sequential driver; `touch STOP` stops it between chunks).
- Rebuild covbin (e.g. after a coverlet call was killed: it instruments in place):
  `rm` the 3 dlls `covbin/osu.Game.dll`, `osu.Game.Rulesets.Osu.dll` and `osu.Framework.dll`, then
  `cd oracle && tools/heavy dotnet build oracle.csproj -c Release -m:1 -o ../data/wip/lazer-coverage/covbin`, then
  `tools/prune_runtimes.sh`. `covbin/osu.Framework.pdb` comes from the nuget .snupkg (`data/wip/lazer-coverage/fw.snupkg`);
  copy it back if it is missing.

**Gotchas:**
- Chunk size: about 40 real replays or about 110 synthetic jobs per heavy call (~8 min). A 150-replay chunk held a slot
  for 25 min.
- Runs must be sequential (`.lock`).
- Do not `pkill -f` a pattern that appears in your own command line.

**Next (optional):** re-measure after a lazer pin change; value-coverage (setting extremes) instead of branch coverage.

## Spec totality / provability fixes (D27)

**Done (d7c2a91, 2026-10-22).** No `partial def` / `implemented_by` / `unsafe` remains in model/OsuModel reachable from
Net/Beatmap/Sim/Replay/Eval; the only opaque constructs left are the trusted `@[extern]` primitives (libm via `Float.*`,
LZMA shim). Audit table + blocked Rust fns: docs/proof-status.md "Hard residue" / "Opaque-construct audit".
- `Settings.assign` = `assignF assignFuel` (fuel 4; Rust `assign_f`/`set_d(fuel)`/`ASSIGN_FUEL`). Bound check:
  `cd model && lake env lean --run scripts/assign_depth.lean` (49,928 WU/WD states: fuel 2 always suffices).
- `SimJson.ws = modify wsL`, `strBody = strBodyL` (structural), `value = valueF (len+1)` (nesting fuel; Rust `value_f`).
- Rust `slider_path::calculate_path_segment` returns `Option<F64>` (objects-proof request).
- Regen of proofs/OsuProofs/Generated requested in STATE.md Requests (lead proof agent owns it, D29).
**How to verify a later change of this kind:** build Lean (bmdump/simtest/evaltest) and Rust in a `git worktree` under the
scratchpad (copy model/.lake and impl/target first; a separate CARGO_TARGET_DIR if runs are still using the binaries), then
bm_rs_vs_lean.py (copy with BMDUMP pointed at the worktree), run_chunks.py with sim plans (`--gen-mods M5rate/M5/ALL`),
run_eval_chunks.py with pinned data/wip/rust-eval/evaltest_lean_1b0a176 vs the new osu_eval and vs the new Lean evaltest
(same CLI). **Gotchas:** never keep bmdump dump dirs (a 13k-job grid wrote 3.2 GB): compare per chunk and delete;
`pgrep -f` waiters match their own command line.

## Post-headline fidelity plan (D71, queued 2026-10-23)
Run after the headline theorem lands (machine memory). Source: docs/fidelity-evidence.md §4.
1. `oracle player` on ~40 wiring-risk replays + explicit-schedule replay into `oracle run` and evaltest (1-2 machine-h).
2. Explicit-schedule fuzz (~1 h).
3. The 8 never-compared suspicious server scores, then ~570 early v2 cache entries.
4. Re-run bmtest vs model, sim_diff and the stable rows at the current spec.
5. Bezier fuel exhaustion -> reject (spec/Rust/proof patch, D20(c)).

## Status 2026-10-23 07:34 (orchestrator)
- **Headline:** DONE. Tag headline-v1 = ab24f87; check_all e2b3db0 OK.
- **D72 spec+Rust patch:** worktree branch worktree-agent-ab4030d638366f6d6. The checkpoint note is in that branch's STATE.md. After a clean check_all it merges itself into main.
- **D86 portability:** vendored glibc 2.39 libm + xz 5.4.5 in impl/osu_eval_core/vendor/, RUNNABLE at b11d2a0. Full validation in progress; the results go into docs/proof-pipeline.md §5.
- **D88 performance (proved-only):** the perf lead's worktree. docs/perf-plan.md has the plan; helpers launch after "[perf] PLAN READY". It merges after D72.
- **oracle_bg:** paused (D89). Restart with `rm data/oracle_v2/STOP; setsid nohup sh tools/oracle_bg.sh > data/oracle_v2/bg.log 2>&1 &`.
- **Repo:** ~/lazerproof (~/osu-verified is a symlink); Forgejo osu/lazerproof. History was rewritten once (D85); the old hashes are in ~/backups/.

## Status 2026-10-23 12:35 (orchestrator)
- **D72:** MERGED into main at 45f1c73. Its agent is running the clean check_all on main, then tags headline-v2.
- **Perf (D88):** the lead's branch is worktree-agent-a4556b3114585f3dd. Merged into it: H-P1s (hover frames) and H-P3 (sort). H-P2 (transforms) is done on worktree-agent-a101f1364f1af204f @ 8186cef, still to merge. Next: merge main, regenerate, check_all, merge to main.
- **D86:** vendored libm/xz on main. Final validation (pow/powf reruns) in progress; the final numbers then go into proof-pipeline §5.2.
- **Final report:** docs/final-report.md, written by the report writer (D95).
