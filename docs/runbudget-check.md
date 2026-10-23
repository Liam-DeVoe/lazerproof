# RunBudgetS / F3 corpus check (audit M1 acceptance test; D67, D70, D77)

**Verdict: PASS.** RunBudgetS (`proofs/OsuProofs/Sim/StepInv.lean`) and the D77 F3 conjunct (`e2AccBudS` /
`s9AccBudS`) hold on every real input in the corpus. This covers every schedule kind, and every replay also run
with Wiggle (WG) added. The smallest margin is 145x on real inputs and 99x on the synthetic worst case (a WG replay with a frame every 0.5 ms on the 55-minute map 2147769, dense1ms).

## What is checked

- **RunBudgetS:** `(2U + Σ(nested+1) + 1)(2n+4) + objects·(4n+8) + 1 < 2^64-1 ∧ (U+1)·2·10^6 ≤ 2^54`.
  - U = `runBudgetNeed C S0`, the Σ over steps of the spec active-list size after the lifetime phase.
  - n = `sc2CsCostS cfg`, which is 2^31+2^25 (+ the other vis-mod costs) when WG is on.
  - With WG, the first conjunct needs 2U + unj + 2·objects < ~4.23·10^9. The second conjunct (U ≤ 9.0·10^9) does not depend on WG.
- **F3 (D77):** `Σ(nested+1)·(1 + 2·#AC) ≤ 2^64-1`.
- **Inputs (12490 real pairs):** all pairs with status ok, 8000 from data/index_v2.sqlite (data/replays_v2) and 4490 from data/index.sqlite (data/replays).
  - This includes every replay in the data/oracle_v2 score lists. (45 jittered replays from oracle_v2's perturbation runs are not real inputs and are excluded.)
  - Every pair is run under catchup, perframe and dense1ms.
  - Every pair is run twice: with the replay's own mods (4 replays already have WG) and with WG added through the `--mods`-style override.
  - Total: 74940 triples. 0 input/mkCtx rejections.
- **Env:** `Eval.defaultEnv` (the headline's env).

## Tool (tools/runbudget/)

- **`RunBudget.lean` (`rbcheck`):** compiled against the model at HEAD in a throwaway worktree (`build.sh`).
  - It mirrors `evaluate` up to the simulation inputs: decode, ResolveMods, playable, frames, Config.
  - It holds a **verbatim** copy of `sc2PreDho`, `sc2UnitsRun`, `runBudgetNeed`, `sc2VmCostS`, `sc2CsCostS` and the RunBudgetS inequality. `check_defs.py` checks the copy against StepInv.lean (OK at this commit).
  - The proofs package itself (Aeneas imports) is not compiled.
  - **Why a loop:** `sc2UnitsRun` is not tail-recursive and would overflow the stack on 3·10^6 steps. `unitsLoop` computes the same fold as a loop, and `selftest` checked it equal to the recursive definition.
  - **One-pass mode:** `exact1` takes stepOnce = `sc2PreDho` then the update loop, so each step runs once. It is cross-checked against the two-pass fold:
    - same U (14,541,791) on the largest input, 2147769/7738496475 dense1ms;
    - `exact2` self-tests give the same U and the same judgement count as `Sim.run`.
- **Phase 1 (`bound`, `bound.py`):** uses the cheap bound U ≤ steps × objects, with the exact spec step count from `mkCtx` (no simulation).
- **Phase 2 (`exact.sh`):** computes the exact U for the triples the bound cannot clear.
- **Hypothetical worst case (`synth`):** a lazer replay with a no-button frame every 0.5 ms at the playfield centre, from r0-1 s to end+1 s. Unaligned frames make about 2 steps per ms under dense1ms.

## Results

**Phase 1:** the bound clears 74907 of 74940 triples.

| schedule | mods | triples | cleared by bound | max steps | max steps×objects |
|---|---|---|---|---|---|
| catchup | own | 12490 | 12490 | 363370 | 4.36e9 |
| catchup | +WG | 12490 | 12489 | 363370 | 4.36e9 |
| perframe | own | 12490 | 12490 | 217172 | 2.61e9 |
| perframe | +WG | 12490 | 12489 | 217172 | 2.61e9 |
| dense1ms | own | 12490 | 12485 | 3297117 | 3.96e10 |
| dense1ms | +WG | 12490 | 12464 | 3297117 | 3.96e10 |

The 5 triples that the bound could not clear without WG are all dense1ms; the binding conjunct there is the 2^54 one. They are 2147769/7738496475, 4792723/7738602650 and 3340682 with 3 v1 replays.

**Phase 2:** all 33 remaining triples are `ok = true`.
- **Max U** is 14,541,791 (dense1ms, 2147769, 55 min, 12000 objects, at most 18 active).
- **Max U per schedule:**
  - catchup: 1,613,241
  - perframe: 977,558
  - dense1ms: 14,541,791
  - All three maxima are on 2147769. Every other triple has U ≤ steps×objects, which already clears.
- **Max LHS against 2^64:** 1.27·10^17 (2147769 dense1ms + WG), a margin of **145x**.
- **Max (U+1)·2·10^6 against 2^54:** 2.91·10^13, a margin of **619x**.
- Without WG, the 2^64 conjunct has a margin of at least about 10^11.
- Margins against 2^64 below are `(2^64-1)/LHS`; margins against 2^54 are `2^54/((U+1)·2·10^6)`.

| map | replay | schedule | mods | steps | objects | U | max active | 2^64 margin | 2^54 margin |
|---|---|---|---|---|---|---|---|---|---|
| 2147769 | 7738496475 | dense1ms | HD | 3297117 | 12000 | 14541791 | 18 | 1.06e+11x | 619x |
| 2147769 | 7738496475 | dense1ms | HD+WG | 3297117 | 12000 | 14536112 | 18 | 145x | 620x |
| 4792723 | 7738602650 | dense1ms | DC | 1572368 | 7986 | 9380103 | 18 | 2.45e+11x | 960x |
| 4792723 | 7738602650 | dense1ms | DC+WG | 1572368 | 7986 | 9377111 | 18 | 225x | 961x |
| 3340682 | 4657119895 | dense1ms | SD+CL | 1976009 | 5068 | 6224512 | 10 | 2.47e+11x | 1447x |
| 3340682 | 4657119895 | dense1ms | SD+CL+WG | 1976009 | 5068 | 6224512 | 10 | 339x | 1447x |
| 3340682 | 4353591669 | dense1ms | HD+CL | 1976008 | 5068 | 6241143 | 10 | 2.46e+11x | 1443x |
| 3340682 | 4353591669 | dense1ms | HD+CL+WG | 1976008 | 5068 | 6241143 | 10 | 338x | 1443x |
| 3340682 | 4496897980 | dense1ms | HR+HD+CL | 1975624 | 5068 | 5554229 | 10 | 2.76e+11x | 1622x |
| 3340682 | 4496897980 | dense1ms | HR+HD+CL+WG | 1975624 | 5068 | 5553024 | 10 | 380x | 1622x |
| 4699298 | 7742512989 | dense1ms | NF+DA+WG | 1385450 | 5654 | 5653505 | 14 | 373x | 1593x |
| 4796487 | 7742696693 | dense1ms | RX+WG | 1167939 | 6351 | 7122236 | 23 | 296x | 1265x |
| 2067820 | 4183614379 | dense1ms | SD+CL+WG | 1409159 | 4922 | 5898608 | 16 | 358x | 1527x |
| 2157291 | 7740767126 | dense1ms | RX+WG | 932152 | 7205 | 8757833 | 21 | 241x | 1028x |
| 2067820 | 4506138189 | dense1ms | CL+WG | 1409136 | 4922 | 5895552 | 16 | 358x | 1528x |
| 2067820 | 4220244333 | dense1ms | HD+CL+WG | 1409077 | 4922 | 5912143 | 16 | 357x | 1524x |
| 849199 | 7740992435 | dense1ms | NF+WG | 1318901 | 4359 | 4638287 | 12 | 455x | 1942x |
| 3708050 | 7742144433 | dense1ms | HR+HD+WG | 1041527 | 5671 | 6611637 | 17 | 319x | 1362x |
| 1529189 | 7740372684 | dense1ms | WG | 972338 | 6362 | 7866279 | 21 | 268x | 1145x |
| 4557237 | 7742741587 | dense1ms | RX+WG | 758653 | 5706 | 7013394 | 18 | 301x | 1284x |
| 2147769 | 7738496475 | catchup | HD+WG | 363370 | 12000 | 1613241 | 18 | 1.29e+03x | 5583x |
| 5666128 | 7738547059 | dense1ms | WG | 1197030 | 4741 | 5856260 | 17 | 360x | 1538x |
| 3609961 | 4858291240 | dense1ms | CL+WG | 812015 | 4648 | 5477873 | 19 | 385x | 1644x |
| 3609961 | 4853068614 | dense1ms | HD+CL+WG | 812084 | 4648 | 5490177 | 19 | 385x | 1641x |
| 3609961 | 4751091632 | dense1ms | CL+WG | 812581 | 4648 | 5495823 | 19 | 384x | 1639x |
| 2147769 | 7738496475 | perframe | HD+WG | 217172 | 12000 | 977558 | 18 | 2.11e+03x | 9214x |
| 2496130 | 7742987194 | dense1ms | EZ+WG | 732328 | 3319 | 6396015 | 25 | 330x | 1408x |
| 1919449 | 4640216155 | dense1ms | HD+CL+WG | 830276 | 2913 | 3866946 | 18 | 546x | 2329x |
| 806325 | 7742589536 | dense1ms | HT+WG | 624564 | 5762 | 6992138 | 25 | 302x | 1288x |
| 1919449 | 4082225986 | dense1ms | HR+HD+CL+WG | 830258 | 2913 | 3433223 | 16 | 615x | 2624x |
| 1919449 | 2899969149 | dense1ms | HR+CL+WG | 830704 | 2913 | 3437570 | 16 | 614x | 2620x |
| 1811527 | 7742036157 | dense1ms | NF+HT+DA+CL+WG | 655285 | 3260 | 3413526 | 16 | 618x | 2639x |
| 1785329 | 7738259083 | dense1ms | HR+RX+WG | 784933 | 2788 | 3083128 | 11 | 685x | 2921x |

**F3 (D77):** the largest Σ(nested+1)·(1 + 2·max(#AC, 1)) is 73002 (2147769), far below 2^64. The corpus has at most 1 AC mod. F3 would still hold with up to about 7·10^14 AC mods.

**WG on long ranked maps (hypothetical, synthetic 0.5 ms replay, dense1ms):**

| map | mods | steps | objects | U | max active | 2^64 margin | 2^54 margin |
|---|---|---|---|---|---|---|---|
| 3340682 (longest ranked map in the corpus, 33 min) | WG+EZ | 3952997 | 5068 | 16696426 | 11 | 127x | 540x |
| 2147769 (55 min, the longest map in the corpus; ranked status unknown) | WG | 6592159 | 12000 | 21280308 | 11 | 99x | 423x |

Both are `ok = true`. These are the worst cases we know of. The synthetic replays have about twice as many steps as any real dense1ms run.

## Notes

- **Why U is so far below the bound:** U grows with steps × the number of alive objects, which never exceeds 25 here. The bound uses steps × all objects.
- **What could break it:** a WG run fails RunBudgetS only if U reaches about 2.1·10^9. At 25 alive objects that is about 8.5·10^7 dense1ms steps, roughly 23 hours of map, or a replay with an extreme frame count. Such crafted inputs are outside the hypothesis by design.
- **Reproduce:**
  1. `tools/runbudget/build.sh W`
  2. `W/rbcheck bound LIST` (lines are `map<TAB>osr`)
  3. `bound.py OUT *.out`
  4. `exact.sh W/rbcheck OUT exact.jsonl`
  5. `W/rbcheck synth MAP dense1ms '[{"acronym":"WG"}]' 0.5`
- Run every step through `tools/heavy` with nice 19.
