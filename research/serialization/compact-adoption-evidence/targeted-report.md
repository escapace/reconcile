# Final controlled recheck: gains remain, records warning is not separated

**Original A retains substantial undefined-decode and mixed-roundtrip gains against both baselines in both trios. The earlier 33% records-encode warning does not reproduce distinctly from identical-code variation. Smaller or history-dependent regressions remain unresolved, particularly trailing-hole decode. This is the final measurement in this line, not full-suite acceptance.**

The complete round took **149.673 seconds**. All six children exited 0 and were reaped. All 174 graph/topology checks passed; the two baseline payloads are identical on every fixture, A's payload hashes are stable, and frozen source/input hashes match. Each child executed the same 181,490-call history and all five interspersed targets. No production source or bundle changed. No further measurement is planned from this report.

## All five targets, both independent trios

All ratios are candidate A / comparator except the explicit copy/baseline control column. Primary rates use every target wall interval and every call, including expensive blocks.

| Target | Trio | A / baseline | A / exact copy | Copy / baseline |
| --- | ---: | ---: | ---: | ---: |
| undefined-10k decode | 0 | 0.260 | 0.281 | 0.927 |
| undefined-10k decode | 1 | 0.224 | 0.117 | 1.917 |
| mixed-10k roundtrip | 0 | 0.774 | 0.697 | 1.110 |
| mixed-10k roundtrip | 1 | 0.638 | 0.830 | 0.769 |
| strings-10k decode | 0 | 0.918 | 0.956 | 0.960 |
| strings-10k decode | 1 | 0.707 | 0.738 | 0.958 |
| hole-last decode | 0 | 0.961 | 0.796 | 1.208 |
| hole-last decode | 1 | 1.193 | 1.363 | 0.876 |
| records-10k encode | 0 | 1.160 | 1.102 | 1.053 |
| records-10k encode | 1 | 0.971 | 0.818 | 1.187 |

Two-trio geometric means, as summaries rather than additional independent evidence: undefined 0.242 / 0.181 against baseline/copy, mixed 0.703 / 0.761, strings 0.806 / 0.840, hole-last 1.071 / 1.041, records 1.061 / 0.949. Do not multiply these by earlier ratios or infer accuracy from their decimal precision.

## Sensitivity and concrete warnings

Each cell below lists trio0 / trio1. Inclusive time spans the full active command, including native brackets and instrumentation, excluding stopped wait. Sentinel time is never subtracted or used for normalization.

| Target | Median-block A / baseline | Median-block A / copy | Inclusive A / baseline | Inclusive A / copy |
| --- | --- | --- | --- | --- |
| undefined decode | 0.282 / 0.234 | 0.299 / 0.304 | 0.610 / 0.327 | 0.648 / 0.231 |
| mixed roundtrip | 0.747 / 0.778 | 0.700 / 0.483 | 0.921 / 0.839 | 0.848 / 0.680 |
| strings decode | 0.903 / 1.088 | 0.954 / 1.110 | 0.952 / 0.730 | 1.013 / 0.789 |
| hole-last decode | 0.931 / 1.056 | 0.879 / 1.179 | 0.953 / 1.057 | 0.860 / 0.907 |
| records encode | 0.974 / 0.961 | 1.002 / 1.011 | 1.100 / 0.919 | 1.041 / 0.917 |

- **Undefined and mixed:** both gain against both baselines under total-time, median-block and inclusive accounting in both trios. Process-CPU ratios support these directions: undefined 0.259/0.224 against baseline and 0.280/0.129 against copy; mixed 0.772/0.661 and 0.696/0.828. Each candidate beats both baselines in seven of eight adjacent two-block groups. Large second-trio events distort exact speedup percentages; the substantial direction is better supported than a precise percentage.
- **Records:** trio0 retains a real adverse observation, A 44.480 ms/encode against baseline 38.346 and copy 40.375. Its all-time penalty is 10–16%, with inclusive penalty 4–10%, while median blocks are essentially equal. Trio1 is A 39.928 against baseline 41.117 and copy 48.820. The copy's final two-call block takes **247.243 ms**, versus A's corresponding block 70.593 ms. Every block is retained. The 33% earlier warning is not reproducibly separated from the control behavior; a smaller condition-dependent penalty has not been excluded.
- **Trailing-hole decode:** the first trio favors A, while the second has 19–36% higher all-time cost and 6–18% higher median cost. A's last64-call block takes **191.491 ms**, compared with baseline94.067 and copy77.023 ms. The full-block comparison also depends materially on native sentinel variation. This remains inconsistent evidence, not a clean nonregression result or an established universal sparse-path defect.
- **Strings:** all-time averages favor A, but the second trio's median is 9–11% slower. Baseline's400.548 ms block and copy's206.919 ms block inflate their averages. Do not label this a robust20% string improvement.

The primary exact-copy discrepancy magnitudes across ten target/trio cells have median **1.126** and maximum **1.917**. That describes this round; it is not an acceptance threshold. For the actual records question, control ratios are 1.053 and 1.187. Consistent direction alone is not sufficient evidence of a source effect, as earlier identical-code diagnostics already demonstrated.

## Retained tails and scope

There are240 target blocks, ranging from20.493 ms to3514.483 ms. The largest is exact-copy undefined decode in trio1, with3128.204 ms process CPU; it is the only target block with CPU/wall below0.9. Other retained long events include baseline mixed922.015 ms, baseline undefined803.706/716.922 ms and A mixed525.594 ms. These events cannot all be described as descheduling. No compiler/GC trace or profiler was enabled, so this round does not assign them a particular GC, JIT, frequency or host cause.

All warmup and target trajectories remain in the raw logs. Most wall and process-CPU directions agree, but their bookkeeping scopes differ slightly; full active-block accounting is an additional diagnostic view rather than proof that every future GC cost is attributed to the producing call. No observations were trimmed, rescaled by sentinels or replaced with medians in the primary result.

The exact earlier five-target recipe is preserved: undefined decode64, mixed roundtrip24, strings decode96, hole-last decode64 and records encode2 calls per block, eight blocks per target per child. Target-order cycles and the full181,490-call mixed history match `local-original-a-interleaved`. Hole-last is the original length10,000 array with own index9999 deleted, not empty-sparse or a last-position singleton.

The baseline/copy/A trios use separate heaps and one shared import URL, with every inactive process and its V8 threads SIGSTOP-paused. Six-slot order-and-reverse groups balance distance from the group midpoint. Rotation and identity permutation produce two or three outer/middle/inner assignments per identity across both trios, not perfect three-role crossing. There are only **two independent trios**. Nested blocks and five different workloads do not create more independent process replications. Tracing was removed and the time-local schedule now has three identities, so this reproduces the counted input/workload condition, not every aspect of the earlier environment.

## Decision value

The simultaneous code-null supplied the missing information: records can differ substantially between byte-identical baselines under this retained history. A's old1.332 ratio should therefore not be treated as a demonstrated intrinsic33% record-encoder cost. The records-only experiment and focused profile also failed to sustain that magnitude, while the source audit found no additional record operation to remove.

This does not prove the absence of smaller regressions, and it does not overturn the concrete adverse first-trio record observation or second-trio trailing-hole observation. The portable candidate has strong, repeated undefined/mixed benefits; deciding whether those benefits justify the remaining finite performance uncertainty belongs to the adoption decision. The current evidence does not establish full-suite nonregression. Repeating another local protocol is not an evidence-backed solution; this measurement line stops here.

## Artifacts and checks

`receipt.json` and `verification.json` confirm completion, six reaped exits, all174 checks, unchanged inputs, stable wire hashes and identical1,668-chunk sequences per child. The controller ledger records six launches,246 confirmed stops,246 resumes and six exits, without simultaneous running children. `comparison.json` contains every wall/CPU/thread/inclusive/native/median ratio and trajectory; `groups.csv`, `samples.jsonl`, its compressed copy and six raw worker logs retain all observations. `PROTOCOL.md`, `manifest.json`, `replay.json`, `worker.mjs`, `round.py` and `analyze.py` retain the exact method and provenance.
