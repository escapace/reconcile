# Isolated large-record encoding: no candidate-specific slowdown identified

**The reviewed, isolated rerun provides no record-encoding regression that should block adoption of original A. A is faster than both identical baselines in one trio and falls between them in the other two. CPU, inclusive-batch timing and median-block sensitivity support that interpretation. The result does not establish a small speedup or rule out small costs under other conditions.**

Per the user's instruction, the superseded historical slowdown is set aside as adoption-decision evidence. Its raw files remain untouched. This report assesses the new isolated result; it does not perform adoption or claim full-suite acceptance.

The round completed in **34.731 seconds**. All nine children exited0 and were reaped. All18 post-timing graph checks and all nine output-count/length checks passed. The complete fixed workload ran; no counts were shortened when execution finished sooner than estimated.

## Direct result

Ratios below use all measured time / all measured calls, retaining every expensive block. Lower A/comparator ratios mean less encode time.

| Independent trio | Baseline ms/encode | Exact-copy ms/encode | A ms/encode | A / baseline | A / copy | Copy / baseline |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 32.992 | 30.491 | 29.666 | 0.899 | 0.973 | 0.924 |
| 1 | 21.006 | 25.208 | 22.571 | 1.075 | 0.895 | 1.200 |
| 2 | 27.208 | 21.565 | 22.945 | 0.843 | 1.064 | 0.793 |
| Geometric mean of trio ratios | — | — | — | **0.934** | **0.975** | **0.958** |

The apparent aggregate advantage is not a claimed optimization benefit on records: choosing either identical baseline changes its size. A is never slower than both simultaneous baselines. Its7.5% slower result against one baseline in trio1 and6.4% slower result against the copy in trio2 are each inside the spread between the two identical implementations in that trio.

| Trio | CPU A / baseline | CPU A / copy | Inclusive A / baseline | Inclusive A / copy | Median-block A / baseline | Median-block A / copy |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.899 | 0.973 | 0.895 | 0.972 | 0.896 | 0.951 |
| 1 | 1.074 | 0.895 | 1.074 | 0.895 | 1.071 | 0.957 |
| 2 | 0.844 | 1.064 | 0.843 | 1.062 | 0.998 | 1.046 |

Median-block geometric means are0.986 against baseline and0.984 against copy. Medians are sensitivity checks only; the primary result retains all time. There is no comparator-normalized correction, tail trimming, synthetic acceptance threshold or ratio multiplied from another experiment.

## What was reviewed and run

- Exact fixture: an array of10,000 `{id, name, active, values:[i,i+1,i+2]}` records, with the same factory as the retained `records-10k` benchmark. It contains ordinary positive numbers, strings, booleans and nested arrays; no mixed special-scalar fixture, getters, proxies or native-object payloads are involved.
- Exact production artifacts: frozen restored-baseline and original integer-A bundles. Baseline-copy uses the same baseline bytes. There was no production edit or rebuild.
- Each child constructs only this input, performs one initial encode, runs two initial explicit collections, then64 warmup encodes and48 measured encodes. Both phases use four-call chunks. There is no codec decoder call, roundtrip or graph-oracle import before measurement.
- Every returned output contributes its string length to a numeric sum and increments a count. After timing, assert exactly113 outputs per child, the exact expected length sum and full equality of the final string with the initial string. The fixture's output is ASCII, so length equals UTF-8 bytes; this is checked afterward. Full-string hashing is outside the timed loop.
- After timing, parse/check both the initial and final output using the ordinary graph oracle, including prototype, own-key order, detachment and applicable graph-identity checks. Baseline/copy emit618,410 bytes; A emits618,430 bytes and reconstructs the same graph. Initial and final hashes match the saved exact output for each variant.
- Three fresh trios rotate baseline/copy/A across all three roles and initialization positions. Six order-and-reverse groups per trio place each identity at each outer/middle/inner timing depth twice. Inactive child processes and all their V8 threads are SIGSTOP-paused; the controller confirms the stop before another child runs.
- The independent pre-launch review passed for the fixture, fixed counts, delayed decoder checks, output consumption, balanced schedule and cleanup. There are no PBKDF2 brackets, allocating JSON diagnostic controls, profiler, compiler/GC trace, forced optimization or target-phase forced collection.

These are repeated encodes of one retained input, in time-local bursts from separate paused heaps. They are not uninterrupted single-process sustained throughput, fresh-input generation, or getter-observation benchmarks. The unchanged source audit finds no special-scalar allocation-saving path on this input; the reference values and20 output bytes differ. Approximate parity here is therefore compatible with substantial gains on different scalar-heavy workloads, without estimating those gains from this round.

## Retained variation and measurement limits

All108 target blocks remain, comprising432 timed encodes. Blocks range65.165–325.867 ms. The largest retained blocks include baseline325.867 ms in trio0, baseline312.349 ms in trio2, copy260.027 ms in trio0 and A257.722 ms in trio0. CPU/wall lies between0.996 and1.004 across targets; this does not identify the cause of the remaining variation. No GC or JIT attribution is claimed.

The execution is not uniformly steady: last-half/first-half target ratios are baseline0.639/0.927/1.368, copy0.761/0.981/1.043 and A1.203/1.061/1.256. Warmup and target trajectories are retained in `comparison.json` and raw events. Three trios are the independent process replications; their12 nested blocks per identity are not36 independent experiments.

Raw codec timing includes the result-length/count sink. Inclusive active-batch timing also includes chunk measurement and logging, but excludes command-boundary resource snapshots and stopped wait. Wall/process-CPU/thread-CPU have slightly different bookkeeping scopes. Neither timing view guarantees attribution of every deferred VM cost. Node v24.19.0 runs on the reported Xeon Platinum8573C with CPU4 affinity, no compile cache and flags `--harmony-temporal --expose-gc`.

## Recommendation and evidence

**Treat this isolated records benchmark as neutral for the adoption decision: it supplies no demonstrated candidate-specific regression and no reliable extra speedup.** The result supports removing this particular benchmark as a reason to reject original A, while preserving ordinary uncertainty from finite local measurements. Adoption remains a separate decision; no source change, commit or push was made by this benchmark.

`verification.json` confirms18 fidelity checks, nine output-consumption checks, unchanged frozen hashes, equal64-call warmup histories and equal28-chunk sequences per child. The ledger records nine launches,117 confirmed stops,117 resumes and nine exits with no overlapping running children. `receipt.json` confirms all descendants reaped. `comparison.json`, `groups.csv`, `samples.jsonl`, compressed samples and all nine raw worker logs retain the observations. `PROTOCOL.md`, `manifest.json`, `replay.json`, `worker.mjs`, `round.py` and `analyze.py` retain the reviewed method and provenance.
