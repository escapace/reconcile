# Encoder capture evidence

Evidence for [ENCODER-CAPTURE.md](../ENCODER-CAPTURE.md). The harness ran outside the
repository; its sources are archived unchanged in `harness.tar.gz` (extract it to get
`harness/`), so the frozen scripts are not linted as maintained code. Absolute scratch paths in the
receipts refer to that environment and no longer exist.

## Method

- **Arms.** Each arm is a source tree built with the package build, then bundled as
  `{stringify, parse}` by `harness/build-arm.mjs` (esbuild, browser, ES2020, minified).
  The baseline bundle reproduced the accepted consumer SHA-256 `09ffefd2…5940`. The identical
  copy is the same bytes at another path. devalue 6.0.3 was bundled twice: portable (its
  `btoa`/`atob` backend forced) and as shipped (Node `Buffer`).
- **Workloads.** The 22 retained fixtures from `interleaved-a/corpus.mjs`, unchanged, plus
  labelled supplements in `harness/corpus.mjs`: Unicode and long strings, small collections,
  shared Set members, object-keyed Maps, wide and varied records, nested and large sparse
  arrays, and two dictionary diagnostics added after the review.
- **Counts.** Fixed call counts per fixture and operation were frozen from the baseline before
  any comparison (`manifest-v1.json`, then `manifest-v2.json`, which adds the dictionary
  diagnostics with v1 counts unchanged). Decode-only manifests reuse the same counts.
- **Processes.** `harness/runner.py` launches one fresh Node process per arm and fixture
  (isolated mode) or per arm (history mode), sequentially, in a rotated and reversed arm order
  per repetition. Each wrapper ran under `scripts/bounded-check.py` with a 295-second budget.
  No test, build, profiler or other benchmark overlapped a round.
- **Operations.** Encode returning the string; encode with complete consumption (native
  `TextEncoder.encodeInto` reads every UTF-16 code unit and flattens any rope); decode; round
  trip. Each process verifies graph fidelity with an independent bijection check and wire
  determinism before timing, interleaves operations in rotating order, keeps 3 warmup and
  6 (or 8) timed batches, and measures JS-heap allocation per call with `v8.GCProfiler`
  afterwards. GC events from `PerformanceObserver` are attributed to batches by start time.
- **Analysis.** `harness/analyze.py` computes per-repetition median ratios against the
  reference arm; `harness/decide.py` applies the pre-registered rule in
  [REGISTER.md](REGISTER.md); `harness/tables.py` produces the report tables.

An early version consumed output with a JavaScript `charCodeAt` loop. It was bimodal across
processes (consumer JIT tiering, up to 2.2× for identical code) and was replaced before any
candidate round; the first A/A round (`null-aa-1`) used that version.

## Rounds

| Round                            | Mode                                   | Arms                                       | Purpose                                           |
| -------------------------------- | -------------------------------------- | ------------------------------------------ | ------------------------------------------------- |
| `null-aa-1`                      | isolated, 3 reps                       | baseline, copy                             | identical-code variation (old consumer)           |
| `screen-*`                       | isolated, 2 reps                       | per mechanism                              | screens for M1, M2, M3/M5, D2, M6/D7/combinations |
| `full-m12-1`, `hist-1`, `hist-2` | isolated / history                     | M1+M2, M5                                  | first full-corpus and history evidence            |
| `F1`, `F2`, `H3`, `F1d`          | isolated / history / decode-only       | final with per-key trie, without M5        | M5 decision                                       |
| `F3`, `F4`                       | isolated, 3 reps each                  | baseline, copy, final                      | decision rounds for the final sources             |
| `F3d`                            | decode-only, 4 reps                    | baseline, copy, final                      | decode without encode-induced GC                  |
| `H4`                             | history, 4 reps                        | baseline, copy, final                      | polluted type feedback                            |
| `FP1`                            | isolated, `--json-stringify-fast-path` | baseline, copy, final                      | engine variant                                    |
| `DV1`                            | isolated, 30 fixtures                  | baseline, final, devalue portable and Node | external comparison                               |

Each `rounds/<name>.csv.gz` holds every warmup and timed batch: arm, repetition, position,
fixture, seed, block, operation, call count, wall and CPU milliseconds, GC count, total and
maximum GC milliseconds in the batch, wire hash, wire length and allocation per call. Each
directory holds the design (bundle hashes, harness hashes, Node version, load average),
receipt, summary and printed table. `core/` holds the eight `scripts/ab-time.py` rounds
(plans, reports and logs); `sizes/` holds bundle sizes and the normalized package diff (`lib-normalized.diff.gz`).

## Reproduction

With Node 24.22.0, a built control tree and candidate tree, and arms bundled by
`build-arm.mjs`:

```sh
python3 scripts/bounded-check.py --seconds 295 --receipt <receipt.json> -- \
  python3 harness/runner.py --arms baseline=<a>,copy=<b>,final=<c> \
    --manifest harness/manifest-v2.json --reps 3 --seed 303 --out <round>
python3 harness/analyze.py <round> --json <round>/summary.json
python3 harness/decide.py --arm final <round>/summary.json
```

Semantic checks: `node harness/difftrace.mjs <base> <cand>`,
`node harness/inline-differential-normalized.mjs <base> <cand> 4000` (the reviewer's
`inline-differential.mjs` with minified library error class names normalized; native error
classes are still compared exactly),
`node harness/shapefuzz.mjs <base> <cand> 20000` and
`node --stack-size=4000 harness/decodediff.mjs <base> <cand> 60`, all with
`--harmony-temporal`.

`reports/prior-art.md` is the primary-source review produced by a research agent during the
investigation. It cites engine source, specifications and papers; not every engine claim was
independently re-verified, and the measured outcomes in ENCODER-CAPTURE.md take precedence.
