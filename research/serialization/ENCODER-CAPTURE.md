# Encoder capture optimization (2026-10-17)

The encoder now tokenizes container children in place, builds array rows directly, interns
record shapes in a per-call path-compressed trie and gives every traversal frame one field
layout. The wire is byte-identical to the accepted baseline `b6299905` for every tested input.
The decoder is unchanged. Snapshot, reconcile and produce sources are unchanged.

Across two independent full-corpus rounds, encoding took 0.765 of the baseline's time
(geometric mean of 33 fixture ratios; range 0.64–1.01), encoding with complete output
consumption 0.769, and round trips 0.844. No fixture or operation was slower than the
baseline beyond identical-copy variation in both rounds. Native-dominated workloads (binary,
Temporal, Dates, long strings, views) are at parity. The combined consumer bundle grew by 257
gzip bytes (+5.2%); the decoder bundle did not change. No universal speedup is claimed.

## What changed and why

Exploratory decomposition on Node 24.22 attributed most encode time to JavaScript capture,
not native emission. Native `JSON.stringify` of the finished transport tree was 9–28% of
encode time for records, DAGs, collections and deep graphs, and 50–90% for primitive and
string arrays. That explains why the three rejected custom-emission designs lost on strings,
records and Unicode: they replaced the fast native part. The accepted changes leave
whole-document native `JSON.stringify` in place and remove capture work.

| Mechanism                      | Counted work removed                                                 | Isolated screen (encode)                 |
| ------------------------------ | -------------------------------------------------------------------- | ---------------------------------------- |
| M1 in-place child tokenization | one driver dispatch, `frame.input` round trip and re-entry per child | primitive arrays 0.67–0.88               |
| M4 direct array rows           | the `entries` buffer and its spread copy per array                   | (combined with M1)                       |
| M2 shape trie                  | one `JSON.stringify(keys)` string, hash and compare per record       | records 0.68–0.79                        |
| M5 one frame layout            | polymorphic frame maps in the driver loop                            | none isolated; 0.89–0.97 in history mode |
| Radix refinement of M2         | one node and one `Map` per key on new shapes                         | `dict-10k` 0.93 instead of 1.37          |

A per-key trie (M2 as first screened) made a record used as a dictionary with 10,000 unique
keys about 37% slower in a single-process check, because it allocated one `Map` per key. The independent review raised
the risk; a diagnostic fixture confirmed it; the path-compressed trie removed it before the
decision rounds. Allocation per encode call fell to 0.35–0.43 of the baseline on array-heavy
fixtures and 0.76–0.96 on record-heavy ones; see the [evidence](encoder-capture-evidence/README.md).

## Results

Ratios are candidate over baseline; below 1 is faster. "Encode", "Consumed encode" and
"Round trip" pool both decision rounds (F3, F4: 6 fresh-process pairs; median and range).
"Decode-only" uses processes that never encode (F3d), because decode code is unchanged and
mixed-operation processes moved GC work between operations. "History" runs every fixture in
one process per arm, with polluted type feedback (H4). "Fast-path" repeats the isolated round
with `--json-stringify-fast-path`, the default in Node 25+ and current Chrome (FP1).

| Fixture             | Baseline encode µs |           Encode |  Consumed encode |       Round trip | Decode-only | Copy encode range | History encode | History round trip | Fast-path encode |
| ------------------- | -----------------: | ---------------: | ---------------: | ---------------: | ----------: | ----------------: | -------------: | -----------------: | ---------------: |
| `records-1k`        |              1,517 | 0.64 (0.58–0.90) | 0.67 (0.62–0.89) | 0.73 (0.65–0.96) |        0.97 |         0.85–1.11 |           0.58 |               0.69 |             0.65 |
| `records-10k`       |             21,500 | 0.71 (0.60–0.98) | 0.80 (0.62–0.96) | 0.82 (0.66–0.88) |        0.88 |         0.81–1.37 |           0.62 |               0.72 |             0.71 |
| `records-wide`      |              4,883 | 0.76 (0.63–0.85) | 0.70 (0.64–0.86) | 0.83 (0.76–0.92) |        1.00 |         0.94–1.14 |           0.61 |               0.73 |             0.68 |
| `records-varied`    |              1,881 | 0.65 (0.63–0.69) | 0.62 (0.56–0.71) | 0.73 (0.67–0.77) |        0.98 |         0.94–1.09 |           0.61 |               0.70 |             0.75 |
| `records-small`     |                  2 | 0.71 (0.67–0.87) | 0.74 (0.52–0.85) | 0.87 (0.76–0.91) |        0.95 |         0.88–1.09 |           0.65 |               0.88 |             0.72 |
| `dict-10k`          |              3,073 | 0.93 (0.86–0.99) | 0.93 (0.82–0.97) | 0.94 (0.81–1.11) |        0.99 |         0.99–1.11 |           0.84 |               0.89 |             0.96 |
| `dict-records`      |              2,716 | 0.68 (0.64–0.69) | 0.73 (0.59–0.82) | 0.85 (0.74–1.14) |        0.93 |         0.93–1.28 |           0.62 |               0.83 |             0.80 |
| `dag-2k`            |              1,553 | 0.65 (0.64–0.70) | 0.64 (0.59–0.67) | 0.69 (0.68–0.86) |        0.99 |         0.92–1.14 |           0.61 |               0.68 |             0.66 |
| `dense-dag`         |              1,113 | 0.71 (0.64–0.76) | 0.73 (0.69–0.79) | 0.79 (0.74–0.89) |        1.03 |         0.88–1.04 |           0.60 |               0.68 |             0.70 |
| `cycle-300`         |                197 | 0.63 (0.59–0.66) | 0.65 (0.61–0.68) | 0.80 (0.76–0.83) |        1.04 |         0.84–1.23 |           0.60 |               0.78 |             0.64 |
| `deep-200`          |                 97 | 0.68 (0.65–0.77) | 0.70 (0.66–0.71) | 0.80 (0.76–0.88) |        0.97 |         1.00–1.07 |           0.62 |               0.75 |             0.68 |
| `deep-2000`         |              1,059 | 0.71 (0.62–0.81) | 0.70 (0.67–0.76) | 0.86 (0.78–0.92) |        1.01 |         0.94–1.09 |           0.61 |               0.75 |             0.76 |
| `collections`       |                760 | 0.67 (0.57–0.74) | 0.66 (0.62–0.73) | 0.76 (0.69–0.82) |        0.99 |         0.84–1.02 |           0.60 |               0.70 |             0.71 |
| `small-collections` |              2,658 | 0.70 (0.65–0.76) | 0.73 (0.68–0.76) | 0.82 (0.78–0.84) |        1.00 |         0.81–1.05 |           0.74 |               0.78 |             0.74 |
| `set-shared`        |                796 | 0.65 (0.62–0.73) | 0.64 (0.62–0.69) | 0.77 (0.75–0.82) |        0.95 |         0.92–1.14 |           0.59 |               0.73 |             0.68 |
| `map-object-keys`   |              3,071 | 0.71 (0.67–0.78) | 0.71 (0.62–0.72) | 0.76 (0.70–0.84) |        0.97 |         0.97–1.12 |           0.63 |               0.71 |             0.73 |
| `numeric-10k`       |              1,031 | 0.78 (0.65–0.80) | 0.78 (0.66–0.79) | 0.83 (0.77–0.88) |        0.97 |         0.85–1.06 |           0.72 |               0.76 |             0.75 |
| `strings-10k`       |                863 | 0.82 (0.76–0.89) | 0.79 (0.66–0.82) | 0.87 (0.83–0.91) |        0.98 |         0.87–1.13 |           0.67 |               0.75 |             0.89 |
| `unicode-10k`       |              1,321 | 0.90 (0.86–0.94) | 0.93 (0.84–0.94) | 0.90 (0.88–0.98) |        1.05 |         0.95–1.11 |           0.72 |               0.82 |             0.87 |
| `long-strings`      |                385 | 0.98 (0.90–1.02) | 0.96 (0.87–1.01) | 0.99 (0.98–1.07) |        0.98 |         0.95–1.07 |           0.98 |               0.95 |             0.98 |
| `undefined-10k`     |                366 | 0.67 (0.64–0.72) | 0.69 (0.66–0.71) | 0.79 (0.77–0.85) |        1.00 |         0.90–1.13 |           0.55 |               0.65 |             0.70 |
| `mixed-10k`         |                693 | 0.81 (0.73–0.90) | 0.78 (0.72–0.93) | 0.92 (0.83–0.97) |        1.04 |         0.90–1.06 |           0.60 |               0.75 |             0.69 |
| `scalar-boundaries` |              1,120 | 0.82 (0.78–0.87) | 0.86 (0.83–0.97) | 0.90 (0.82–0.93) |        0.98 |         0.85–1.16 |           0.65 |               0.84 |             0.84 |
| `nested-arrays`     |              1,529 | 0.66 (0.63–0.71) | 0.68 (0.65–0.70) | 0.78 (0.76–0.81) |        0.96 |         0.99–1.24 |           0.60 |               0.71 |             0.60 |
| `hole-first`        |              1,065 | 0.66 (0.58–0.69) | 0.69 (0.63–0.72) | 0.73 (0.70–0.75) |        0.97 |         0.97–1.03 |           0.74 |               0.84 |             0.64 |
| `hole-last`         |              1,138 | 0.77 (0.72–0.87) | 0.73 (0.70–0.88) | 0.81 (0.76–0.89) |        1.04 |         0.89–1.11 |           0.77 |               0.85 |             0.67 |
| `sparse-big`        |                440 | 0.88 (0.68–0.90) | 0.85 (0.73–0.88) | 0.97 (0.88–1.05) |        1.01 |         0.93–1.06 |           1.02 |               1.01 |             0.74 |
| `rich`              |                 11 | 0.84 (0.75–0.88) | 0.82 (0.78–0.85) | 0.91 (0.84–0.91) |        0.98 |         0.92–1.11 |           0.78 |               0.89 |             0.79 |
| `url-linked`        |                196 | 0.81 (0.70–0.91) | 0.79 (0.76–0.85) | 0.89 (0.80–0.97) |        0.95 |         0.92–1.08 |           0.77 |               0.86 |             0.80 |
| `dates-2k`          |                395 | 0.96 (0.94–1.08) | 1.00 (0.96–1.03) | 0.96 (0.87–1.08) |        0.94 |         0.96–1.10 |           0.83 |               0.89 |             0.98 |
| `temporal-exact`    |                514 | 0.97 (0.92–1.04) | 1.02 (0.96–1.12) | 1.02 (0.77–1.08) |        1.05 |         0.92–1.06 |           0.99 |               1.03 |             0.96 |
| `views-shared`      |                  9 | 0.97 (0.90–1.19) | 0.93 (0.89–1.10) | 0.99 (0.94–1.02) |        0.91 |         0.95–1.09 |           0.85 |               0.94 |             0.95 |
| `binary-1m`         |             12,642 | 1.02 (0.91–1.14) | 0.98 (0.93–1.10) | 1.02 (0.91–1.09) |        0.95 |         0.87–1.06 |           1.00 |               1.01 |             1.02 |

Pre-registered rule: a cell is a regression when its median ratio exceeds 1.03 and its whole
range lies above the identical copy's range, in both decision rounds. None qualified. Single
rounds flagged `cycle-300` decode (1.11), `hole-last` decode (1.07) and `temporal-exact`
round trip (1.04); none repeated, and decode-only processes put all three inside copy
variation. The history and fast-path rounds had no repeated flags either.

## Against devalue

devalue 6.0.3 (the latest release) was measured in the same round (DV1) on the 30
fidelity-equivalent fixtures. It splits URL-owned search parameters, loses Temporal state and
overflows the stack on `deep-2000`, so those fixtures are excluded. The comparable arm uses
devalue's portable `btoa`/`atob` backend, matching this codec's backend on Node 24 (no native
`Uint8Array.toBase64`). devalue's Node `Buffer` backend was measured as an informational arm
only.

The candidate was faster in median encode on 27 of 30 fixtures, decode on 26 and round trip on 27. The baseline already led on most. The remaining devalue advantages are specific:

| Fixture                                 | Encode | Decode | Round trip | Cause                                                                                           |
| --------------------------------------- | -----: | -----: | ---------: | ----------------------------------------------------------------------------------------------- |
| `scalar-boundaries`                     |   1.45 |   3.46 |       2.08 | every negative number is escaped as `[-7, x]`; devalue also stores each distinct primitive once |
| `sparse-big`                            |   0.65 |   1.84 |       0.88 | `new Array(length)` preallocates; devalue forces dictionary elements with a maximum-index write |
| `records-small`                         |   0.65 |   1.33 |       0.90 | fixed per-call decode overhead on a 108-character document                                      |
| `binary-1m`, `views-shared`, `deep-200` |     ≈1 |     ≈1 |         ≈1 | parity                                                                                          |

Full per-fixture ratios are in the evidence's `rounds/DV1/table-vs-devalue.txt`. Bundle sizes:
devalue 4,027 gzip bytes combined, this codec 5,229.

## Core operations

Snapshot, reconcile and produce sources are unchanged, but their packaged bundles are not
byte-identical: the package build assigns mangled property names by frequency, and the codec
no longer uses `count`, so two mangled names changed length. The normalized package diff
outside `src/serialization` is two lines of mangled names. Consumer gzip sizes moved by
−0.01% to +0.08%.

The profile harness bundles the whole library, so the documented `ab-time` protocol was run.
At 20 batches the harness could not resolve the 3% guard on this machine: identical-code A/A
rounds reached +5.0%, and candidate rounds swung from −10.7% to +9.3% with sign changes.
Raised to 60 batches after that observation, the A/A spread was −2.2% to +2.8%, and the two
candidate rounds were snapshot −2.0%/−4.2%, reconcile +3.3%/+0.5%, plain-object reconcile
+0.9%/+1.7% and produce +2.2%/+4.1%. No workload exceeded the guard in both rounds. All rounds,
including the noisy ones, are retained.

## Proofs and semantic checks

`Inline.lean`, `ShapeRadix.lean` and `ShapeTrie.lean` were checked before the corresponding
runtime edits. They prove that in-place stepping refines the existing DFS stack machine and
recursive specification, that direct rows equal the previous entries construction for every
element sequence, and that both trie forms assign exactly the signature memo's ids. The scope,
premises and the local-simulation argument for observations are in
[ENCODER.md](../../lean/Serialization/ENCODER.md). The theorems constrain object entry and
reference order over a static graph; dynamic observations rest on that local simulation and
on differential tests:

- a trace checker over 14 fixtures with a throw injected at every observation (364 checks);
- an independent reviewer's seeded suite (4,044 cases, identical);
- 20,000 random shape sequences, byte-identical wire;
- decode fuzzing (2,511 valid and mutated documents) for the unchanged decoder;
- new public tests for proxy, hole, Map-entry and growing-array traces, which also pass on
  the baseline source.

The runtime gate passed in 68.9 s (1,448 source tests, 22 built codec tests, scoped lint), the
Lean gate in 48.2 s with native Temporal, and the axiom audit over 7,655 declarations in 94
modules.

## Rejected and unsupported hypotheses

| Hypothesis                                                   | Result                                                                                                                                                 |
| ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------ |
| M3: `recognize` returns a packed integer                     | within ±5% in isolation, mixed direction; not adopted                                                                                                  |
| M6: `value[key]` instead of `Reflect.get`                    | no gain; some adverse cells; not adopted                                                                                                               |
| D2: dense decode as `row.slice(2)` then in-place replacement | `undefined-10k` decode 1.18, `dense-dag` 1.09, `records-1k` 1.07; only numeric arrays gained                                                           |
| D7: sparse shells as `[]` plus `length`                      | no `sparse-big` decode gain; V8 grows capacity incrementally                                                                                           |
| Per-key shape trie                                           | `dict-10k` encode 1.37 in a single-process check; replaced by the path-compressed trie                                                                 |
| W1: emit negative non-integers literally (wire change)       | single-process check on geo-style records: encode 0.95 but decode 1.16, because rows of floats become double arrays and every read boxes; not proposed |

## Earlier experiments and missing artifacts

The local experiment directories named in earlier reports (`/workspace/serialization-lab`,
`/workspace/reconcile-serialization`, `/workspace/reconcile-scalar-*`,
`/workspace/reconcile-dense-codec`, `/workspace/scratch`, `/workspace/shared`) do not exist in
this environment. No source, report or sample from the three emission experiments (second-pass
writer, fused emission, per-node native stringify) is in the repository; their outcomes are
known only from the handoff brief. HANDOFF.md also names sparse-order, array-row, link-phase,
lazy-ownership, synchronous-child, base64, shape-trie and row-batching experiments whose
artifacts are absent. M1, M4 and M2 may overlap synchronous-child, array-row and shape-trie;
their earlier designs and results could not be compared and are not reconstructed here.

## Limits

Measurements used Node 24.22.0 (V8 13.6) on a 4-core cloud VM, with native Temporal and the
fallback base64 backend. Browser engines were not measured. Fixture timings depend on
execution history; isolated and history modes are both reported and neither represents every
application. Ranges are observed minima and maxima over 3–6 independent processes, not
confidence intervals.

## Next mechanisms worth investigating

- **Negative numbers.** The `[-7, x]` escape is the largest remaining gap to devalue. Literal
  fractions failed because of double-array boxing on decode. A design must avoid both the
  escape and float-only rows, and it is a wire change that needs approval.
- **Small-document decode overhead.** `records-small` decode is 1.33 of devalue. The three
  decode passes and context setup are fixed costs; measure them before changing them.
- **Sparse-array decode.** The maximum-index technique would close the `sparse-big` gap but
  revisits the explicitly accepted native allocation decision.
