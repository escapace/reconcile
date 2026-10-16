# Compact scalar wire: retain the restored baseline

Neither compact-scalar candidate meets the user's requirement that other workloads must not suffer. Both preserve the tested value contract and substantially improve undefined-heavy decoding, but other measured operations are slower. The restored 5,021-byte-gzip codec in `/workspace/reconcile-serialization` remains the active candidate. All 285 baseline hashes were verified unchanged after measurement. No core changes, publication or merge occurred. No further experiment is scheduled.

## Representations considered

| Design | Special values in order undefined, NaN, +Infinity, -Infinity, -0 | Reference for node i | Disposition |
|---|---|---|---|
| A: shifted integers | -1, -2, -3, -4, -5 | -(i + 6) | Implemented and measured; strongest target gains, not accepted |
| B: half-integers | -0.5, -1.5, -2.5, -3.5, -4.5 | -(i + 1) | Implemented and measured; not accepted |
| Reserved strings | Five reserved strings with escaped matching user strings | Existing references | Not implemented; introduces escaping and dispatch on a currently strong string path |

Both implemented designs preserve nonnegative finite numbers, ordinary strings, booleans and null. Finite negative values still use `[-7, number]`; bigint still uses `[-6, decimalString]`. Tokens and node payload fields remain distinct grammar contexts. Legacy singleton special arrays reject; there is no compatibility branch, identifier, version framework, quota or whole-document validation pass. Matching producer/consumer versions remain required.

A adjusts object references, URL parameter token-to-id conversion, and view-buffer reference decoding. URL owner metadata remains an ordinary nonnegative node id. B leaves all reference arithmetic unchanged. Both preserve capture traversal, holes, explicit undefined, native array allocation, aliases/cycles, Vue behavior, getter/iterator ordering and supported native state. Unsupported value policy is unchanged.

For `[1, , undefined, 4]`, exact measured JSON is:

```text
Baseline: [-1,[],[[3,4,0,1,2,[-1],3,4]]]
A:        [-6,[],[[3,4,0,1,2,-1,3,4]]]
B:        [-1,[],[[3,4,0,1,2,-0.5,3,4]]]
```

JSON.parse returns the transport arrays. Each matching codec parse restores length four with index 1 absent and index 2 present with undefined. These are graph transports, not transparent ordinary data objects.

## Correctness and proof evidence

Finite proofs passed before runtime edits. They cover round-trip and representation injectivity, disjoint special/reference ranges, reference bounds, legacy-singleton rejection and JSON-tree encode/decode correspondence. The actual runtime bridge classifies parsed JavaScript numbers, canonicalizes half-integers and tests rounding/nonfinite boundaries. Native JSON/IEEE754 behavior and host constructors remain explicit correspondence boundaries; this is not a proof of the whole JavaScript runtime.

Each candidate passed typecheck, build, full lint, 1,439 source tests and 1,439 built tests. Independent review passed 205 assertions for A and 203 for B on each base64 backend, plus the 61-case observation corpus for each candidate. Coverage includes marker collisions, escaped negatives equal to sentinels, quoted numeric-looking strings, malformed reference bounds, old tokens, prototype pollution, shared buffers/views, and URL parameters encountered before their owner.

Each integrated Lean gate passed 99 actual graph documents, eight malformed documents and 35 scalar cases. The combined Lean round took 87.04 seconds. The runtime/static validation interval, including coordination and a corrected checker-only lint failure, was 257.75 seconds. The initial lint failure remains recorded rather than presented as a pass.

Artifacts: `/tmp/compact-validation-summary.json`, `/tmp/compact-both-lean-receipt.json`, `/tmp/compact-runtime-frozen.json`; independent harness: `/workspace/serialization-lab/scalar-wire-review/check.mjs`. Candidate source locations are `/workspace/reconcile-scalar-wire` (A) and `/workspace/reconcile-scalar-half` (B).

## Measured outcome

The complete bounded round passed all 264 fidelity observations in 224.03 seconds. It used 22 fixtures (the existing suite, ordinary strings and an added negative/special/string-boundary fixture), four arms (A, B, frozen baseline and byte-identical baseline control), three rotated fresh-process repetitions and three batches of at least 80 ms per encode/decode/round-trip operation. All comparisons below are candidate divided by the restored baseline; less than one is faster. Ranges are observed minimum and maximum, not confidence intervals. Encode, decode and round-trip were measured separately.

| Target measurement | A | B |
|---|---:|---:|
| Undefined-10k decode | 0.233 [0.232, 0.242] | 0.464 [0.440, 0.480] |
| Undefined-10k round-trip | 0.340 [0.325, 0.372] | 0.815 [0.638, 0.846] |
| Undefined-10k payload bytes | 30,019 | 50,019 |
| Combined codec gzip bytes | 4,998 | 5,004 |

Baseline undefined payload is 50,019 bytes and combined codec gzip is 5,021 bytes. B removes the per-special JSON arrays without reducing their spelling length; A removes them and shortens the spelling. The gains are materially larger than the identical-control variation for these target operations. The matrix did not remeasure devalue; multiplying these ratios by previous devalue comparisons would not establish a new direct comparison.

Other workloads prevent acceptance:

- A depth-200 round-trip: **1.111 [1.055, 1.258]**, versus control **0.980 [0.925, 1.076]**.
- A Dates decode: **1.117 [1.030, 1.185]**.
- A cycle encode: **1.126 [1.014, 1.224]**.
- B records-1k round-trip: **1.085 [1.064, 1.093]**, versus control **0.984 [0.966, 1.030]**.
- B hole-first decode: **1.090 [1.047, 1.119]**, versus control **0.963 [0.889, 1.001]**.

These repeated slower observations do not identify a universal causal mechanism, but they do not satisfy unchanged-workload acceptance. Large target gains and slightly smaller bundles do not override that requirement. See [the full report](REPORT.md) for every workload's separate operation results, paired controls, raw examples, payloads and uncertainty. `samples.json`, `summary.json`, `sizes.json`, `manifest.json`, `receipt.json`, `corpus.mjs`, `worker.mjs`, `build.mjs` and `round.py` preserve reproducible evidence.

Performance was measured on Node 24.19.0 with native Temporal enabled and the observed fallback base64 backend. No browser, cross-engine, native-base64 performance or new general binary-speed claim is made. The accepted trusted-state sparse-memory tradeoff remains unchanged.

## Recommendation

Keep the restored baseline. A is the more promising research direction because it produces the strongest target gain and smaller payloads, but it is not an acceptable replacement under the current whole-workload requirement. Both candidates remain isolated for review. Accepting a measured tradeoff or expanding the optimization scope would require a further decision; neither has been assumed.
