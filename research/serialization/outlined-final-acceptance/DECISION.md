# Integer-sentinel diagnosis: retain the restored baseline

The bounded diagnosis does not establish shifted-reference handling, extra scalar dispatch, payload size or a specific JIT mechanism as the cause of the earlier regressions. One small code-placement adjustment passed correctness checks but did not demonstrate an additional benefit or satisfy full-suite nonregression acceptance. Keep the restored 5,021-byte-gzip codec in `/workspace/reconcile-serialization`. No change was adopted, and no further experiment is scheduled.

## What the source establishes

Valid references return before the integer candidate's special-scalar fallback. Date construction and the graph allocation/link/fill order are unchanged. Cycle encoding changes the reference offset constant without adding a per-object operation. Therefore extra executed special checks do not explain these particular workloads.

Shifted references add decimal digits at some node-id boundaries. The measured payload increases are depth-200 +10 bytes (0.47%), Dates-2k +15 bytes (0.054%), and cycle-300 +20 bytes (0.35%). These differences are real, but neither their presence nor their small size establishes a timing cause. No payload-conversion cost was independently measured.

## Focused diagnosis

The completed diagnosis passed all 200 fidelity observations in 168.86 seconds: five fixtures, A and its byte-identical copy, the restored baseline and its byte-identical copy, combined/separate export modes, and five rotated process repetitions. Timed batches were at least 100 ms. Combined mode measured encode/decode/round-trip; separate mode measured encode/decode.

| Target in combined mode | A / baseline median [observed range] | Baseline copy / baseline |
|---|---:|---:|
| Depth-200 round-trip | 0.975 [0.743, 1.077] | 0.925 [0.737, 1.271] |
| Dates-2k decode | 1.045 [0.947, 1.070] | 1.044 [0.877, 1.113] |
| Cycle-300 encode | 1.069 [0.956, 1.128] | 1.150 [1.064, 1.155] |

With separate exports, Dates decode measured 0.992 [0.917, 1.137] and cycle encode 0.995 [0.892, 1.068]. The previous consistently slower results did not reliably reproduce. The control variation and export-context differences prevent attribution to shifted references and do not prove a JIT explanation. No optimization/deoptimization trace or CPU-profile attribution was performed.

Undefined decoding remained clearly improved: 0.239 [0.191, 0.251] in combined mode and 0.241 [0.239, 0.248] in separate mode. These are paired latency ratios; less than one is faster. Ranges are observed minima/maxima, not confidence intervals.

Full focused evidence: [diagnosis report](../scalar-a-diagnosis/REPORT.md), `samples.json`, `summary.json`, `manifest.json`, `source-differences.patch` and `receipt.json` in that directory.

## The one adjustment tested

`/workspace/reconcile-scalar-outlined` differs from original A only in `src/serialization/parse.ts`: the failed-reference special dispatch is moved into `readSpecial(token)`. The helper preserves arithmetic, the integer check, special lookup and `fail('reference')` in the same order. No encoder, wire, native allocation, core, observation-order or validation-policy changes were made. This tests code-placement sensitivity, not reduced algorithmic work.

Existing finite proofs apply unchanged; the correspondence note records the additional JavaScript error-stack frame. The adjusted implementation passed typecheck, build, full lint, 1,439 source tests, 1,439 built tests, 499 independent exact wire/result/error comparisons against A, 205 focused assertions on each base64 backend, 61 semantic cases, and the full Lean gate including 99 graphs, eight malformed documents and 35 scalar cases.

The environment disconnected after the focused diagnosis had completed and before validation processes could start. A harmless execution check confirmed recovery. The failed process-creation attempts were not counted as validation; resumed runtime validation completed in 85.73 seconds and Lean checks in 33.30 seconds. No timed benchmark was interrupted.

Evidence: `/tmp/outline-runtime-receipt.json`, `/tmp/outlined-lean-gate.log`, `/tmp/scalar-outline-frozen.json`; independent harness: `/workspace/serialization-lab/scalar-wire-review/outlined-check.mjs`.

## Final full-suite acceptance

The final round passed all 330 fidelity observations in 255.03 seconds: the complete 22-fixture suite, original A, adjusted A, restored baseline, exact adjusted copy and exact baseline copy, three repetitions and three batches of at least 70 ms per encode/decode/round-trip operation. A and adjusted A produced identical wire hashes on every fixture; their encode-only bundles were byte-identical. It was not a selected-workload acceptance check.

The adjusted candidate retained the undefined benefit against restored baseline: decode 0.257 [0.233, 0.261], round-trip 0.350 [0.348, 0.406]. Against original A, its undefined decode ratio was 0.993 [0.898, 1.107], so no additional helper benefit is demonstrated.

Unresolved full-suite observations include adjusted depth-200 round-trip 1.082 [0.973, 1.115], records-10k round-trip 1.102 [0.930, 1.273], and Dates round-trip 1.047 [0.973, 1.091], all against restored baseline. The exact adjusted copy divided by adjusted depth-200 round-trip was 0.864 [0.813, 1.008], illustrating material identical-code variation. These observations must not be promoted to either a formal causal-regression finding or a nonregression pass.

Combined gzip sizes: restored 5,021 bytes, original integer A 4,998 bytes, adjusted A 5,004 bytes. The size differences do not override the performance requirement. Measurements used Node 24.19.0 with native Temporal and fallback base64; no cross-engine or browser performance conclusion follows.

See [full acceptance report](REPORT.md) for all workload operations, controls, paired ranges and reproduction commands. Raw samples, summaries, frozen manifests, bundles and the successful bounded receipt are retained alongside it.

## Disposition

The baseline's 285 frozen inputs were reverified unchanged. The half-integer candidate was not revisited; no unrelated optimization, quota, format identifier, extra validation pass, core change, publication or merge occurred.

The helper experiment is not accepted. Original A remains promising for undefined-heavy state but is not established as a full-suite replacement under the current requirement. No further wire or semantic decision is justified by this diagnosis; the unresolved issue is performance attribution and acceptance evidence. The isolated candidates and completed results are preserved, and execution has stopped.
