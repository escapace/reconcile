# Hole-preserving codec readiness

The local release candidate is restored in `/workspace/reconcile-serialization` and passes its correctness and review gates. It is ready for release review under the user's accepted trusted-application-state scope. No commit, merge, publication or deployment occurred. Core runtime behavior is unchanged.

The user explicitly rejected dense-only semantics, required holes to remain preserved, and accepted native sparse-array memory cost. The dense-only experiment remains separately in `/workspace/reconcile-dense-codec` and `../dense-only/`; its recommendation is superseded. No further sparse allocator research was performed.

## Restored contract

The typed codec retains optimized observation-preserving capture, integrated Lean checks, root `parse`/`stringify` exports and the three-part `[root, shapes, nodes]` transport. Both array kinds allocate with validated native `new Array(length)`. Sparse fill writes only the explicitly represented indices. No MAX-index helper, format identifier, quota or global validation pass remains in the active implementation. Producers and consumers must use matching codec versions.

For `[1, , undefined, 4]`, exact output is:

```json
[-1,[],[[3,4,0,1,2,[-1],3,4]]]
```

Ordinary `JSON.parse` returns those transport arrays. The proposed `parse` returns length four, no own property at index 1, and an own undefined property at index 2. Graph aliases, cycles and supported native identities remain preserved. Records become mutable data properties; descriptors and arbitrary prototypes are not a general serialization contract. Array/native extra properties remain omitted, as documented in the package README.

Short sparse rows can request substantial native memory. The parser is intended for trusted application state and makes no resource-safety claim for arbitrary hostile input. Native allocation failures propagate. This accepted limitation is not a remaining implementation blocker.

## Completed validation

- Typecheck, build and lint passed.
- Full source and full built-package suites each passed 1,438 tests, with the existing one expected failure and 39 skips. Complete runtime gate: 82.16 seconds.
- Full Lean gate passed in 41.60 seconds, including existing runtime families, 99 actual typed sparse/dense graph documents and eight malformed documents. The oracle directly executes native empty-shell finite allocation followed by present-entry filling. Historical alternative-constructor theorems remain checked but inactive. Native memory and host behavior are outside the proof.
- Independent review found no correctness blocker. External malformed/fidelity checks passed 16/16 on each base64 backend; semantic observation checks passed 61/61 on the fallback backend. Exact coverage and commands: [review](../restored-sparse-review/REVIEW.md).
- All core runtime files and the seven benchmark workload files are unchanged. The existing tracked source changes are confined to public exports, shared serialization errors and their API/error tests; new codec files remain isolated from core algorithms.
- All 285 frozen input hashes were independently rechecked after measurement with no changes. Built entry SHA-256: `37cdfa0494779526e6a4c1f62cf3197796dfcc337460fd3c66e5aa84e6a54514`.

Runtime receipt: `/tmp/native-sparse-final-receipt.json`. Frozen manifest: `/tmp/native-sparse-frozen-inputs.json`. Lean log: `/tmp/restored-sparse-lean.log`.

## Performance and size

The exclusive final round completed 240 observations in 48.26 seconds: 20 fixtures, four codecs, three rotated fresh-process repetitions. The candidate passed all 20 fixtures, including both sparse cases. No tests, builds or competing measurements overlapped the timed round.

Combined codec gzip size is 5,021 bytes, versus prior typed 5,091, frozen v8 prototype 4,847 and raw devalue 6.0.3 4,011. The candidate's core-only bundle exactly matches the prior typed bundle (47,778 minified / 17,264 gzip bytes); this is not a claim of byte identity against the original upstream bundle. Adding serialization exports does not retain codec code in that tested core-only import.

Candidate sparse decode timings are approximately 0.54 times the prior typed candidate on both 10k sparse fixtures. Other results are mixed and do not establish universal performance parity or a general improvement. The encode implementation and bundle are unchanged from the prior typed codec, so measured encode differences must not be described as implementation gains. Devalue's linked URL-owned parameter identity, exact Temporal fidelity and deep-2000 encoding failures remain explicit exclusions; it passes the other 17 fixtures.

Slower observations against the closer typed prior occurred in all three pairs for DAG roundtrip (median +13.9%, observed range +6.2% to +14.7%), binary-1m roundtrip (+9.5%, +3.7% to +28.3%), URL decoding (+13.4%, +0.4% to +24.4%) and Temporal decoding (+8.5%, +1.3% to +11.5%). These short measurements do not isolate a cause; they prevent claiming a clean performance-parity gate. No tuning or additional allocator experiments followed.

See [full benchmark report](REPORT.md) for workload ratios and observed ranges, payloads, memory measurements, source differences and reproducible commands. `samples.json`, `summary.json`, `sizes.json` and `receipt.json` retain the evidence. Memory measurements are occupancy deltas and RSS highwater growth, not true heap peaks. No browser performance or general hostile-input safety claim follows.

## Disposition

Ready for review as the hole-preserving release candidate with the accepted native memory tradeoff. No known correctness blocker remains. Performance evidence remains workload-dependent; there is no new performance SLA or universal parity claim. Publishing and merging remain outside authorization. Existing inline/sidecar/library research remains historical evidence, not a reason to reopen the user's settled sparse-array decision.
