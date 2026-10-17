# Final restored sparse-codec independent review

No source-level correctness blocker was found in the reviewed restored candidate. Both array wire kinds use native `new Array(length)` with mandatory integer/arity checks; sparse fill visits explicit ordered index/value pairs. Graph reconstruction retains allocation, dependency linking, then filling. Scalar references, target kinds, URL ownership, selected shapes and own `__proto__` handling remain checked. Capture retains DFS source-receiver reads, dynamic array length/membership observations, holes and iterator cleanup.

`src/types/array.ts` has no diff against the clone baseline, and source searches found no remaining allocator-helper imports. API documentation explicitly targets trusted application state: short sparse input may request substantial native memory, and there are no allocation quotas. This is not a hostile-input resource-safety claim or a new performance claim.

## Exact external checks

Commands ran from `/workspace`, after the final restored build was declared ready, with no concurrent benchmark:

```sh
timeout 295s node --harmony-temporal serialization-lab/restored-sparse-review/malformed-check.mjs /workspace/reconcile-serialization/lib/neutral/index.js
timeout 295s node --harmony-temporal --js-base-64 serialization-lab/restored-sparse-review/malformed-check.mjs /workspace/reconcile-serialization/lib/neutral/index.js
timeout 295s node --harmony-temporal serialization-lab/v6/semantic-check.mjs /workspace/reconcile-serialization/lib/neutral/index.js
```

- Malformed/fidelity harness: **16/16 fallback**, 504 ms; **16/16 native base64**, 310 ms. Backend detection in the JSON receipts reports `native: false` and `native: true` respectively.
- Source-receiver/DFS/Vue/native-shadow semantic corpus: **61/61, no skips**, on the **fallback base64** runtime (no `--js-base-64`). This exact 61-case corpus was not repeated with native base64. Both backends were externally exercised by the malformed/fidelity harness, including exhaustive short base64 acceptance, backing identities and native field checks.
- The preserved five sparse decoder regression cases are in `src/__tests__/sparse-codec.spec.ts`; their final source/built integration gate is owned separately by the final-check agent, not counted in the external totals above.

The malformed harness is copied here from v9 so its new receipts do not overwrite the frozen v9 evidence. Both backend result files are retained alongside it. The semantic command's complete result was printed to the execution receipt; no separate semantic JSON file was written here. No external process remains active.

## Reviewed source identity

All `72` non-test TypeScript files under `src` were recorded in `source-hashes.json`. Aggregate source SHA-256:

`d417f4f70d33415828c1868d80100a5dfd0003228abd0591d781733d4a30e69f`

Algorithm: sort relative paths, then hash each UTF-8 path, NUL, exact file bytes, NUL. Built `lib/neutral/index.js` SHA-256:

`37cdfa0494779526e6a4c1f62cf3197796dfcc337460fd3c66e5aa84e6a54514`

These identify the reviewed source/build; later edits require the relevant checks to be reconsidered.
