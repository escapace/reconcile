# Original compact-token A adoption

The user approved applying original A and updating the existing WIP branch. This change applies only `integer-sentinel.patch` to baseline `739ad363`, with adoption-status documentation. It does not include the sparse-order, array-row, link-phase, lazy-ownership, synchronous-child, base64, shape-trie or row-batching experiments. Core algorithms and all seven `perf/` workloads are unchanged.

## Representation and counted work

Undefined, NaN, positive infinity, negative infinity and negative zero use scalar −1 through −5. References use −(id+6). Negative finite values keep `[-7,value]`; bigint keeps `[-6,decimal]`. Ordinary scalar values, holes, identity, native ownership and source-observation order retain their existing semantics. Singleton special-token arrays are rejected. Matching producer/consumer versions are required; there is no format identifier or legacy auto-detection.

This removes one private singleton array per special scalar and its JSON array syntax. It adds no source prepass, separate validation pass, policy quota, persistent cache or platform-specific runtime path. The unchanged `Compact.lean` proofs establish the finite token claims and JSON-tree embedding, with the existing scoped oracle and native correspondence limits. The retained half-integer proof layout is not active runtime code.

## Decision evidence

The [targeted controlled recheck](compact-adoption-evidence/targeted-report.md) completed in 149.673 seconds. Undefined-array decode used 0.224–0.260 of baseline time across its two independent trios; mixed-array roundtrip used 0.638–0.774. Both improvements held against the simultaneous byte-identical baseline copies. Exact percentages remain sensitive to runtime variation.

The later [isolated large-record rerun](compact-adoption-evidence/records-report.md) completed in 34.731 seconds with three independent baseline/copy/A trios. A was faster than both baselines in one trio and between them in the other two. All-time aggregate ratios were 0.934 against baseline and 0.975 against its copy; median-block ratios were 0.986 and 0.984. Treat this as neutral: no candidate-specific records slowdown and no reliable records speedup were established.

The user requested that the superseded historical 33% records warning be excluded from the adoption decision. Raw history remains preserved; it has not been deleted or rewritten. Smaller or history-dependent differences elsewhere remain possible. Adoption is an explicit decision supported by the targeted gains and neutral isolated rerun, not a claim of universal full-suite nonregression. Browser-wide performance has not been measured.

## Final adoption checks

The complete final gate passed in **270.924 seconds** under its 295-second process-tree budget: typecheck, build, 1,439 source tests (plus the retained expected-failure/skip boundaries), Fallow, scoped ESLint, filename lint, 13 built-codec tests, full Lean build/audit/runtime bridges and 205 independent A-wire checks. The audit covered 7,055 declarations across 89 modules with only standard axioms. The serialization bridge covered 99 graphs, eight malformed documents and scalar lexical/type cases; native ownership and Temporal checks also passed. All gate descendants exited.

The compact proof was recompiled successfully before runtime installation. Independent source/proof/test/document review found no blocker. Rebuilding the combined browser-target consumer produces bytes **identical to the measured original-A bundle**, 12,939 minified bytes and 4,998 gzip bytes (Node gzip level 9). No other source experiment is present. The [validation receipts](validation/compact-adoption-validation.json), [proof receipt](validation/compact-adoption-proof.json) and [bundle correspondence](validation/compact-adoption-bundle.json) preserve the checks. No new benchmark ran during adoption.

Commit hooks are not repeated after these explicit gates: the local tsx CLI IPC limitation requires the direct Node script invocation recorded in the receipt. No runtime/proof/test input changed after validation.

Only a local WIP commit is prepared here; the parent workflow handles the approved branch push. No main-branch merge, package publication or release is authorized.
