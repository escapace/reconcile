# Serialization WIP handoff

The production candidate is the restored hole-preserving codec at this branch root: 5,021 gzip bytes for the previously measured combined consumer bundle. Core snapshot/reconcile/produce algorithms and all seven perf workloads remain unchanged. This is a recoverable WIP, not a release or approval to merge.

## Where work stopped

The final controlled benchmark FINISHED in 240.364 seconds: 44 independent fixture/process clusters, 176 isolated child processes, 3,168 nested timed blocks, all fidelity checks passed, all children exited. The incomplete part is analysis and independent review. Both assigned agents stopped with usage-limit errors after collection. No result from this final round has been accepted as a performance conclusion. Do not describe it as an interrupted or passing performance gate.

The original integer-sentinel candidate A remains unaccepted. Previous runs repeatedly showed a large undefined-array decoding gain (roughly 0.24 baseline time), but whole-suite nonregression was unresolved because identical-code controls varied. The outlined-helper experiment showed no demonstrated incremental benefit and is also unaccepted. Earlier cycle/date/deep slower observations are not established causal defects. Do not multiply speed ratios from different rounds or claim universal parity.

Next: analyze the saved controlled data, particularly undefined arrays, shared views and depth-200/2000, with all other fixtures as regression controls. Compare both independent clusters and both exact-copy controls; six nested blocks are not six independent process replications. Inspect warmup trends, CPU/wall time and cgroup changes. Keep every observation. If controls remain unsuitable, report the strongest supported result and uncertainty; do not enter an endless retry loop. No new implementation is required to resume analysis.

## Preserved work

- Root src/serialization, public parse/stringify, tests and lean/Serialization: restored baseline.
- integer-sentinel.patch: complete source/test/proof delta from that baseline to A.
- outlined.patch: complete delta from the same baseline to the outlined experiment; do NOT apply on top of A.
- interleaved-a: measured consumer bundles, fixtures, protocol, original and portable runners, raw compressed observations, manifest and completion receipt.
- Prior reports document decisions, known limitations and correctness evidence. Absolute /workspace and /tmp links in historical reports describe the old environment and are not all packaged. Archived reports mentioning no publication predate this explicitly authorized WIP push.
- validation: small existing receipts/summaries. These record past execution, not new tests during packaging.

No dependencies, build caches, credentials or full generated library trees are included. The two small measured consumer bundles are intentional benchmark inputs. samples.json.gz preserves the complete raw result without shipping a bulky formatted JSON file. Historical manifest hashes refer to the original measured files; round.py only changes bundle input paths for portability, and round-measured.py preserves the exact original runner.

## Resume commands

Use Node 24.19.0, pnpm from package.json, and the Lean version in lean-toolchain. The measured runtime used --harmony-temporal --expose-gc and the fallback base64 backend. Linux cgroup v2 and taskset are used by this harness; it pins CPU4 if available. No host-isolation claim is made.

From the repository root:

```sh
pnpm install --frozen-lockfile
gzip -dc research/serialization/interleaved-a/samples.json.gz > /tmp/serialization-controlled-samples.json
python3 -c 'import json; x=json.load(open("/tmp/serialization-controlled-samples.json")); print(len(x), sum(len(r["blocks"]) for r in x))'
```

Expected counts: 44 clusters, 3168 blocks. Analyze these saved results first. To reproduce collection without overwriting the preserved evidence, and only when no tests/builds/profilers/benchmarks overlap:

```sh
cp -R research/serialization /tmp/reconcile-serialization-rerun
rm /tmp/reconcile-serialization-rerun/interleaved-a/receipt.json
python3 scripts/bounded-check.py --seconds 295 --receipt /tmp/reconcile-serialization-rerun/interleaved-a/receipt.json -- python3 /tmp/reconcile-serialization-rerun/interleaved-a/round.py
```

Use a fresh destination if it already exists. The outer deadline includes descendant cleanup. All output is overwritten in that copy; retain the original branch evidence.

To recover independent experiment worktrees (replace HANDOFF_COMMIT with this branch tip):

```sh
git worktree add --detach ../reconcile-integer HANDOFF_COMMIT
git -C ../reconcile-integer apply research/serialization/integer-sentinel.patch
git worktree add --detach ../reconcile-outlined HANDOFF_COMMIT
git -C ../reconcile-outlined apply research/serialization/outlined.patch
```

Each worktree needs its own dependency installation. Existing validation commands are pnpm typecheck, pnpm build, pnpm lint, pnpm test, pnpm test:lib and pnpm check:lean, subject to AGENTS.md complete-round budgets. Do not rerun all validation merely to analyze frozen benchmark data. Independent candidate check after building: node --harmony-temporal research/serialization/scalar-wire-review/check.mjs "$PWD/lib/neutral/index.js" A. The outlined candidate uses the same A wire.

## Fidelity and limits

Preserve holes versus own undefined, aliases/cycles, collection and buffer/view identities, exact supported Temporal and owned URL state, getter/Vue/iterator observation ordering and native allocation semantics. Records materialize data properties; arbitrary descriptors/prototypes, function/symbol identity and unsupported native classes are not promised. Native sparse allocation cost is accepted for trusted application state. Do not add quotas, a format identifier, global validation pass or persistent caches. Matching producer/consumer versions are required. Lean finite claims and executable bridges are scoped; host allocation, native JSON/IEEE754 and constructor behavior remain correspondence boundaries.

Prior correctness: baseline 1,438 source and built tests; A/outlined 1,439 each, plus typecheck/build/lint and integrated Lean gates. A external checks covered 205 assertions per base64 backend and 61 observation cases. See preserved reports for exact counts, skips and scope. No additional tests or benchmarks were run while packaging; patch applicability and archive integrity were checked. No main changes, merge or release is authorized.
