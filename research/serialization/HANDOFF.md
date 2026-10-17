# Serialization WIP handoff

The active codec adopts the original compact-token integer layout A, following explicit user approval to apply it and update the existing WIP branch. See [ADOPTION.md](ADOPTION.md) for the exact scope, current evidence and final validation. This remains WIP, not a release or approval to merge.

## Active implementation

Special values use scalar −1 through −5; references use −(id+6). Negative finite and bigint escapes remain unchanged. Holes, aliases, shared buffers/views, owned URL parameters, Temporal state and source getter/proxy/iterator observations retain their existing contracts. Matching producer/consumer versions are required. Old singleton special arrays are rejected; there is no version field or legacy auto-detection.

Only original A is applied. None of the later sparse-order, array-row, link-phase, lazy-ownership, synchronous-child, base64, trie or row-batching experiments is included. Core snapshot/reconcile/produce algorithms and all seven perf workloads are unchanged.

## Encoder capture optimization (2026-10-17)

The encoder now tokenizes children in place, builds array rows directly, interns shapes in a
per-call path-compressed trie and uses one frame layout. The wire is byte-identical and the
decoder unchanged. See [ENCODER-CAPTURE.md](ENCODER-CAPTURE.md) for results against the
baseline and devalue, rejected hypotheses, missing earlier artifacts and next mechanisms, and
[ENCODER.md](../../lean/Serialization/ENCODER.md) for the proofs and correspondence
obligations. The sections below describe the earlier layout-A adoption.

## Evidence and limits

Undefined decoding and mixed roundtrip retain substantial targeted gains. The requested isolated records-only baseline/copy/A rerun is neutral for adoption: no candidate-specific slowdown was separated from identical-code variation. The superseded historical 33% warning is excluded from decision evidence as requested, while raw history remains intact. Finite local measurements do not establish universal performance parity.

[Compact adoption evidence](compact-adoption-evidence/README.md) contains the two decision reports, compressed raw event streams and small provenance/verification files. The already tracked historical reports, patches and measured bundles remain for reproducibility; their older adoption-status statements describe their original date. `integer-sentinel.patch` is a historical baseline-to-A delta and must not be reapplied to this active tree. Other patches remain inactive research. Large local experiment outputs and dependency/build caches are not added to this commit.

## Correctness and continuation

Release review added the [native collection reconstruction repair](COLLECTION-FOLD.md):
repeated Map/Set iterator visits now use the same native insertion rules as snapshot,
while every entry is still decoded. This is separate from the historical optimization
experiments and retains layout A.

`lean/Serialization/Compact.lean` and the structural/scalar bridge describe the active finite claims. Native JSON/IEEE754, constructors, allocation and application observations remain explicit correspondence boundaries. The inactive half-integer proof layout is retained without adding a runtime mode.

Use the Node/pnpm versions in the project and Lean version in `lean-toolchain`. Follow AGENTS.md: complete rounds stay within 300 seconds including descendant shutdown; benchmarks never overlap validation. Existing checks are typecheck, build, lint, tests, built-codec tests and the Lean/runtime bridge. The local executor runs TypeScript scripts with `node --import tsx` because the tsx CLI IPC listener is unavailable.

The final validation result and exact measured-bundle correspondence are recorded in [ADOPTION.md](ADOPTION.md). No further benchmark, merge, main-branch update or release is implied by this handoff.
