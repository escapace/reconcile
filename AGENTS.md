# Working constraints

- Preserve capture, discovery/sealing, preflight, publication and readback observation
  boundaries. Getters, iterators and wrappers can make repeated reads observable.
  A known kind or descriptor is authoritative only within its established lifetime.
  Equal values do not establish independent storage; shared storage does not identify
  distinct visible wrappers.
- Prove changed finite algorithms before their runtime implementation. Preserve retained
  theorem statements and state native correspondence obligations explicitly. An axiom
  audit alone does not establish an inhabited or useful correctness claim; retain
  executable bridges and counterexamples.
- Keep the seven `perf/` workloads unchanged. Freeze source and the counted-work
  hypothesis before optimization edits. Never overlap a benchmark or profiler with
  tests, builds, another profiler or another benchmark. Cumulative speed claims need
  a direct comparison, not multiplied local ratios.
- Keep complete validation and measurement rounds within 300 seconds, including
  descendant shutdown. A timeout is incomplete evidence, not a pass. Do not disguise
  an over-budget suite as successive chunks. Reuse passing evidence only after
  verifying the relevant inputs are unchanged.
- Bounded per-call runtime state is permitted; persistent caches and shape-specific
  fast paths are not. Avoid exception-driven normal control flow while preserving
  native recovery and public error boundaries.

See [the development workflow](docs/development.md) for checks and profiling, and
[the proof documentation](lean/README.md) for finite claims and correspondence limits.
