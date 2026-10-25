# Working constraints

Only rules that are easy to miss and costly to break. Procedures, commands and evidence are in
[the development guide](docs/development.md) and [the Lean guide](docs/lean.md).

- Preserve capture, discovery and sealing, preflight, publication, readback and `serialize`
  source-traversal observation boundaries. Getters, proxies and iterators make an added or
  reordered read visible. A value of `current` read before the first write is read once and
  serves every phase up to readback; a kind, prototype, key list or descriptor read then may too.
  Readback reads every node again after any write, so a getter of `current` runs at most once
  without writes, twice with them and once more per demotion pass, apart from reading `next`.
  Library reads run any other getter once per call. The exact trace is otherwise internal and
  must stay deterministic.
- Prove a changed finite algorithm in Lean before its runtime. Keep theorem statements, bridges
  and counterexamples, and state the runtime's obligations; an axiom audit alone proves nothing.
- Library code must not read or write through `Object.prototype` or `Array.prototype`. Use
  `src/standard-prototypes.ts`; internal records hold every field they read and never gain one
  by assignment; internal loops do not destructure, `concat` or leave `for...of` early.
- Per-call state is allowed; persistent caches and shape-specific fast paths are not. Normal
  control flow does not throw, and application and native errors keep their identity.
- Treat a semantic rule or fix as library-wide: check every function and value kind, including
  subclasses and linked URL and buffer pairs. Decide from what each function's
  users need; fix all consistently or none.
- Keep the frozen workloads unchanged: those in `perf/` and the small ones in
  `scripts/bench-workloads.ts`. Freeze a control and the counted-work hypothesis before optimizing.
  Never overlap a benchmark or profiler with any other work. Report each workload against the
  control or trunk directly, never as an aggregate or multiplied ratios.
- Each complete validation or measurement round finishes within 300 seconds, child processes
  included. A timeout is incomplete evidence, not a pass, and is not split into chunks. Reuse a
  pass only after checking that its inputs are unchanged.
- CI runs only build, typecheck and `pnpm test`; the pre-commit hook adds ESLint and Prettier.
  Run the `pnpm lint`, `pnpm check:lean`, `pnpm test:lib` and `pnpm bench size` checks your
  change needs before committing, and do not add them to the hook.
- Documentation is `README.md` for users plus these two guides; add no other docs, notes or
  reports. The README follows the TSDoc voice, gives each limitation one home and puts advanced
  material after the common case. Change it minimally, through independent editorial and
  fact-check review rounds.

## Ask first

- Ask before a semantic, API or wire-format change, and before starting a library-wide change.
- Before pushing a behavior change, report what it changes, what it could break and its measured
  performance, then wait for confirmation. If a change exceeds the regression budget a task
  sets, stop and report. Never merge or release without authorization.

Delete a line once a test, lint rule, CI step or script enforces it.
