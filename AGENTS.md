# Working constraints

Only rules that are easy to miss and costly to break. Procedures, commands and evidence are in
[the development guide](docs/development.md) and [the Lean guide](docs/lean.md).

- Preserve the observation boundaries and the read discipline in
  [What must not change](docs/development.md#what-must-not-change): before `reconcile`'s first
  write, read each value of `current` once (reads of `next` do not count), and let library reads
  run any other getter once per call. Getters, proxies and iterators make an added or reordered
  read visible; within that discipline the trace may change but must stay deterministic.
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
- Order is the user's information, never the library's choice. Every result keeps the order the
  user gave: object keys, array elements and holes, and `Map` and `Set` entries. `reconcile`
  matches by position (key, index, insertion order), not by identity or identifier, and replaces
  an object or throws rather than end with another order. Keeping an object already in place may
  change which objects hold the values, never their order or contents.
- Keep the frozen workloads unchanged: those in `perf/` and the small ones in
  `scripts/bench-workloads.ts`. Freeze a control and the counted-work hypothesis before optimizing.
  Never overlap a benchmark or profiler with any other work. Report each workload against the
  control or trunk directly, never as an aggregate or multiplied ratios.
- Take validation and measurement evidence only from `pnpm check` and `pnpm bench`. An incomplete
  round (exit 124) is not a pass, and is not split into chunks.
- CI runs only build, typecheck and `pnpm test`; the pre-commit hook adds ESLint and oxfmt on
  staged files, and its build type-checks only `src/`. Before committing, run `pnpm check`; keep
  it out of the hook.
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
