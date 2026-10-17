# Development workflow

This guide is for anyone changing the library: fixing behavior, adding a feature, or
making an operation faster or smaller. It explains how the code is organized, which
checks to run, how to measure speed and bundle size, and which ideas were already tried.

The public contract is in the [README](../README.md). Proof statements, their premises
and the runtime bridges are in the [Lean README](../lean/README.md). Run every command
from the repository root.

## Ground rules

These rules restate [AGENTS.md](../AGENTS.md); MUST and MUST NOT carry their RFC 2119
meaning. The sections below explain how to follow them.

- **Keep observations unchanged.** A change MUST leave what each operation observes on
  application objects, and the order of those observations, unchanged unless it is a
  deliberate contract change. See [What must not change](#what-must-not-change).
- **Prove before implementing.** A change to a finite algorithm MUST be proved in Lean
  before the runtime changes. Keep existing theorem statements, executable bridges and
  counterexamples, and state what the runtime must supply. An axiom audit alone does not
  show that a claim is useful.
- **Keep the benchmarks fixed.** The files in `perf/` MUST NOT change. Add a diagnostic
  scenario for a new shape instead.
- **Freeze before optimizing.** Before an optimization edit, copy the source tree and
  write down which counted work should disappear.
- **Stay within 300 seconds.** Each complete validation or measurement round MUST finish
  within 300 seconds, including shutdown of child processes. A timeout is incomplete
  evidence, not a pass, and MUST NOT be presented as a pass by splitting the round.
- **Measure alone.** A benchmark or profiler MUST NOT run at the same time as tests,
  builds or another measurement.
- **Keep state per call.** State that lives for one call is fine. Persistent caches and
  fast paths for particular object shapes MUST NOT be added. Ordinary control flow does
  not use exceptions.

## How the library works

### What must not change

An application can see everything the library does to its objects: which properties are
read and in what order, which getters, setters, proxy traps and iterators run and with
which receiver, and which error is thrown. This guide calls each such access an
_observation_ and the ordered list of them the _trace_. A phase that performs
observations is an _observation boundary_.

A change preserves behavior only if every operation returns the same result, leaves the
same trace and throws the same error. Objects created during the call may differ in
identity, as long as aliasing and storage sharing stay the same. Work on private data,
such as the captured graph and the selection tables, can change freely.

Three consequences come up in almost every change:

- Equal contents never prove that two values are the same object, or that they use
  separate storage. Two different visible wrappers can share one storage object.
- A fact learned in one phase, such as an object's kind or a property descriptor, holds
  only within that phase. A getter or proxy can change the object before the next phase.
- A cheap private summary can replace private work, but it cannot replace an
  observation. Merging the reads of two phases into one is a contract change.

### Operations and phases

The three graph operations below each build a private _captured graph_ of the
relevant objects, works on that graph, and touches application objects only in the phases
marked "observes" below. A captured graph has one node per object. Each node has a
kind-specific layout and an ordered list of slots, and each slot holds a value or a
reference to another node.

The independent serialization pipeline lives under `src/serialization/`, behind the
`src/stringify.ts` and `src/parse.ts` public wrappers. It uses its own wire facets and
explicit traversal frames; the three graph operations do not call it. Native URL
extraction shares the existing intrinsic helpers. Parsing allocates nodes, links
dependent native wrappers, then fills graph edges. Layouts and shapes are read in place
from the control table and checked when a node uses them.
Collection filling decodes every captured entry before applying native `Map.set` or
`Set.add`; repeated entries retain first insertion order and the last Map value.
The wire has no format identifier, allocation policy or custom-codec registry. See
[serialization](../README.md#serialize-a-graph) for its narrower value contract.

**`reconcile(current, next)`** writes the contents of `next` into `current`, keeps
existing objects where it can, and returns `current` when both roots are objects.

1. _Capture and alignment_ (observes; `publication/capture.ts`). Reads `next` together with the
   object at the same own-property slot of `current`. A child that is the very same
   object in both is walked once and kept as is, unless the walk reaches either root.
2. _Candidate discovery_ (observes; `publication/candidates.ts`). For each node, lists the
   aligned current objects, recognizes their kind and scans their fixed slots for
   identity requirements.
3. _Selection_ (private; `graph/selection.ts` with `forced-groups.ts`,
   `supported-choices.ts`, `claims.ts`, `incoming-consensus.ts` and `checked.ts`).
   Streams every feasible plan in decreasing number of kept objects, in a fixed tie
   order. Returning a different plan with the same score is a behavior change.
4. _Execution_ (observes; `graph/driver.ts`, `graph/execution.ts`,
   `publication/publication-engine.ts`, `graph/construction.ts`). Prepares targets, writes and
   reads back. When a native write or readback fails, it moves to the next plan. After
   the call's first write, it reruns the requirement scan on kept targets before each
   later attempt.

**`produce(current, recipe)`** runs `recipe` against a draft and returns a new graph that
reuses unchanged objects from `current`.

1. _Draft_ (observes; `draft-session.ts`, `types/shared/draft-properties.ts`). Proxies
   read from the base object until the first write, which copies the base's descriptors
   into a private store.
2. _Finalization_ (observes; `finalization.ts`). A probe finds which subtrees changed and
   runs each getter once. Discovery records the changed objects and keeps unchanged
   subtrees as fixed leaves. A sealed full pass runs instead when a special value needs
   cloning, an accessor was observed, or the kept leaves conflict over storage.
3. _Identity restoration_ (observes for readback; `restore-identities.ts`,
   `graph/immutable-selection.ts`, `graph/construction.ts`). Checks changed records
   against their bases, selects the largest set of objects to keep, then allocates and
   writes the fresh objects in a fixed order.

**`snapshot(value)`** copies a graph with its cycles and shared references
(`snapshot.ts`, using `traverse` in `publication/capture.ts`).

`reconcile(current, produce(current, recipe))` is the supported way to apply a recipe to
live state.

### Type modules and storage

Each built-in kind is a module in `src/types/`: plain object, array, `Map`, `Set`,
`Date`, `ArrayBuffer`, typed arrays and `DataView`. A module supplies one _facet_ per
operation: capture, snapshot, publication, immutable reuse and draft rules. The registry
in `src/types/registry.ts` builds one table per operation, so each operation's bundle
contains only its own facets. Recognition tries the kinds in order and stops at the first
match; the plain-object kind is the fallback.

`src/adapters/vue.ts` maps Vue reactive wrappers to the raw object that holds their data.
This guide calls that object _storage_. Selection never lets two kept objects claim the
same storage. Typed-array views reference their buffers through explicit edges.

### Where the proofs are

Each kernel algorithm has a Lean model. A _bridge_ runs the runtime on a finite corpus and
compares the result with a Lean program, the _oracle_. The
[Lean README](../lean/README.md) states what each model proves and what the runtime must
supply.

| Runtime area                                                     | Lean models                                                                                             |
| ---------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Selection stream and its pruning layers                          | `GraphPolicy`, `ForcedGroups`, `SupportedChoices`, `ForwardDemands`, `ActiveDemands`, `SelectionUnwind` |
| Claims, dense checks, incoming demands, special-value provenance | `Claims`, `DenseChecks`, `IncomingConsensus`, `Provenance`                                              |
| Requirement closure                                              | `Requirements`, `RequirementPropagation`, `SeededRequirements`                                          |
| Construction order                                               | `Construction`, `ConstructionScheduler`                                                                 |
| Execution and retries                                            | `Execution`, `Driver`                                                                                   |
| Application objects used as kernel labels                        | `FactRenaming`                                                                                          |
| Plain-object property order                                      | `PropertyOrder`, `DeferredOrder`                                                                        |
| Identical-occupant pruning                                       | `PrunedReconcile`                                                                                       |
| Immutable selection in `produce`                                 | `CompactImmutable`, `CompactOwners`                                                                     |
| Public contracts                                                 | `ReconcileSpec`, `ProduceSpec`, `SnapshotSpec`, `RecipePublicationSpec`                                 |

## Making a change

### Choose the path

Pick the path by what the change touches. Every path ends with the gates in
[Checks and time budget](#checks-and-time-budget).

- **Behavior fix.** Write a failing test that states the contract, then fix the code. A
  changed test expectation needs a contract argument, not agreement with the new
  implementation. Keep the suite's expected-failure and skipped-test boundaries.
- **Finite algorithm or new feature.** Work proof first. Identical-occupant pruning is the
  worked example: its model is `PrunedReconcile` and its bridge is
  `scripts/lean-pruned-bridge.ts`.
  1. Write the contract, the Lean deliverables and the runtime steps as a plan.
  2. State the contract in Lean, with an inhabited example and counterexamples in
     `ContractTest`.
  3. Add an oracle and a bridge that compares the runtime with Lean.
  4. Implement the runtime. Run the public API fuzz files early: they rejected all three
     unsound runtime shortcuts during the pruning work.
  5. Describe the model, its premises and what the runtime establishes in
     `lean/README.md`.
- **Public API or errors.** Update the TSDoc and the README. Errors follow
  `src/error.ts`: one factory per error type, so bundles keep only the errors they can
  raise; a type name of the form `<Phase><Subject><Condition>`; and only facts the
  detecting phase already holds. Application exceptions and native `RangeError`s keep
  their identity. A public property name cannot be on the mangle list.
- **Speed.** Follow [Performance work](#performance-work).
- **Bundle size or packaging.** Follow
  [Bundle size and tree shaking](#bundle-size-and-tree-shaking).

### Couplings that fail silently

Some tooling depends on exact source text or names. A mismatch breaks `pnpm check:lean`,
the counters or the package, but not `pnpm test`. Update the tooling in the same change.

- **Benchmark runner.** `pnpm bench` uses Tinybench directly through
  `scripts/bench.ts` and `scripts/bench-scenarios.ts`, using the factories in
  `perf/scenarios.ts`. The frozen `perf/*.bench.ts` files retain their Vitest 4
  declarations as references; Vitest 5 removed their `bench` export, so these files are
  excluded from typechecking and linting and are no longer executed. The new runner
  preserves at least 500 measured iterations, five warmup iterations and 100 ms of
  warmup per task. Tasks run sequentially, and reported throughput counts 150-operation batches,
  not individual library calls. Check benchmarks as well as tests after dependency
  updates.
- **DeferredOrder bridge.** `scripts/check-deferred-order-runtime.ts` copies
  `src/types/shared/property-publication.ts` and rewrites exact text: three import
  specifiers and three lines in `canPublishProperties`. Keep the eager desired-key
  buffering that the cursor model relies on.
- **Counter instrumentation.** `scripts/profile-counts.ts` finds call sites by name: the
  `kindOf` memos in `finalization.ts` and `publication/candidates.ts`, `recognize` inside them,
  the `begin` and `edge` observation callbacks, `module.recognition.test`,
  `this.untrackedSpecialsToClone.add` and `state.checked.add`. A renamed function or a new
  memo shows up as missing counters or a failed `memoHits` assertion.
- **Lean policy bridge.** The oracle reads execution events under the field `type`; the
  runtime calls that field `tag`, and `scripts/lean-policy-bridge.ts` translates it.
- **Mangle list.** `scripts/constants.json` lists internal property names that the package
  build renames. A listed name that the library also reads on an application or native
  object breaks only the built package. `pnpm test:lib` resolves public API imports to that
  package. Tests that inspect private source members use explicit `.ts` imports, so
  their source spies and registry inspections stay meaningful.
- **Snapshot traversal.** `traverse` serves both `snapshot` and `capture`. Aligned capture
  decides a child through the sink's optional `adopt` hook, which the snapshot sink does
  not supply. Publication logic belongs in that hook; otherwise the `snapshot` bundle
  grows.
- **Selection counters.** `selection.plans` counts the plain `yield` in
  `graph/selection.ts`. Every function declaration in `graph/forced-groups.ts` gets its
  own `selection.<name>` entry counter, so a new helper there appears as a new counter.
- **Shared helpers.** Helpers in `object-property.ts`, `types/shared/` and the registry
  run under all three operations. Check the other operations' tests and bundles when
  editing them.
- **Architecture zones.** `.fallowrc.jsonc` assigns each file to a zone by its path, and
  each zone may import only from the zones listed for it. Moving or adding a file under
  `src/` therefore changes which imports it may make. A new script that only a Python
  wrapper launches needs an entry in the `repository-tooling` definition of that file.

### Tooling layout

- `scripts/build.ts` builds the package; `scripts/bundle-size.ts` measures consumer
  bundles.
- `scripts/profile.py` bounds `profile.ts`. The `profile-*` modules supply scenarios,
  counter instrumentation, attribution and deoptimization reports.
- `scripts/ab-time.py` runs alternating timing rounds against a frozen control.
- `scripts/check-lean.py` bounds the Lean build, axiom audit and bridges. `check-lean.ts`
  owns the oracle session; the `check-*-runtime.ts` and `lean-*-bridge.ts` files are the
  bridges.
- `scripts/bounded-check.py` enforces a deadline on any command and its child processes.
- `.fallowrc.jsonc` configures fallow, which `pnpm lint` runs between ls-lint and ESLint.

Experiment-specific overlays, frozen sources and receipts belong outside the repository.

## Checks and time budget

### Which checks to run

| Change                           | While editing                                                  | At the checkpoint                       |
| -------------------------------- | -------------------------------------------------------------- | --------------------------------------- |
| Runtime behavior                 | `pnpm exec vitest run src/__tests__/<file>.spec.ts`            | Combined round                          |
| Types, declarations or exports   | `pnpm typecheck`                                               | Combined round and `pnpm test:lib`      |
| Finite algorithm or Lean         | `lake build <Module>`, then `lake env lean lean/<Module>.lean` | `pnpm check:lean`                       |
| Bundle, packaging or mangle list | `pnpm build`, then `scripts/bundle-size.ts`                    | `pnpm test:lib` and `bundle-size.ts`    |
| Documentation                    | `pnpm exec prettier --check <files>` and local links           | `git diff --check`                      |
| Deadline tooling                 |                                                                | `python3 scripts/test-bounded-check.py` |
| Axiom-audit tooling              |                                                                | `python3 lean/test-axioms.py`           |

fallow, run by `pnpm lint`, fails on unused files, exports, types and dependencies, on
duplicated code, on functions above the complexity thresholds, and on imports that cross
the architecture zones. Run `pnpm exec fallow` alone for the full report with health scores
and refactoring targets. When `package.json` or the lockfile changes, the pre-commit hook
runs its dependency checks only. The CRAP score reads the coverage map that `pnpm test`
writes, so run the tests first. A missing map fails the run, and a stale one scores moved
functions by an estimate.

The combined round is one bounded command:

```sh
python3 scripts/bounded-check.py --seconds 295 --receipt /tmp/check-<unique>.json -- \
  bash -c 'pnpm typecheck && pnpm build && pnpm test && pnpm lint'
```

`pnpm check:lean` builds every Lean module and the native oracle, audits all owned
declarations for axioms beyond the three standard ones, then runs every bridge. It needs
Lean, Lake, the pinned Mathlib dependency with its build cache, Python 3.11 or later, a
POSIX shell and a C compiler. The system `cc` compiles the oracle without optimization to
save time. `python3 lean/check-axioms.py` audits an already built tree without running
the bridges.

### Optional Temporal verification

Temporal is optional at runtime. The native Temporal cases in
`src/__tests__/temporal.spec.ts` run when the test worker has a global `Temporal`;
otherwise they skip, and the absence case still runs. A default run on a runtime
without Temporal does not validate its native behavior.

On Node 24, the experimental V8 implementation can exercise those cases without
adding a polyfill dependency. Select the project config directly so the worker flag
is applied. Run the source check, build, then check the built package:

```sh
pnpm exec vitest run --config vitest.config.neutral.ts src/__tests__/temporal.spec.ts --execArgv=--harmony-temporal
pnpm build
pnpm exec vitest run --config vitest-library.config.ts src/__tests__/temporal.spec.ts --execArgv=--harmony-temporal
```

To include native Temporal in the Lean/runtime bridge, forward the same runtime flag
through the bounded gate with `pnpm check:lean --harmony-temporal`. Extra arguments to
`check:lean` are passed as Node/tsx options; its default command is unchanged.

This checks the available implementation, not Temporal specification conformance.
Use a conforming native implementation or a standards-compatible global polyfill in
applications; the library neither installs one nor requires the experimental flag.

### Time budget

`bounded-check.py`, `pnpm check:lean` and `pnpm run profile` stop the whole process tree
at 295 seconds and write a receipt. The wrapper refuses to overwrite a receipt and exits
with code 124 on timeout. Keep the receipt with any evidence you retain.

Typical durations on the development machine on 2026-10-08:

| Round                                                        |    Duration |
| ------------------------------------------------------------ | ----------: |
| Combined round (typecheck, build, tests with coverage, lint) |   245–280 s |
| `pnpm test:lib`                                              |    90–100 s |
| `pnpm check:lean`                                            |   135–160 s |
| `ab-time.py`, 8 pairs, 20 measured and 10 warmup batches     | about 137 s |
| `profile --mode counts --compare`, 2 repeats, one scenario   |     80–95 s |
| `pnpm build` and `bundle-size.ts`                            |  about 25 s |

The combined round sits close to the limit. It timed out twice on 2026-10-08 while
another user's process held a CPU core. Check `uptime` before a round. After a timeout,
wait for a quiet machine and rerun the whole round. Reuse a passing result only while its
inputs are unchanged.

Tests run on two workers because high-fanout graph cases time out under more contention.
The public API fuzz corpus is split across two files so both workers carry it, and ESLint
lints on worker threads. These settings keep the combined round under the limit.

## Performance work

### Protocol

1. **Freeze a control.** Copy the source tree outside the repository and record
   `git rev-parse HEAD` and `git status`. This frozen copy, the _control_, is the
   baseline for every comparison.
2. **Register the premise.** Write down which repeated work disappears, which counters
   should fall, which must stay equal, and the expected effect. Check it with the
   [cost screen](#cost-screen). For an idea from another library, read the actual change
   and its later fixes, and check who owns the data and what invalidates it, before
   counting anything.
3. **Count first.** Run `--mode counts` against the control. Counts are deterministic. If
   the predicted counter does not move, stop.
4. **Find the time.** Run `--mode cpu` and attribute self time to callers from the raw
   `.cpuprofile`.
5. **Change one thing.** Keep it if counts and a timing screen agree. Allow one
   evidence-led refinement, then record keep, revert or premise rejected.
6. **Time it.** A pair runs the control and the candidate in fresh processes, in
   alternating order. Screen with five pairs. On the final sources, run two independent
   eight-pair rounds.
7. **Measure bundles** on a fresh build against the control's sizes.
8. **Gate and record.** Run the gates on the final sources, add the outcome to
   [Decisions](#decisions), update [Current state](#current-state-and-open-directions),
   and keep the raw evidence outside the repository.

### Acceptance

- Report `snapshot`, `reconcile` and `produce` separately.
- A workload whose median slowdown exceeds the 3% guard in both rounds rejects the
  candidate. A large win on a stress case does not excuse a loss on an ordinary workload.
- Counters for observations, classification, selection and readback stay equal unless
  the change is meant to move them.
- Do not multiply ratios across rounds. A cumulative claim needs a direct comparison with
  the original control.
- An algorithmic candidate declares its target before sampling. The 2026-09 campaign
  required at least 20% lower latency on the target workload, at least six favorable
  pairs out of eight, and an independent confirmation.

### Cost screen

Let `f` be the share of time spent in the affected region, `s` the speed-up of that
region, and `h` any added cost elsewhere as a share of the old total:

```text
new time / old time ≈ (1 − f) + f / s + h
```

A region that takes 3% of the time cannot save more than 3%. A 20% gain from a region
that takes 70% needs that region to run about 1.4 times faster with no added cost.
Profiler shares include harness work, so treat them as upper bounds.

### Tools

| Question                                     | Command                                                                                           |
| -------------------------------------------- | ------------------------------------------------------------------------------------------------- |
| Which native and private work changed?       | `pnpm run profile <scenario> --mode counts --compare <control> --repeats 2 --out <dir>`           |
| Where does the time go?                      | `pnpm run profile <scenario> --mode cpu --out <dir>`                                              |
| Allocation or deoptimization signals         | `--mode heap` or `--mode deopt`                                                                   |
| Is the candidate faster on frozen workloads? | `python3 scripts/ab-time.py --baseline <control> --pairs 8 --batches 20 --warmup 10 --out <dir>`  |
| How does a targeted shape scale?             | `pnpm run profile diag-<name> --mode time --size <n> --compare <control> --repeats 2 --out <dir>` |
| Did the bundles change?                      | `pnpm build && pnpm exec tsx scripts/bundle-size.ts --out <dir> --compare <sizes.json>`           |

The frozen workloads are `snapshot`, `reconcile`, `reconcile-plain-object` and `produce`,
built from `perf/`. `pnpm run profile --help` lists the 19 diagnostic scenarios. Every
batch runs 150 operations, so a heavy diagnostic size needs
`--batches 2 --warmup 1 --timeout 280000`. `pnpm bench` confirms results after the
correctness checks; it does not replace paired timing.

Read each output for what it measures:

- **Time** is warmed latency in a separate process without a profiler.
- **Counts** are instrumented source events. An object-literal or `Map` counter counts
  constructions in the source, not physical allocations.
- **CPU and heap** profiles are sampled attribution. Inclusive shares include fixture work
  and are not removable fractions.
- **Deoptimizations** are signals, not estimates of removable time.

### Traps

- **Machine load.** Another process on the machine moved identical `snapshot` code by up
  to 9%. Check `uptime` and the busiest processes before each round. With unchanged
  sources, `snapshot` should land within about 2% of zero; otherwise suspect load and
  rerun.
- **Stale build.** `bundle-size.ts` measures `lib/neutral/index.js`. Run `pnpm build`
  first.
- **Mangled and unmangled code.** The profile harness bundles the sources without the
  mangle list. Bundle sizes come from the mangled package.
- **Counter gaps.** A new memo or renamed function without matching instrumentation gives
  wrong counts. See [Couplings that fail silently](#couplings-that-fail-silently).
- **Micro-benchmarks** in one process can explain a mechanism. They do not decide a change.

## Bundle size and tree shaking

Consumer bundlers drop code that no used export reaches; this is _tree shaking_. The
rules below keep each operation's bundle limited to its own code.

### Rules

- The entry point exports `snapshot`, `reconcile`, `produce`, `stringify` and `parse`, plus
  the error surface. The package
  declares `sideEffects: false`. An unused import adds zero bytes; `bundle-size.ts`
  checks this.
- Each operation reaches only its own facets. Keep publication code out of `traverse`.
  `produce` copies special values through the registry's `specials` facet, so it carries
  no snapshot code.
- Pure annotations mark only private module initialization, such as computed symbol keys
  and draft classes. Removing them can keep unused drafting or publication code in
  consumer bundles. They never permit skipping a native read.
- Class fields use `declare` and are assigned in the constructor; see the
  [engine notes](#javascript-engine-notes).
- Stable protocol identities use namespaced `Symbol.for` keys. Attempt identities and
  lookup sentinels use private objects, because they must be fresh or must not collide
  with user symbols.
- The mangle list holds only protocol fields, facet members and private methods. Descriptor
  fields, collection and iterator methods, Vue markers, proxy trap names and every key
  used with `in` stay unrenamed. Before adding a name, check that the library never reads
  it on an application or native object.

### Measuring

`bundle-size.ts` bundles all seven non-empty export combinations of the built package with
esbuild, minified for browsers at ES2020, with peer dependencies included, and compresses
them with gzip level 9. It smoke-tests every bundle and writes `sizes.json` for later
comparison. Keep the control's `sizes.json` with the frozen control.

To find which module grew, bundle the sources directly with esbuild, the mangle list from
`scripts/constants.json` and a metafile, then compare `bytesInOutput` per input file.

Gzip removes repetition, so savings come from removing distinct logic. Sharing 240
minified bytes of constant facet members saved no gzip bytes. In the `reconcile` bundle,
type policies take about 37%, the proven kernel about 36%, and the publication adapter,
candidate compiler and capture traversal about 16% (measured 2026-10-07). The proofs fix
the kernel's bytes, so source-level size work mostly targets policies and the adapter.

## JavaScript engine notes

These V8 behaviors, measured on Node 24, explain code that might otherwise look arbitrary.
In _dictionary mode_, V8 stores an object's properties in a hash table instead of a fixed
layout, which makes lookups and key listing slower. Check an object with
`node --allow-natives-syntax` and `%HasFastProperties(object)`.

- **Own-key listing.** `Object.getOwnPropertyNames` followed by
  `Object.getOwnPropertySymbols` is about twice as fast as `Reflect.ownKeys` on ordinary
  objects. The `ownKeys` helper uses the two calls.
- **Null-prototype objects.** `Object.create(null)` produces an object in dictionary mode.
  The draft descriptor store is instead created behind a frozen, empty, null-prototype
  object, which keeps fast properties and the same lookup behavior. Listing and reading a
  six-slot store took about 280 ns instead of 1,700 ns.
- **Deleted keys.** Deleting an own property moves the object to dictionary mode for the
  rest of its life; value-only updates do not. `reconcile` deletes keys from current roots
  by contract, so later key listings on those roots run about six times slower. On the
  key-toggling `reconcile` workload this costs about 8% of the time. Applications that set
  a key to `undefined` instead of deleting it avoid the cost.
- **Class fields.** Consumers that compile for ES2020 lower each class field through a
  `defineProperty` helper, which adds several hundred bytes and runs slower. Declared
  fields assigned in the constructor avoid both.
- **Fresh plain objects.** When the prototype is `Object.prototype` or `null` and the key
  is not `__proto__`, ordinary assignment creates the same property as `defineProperty`
  with default attributes, without building a descriptor object. `produce` writes such
  fresh objects by assignment.
- **Property names.** Ordinary minification renames identifiers, not properties. If enabling
  opt-in property mangling, restrict it to application-private properties and preserve library,
  native and public property names. The package uses its own audited mangle list.
- **Per-node allocation.** Per-node `Map`s, `Set`s, closures, spread copies and iterator
  destructuring were the main overhead before 2026-10-07. Removing them, together with the
  per-call identity tables, made `reconcile` 16% and `produce` 15% faster. Hoisting the
  remaining per-node callbacks later gave no measurable gain.

## Decisions

Each entry states what was decided and why. Read this list before proposing an
optimization; rejected entries are not a work queue.

### Selection kernel

- **Kept: forward-demand guard (2026-09-26).** Rejects a choice whose identity demand
  on a later node conflicts with a demand the selected prefix already made. With 12
  unrelated distractors, choice visits fell from 184,337 to 20. Ordinary workloads stayed
  within the 3% guard after a registered resolution round. Proof: `ForwardDemands`.
- **Kept: forced groups and unsupported-choice deletion.** Disabling both raised choice
  checks from 4.4 million to 7.8 million on `diag-shared-cycle`, and from about 5,000 to
  40.5 million on `diag-unsupported-cycle`.
- **Kept: application objects as kernel labels (2026-10-07).** This removed the per-call
  identity tables. `FactRenaming` proves that relabeling preserves closures, queries and
  streams; bridges relabel to numbers before calling the oracle.
- **Reverted: retention-capacity certificate (2026-09-26).** Late storage conflicts
  ran 85% faster, but small and early conflicts ran 12% and 19% slower and ordinary
  `produce` 6% slower. Only `SelectionUnwind` remains from its proofs.
- **Reverted: empty-range certificate for draft array truncation (2026-09-26).**
  Draining a 1,024-element array with `pop()` ran 95% faster, but ordinary `produce` ran
  4.6% to 6.2% slower, before and after one refinement.
- **Rejected: the `SupportedChoices` rounds reference in place of the bucket worklist.**
  It turns quadratic on the 12,000-node chain in the deep-cascade test.
- **Premise rejected: early return before an empty propagation queue.** None of
  1,800 closure calls in a warmed `produce` batch started with an already-present seed.
- **Not admitted (2026-09-22 screen).** Native scan fusion, dirty-region read suppression,
  cached wrapper equivalence, generated policy interpreters, packed graph
  representations, vectorized byte comparison, and general backjumping or clause
  learning. Each repeated earlier work or lacked both a counted removable cost and a
  correspondence argument. Earlier rejections also stand: decimal index scanning,
  streaming keys, implication filtering, early numbering, staged compilation and an
  alignment ledger. The deferred private property cursor is kept.

### Reconcile publication

- **Kept: identical-occupant pruning (2026-10-08).** A `next` child that is the same object
  at the same slot of `current` is walked once and kept. Spread-style updates ran 4.4
  times faster with 100 shared children, 5.4 times with 1,000 and 4.8 times with 10,000.
  The `reconcile` bundle grew 7.2% gzip. Proof: `PrunedReconcile`. Every shortcut around
  the design failed:
  - Skipping the walk was 70 times faster but unsound. Skipping it only when no other node
    was captured missed kept subtrees that reference the `next` root.
  - Not protecting walked objects from reuse let a shifted list rewrite a kept array.
  - Redirecting references to the current root to the live root broke
    `reconcile(raw, [raw])`, which must publish a copy of the old root.
  - Representing kept children as pinned kernel records instead of value edges cost about
    28 µs per node and erased most of the gain.
- **Kept: candidate discovery as the only preflight (2026-10-08).** Discovery already scans
  requirements on every kept candidate before any write. The engine reruns the scan only
  after the call's own writes and only on kept targets.
- **Kept: fewer repeated reads (2026-10-08).** Unchanged values are detected from presence
  and one read, without a descriptor. Storage identity is probed once per object per call,
  and recognition is memoized per call. Per operation, descriptor reads fell from 286
  to 119.
- **Rejected: merging the requirement, publication and readback key scans.** They are
  three observation boundaries; see [open directions](#open-directions).
- **Rejected: returning key-deleted roots to fast properties.** The only V8 mechanism
  would give every reconciled root its own prototype map.
- **Rejected: one traversal shared by `snapshot` and `reconcile`.** It saved no measurable
  time and added 79 gzip bytes to `snapshot`.
- **Reverted: a receipt-building helper in the driver.** It added one allocation per
  checked node.

### Produce finalization

- **Kept by choice: fixed leaves for unchanged subtrees (2026-10-08).** During discovery,
  an unchanged subtree backed by `current` is kept by identity without being observed or
  selected. When one value changes under many unchanged subtrees, `produce` runs twice as
  fast: 5.1 ms instead of 8.8 ms with 100 subtrees, 60.7 ms instead of 128.5 ms with
  1,000. It does nothing on the frozen workload, which changes nearly every object. It
  costs about 120 gzip bytes: without it, `produce` would be 0.7% smaller than the
  2026-10-08 control instead of 1.5% larger. Rejected variants:
  - leaves whose interior is not expanded after collection, which hid an object whose
    storage a changed Vue wrapper shared and let a cycle duplicate the root record;
  - leaves for subtrees not backed by `current`, whose buffers stayed fixed while the
    record path cloned them;
  - leaves without the storage-conflict fallback, which took storage from a larger
    compatible set;
  - a by-target map built for every record, which cost the frozen workload 2%.
- **Kept: less repeated finalization work (2026-10-08).** Records the probe found unchanged
  skip their reuse readback. Discovery reuses the probe's answers. Recognition is
  memoized per phase and seeded from drafted states.
- **Rejected: skipping descriptor reads while observing unchanged records.** It saved
  under 1% of time for about 90 gzip bytes.
- **Fixed: a special-value shortcut tied to the discovery plan.** It split a buffer alias
  in the sealed pass; the fuzz corpus caught it.

### Packaging and API

- **Kept: per-operation facets (2026-10-06).** Standalone gzip fell 76% for `snapshot`,
  28% for `reconcile` and 17% for `produce`.
- **Kept: mangle list (2026-10-07).** It cut a further 4.5% from `reconcile` and 6.9%
  from `produce` gzip, which source changes could not.
- **Kept: `ReconcileError` (2026-10-08).** Every detected failure carries `cause.type` with
  a `Draft`, `Finalization` or `Publication` prefix. There is no `path` field, because
  tracking one would add work to every call for the failure case only. The internal
  discriminant is named `tag` so it stays mangled. It cost 0.8% gzip in `reconcile` and
  4.0% in `produce`.
- **Kept: no `coastal` peer dependency (2026-10-07).** Local `isObject` and `ownKeys`
  replace it.
- **Deferred: `fork(value)` returning a copy and a commit function.** After pruning, its
  only remaining benefit is restoring moved copies onto their original objects. No
  consumer needs identity across reorders.
- **Not pursued: long-lived drafts (`createDraft`, `finishDraft`, `applyDraft`).** A
  copy-on-read draft freezes a container only when first touched, so a later reducer can
  see diverged data. In-place replay already costs constant time.
- **Kept: built-in recognition predicates (2026-10-09).** The five es-toolkit predicates
  were single `instanceof` or `ArrayBuffer.isView` checks. Writing them in the type modules
  saved 30 to 40 gzip bytes in each bundle. The library no longer imports es-toolkit;
  `package.json` still declares it as a peer dependency, and only the workloads use it.
- **Rejected: es-toolkit `merge` as a benchmark comparison.** It keeps omitted keys and
  array tails and duplicates shared objects, which breaks the workloads' contracts. The
  workloads keep `cloneDeep(next)` as a labelled detached-clone reference; it is not an
  equivalent publication.

### Tooling

- **Kept: fallow instead of knip (2026-10-08).** It covers knip's unused-code and
  dependency checks and adds duplication, complexity and architecture boundaries, in about
  one second. Thresholds are the published defaults of each metric, not values fitted to
  the current code.
- **Rejected: fallow's type-aware mode.** It took 35 seconds instead of 1.2 and resolved
  only two class-member findings, which the time budget of the combined round cannot
  absorb.
- **Kept: complexity splits outside per-node loops (2026-10-09).** Every fallow finding is
  resolved. A split costs time when it adds a call or a closure inside a loop over nodes or
  edges, so splits sit at boundaries crossed once per call. Both timing rounds measured
  between 2.0% faster and 0.7% slower than before, and every bundle stayed at or below its
  earlier size.
- **Kept: complexity exceptions instead of contorted code (2026-10-09).** Sixteen
  suppressions remain, each with its reason. `selections`, `compatible` and
  `immutableSelections` keep their original search loops, because moving the loop into a
  nested generator cost about 25%, and into a closure called per step cost 0.7% to 1.5%.
  The others keep the layout and draft-state types that the declared type of
  `builtinModules` names, the unsupported Map and Set iteration methods, and one export
  that a generated bridge module reads.
- **Rejected: `records.map` for the targets of identity restoration.** It saved bundle
  bytes but cost `produce` 1.4% against the loop that writes only the kept targets.
- **Rejected: `Array.prototype.flat` for the construction order.** It is about twice as
  slow as the explicit loop and cost `produce` 2%.
- **Rejected: a `forEach` callback per fixed node in target preparation.** It allocated a
  closure for each kept node and cost plain-object `reconcile` about 2.5%.

## Current state and open directions

Status on 2026-10-09.

### Code organization

fallow reports no unused code, duplication, complexity or boundary findings, and
`pnpm lint` passes. Its health thresholds are the published defaults: cognitive complexity
15, cyclomatic complexity 20 and CRAP score 30. The search loops in `graph/selection.ts`
and `graph/immutable-selection.ts` carry complexity exceptions for speed. The
native-observing publication modules live in `src/publication/`, outside the kernel
directory, and the type modules depend on the draft context interface rather than the
draft session.

### Bundle sizes

Gzip bytes of each standalone export, and of all three together, before the first round
and after each round:

| State                                   | `snapshot` | `reconcile` | `produce` | All three |
| --------------------------------------- | ---------: | ----------: | --------: | --------: |
| Before per-operation facets             |      7,828 |      12,296 |    11,428 |    15,704 |
| Per-operation facets, 2026-10-06        |      1,856 |       8,808 |     9,490 |    15,746 |
| Overhead round and mangling, 2026-10-07 |      1,646 |       8,078 |     7,921 |    14,444 |
| Error harmonization, 2026-10-08         |      1,640 |       8,139 |     8,236 |    14,773 |
| Identical-occupant pruning, 2026-10-08  |      1,637 |       8,728 |     8,240 |    15,480 |
| Second overhead round, 2026-10-08       |      1,634 |       8,690 |     8,360 |    15,614 |
| fallow findings resolved, 2026-10-09    |      1,601 |       8,610 |     8,313 |    15,390 |

### Speed

Each row compares a round with its own control, so the rows do not multiply. Negative
changes are faster.

| Round                                  |      `reconcile` | Plain-object `reconcile` |      `produce` | Targeted diagnostic                   |
| -------------------------------------- | ---------------: | -----------------------: | -------------: | ------------------------------------- |
| Overhead round, 2026-10-07             |           −16.4% |                   −20.6% |         −15.2% |                                       |
| Identical-occupant pruning, 2026-10-08 |   +0.6% to +1.5% |           −2.5% to −0.4% | +0.1% to +0.5% | Spread roots 4.4 to 5.4 times faster  |
| Second overhead round, 2026-10-08      | −10.7% to −10.2% |           −9.6% to −7.2% | −4.6% to −4.4% | Deep unchanged subtrees twice as fast |
| fallow findings resolved, 2026-10-09   |   −2.0% to −1.0% |           −0.8% to −0.7% | −0.2% to +0.6% |                                       |

`snapshot` stayed within its noise band in every round.

### Where the time goes

CPU profiles of the frozen workloads on 2026-10-08, as shares of profiled time:

- **`reconcile`:** publication about 37% (writes 22%, readback 8%, target preparation 7%),
  candidate discovery about 22% (requirement scans 8% of it), capture and alignment about
  21%, selection about 7%. Key listings against dictionary-mode roots take about 8% across
  these phases.
- **`produce`:** the recipe's draft operations about 35% and finalization about 60%, of
  which identity restoration is about 24% of the total. These shares predate the
  descriptor-store change. After it, no single function exceeds 6% of self time.

### Open directions

None of these is scheduled. Each needs the stated evidence before work starts.

- **Fewer key scans in `reconcile`.** The requirement scan, publication and readback each
  list a kept object's keys. Merging them is the only remaining route to another large
  `reconcile` gain on data that deletes keys. It changes three observation boundaries, so
  it needs a contract change in the README, a Lean model of the merged boundary and new
  bridge fixtures first.
- **One finalization read pass in `produce`.** The getter probe and discovery read
  unchanged objects separately. Merging them changes when getters run relative to draft
  observation, with the same prerequisites.
- **Ordered index for draft array truncation.** Each shrink of a draft array scans the
  whole private store, so draining an array takes quadratic time. A balanced index would
  make it O(n log n). It needs a real workload with that pattern, because the reverted
  empty-range certificate showed that ordinary `produce` loses about 5% to added array
  bookkeeping.
