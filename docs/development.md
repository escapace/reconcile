# Development guide

This guide is for anyone changing the library: fixing behavior, adding a feature, or making an
operation faster or smaller. The public contract is in the [README](../README.md) and the working
rules in [AGENTS.md](../AGENTS.md); proof statements, premises, bridges and correspondence limits
are in the [Lean guide](lean.md). Run every command from the repository root.

## How the library works

### What must not change

An application can see everything the library does to its objects: which properties are read and in
what order, which getters, setters, proxy traps and iterators run with which receiver, and which
error is thrown. This guide calls each access an _observation_ and their ordered list the _trace_. A
phase that observes is an _observation boundary_: capture, discovery (and the sealed pass of
`produce`), preflight, publication and readback, and source traversal in `serialize`. A change
preserves behavior only if every operation returns the same result and throws the same error, and
its trace keeps the _read discipline_:

- The library's own reads run each getter of an object other than `current` once per call; a
  recipe's reads through a draft are the recipe's.
- In `reconcile`, a value of `current` read before the first write is read once and serves every
  phase up to readback; a kind, prototype, key list or descriptor read then may serve them too. At
  the node of `next` that an object of `current` is, the value read as part of `next` serves, so
  the object is not read as `current` there.
  Reads of `next` do not count: when `next` holds an object of `current`, `reconcile` can read it
  more than once as part of `next`, as the [`reconcile` remarks](../README.md#function-reconcile)
  state.
- After any write, readback reads again, once per pass, every node that is neither pinned nor
  _untouched_ (a node whose kept object is the object `next` holds there), so an own getter of
  `current` runs at most once without writes, twice with them and once more per _demotion pass_ (a
  pass that decides again without a blocked object), not counting reads of `next` or proxy traps.

Within that discipline the exact trace is internal: a change may drop, merge or reorder reads if
the new trace is deterministic. A getter or trap that changes what the call already read before the
first write is unsupported; readback still catches a write that such code undoes. Objects created
during the call may differ in identity, as long as aliasing stays the same; private work can change
freely.

### Type modules

Each built-in kind is a module in `src/types/`: plain object, array, `Map`, `Set`, `Date`,
`ArrayBuffer`, typed arrays, `DataView`, `URL` (`url.ts`), `URLSearchParams`
(`url-search-parameters.ts`) and the Temporal value classes (`temporal.ts`). A module supplies
one _facet_ per concern: capture, publication, immutable reuse and draft rules. Modules of kinds
that `snapshot` does not observe inline also supply a snapshot facet. `types/builtins.ts` defines
recognition and builds one registry per graph operation (`snapshotTypes`, `publicationTypes`,
`produceTypes`), so each bundle contains only its own facets. Recognition tries kinds in order and
falls back to the plain object.

The decision never lets two nodes keep one object, and typed-array views reference their buffers
through explicit edges. `src/standard-prototypes.ts` holds the helpers
that keep internal objects and reads independent of `Object.prototype` and `Array.prototype`.

### The graph operations

`snapshot`, `reconcile` and `produce` build a private _captured graph_ with one node per object;
each node has a kind-specific layout and ordered slots holding values or references.

**`snapshot(value)`** copies a graph with its cycles and shared references.

1. _Walk_ (observes; `snapshot.ts`). One depth-first walk (`SnapshotWalk`), separate from
   capture, reads each object once: own keys and descriptors, collection entries, buffer bytes
   and view ranges. Plain objects, arrays, `Map`, `Set`, `Date`, `ArrayBuffer`, typed arrays and
   `DataView` are observed inline; URL, `URLSearchParams` and Temporal values go through their
   facets.
2. _Writing_ (private). Each visited object gets one fresh copy, recorded in a memo before its
   children are walked, so shared references and cycles stay shared; views are rebuilt over the
   copied buffer. The optional `seen` argument seeds the memo.

**`reconcile(current, next)`** writes `next` into `current`, keeping existing objects where it
can.

1. _Capture and alignment_ (observes; `publication/capture.ts`) reads `next` with the object at
   the same slot of `current`. A child that is the same object in both is walked once and kept,
   unless walking it reaches the root of `current` or `next`.
2. _Candidate discovery_ (observes; `publication/candidates.ts`) lists the aligned current
   objects, recognizes the kind of each that capture did not, and checks, before any write,
   which of them must stay the same object (_identity requirements_). This is the _preflight_.
   Among a node's candidates, those that an admitted candidate's fixed slot requires there come
   first, then the rest, each group in discovery order. Capture's prototype read of each object
   serves discovery and the preflight (`Types.Ingress`).
3. _Decision_ (private; `publication/publication-engine.ts` `decide`) keeps, in node order, the
   first candidate of each node that qualifies: it is not blocked, it is not kept at another
   node, and each object its fixed slots hold is kept at that slot's node. A different decision
   for the same candidates is a behavior change.
4. _Write_ (observes; `publication/publication-engine.ts`, `graph/construction.ts`). Before each
   pass allocates, `keepsNextAt` checks, without reading an application object, the rule of
   `Spec.KeepsNext`, which keeps the pass's writes out of every object `next` holds; when it fails,
   `reconcile` throws `PublicationWouldChangeNext`. The pass then allocates the new objects in
   construction order, writes every node but the pinned and untouched ones, new objects first, and
   reads each written object back to confirm the write (_readback_). A kept object whose write is
   refused or does not read back is _blocked_: the next pass decides again without it, every object
   the earlier pass wrote staying at its node, and the passes end when no object is blocked; a
   blocked root rejects the call. After the first write, the requirement scan reruns before each
   pass on the kept targets that pass writes. When every node of the first pass wrote nothing and
   kept its key order, the readback is skipped (`Property.WriteFreeReadback`); that pass also reuses
   the preflight's key lists and descriptors.

**`produce(current, recipe)`** runs `recipe` against a draft and returns a new graph that reuses
unchanged objects.

1. _Draft_ (observes; `draft-session.ts`, `types/shared/draft-properties.ts`). Proxies read the
   base until the first write, which copies its descriptors into a private store.
2. _Finalization_ (observes; `finalization.ts`). A first pass, the _probe_, finds changed subtrees
   and runs each getter once; discovery then keeps each unchanged subtree whole, as a _fixed leaf_,
   so one change under many unchanged subtrees does not revisit them; an unchanged object settles
   as soon as its walk ends unless a cycle leads back into the walk, and identity restoration takes
   each fixed leaf's children from those walks. A full _sealed_ pass runs instead when a special
   value (a `Date`, buffer or other kind `produce` copies) needs cloning, an accessor was observed
   or two leaves claim one object.
3. _Identity restoration_ (observes for readback; `restore-identities.ts`,
   `graph/immutable-selection.ts`) keeps the largest set of objects, treating each unchanged
   subtree it keeps whole as one choice, then allocates and writes the fresh ones in a fixed order.

### The serialization pipeline

`serialize`, `deserialize` and `requiredMaxBytes` (`src/serialization/`) have their own facets in
`facets/`, use neither the type registries nor the captured graph, and share only `error.ts`,
`standard-prototypes.ts`, `object-property.ts` and the URL and binary helpers in
`types/shared/url-carrier.ts` and `types/shared/binary-native.ts` with the graph operations. The
[Lean guide](lean.md) describes the format.

- **Encoding** observes. An explicit frame stack (`frames.ts`) reads each record's own string keys
  and values depth first with the source as receiver, and iterates collections with the built-in
  iterators. Those iterators have no `return` method, so a throw propagates with nothing to close.
  Shapes and layouts are interned per call in path-compressed tries (`radix.ts`); output is new JSON
  data, which the caller writes as text.
- **Decoding** takes ownership of the JSON data it is given: payload rows become decoded arrays
  and slots are overwritten, and a literal root is returned as given. It observes nothing in data
  from `JSON.parse`. It checks the control table, allocates nodes, links dependent natives (views,
  URL-owned search parameters) and fills references in reverse order; collections decode every
  entry before `Map.set` or `Set.add`.
- **Size charges.** Under a finite `maxBytes`, decoding charges the value's size (`size.ts`,
  `Size.lean`) along the way: headers, slots, declared lengths, binary sizes and the node count
  before they are allocated; URL, search parameter, Temporal and bigint text right after
  construction; strings, literals and bigint occurrences while resolving slots. It reads a
  literal's own keys and values to charge them, so a caller-built literal's getters would run,
  and it rejects a literal `JSON.parse` cannot produce. With `Infinity` it reads no literals.
- **Measuring.** `requiredMaxBytes` runs the decoder's checks and charges without restoring the
  value (`measureGraph` in `decode.ts`).

## Making a change

Every change ends with its checkpoint in [Checks and time budget](#checks-and-time-budget).

- **Behavior fix.** Write a failing test that states the contract, then fix the code. A changed
  expectation needs a contract argument, not agreement with the new implementation. Do not turn
  an expected failure (`it.fails`) or a skipped test into a passing one, or the reverse, without
  stating the contract change. A bridge can encode the old behavior too, so the checkpoint's
  `lean` round can fail; [Checks and failures](lean.md#checks-and-failures) says how to resolve a
  mismatch.
- **Finite algorithm or new feature.** Work proof first, following [Adding or changing a
  model](lean.md#adding-or-changing-a-model); the reference models (`Spec.Reconcile`,
  `scripts/check/bridges/spec.ts`) are the worked example. Then implement. Run these tests early,
  because they catch unsound shortcuts: the public API fuzz files
  (`src/__tests__/public-api-fuzz*.spec.ts`); the invariants file
  (`src/__tests__/public-api-invariants.spec.ts`), which checks the documented contracts on graphs
  of up to 120 objects; the native differential file
  (`src/__tests__/native-differential.spec.ts`), which compares `produce` and `reconcile` results,
  descriptors included, with native JavaScript applied to plain copies; and the stress file
  (`src/__tests__/reconcile-keeps-next-stress.spec.ts`), which builds `next` from `current` with
  immutable idioms and `produce` recipes and checks, with the helpers in
  `src/__tests__/fixtures/graph-state.ts`, that `reconcile` never changes `next`. The README rules that let a
  result differ from native mutation are the policies in the native differential fixture.
- **Public API or errors.** Update the TSDoc and the README, its API section included, by hand.
  A new export also goes into `OPERATIONS` or `OTHERS` and the smoke `checks` in
  `scripts/bundles.ts`. Errors follow `src/error.ts`: one factory per
  type, so bundles keep only the errors they raise; names of the form
  `<Phase><Subject><Condition>`, such as `DeserializeLimitExceeded`; and only facts the
  detecting phase already holds.

### Adding a built-in kind

A new kind changes every operation's contract and bundle.

1. **Prove first.** Recognition is proved for a fixed sequence of probes (`probes` and `scanTrace`
   in `Types.RecognitionPlain`), so a new kind needs its probe there and the module's theorems
   proved for the longer sequence. A kind that can accept a plain or `null`-prototype object also
   invalidates `plain_probes`, which lets `builtinFirstMatch` decide such an object plain from its
   one prototype read. A kind that is kept by reference today also changes `Types.Atoms` and
   `scripts/check/bridges/atoms.ts`. A kind that `produce` copies when read also changes `Kind`,
   `WF` and `differs` in `SpecialValues` and the SpecialValues bridge's scenarios. A kind that
   `reconcile` publishes outside the `Spec` model, as it does a URL, changes `Types.NativeWrites`.
   Extend the fixtures of the native-value and copy-prototype bridges.
2. **Write the module** in `src/types/<kind>.ts`, supplying each facet that
   [Type modules](#type-modules) lists for it and using `src/standard-prototypes.ts` for every
   internal object and read.
3. **Register it.** Choose its position before any kind whose recognition also accepts it; the
   plain object stays last. Register it in `src/types/builtins.ts` at that position in `KINDS`,
   every facet table and the unrolled `builtinFirstMatch` and `builtinRemainingMatch` chains. In
   the two chains, add a `last === <position>` check after the new predicate, renumber the later
   ones and increase `FALLBACK_RANK`. Add it at the same position to the ordered scan in
   `scripts/check/fixtures/recognition-scan.ts`, against which the tests check recognition.
4. **Update the couplings** below: the counter rules in `scripts/bench/counts.ts`, the
   snapshot walk if the kind is observed inline, and for serialization a wire tag with its
   facets, size charge, Lean format and README entries, or else `serialize` rejects it.
5. **Check** with `builtin-recognition.spec.ts` and `builtin-facets.spec.ts`, then `pnpm check`,
   `pnpm bench size` and a default `ab` round.

### Changing the wire format

Serialized data carries no format version, so stored data from an
earlier version stops decoding.

1. Change `Serialization/Positional.lean` first, and `tableCharges` in `Serialization/Size.lean` if
   sizes or the record, array or bigint tags change.
2. Change the tags in `layout.ts` with the `decoders` table in `facets/decode.ts` and the tag
   choice in `facets/index.ts` and `native.ts`, the encoder and decoder, the charges in
   `facets/*.ts`, and the README's _How size is counted_ table.
3. Update every spec with a hand-written wire document, including `serialization*.spec.ts`,
   `deserialize-limit.spec.ts` and `arktype-contract.spec.ts`, and the corpus of
   `scripts/check/bridges/serialization.ts`.
4. Run `pnpm check`, `pnpm bench size`, and `ab` on `serialize` and `deserialize`; those
   workloads measure value to text and back, so they compare across a format change.

### Couplings that fail silently

Some code and tooling must change together, and `pnpm test` does not catch a mismatch: it breaks
`pnpm check lean`, the counters, the measurements, the package or an invariant. Change both
sides together.

- **Profile harness.** `scripts/bench/harness.ts` rewrites `perf/profile-harness.ts` by exact
  text (the `./scenarios` imports, the `profileScenarios` registry, the measurement loop) and, for
  the `diag-*`, `serialize`, `deserialize` and small scenarios, imports the measured tree's
  `src/index.ts`. Renaming or moving any of these breaks `pnpm bench profile`, `counts` and `ab`,
  which bundle the same harness. These scenarios always come from the current checkout's
  `scripts/bench/diagnostics.ts`.
- **Counters.** `scripts/bench/counts.ts` instruments call sites by file path and exact callee,
  function or expression text. `counts.spec.ts` fails only when one of its four
  text-matched counters finds no site at all or the `observation.events` sites leave their two
  files; renaming or moving any other rule's site, such as
  `propertySlots` or `matchesKind`, drops a counter, and a new recognition predicate in
  `builtins.ts` gets none.
- **Test fixtures in the tooling.** `scripts/check/bridges/compact-immutable.ts` imports
  `src/__tests__/fixtures/compact-immutable.ts`, so changing that fixture for a test also changes
  a `pnpm check lean` corpus.
- **Hooked bridges.** The DeferredOrder, phase, SpecialValues and CollectionWrites bridges bundle
  the sources with recorder calls after exact statements: three in the preflight of
  `types/shared/property-publication.ts`, two in `publishGraph`
  (`publication/publication-engine.ts`), one after the first line of `chooseSpecial`
  (`graph/provenance.ts`), and two in `types/shared/collection.ts`, one after the signature of
  `collectionSurface` and one after the statement that sets `note.unchanged`. Editing, moving or
  duplicating one of those statements, or renaming one of those files, breaks `pnpm check lean`.
- **Lean names in comments.** Source comments name their Lean theorems, and nothing checks them.
- **Serialization bridges.** `scripts/check/bridges/serialization.ts` requires Lean's re-emission to
  equal every `serialize` output in its corpus, so a wire change fails `pnpm check lean` until
  `Positional.lean` changes too. `scripts/check/bridges/serialization-collection.ts` calls the production
  `map` and `set` decoders with a hand-built `DecodeContext`. The record, array, literal and
  bigint charges exist three times: in `facets/*.ts`, in `Size.lean`'s `tableCharges`, and in the
  README's size table. The `Map`, `Set` and native charges exist only in `facets/collection.ts`,
  `facets/native.ts` and the README. Nothing checks the README.
- **Snapshot walk.** For the kinds it observes inline (listed under
  [The graph operations](#the-graph-operations)), `snapshot.ts` repeats, in the same order, the
  reads that each kind's capture facet makes in `observe`, except that a buffer's or view's copy
  takes the prototype recognition read and a view's reads its element type once (`Types.Ingress`);
  `viewBuffer` repeats the view facets' buffer-edge answer. A capture change for these kinds must be
  made there too.
- **Head shortcut.** Identity restoration tries `immutableHead`'s mask before searching, because
  the head theorem proves it comes first.
- **Mangle list.** A name in `scripts/constants.json` that is also read on an application or
  native object, or is public, breaks only the built package, which `pnpm check lib` tests.
- **Library tests.** `vitest-library.config.ts` redirects only imports of the entry modules it
  names to `lib/neutral/index.js`; a test that imports another source module tests the sources
  under `pnpm check lib`.

## Checks and time budget

While editing, run the narrowest check:

| Change                           | While editing                                                     |
| -------------------------------- | ----------------------------------------------------------------- |
| Runtime behavior                 | `pnpm exec vitest run src/__tests__/<file>.spec.ts`               |
| Types, declarations or exports   | `pnpm typecheck`                                                  |
| Finite algorithm or Lean         | `lake build <Module.Name>`, then `lake env lean lean/<Path>.lean` |
| A runtime-to-Lean bridge         | `pnpm check lean <bridge>`, or the command a failure prints       |
| Bundle, packaging or mangle list | `pnpm bench size`, which builds the tree first                    |

At each checkpoint, run `pnpm check`. It runs, one after another, each _round_ that has not
passed on its current inputs: `static`, `test`, `lib`, `temporal`, `lean` and `mutants`, which
`pnpm check --help` describes. It stops at the first round that does not pass, unless given
`--keep-going`. `pnpm check <round>` runs one round, `--plan` says what would run and why, and
`--fresh` runs a round even when it has passed. A round's inputs are the content and executable
bit of every file of the working tree that `scripts/check/rounds.ts` does not exclude for it,
tracked or untracked but not ignored, plus the platform, the Node version, the installed
dependencies and `NODE_OPTIONS`.

Each round, and each `pnpm bench` command but `report`, runs within a 295-second budget and
holds a machine-wide lock, so no two of them overlap. Other commands take no lock, so run a round
only when nothing else is running. A round stops every process it started when it ends, runs out
of budget or is interrupted, including a descendant that left its process group but holds the
step's output; if the round itself is killed, the next round stops what it left running. It keeps
its logs and a receipt under `$XDG_STATE_HOME/reconcile/runs`, by default
`~/.local/state/reconcile/runs`, or in the experiment of a `pnpm bench` command that names one.
`RECONCILE_STATE` moves that state directory, which also holds the recorded passes, and
`RECONCILE_LOCK` the lock, by default `/tmp/reconcile-round.lock`.

The exit code says what a run established, and with `--keep-going` the most severe code counts:

- 0: every round passed.
- 1: a check failed.
- 2: a usage error.
- 3: nothing was judged: a tool is missing, another round holds the lock or the tooling itself
  failed.
- 124: incomplete, not a pass: a round ran out of budget, or files it reads changed while it ran.
  Rerun the whole round.
- An interrupt (Ctrl-C, SIGTERM or SIGHUP) stops the round, keeps its receipt and ends the command
  by that signal, which a shell reports as 130 for Ctrl-C; a second interrupt stops the steps at
  once. Node restores SIGHUP's default action when it starts, so `nohup` does not keep a run alive
  after logout; `setsid` or a terminal multiplexer does.

A cold `lake build` takes most of a round's budget, so load on the machine can time out the first
round that builds the proofs, usually `temporal`.

`pnpm test` runs every spec in the neutral project, and again in the poisoned project all except
those that run no library code in their own process; the poisoned project's setup file,
`src/__tests__/fixtures/poisoned-prototypes.ts`, says what it catches.
[Running the gate](lean.md#running-the-gate) describes the `lean` round, and
[Checks and failures](lean.md#checks-and-failures) says how to resolve a failure.

**Optional native features.** The Temporal cases, including serialization of the eight Temporal
classes, skip without a global `Temporal`. `pnpm check temporal` runs them with Node's
experimental flag on the sources, on the built package and through the bridges. This checks the
available implementation, not conformance. Without native `Uint8Array` base64 the binary codec
takes a fallback path; `src/__tests__/serialization-boundaries.spec.ts` checks its validation
through stand-ins.

## Performance work

### Experiments and rounds

`pnpm bench control` freezes a _control_: it exports a revision, `HEAD` by default, or with
`--worktree` the working tree, into a new _experiment_ under `$XDG_STATE_HOME/reconcile/experiments`.
A command given `--control <experiment>` compares the measured tree with that control and keeps its
rounds in the experiment, which `latest` names when it is the newest; `--control` also takes any
source tree, such as a scratch copy, whose rounds no experiment keeps. `--tree` names the measured
tree, this checkout by default. Both trees run and build with this checkout's dependencies, so
`pnpm bench size` cannot build a control whose build needs a tool this checkout no longer
installs. Both must hold the same frozen workloads in `perf/`. An experiment pins its control:
once the control's sources or frozen workloads change, commands refuse the experiment.

- A _default round_ is `pnpm bench ab default --control <experiment>` over the six default
  scenarios, and a _small round_ is `pnpm bench ab small` over the ten small ones. Each guards
  against large regressions only, and a change runs both.
- A _deciding round_ is `pnpm bench ab <scenario> --decide`: 32 pairs, each process measuring for
  about a second. Two deciding rounds are two separate runs.
- An _A/A round_ passes the control's own tree, `tree/` in the experiment, as `--tree`, to check
  noise.
- A _package round_ adds `--package`: each tree's workloads run its built package, which the
  round builds first, instead of its sources. Time a change to the build, such as a Rolldown
  option, this way; a source round cannot see it.
- `pnpm bench report` judges together only rounds that measured the same things: rounds that
  passed, against the control as it was frozen, with the same frozen workloads in both trees. A
  diagnostic's readings combine only across rounds of the same shared workloads and `--size`,
  package rounds only with package rounds of the same packages, and a size comparison counts only
  for the sources or package judged.

The header of `scripts/bench-workloads.ts` says what each scenario runs. The serialization and small
workloads live outside `perf/`, so they run against any control. The `diag-*` diagnostics in
`scripts/bench/diagnostics.ts` target particular shapes, and most scale with `--size`; add one for
a new shape instead of changing a frozen workload. `pnpm bench --help` lists every scenario.

### Protocol

1. **Freeze a control** with `pnpm bench control`.
2. **Write down the hypothesis** before measuring: which repeated work disappears, which counters
   fall or stay equal, and the expected effect, checked with the cost screen below. For an idea
   taken from another library, read its original change and later fixes, and find out who owns
   the data and what invalidates it.
3. **Locate the work** on the control with `pnpm bench profile <scenario>` and
   `pnpm bench counts <scenario>`, each with `--tree` set to the control's tree.
4. **Bound before building.** When the gain is uncertain, remove the work unsafely in a scratch
   copy and time that copy, as `--tree`, with a deciding round. If even the unsafe bound does not
   read faster, drop the idea before any proof work.
5. **Change one thing,** then run `pnpm bench counts <scenario> --control <experiment>`. Stop if
   the predicted counter does not fall or another counter moves; otherwise run a default round to
   check for losses. If the first version misses, one further change justified by the counts or
   profile is allowed; then keep the change, or revert it and reject the hypothesis.
6. **Check semantics beyond the tests.** Near an observation boundary, compare results, errors and
   identities with the control's, and check that each trace difference keeps the read discipline in
   [What must not change](#what-must-not-change). Write a one-off script outside the repository
   that imports both trees' `src/index.ts` and runs a few thousand seeded graphs wrapped in logging
   proxies, covering getters, null prototypes, frozen objects, holes, collections, buffers, sharing
   and cycles; `randomSource` and `graphsEqual` in `src/__tests__/fixtures/public-api-fuzz.ts`
   help. Plant a mutant for each new guard to confirm that a test kills it.
7. **Time it** with a default round, a small round and two deciding rounds on the target, and
   **measure bundles** with `pnpm bench size --control <experiment>`, which builds both trees.
8. **Run the checkpoint and report** the outcome alongside the change: each workload's reading
   against the control, which `pnpm bench report` gathers, and the bundle-size change. Keep
   one-off scripts outside the repository.

**Acceptance.** Report `snapshot`, `reconcile`, `reconcile-plain-object` and `produce` separately,
plus `serialize` and `deserialize` when serialization changes, and the small scenarios of each
function a change affects. Keep an optimization only when two deciding rounds both read _faster_ on
its target: the 90% interval lies below zero and the median gains at least 2%. The default and
small rounds guard the other workloads: one that reads _slower_ or _slightly slower_ there needs a
deciding round of its own, and a deciding round that reads _slower_ (interval above zero, median
beyond the 3% guard) rejects the candidate. A stress-case win does not excuse an ordinary loss.
Counters stay equal unless the hypothesis says they move. When the hypothesis predicts a large
gain, write it down as the target before measuring, for example 20% with at least 28 of 32 faster
pairs; a result below the target rejects the hypothesis.

**Cost screen.** With `f` the time share of the affected region, `s` its speed-up and `h` added
cost elsewhere, `new / old ≈ (1 − f) + f / s + h`. A region taking 3% cannot save more than 3%;
20% from a region taking 70% needs it 1.4 times faster. Profiler shares are upper bounds.

### Reading results

`pnpm bench --help` and `pnpm bench <command> --help` list the commands, scenarios and flags. Each
command but `report` prints the directory that keeps its output and receipt.

- **`ab`** prints its table and writes it, with its reading legend, to `report.md`, beside
  `plan.json`, which records the design before the first sample, and `samples.json`. Explicit
  `--batches` and `--warmup` override the automatic sizing, as a heavy diagnostic size needs.
- **`report`** gathers an experiment's `ab` rounds of this checkout's sources, or else of the
  latest sources measured, and apart from them its package rounds of the latest package measured:
  each workload's readings, what the acceptance rule concludes for it as a target and as a guard,
  and which of the default and small rounds and the size comparison are missing. A round whose
  trees time the same sources, or in a package round the same package, is an A/A round, which it
  counts apart.
- **`profile`** writes `summary.json`, the raw artifact (under `raw/`) and the bundle with its
  source map:
  - `--mode cpu` (the default) and `--mode heap` sample time or allocation and attribute frames
    to source through the bundle's source map; the raw `.cpuprofile` and `.heapprofile` files
    open in Chrome DevTools. Samples include fixture work.
  - `--mode deopt` traces optimizations and deoptimizations; treat them as signals only.
- **`counts`** counts instrumented source events (constructions, not allocations), such as
  recognitions, memo hits and alias visits. Counts are exact, so one run per tree decides; with
  `--control`, each scenario's `comparison.json` lists each counter that differs as
  `[control, tree]`. Timing comparisons belong to `ab`.

### Traps

- **Ratio orientation.** A hand-written comparison must print which tree is the numerator, since an
  inverted ratio reports a loss as a gain.
- **Too few pairs.** A gain of a few percent needs 32-pair rounds; 16-pair rounds of one change
  can disagree in sign.
- **Too little measured work.** Short processes are noisy. Keep the automatic batch sizing.
- **Load.** Another process on the machine moves results by several percent; `pnpm bench` warns
  when the load average is above 1.

## Bundle size and tree shaking

Consumer bundlers drop code that no used export reaches (_tree shaking_). These rules keep it so.

- The package declares `sideEffects: false`, but every top-level value must also be removable
  on its own: the built file is one module, so an unannotated top-level call (`Object.freeze`,
  a property read) stays in every consumer bundle. Mark such initialization
  `/* @__PURE__ */`, wrapping a property read in an annotated function.
- Pure annotations mark only private module initialization (computed symbol keys, draft classes,
  frozen policy tables, serialization tables). They never permit skipping a native read.
- Each operation reaches only its own facets. Keep publication code out of capture and graph
  code out of `src/serialization/`. `produce` copies special values through the registry's
  `specials` facet, so it carries no snapshot code.
- `serialize` and `deserialize` share no decoder or encoder code: encoding failures raise the
  `Serialize` error and decoding failures the `Deserialize` errors, so each bundle keeps only its
  own.
- Lookup sentinels are private objects, so no stored value can equal one.
- The mangle list holds only protocol fields, facet members and private methods. Descriptor
  fields, collection and iterator methods, proxy trap names and keys used with `in`
  stay unrenamed.
- Ordinary consumer minification renames identifiers, not properties. A consumer that enables
  opt-in property mangling must restrict it to its own private properties and keep library,
  native and public property names; the package ships its own audited mangle list.

The `lib` round also bundles an import that uses nothing with `sideEffects` ignored; that bundle
must be empty, which is the check that catches an unannotated top-level call.

To find which module grew, `pnpm bench size --modules <exports> --control <experiment>` lists the
bytes each source module adds to the minified bundle of those exports, as the bundle's source map
attributes them. The bundle is built from the sources as the package build does, internal
properties renamed; its total is close to the package bundle's, not equal. Profile and `ab`
bundles are unmangled, so take sizes only from `size`.
Gzip removes repetition, so only removing distinct logic saves bytes.

## JavaScript engine notes

These V8 behaviors constrain code that runs per node or per slot.

- **Per-node allocation.** `Map`s, `Set`s, closures, spreads and iterator destructuring in loops
  over nodes or edges cost time, as do closures passed to array builtins in once-per-call scans.
- **JSON.** Small integers parse inline; a float in an integer row makes a double array whose
  reads box. An all-array document keeps V8's `JSON.stringify` fast path, which one integer-like
  object key disables.

## Design choices

These choices are deliberate; changing one changes the contract or reopens a settled trade-off.

- **Positional wire.** Serialization never marks control in-band, as libraries that tag strings
  do; a slot's kind comes from its node's layout, so no data value can reach control.
- **A required `maxBytes` on the decoded value's size**, with every object counted once and every
  primitive where it occurs. Counting values alone misses repeated keys, bigints and overlapping
  views; counting tree size rejects legitimate shared graphs and cycles; counting excess over the
  input makes the limit depend on the wire format.
- **No format identifier, quotas, custom codecs, replacers or revivers** in serialization.
- **`ReconcileError` with a typed `cause` and no `path`**, which would cost every call for the
  failure case.
- **Writing by assignment.** `reconcile` assigns changed own properties, so own setters run and
  own accessors stay, and never writes or overrides an accessor on the prototype. Never running
  setters breaks accessor-based reactivity.
