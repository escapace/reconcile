# Lean proofs and runtime correspondence

The `lean/` directory holds Lean 4 proofs about the finite algorithms behind `snapshot`,
`reconcile`, `produce`, `serialize` and `deserialize`, and the oracles that the bridges compare
with the TypeScript runtime. Read this guide to learn what a proof guarantees, which model covers
the code you are changing, which facts the runtime must supply itself, and how to add or change a
model. Project-wide commands and budgets are in the [development guide](development.md).

## What the proofs cover

Three kinds of evidence work together:

- **Proofs** establish properties of finite algorithms and of the public contracts over a finite
  heap model. They do not formalize JavaScript, a JavaScript engine or native constructors.
- **Bridges** are scripts that run the TypeScript runtime on a _corpus_, a fixed set of
  enumerated or hand-written cases, and compare its results with a Lean _oracle_: an executable
  Lean definition compiled into `reconcile-oracle` and selected by its _family_ name. A corpus is
  evidence for its cases, not a proof for every input.
- **Runtime obligations** are facts the TypeScript code must supply itself, such as the order of
  native reads. Native tests and bridges cover them, never a proof or axiom.

A theorem therefore reads: if the runtime supplies these facts, the algorithm produces this result.
No whole-library correctness, resource-exhaustion, memory or speed claim follows from the proofs.

A _reference model_ is a direct definition that optimized code must agree with: `GraphPolicy`
defines the ranked selection stream that `produce`'s identity restoration refines, and
`Construction` the construction schedule. The `Spec` modules are reference models of the public
functions themselves: executable definitions of `reconcile`, `produce` and `snapshot` over graphs
with descriptors, which the `Spec` bridge compares with the runtime on seeded random graphs, and
about which `Spec.Promises` proves the documented promises.

## The heap model

`Heap/Defs.lean` defines finite heaps of atoms and references: plain objects with ordered fields,
arrays with holes, ordered maps and sets, dates, buffers and views. Functions are opaque atoms, and
so are objects whose state the library cannot copy, such as a `RegExp`, `Error` or `WeakMap`;
`Types.Atoms` proves how the runtime classifies them. `Heap/Defs.lean` also defines `HeapWF`, which
guarantees that every reference points into the heap, not that the heap is natively valid.
`Heap/WF.lean` defines edges, reachability and `SurfaceEq`, equality of two values at every finite
depth, by which the specifications compare results.

The model does not derive JavaScript semantics. Capture supplies key order and normalized atoms, so
enumeration order, `SameValue`, `SameValueZero` and byte decoding are outside it.
So are invalid dates, typed arrays without a valid constructor tag, non-index array properties and
arbitrary exotic objects.

Identity and storage are separate abstract labels in the models; neither describes physical
memory. The runtime labels each object's storage with the object itself, and several views can
share one explicit buffer node. Ownership proofs assume correct labels; they do not discover hidden
aliases.

## Adding or changing a model

[AGENTS.md](../AGENTS.md) sets the order of work and what must be kept. On the Lean side:

1. **Renames.** A rename that keeps a theorem's statement needs no alias.
2. **Examples.** Put an example whose premises hold, and a counterexample for each premise that
   matters, beside the model.
3. **Name the runtime obligations.** State which premises the runtime must establish and how, as
   the _Full capture_ obligation does, and list them under [Runtime obligations](#runtime-obligations).
4. **Place and register every file.** A model goes in its area's directory under `lean/`:
   `Heap/`, `Spec/`, `Property/`, `Graph/`, `Produce/`, `Types/` or `Serialization/`; its oracle
   goes in `Oracle/`. List the module in `roots` in
   `lakefile.toml`. The axiom audit rejects unlisted files and roots without a file, so change
   both together.
5. **Add an oracle and a bridge.** Give the oracle a namespaced `run` function, add its family to
   `Oracle/RuntimeOracle.lean`, and call it from a bridge run by `check-lean.ts`. Keep
   hand-written fixtures as JSON in `lean/fixtures/`. Prefer comparing
   production code, and say so when a bridge runs a reference transition. Renaming an oracle
   namespace or a fixture file breaks the bridge that uses it.
6. **Document it** in this guide: the correspondence row, its obligations and a bridge-table row.

## Running the gate

`pnpm check:lean` (the _gate_) runs `lake build --wfail`, so a warning fails it, then audits axioms
and runs every bridge against one oracle process. Its budget and receipt are in
[Time budget](development.md#time-budget).

Extra arguments go to Node. `pnpm check:lean --harmony-temporal` adds Node's native Temporal values
to the `NativeValue` bridge, which otherwise skips them and says so. For the commands to use while
editing, see [Checks and time budget](development.md#checks-and-time-budget). Only the `Spec`
bridges have standalone entries: the outcome bridge, the phase bridge and the enumeration.
[Runtime bridges](#runtime-bridges) describes them, the mutation audit that checks them and how to
query one oracle by hand.

## Checks and failures

The axiom audit allows only `propext`, `Classical.choice` and `Quot.sound`, so a `sorry` fails it.

When the gate fails:

- **Build or audit.** Fix the warning, register the file or remove the axiom. Never add an axiom.
- **Bridge mismatch.** Decide which side changed. Fix an accidental runtime change in the runtime.
  For a deliberate contract change, change the model first, then the corpus and the bridge. Never
  change an oracle to make it agree with the runtime. Reproduce one family by hand as shown in
  [Runtime bridges](#runtime-bridges).
- **Instrumentation or field-name assertion.** A bridge that rewrites source text names the
  replacement that failed; update its search text and keep the instrumentation at the same points.
  Keep oracle field names and translate in the bridge. See
  [Couplings that fail silently](development.md#couplings-that-fail-silently).
- **Timeout.** See [Time budget](development.md#time-budget).

## Correspondence

The tables below map every module in `lakefile.toml` to the runtime code it covers, grouped by
operation. The oracle modules are the exception; [Runtime bridges](#runtime-bridges) names them.
_Key theorems_ lists the statements a reader most needs; each module holds more. _Bridge_ names the
oracle family that executes the module's definitions against the runtime, or says _proof-only_; a
proof-only module is still built and audited. _Obligations_ names the
[runtime obligations](#runtime-obligations) the correspondence relies on. The [Promises](#promises)
table instead maps the main promises of the public functions to their theorems, bridges and tests.

### Heap model and public contracts

| Module(s)     | Key theorems                                         | Runtime                                                                                                                       | Bridge               | Obligations       |
| ------------- | ---------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------- | -------------------- | ----------------- |
| `Defs`, `WF`  | `HeapWF` (definition)                                | captured graphs: `src/publication/capture.ts` (`reconcile`), the walk in `src/snapshot.ts`, `src/finalization.ts` (`produce`) | imported by Contract | Capture           |
| `Publication` | `publishRecords_published`, `checkPublication_sound` | `src/publication/*`                                                                                                           | imported by Contract | Capture, Identity |

### Reference models

| Module(s)        | Key theorems                                                        | Runtime                                                          | Bridge            | Obligations                 |
| ---------------- | ------------------------------------------------------------------- | ---------------------------------------------------------------- | ----------------- | --------------------------- |
| `Spec.Graph`     | `Graph.normalize` (definition)                                      | the graphs the bridge builds and reads back                      | Spec              | Spec agreement              |
| `Spec.Reconcile` | `run`, `discover`, `decide`, `demote`, `retainPrefix` (definitions) | `src/reconcile.ts` `reconcile`                                   | Spec, Spec phases | Spec agreement, Spec phases |
| `Spec.Produce`   | `run`, `kept`, `rebuild`, `snapshot` (definitions)                  | `src/produce.ts` `produce`, `src/snapshot.ts` `snapshot`         | Spec              | Spec agreement              |
| `Spec.Promises`  | most theorems in [Promises](#promises)                              | the documented promises of `reconcile`, `produce` and `snapshot` | Spec              | Spec agreement              |

`Spec.Graph` is a heap of plain objects with ordered fields, each a data property with its
attributes or an accessor with the value its getter returns and whether its setter stores,
extensibility, and a prototype label; arrays with holes and an integrity level; maps, sets and
dates; buffers with their bytes and, when resizable, their maximum length; typed arrays and
`DataView`s with their constructor, buffer, byte offset and byte length; primitives and atoms. A
`reconcile` input also gives each class label its own slots, data or accessor, which every object
with that label inherits. `Graph.normalize` reads an empty non-extensible array as sealed, as the
integrity test does.

`Spec.Reconcile.run` is the deterministic reference: a read phase that aligns `next` with `current`
and pins objects already in place, a decision in visit order that keeps an aligned object when it
admits `next`'s contents statically, and a write phase that demotes a kept object whose write
reaches a fixed slot or a setter that drops its value and decides again, never keeping a demoted
object and keeping each object a pass wrote at its node. An object cannot be kept when `next` has a
key that the object lacks and its class holds as an accessor. A buffer is kept only when its length
and maximum length equal `next`'s, and a view only when its constructor, byte offset and byte length
do; a view's buffer counts as a fixed slot. The reference returns the result graph with the object
kept at each node, the writes, the number of passes and the getter counts. `retainPrefix`, the
longest prefix of `next`'s key or entry order that is a subsequence of `current`'s, decides which
keys and entries keep their place. `Spec.Produce.run` applies a recipe of draft operations to a
draft heap and keeps the greatest set of unchanged subtrees (`kept`). A draft reads a `Date`, buffer
or view as a copy. When the copy differs from the original, the result holds the copy in the
original's place, possibly inside a new object. `Spec.Produce.snapshot` copies every node.

`Spec.Promises` proves, about these definitions:

- The retained prefix is a prefix of `next`'s order, a subsequence of `current`'s and the longest
  such prefix (`retainPrefix_prefix`, `retainPrefix_sublist`, `retainPrefix_longest`).
- A getter of `current` runs at most once when its object is read and once per decision pass, and
  at most once when no pass writes (`get_bound`, `read_once_before_write`).
- The decision passes are bounded by the number of node pairs, so no plan is searched
  (`passes_le`).
- A retained key is written exactly when its value differs, and a moved or added key is always
  written (`objectWrites_set_iff`, `objectWrites_delete_iff`). Array elements and lengths, `Map`
  and `Set` entries, a date's time and a buffer's bytes follow the same rule, and a view takes no
  write (`arraySlotWrites_set_iff`, `arraySlotWrites_delete_iff`, `arraySlotWrites_length_iff`,
  `entryWrites_set_iff`, `entryWrites_delete_iff`, `entryWrites_fresh_iff`, `writesOf_date`,
  `writesOf_buffer`, `writesOf_view`). No write reaches a slot that already holds `next`'s value
  (`objectWrites_unchanged`, `arraySlotWrites_unchanged`, `entryWrites_unchanged`). A kept node
  takes no write exactly when its object already holds `next`'s contents under the decision's
  identities, given distinct keys and identities that keep each object at one node
  (`writesOf_nil_iff`). Every decision of the passes keeps each current object at one node, given
  that `same` maps distinct pinned nodes to distinct objects (`decide_injective`,
  `demote_injective`), so the identity premise holds for every node a pass keeps
  (`demote_writesOf_nil_iff`). The theorems name array slots and `Map` and `Set` keys structurally
  (`ArraySlot`, `EntryKey`), because a `Map` or `Set` write reports its key as text, which two
  distinct keys can share.
- A kept object keeps the attributes of every property it had and adds each other property
  writable and configurable, with `next`'s enumerability (`keptObject_attrs`).
- A pass demotes only a blocked object: one with a write that reaches a fixed slot or a setter
  that drops its value (`mem_blockedObjects`). It never demotes an object an earlier pass demoted,
  so every pass that continues demotes a current object for the first time (`blocked_fresh`).
- A candidate whose fixed slot requires another object at the candidate's own node can never be kept
  with that object. The candidate order ignores such a requirement, so it does not reorder that
  node's candidates (`demands_satisfiable`). A candidate whose fixed slots require two objects at
  one node, or another object at a pinned node, is not admitted, so it reorders no node
  (`admitted_pins`, `demands_pinned`).
- A node's origin is the current object it keeps; a node that keeps none holds a fresh copy of
  `next`'s node and has no origin (`publish_origins`, `publish_fresh`).
- `produce` keeps a current object exactly when its subtree is unchanged; `kept` is the greatest set
  closed under the keep conditions (`kept_closed`, `kept_greatest`).
- `snapshot` makes one copy per source node and shares no object with the source (`snapshot_size`,
  `snapshot_copy`, `snapshot_fresh`).

Four counterexamples each show, on one input, a wrong definition that a theorem rules out:
retaining only the common prefix, reading back after a write-free pass, writing every key and
re-adding a moved key as plain data. The runtime meets these promises exactly as far as the bridge
shows it agrees with the reference.

### Promises

The table maps the main promises of the public functions to the theorems that state them over
the Lean models, the bridges that carry them to the runtime and the tests that check the
runtime directly. A row whose _Theorems_ cell reads _tested only_ has no proof.

| Promise                                                                                                          | Theorems                                                                                  | Bridge                                                               | Tests                                                                                                      |
| ---------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- | -------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| Keys and entries keep their place; the retained prefix is the longest                                            | `retainPrefix_prefix`, `retainPrefix_sublist`, `retainPrefix_longest`                     | `Spec` (results; not moves inside a `Map` or `Set`), `PropertyOrder` | `reconcile-property-order.spec.ts`                                                                         |
| An own getter of a kept object runs once without writes, twice with them and at most once more per demotion pass | `get_bound`, `read_once_before_write` (upper bounds)                                      | `Spec` (getter counts), `WriteFreeReadback`                          | `write-free-readback.spec.ts`                                                                              |
| The decision passes are bounded, so no plan is searched                                                          | `passes_le`, `blocked_fresh`                                                              | `Spec --writes --hazards` (getter counts and writes of every pass)   | `public-api-invariants.spec.ts` (hostile setters)                                                          |
| A changed slot is written, an unchanged one left alone, a moved or added one written                             | `objectWrites_set_iff`, `writesOf_nil_iff`, `Types.NativeWrites.publish_nil_iff`          | `Spec --writes` (writes to objects and arrays)                       | `write-free-readback.spec.ts`, `reconcile-accessors.spec.ts`, `public-api-invariants.spec.ts` (write-free) |
| A kept property keeps its attributes; an added one is writable and configurable with `next`'s enumerability      | `keptObject_attrs`                                                                        | `Spec` (descriptors), `PropertyWrite`                                | `public-api-invariants.spec.ts`, `property-enumerability.spec.ts`                                          |
| An object that blocks a change is replaced; a pass demotes no other object                                       | `mem_blockedObjects`                                                                      | `Spec --writes --hazards` (results)                                  | `publication-readback-boundaries.spec.ts`, `publication-failure-boundaries.spec.ts`                        |
| A node with several candidates keeps the first one read unless an admitted candidate's fixed slot needs another  | `demands_satisfiable`, `demands_pinned`; the order is the definition `orderedCandidates`  | `Spec` (identities)                                                  | `demanded-candidates.spec.ts`                                                                              |
| Added objects are new copies                                                                                     | `publish_origins`, `publish_fresh`                                                        | none; `Spec` identifies only current objects                         | `reconcile-semantics.spec.ts`                                                                              |
| `produce` keeps every unchanged subtree and no changed object                                                    | `kept_closed`, `kept_greatest`                                                            | `Spec --op produce` (results)                                        | `produce-properties.spec.ts`, `public-api-invariants.spec.ts`                                              |
| `snapshot` is a detached copy, one new object per source object                                                  | `snapshot_size`, `snapshot_copy`, `snapshot_fresh`                                        | `Spec --op snapshot` (results)                                       | `public-api-invariants.spec.ts`, `graph-capture.spec.ts`                                                   |
| `next` is read once; an object already in place is read as part of `next` and not again                          | tested only                                                                               | none; `Spec` leaves out the getter counts of objects `next` holds    | `reconcile-pruning.spec.ts`                                                                                |
| Each object's prototype is read once before the first write                                                      | `Types.Ingress.ownReads_shared` (at recognition); the rest tested only                    | `Ingress`, `RecognitionPlain` (read counts)                          | `builtin-recognition.spec.ts`, `ingress-reads.spec.ts`                                                     |
| `produce` calls each getter of the result once, depth first, and reads each draft once                           | tested only                                                                               | `DraftSurface` (results)                                             | `produce-reads.spec.ts`, `finalization-observation-boundaries.spec.ts` (once; the order is untested)       |
| `produce` and `snapshot` leave `current` unchanged                                                               | tested only (the models are pure)                                                         | `Spec` (`current-changed` report)                                    | `produce-properties.spec.ts` (`produce`)                                                                   |
| `serialize` calls each getter once, depth first                                                                  | tested only                                                                               | none                                                                 | `serialization.spec.ts`                                                                                    |
| `deserialize` restores ordinary, extensible objects                                                              | `PropertyWrite.constructFromOn_fresh` (each restored property); extensibility tested only | `PropertyConstructOn` (descriptors)                                  | `public-api-invariants.spec.ts`                                                                            |
| `deserialize` accepts at exactly `requiredMaxBytes` and rejects one byte below                                   | `Serialization.Size.accepts_iff_bytes` (the boundary)                                     | `Serialization` (the size `requiredMaxBytes` returns)                | `deserialize-limit.spec.ts`, `public-api-invariants.spec.ts`                                               |

### `snapshot`

`snapshot` is `Spec.Produce.snapshot` in [Reference models](#reference-models), a new object per
source object with atoms shared; the Spec bridge checks the runtime against it on random graphs. The
walk in `src/snapshot.ts` copies most kinds inline and repeats the reads that each kind's capture
facet makes in `observe`; this is the _Snapshot walk_ coupling that [the development
guide](development.md#couplings-that-fail-silently) lists. Its runtime obligations are _Snapshot
memo_ and _Built-in snapshot writer_.

### `reconcile`

| Module(s)           | Key theorems                                                                                                                                                                                                                                                                                                                                                                             | Runtime                                                                                                                                                                                                                                                                                                 | Bridge                                                    | Obligations                                       |
| ------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- | ------------------------------------------------- |
| `PropertyOrder`     | `step_equivalence`, `stream_equivalence`, `aligned_mem`                                                                                                                                                                                                                                                                                                                                  | `src/types/shared/property-publication.ts` `PropertyOrder`; aligned publication in `src/types/object.ts`                                                                                                                                                                                                | PropertyOrder                                             | Capture                                           |
| `DeferredOrder`     | `catchUp_eq`, `execute_eq`                                                                                                                                                                                                                                                                                                                                                               | `src/types/shared/property-publication.ts`                                                                                                                                                                                                                                                              | DeferredOrder (instrumented copy)                         | Property order                                    |
| `PropertyWrite`     | `reconcileKey_no_inherited_setter`, `publish_missing`, `construct_data`, `constructFrom_data`, `constructOn_fresh`, `constructOn_eq_construct`, `constructFromOn_fresh`, `draftSet_eq`, `assignStrict_eq`, `draftThroughSetter_eq`, `draftThroughSetter_refused`, `draftThroughSetter_tamed`, `publish_accessor`, `reconcileKey_rejected`, `reconcileKey_sound`, `reconcileKey_complete` | `src/types/shared/property-publication.ts` `canPublishProperties`, `publishProperty`; `src/types/shared/draft-properties.ts` `set`, `defineProperty`; `setOwnProperty` (`src/set-own-property.ts`); `define` in `src/serialization/common.ts`; the fresh-shell write in `src/types/object.ts`           | PropertyWrite, PropertyConstructOn, PropertyThroughSetter | Property writes                                   |
| `PropertyPlacement` | `matched_maximal`, `place_matched`, `feasible_iff`, `reference_sectors`, `reference_keeps_fixed_iff`                                                                                                                                                                                                                                                                                     | `src/types/shared/property-publication.ts` `canPublishProperties` with `PropertyOrder`                                                                                                                                                                                                                  | PropertyPlacement                                         | Key order                                         |
| `WriteFreeReadback` | `object_writeFree_matches`, `array_writeFree_matches`, `collection_writeFree_matches`, `publishKnown_eq`, `publishPre_eq`, `publishSeen_eq`, `accepts_readsAs`, `acceptsRetry_readsAs`                                                                                                                                                                                                   | readback elision, the preflight facts (`PreflightFacts`, `src/types.ts`) and retried publications in `src/publication/publication-engine.ts`; `occupants` in `src/publication/capture.ts`; `publish` in `src/types/object.ts`, `src/types/array.ts` and the other kinds in `src/types/`; `publishKnown` | WriteFreeReadback                                         | Write-free readback, Reads before the first write |
| `CollectionPlan`    | `plan_eq`, `put_same`                                                                                                                                                                                                                                                                                                                                                                    | `publish` in `src/types/shared/collection.ts`                                                                                                                                                                                                                                                           | proof-only                                                | Ordinal candidates                                |

`src/__tests__/reconcile-semantics.spec.ts` tests the contract case by case: a successful call
keeps the current root, preserves sharing and cycles and never merges distinct nodes, and a kept
plain object keeps its prototype. A failed call throws without rolling back (README: _Not rolled
back_).

Pinning is `Spec.Reconcile.pinned`. A `next` object is pinned when, at capture's first visit, its
parent's aligned current object holds that same object at the same own-property slot, and the
object's subtree reaches neither root. A pinned object stays as it is with everything inside it, and
no other position may keep it (`pinnedAt`). A buffer or view is never pinned, because construction
ties a buffer to its views and a view to its buffer. The Spec bridge checks pinning on random
graphs.

`PropertyOrder` keeps the cursor's decisions while bounding its work. `aligned_mem` proves that when
duplicate-free current keys start with the requested order, a current key is requested exactly when
its position is below the requested count. `DeferredOrder` lets private cursor work wait until
needed, without sharing observations across phases.

`PropertyWrite` models one key of an existing object: its own descriptor, the first descriptor
assignment would reach on the prototype chain, and extensibility, with setters as arbitrary
application code. `reconcile` writes a changed own property by assignment, so an own setter runs
(`publish_accessor`). It never runs a setter on the prototype (`reconcileKey_no_inherited_setter`):
a key whose assignment would reach one fails the check before any write (`reconcileKey_rejected`),
except `__proto__`, which is defined. With setters that store their value, that check decides the
outcome exactly (`reconcileKey_sound`, `reconcileKey_complete`). An assignment to a `produce`
draft, decided in the trap's own order, has the outcome assignment has on the object
(`draftSet_eq`), so a draft of a frozen, sealed or non-extensible object refuses a new key.
`reconcile` follows a refused assignment with a definition only for a key the object holds
read-only; on an ordinary object that is the modelled assignment (`assignStrict_eq`), and a
proxy whose `set` trap refuses a write is not overridden.

`CollectionPlan` models a `Map` or `Set` as its entries in insertion order, with the built-in
`set` keeping an existing key in place; `reconcile` uses the built-in methods (see _Built-in
contents_ below). Publication keeps the current entries that form, in order, the longest prefix of
the next entries (`Spec.Reconcile.retainPrefix`, the fewest moves by `retainPrefix_longest`),
setting only changed values, deletes every other current entry and appends the next entries past
that prefix. A put of an entry's own value changes nothing (`put_same`), so the runtime skips it.

`PropertyPlacement` shows that publication's key order is best effort and never rejects early: a
placement keeping every fixed key exists exactly when greedy matching keeps them (`feasible_iff`),
and `PropertyOrder`'s reference cursor is that matching (`reference_keeps_fixed_iff`).

A new object holds its values as data properties, and building one runs no setter. `construct_data`
covers the property writes of `snapshot`, and `constructFrom_data` adds the source's enumerability:
a non-enumerable property is defined non-enumerable, and every new property is writable and
configurable. Both assume an unmodified `Object.prototype`. `setOwnProperty`, `define` in
`src/serialization/common.ts` and the fresh-shell write assign only a key `Object.prototype` lacks
and define any other; `constructOn_fresh` and `constructFromOn_fresh` prove it without the
unmodified-prototype premise, and `constructOn_eq_construct` shows it matches `construct` where that
premise holds. `publish_missing` covers a key an object lacks, which is how `reconcile` fills an
object it adds: a key whose assignment would reach an accessor is defined.

A `produce` recipe's assignment of a key its object lacks may reach a setter on the prototype,
which receives the draft. A hardened environment's setter, such as those `node --frozen-intrinsics`
and SES put on standard prototypes, defines the key on its receiver as assignment would. The draft
accepts exactly that definition, so the assignment has the object's outcome
(`draftThroughSetter_eq`, `draftThroughSetter_tamed`), and refuses any other definition
(`draftThroughSetter_refused`).

### `produce`

| Module(s)                                                        | Key theorems                                                                                                                | Runtime                                                                                                                                                                                     | Bridge                               | Obligations                |
| ---------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------ | -------------------------- |
| `GraphPolicy`                                                    | `feasiblePlans_exact`, `rankedPlans_exact`, `completion_survives_score_pruning`                                             | the reference ranked stream, to which `CompactImmutable` relates its masks                                                                                                                  | imported by Contract                 | none                       |
| `SettledChildren`                                                | `check_step`, `needs_settled`, `needs_unchanged`, `settled_reach_recorded`, `recorded_getD`                                 | `checkDescendantsForMaterialization` in `src/finalization.ts`; `compileImmutable` in `src/restore-identities.ts`                                                                            | SettledChildren                      | Finalization reads         |
| `FinalizationReads`                                              | `decisions_gated`, `lastSymbol_iff`, `keys_exact`, `reread_exact`                                                           | `DraftObservation.copies` and `checkState` in `src/finalization.ts`; `PropertyDraftState.keys` in `src/types/shared/draft-properties.ts`                                                    | proof-only                           | Finalization reads         |
| `ReuseClosure`, `Immutable`                                      | `reuseSurvivors_greatest`, `selected_published`, `selected_storage_distinct`                                                | `src/restore-identities.ts`                                                                                                                                                                 | Contract (`Immutable`)               | Identity                   |
| `CompactImmutable`                                               | `feasible_iff`, `ranked_decode`, `ranked_head`, `separated_of_injective`, `selected_decode`                                 | `src/graph/immutable-selection.ts` `immutableSelections`, `immutableHead`; `publishFirst` in `src/restore-identities.ts`, which publishes the first ranked mask that can be built           | CompactImmutable                     | Identity                   |
| `KeyOrder`                                                       | `build_nodup`, `ownKeys_ownKeys`, `rebuild_preserves`, `produce_key_order`                                                  | `preparePropertyCopy` in `src/types/shared/draft-properties.ts`; finalization                                                                                                               | KeyOrder                             | Key order                  |
| `DraftSurface`                                                   | `admits_iff_represented`, `refused`, `keeps_iff`, `handle_rebuilds`                                                         | `admits` in `src/types/shared/draft-properties.ts`, non-extensible collection drafts and native copies in `src/draft-session.ts`, `reuse` in `src/types/object.ts` and `src/types/array.ts` | DraftSurface                         | Draft surface              |
| `DraftClass`                                                     | `draft_instanceOf`, `lookup_other`, `lookup_method`                                                                         | `draftCollectionBase` and `adoptDraftClass` in `src/types/shared/draft-collection.ts`                                                                                                       | DraftClass                           | Draft class                |
| `DraftIteration`                                                 | `iterate_entries`, `iterate_kept`, `write_after_iterate`, `kept_untouched`, `drafted_nodup`                                 | `draftWalk` and `draftCollectionBase` in `src/types/shared/draft-collection.ts`                                                                                                             | DraftIteration                       | Draft iteration            |
| `DraftMembers`                                                   | `includesBy_drafted`, `includesBy_form`, `includesBy_single`, `plain_self`                                                  | `memberIdentity` and `arraySearches` in `src/types/shared/draft-members.ts`                                                                                                                 | DraftMembers                         | Draft members              |
| `DraftSetMethods`                                                | `mem_union`, `mem_intersection`, `mem_difference`, `mem_symmetricDifference`, `isDisjointFrom_walk`, `intersection_drafted` | `setMethods` in `src/types/set.ts`                                                                                                                                                          | DraftSetMethods                      | Draft members, Set methods |
| `CopyPrototype`                                                  | `adopt_eq`, `copy_keeps`, `serializes_iff_restored`                                                                         | `adoptPrototype` in `src/types/shared/prototype.ts`; array, `Map`, `Set`, `Date`, `DataView`, URL and Temporal construction; `serialize` recognition                                        | CopyPrototype                        | Copy prototypes            |
| `Requirements`, `RequirementAdmission`, `RequirementPropagation` | `close_least`, `admit_nodup`, `completed_insertion_order`                                                                   | `src/graph/requirements.ts` `closeRequirements`                                                                                                                                             | SeededRequirements, CompactImmutable | none                       |
| `SeededRequirements`                                             | `close_eq`, `run_eq`, `scans_le`                                                                                            | `compileImmutable` in `src/restore-identities.ts`, `src/finalization.ts`                                                                                                                    | SeededRequirements                   | none                       |
| `ClosureHistory`, `FactRenaming`                                 | `expandUnfolded_eq`, `execute_eq`, `observations_eq`                                                                        | `src/graph/requirements.ts` `RequirementClosure`                                                                                                                                            | FactRenaming                         | none                       |
| `Construction`                                                   | `schedule_safe`, `schedule_complete`, `schedule_flat`, `schedule_shells_only`                                               | `src/graph/construction.ts` `constructionOrder`; `publishFresh` in `src/restore-identities.ts`                                                                                              | CompactImmutable                     | none                       |

`GraphPolicy` defines domains, storage separation, identity requirements, feasible plans and the
ranked stream, which keeps domain order within equal scores. Identity restoration chooses which
current objects an immutable result reuses. `CompactImmutable` encodes choices as retained bits and
relates them to the ranked stream; `ranked_head` proves that an admissible, separated and closed
eligibility mask is the first ranked mask. Each record is its own storage, so every mask is
separated (`separated_of_injective`) and the runtime search tracks no owners; the unavailable
records are closed over parents, so the eligibility mask is closed, and `immutableHead` checks only
that every fixed record is eligible.

`SettledChildren` models finalization's question whether an object needs a copy: a walk of its
children that stops at the first changed one and settles the objects it found unchanged. The walk
keeps an object's child list only when it visited every child, so each kept list is complete
(`recorded_getD`). A negative answer settles its object as soon as its walk ends, unless the walk
met an object its question visited but has not settled, which only a cycle back into the walk
produces; such a pending answer waits for the question's. Every check keeps the invariant that each
settled object has its list kept and settled children (`check_step`, `needs_settled`), so identity
restoration's walk of an unchanged subtree the result keeps reads no list again
(`settled_reach_recorded`), and with the changed objects fixed a settled object reaches none of them
(`needs_unchanged`).

`FinalizationReads` proves three reads exact. A slot's provenance matters only for a value with a
special copy, so the observation records it only while the call holds one; the last observation
sees every copy the decision sees, so the decisions agree (`decisions_gated`). A working copy lists
strings before symbols, so its last key is a symbol exactly when it holds one (`lastSymbol_iff`), and
a copy that never held one lists all its keys as its string keys (`keys_exact`). Drafts are only
added and counted, so after a walk a draft found before is unchanged and a missing one can appear
only if the count moved (`reread_exact`). These came after the runtime change they justify, in the
same round.

`Requirements` specifies the least closure. `SeededRequirements` proves that dropping implications
into seed facts keeps the closure and its trace, which `compileImmutable` relies on. `FactRenaming`
proves that relabeling objects as numbers, as the bridges do, preserves every closure, query and
stream, and `expandUnfolded_eq` equates the runtime's admit-then-propagate `require` with expanding
from the fact.

`Construction` defines the construction schedule. A new view needs its buffer first and a new URL
its `searchParams`, and neither of those needs another object, so by `schedule_flat` the schedule
is the new objects that need none, then the others, each in ascending order. The runtime's
`constructionOrder` computes that order for `reconcile` publication, in
`src/publication/publication-engine.ts`; the CompactImmutable bridge checks that it equals the
schedule on dependencies one level deep. Every new object `produce` makes is an object, array,
`Map` or `Set`, which needs no other new object first, so by `schedule_shells_only` the schedule is
the new objects in ascending order; `publishFresh` in `src/restore-identities.ts` allocates them in
that order, then fills each.

### Native type facets

| Module(s)                | Key theorems                                                                              | Runtime                                                                                                                                             | Bridge                                      | Obligations                 |
| ------------------------ | ----------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------- | --------------------------- |
| `Types.Recognition`      | `builtinTrace_eq_scanTrace`, `temporalTrace_eq_scanTrace`, `builtinDispatch_eq_scanTrace` | `src/types/builtins.ts`, `src/types/temporal.ts`                                                                                                    | proof-only                                  | Recognition                 |
| `Types.RecognitionPlain` | `recognize_eq_scan`, `plain_probes`                                                       | `builtinFirstMatch` in `src/types/builtins.ts`, `inChain`                                                                                           | RecognitionPlain                            | Recognition                 |
| `Types.Atoms`            | `classify_atomic`, `classify_reads`, `ingress_atom_iff`, `ingress_structural`             | `isAtomObject` in `src/object-property.ts`, `recognize` in `src/adapters/recognition.ts`                                                            | Atoms                                       | Recognition, Atoms          |
| `Types.Ingress`          | `ownReads_shared`, `walkReads_eq`                                                         | `recognize` with a `PrototypeRead` in `src/adapters/recognition.ts`; `prototypes` in `src/publication/capture.ts`, `createDraft`, the snapshot walk | Ingress                                     | Recognition, Atoms, Ingress |
| `Types.NativeValue`      | `published_payload`, `temporal_compatible_iff`, `clear_append_exact`                      | `src/types/temporal.ts`, `src/types/url.ts`, `src/types/url-search-parameters.ts`                                                                   | NativeValue                                 | Native values               |
| `Types.NativeWrites`     | `publish_nil_iff`, `publish_url`, `publish_parameters`, `publish_temporal`, `result_eq`   | `publish` in `src/types/url.ts`, `src/types/url-search-parameters.ts` and `src/types/temporal.ts`; `replaceNativeParameters`                        | proof-only                                  | Native writes               |
| `Types.LazyOwnership`    | `lazy_eager_equivalent`, `omit_identity_response`                                         | ownership tables in `src/snapshot.ts` and finalization                                                                                              | imported by OwnedNativeChild                | Lazy ownership metadata     |
| `Types.OwnedPublication` | `bulk_equivalent`, `bulk_identity`, `sealed_owner_sound`                                  | `src/types/shared/url-carrier.ts`                                                                                                                   | OwnedNativeChild; native differential check | URL ownership               |
| `Types.OwnedNativeChild` | `adopt_consistent`, `admitted_iff`, `first_prepared_ranked`, `replay_owned_valid`         | `src/types/url.ts`, `src/types/url-search-parameters.ts`, `src/types/shared/url-carrier.ts`                                                         | OwnedNativeChild                            | URL ownership               |

`Types.Recognition` refines first-match recognition by traces of a fixed prefix of predicate calls.
The traces keep the ranks of the predicates visited, the selected rank and the position of an early
exception.

`Types.RecognitionPlain` proves that the built-in registries may decide an object after one
prototype read: when the prototype is `Object.prototype` or `null`, every later probe fails, a
view's included, so the plain-object fallback is the scan's result (`plain_probes`,
`recognize_eq_scan`). Any other object takes the scan, each `instanceof` probe deciding membership
from the prototype already read, so the result and a raised error are the scan's while the object
itself is read once. A typed array holds the typed-array brand and inherits
`%TypedArray%.prototype`, so a `DataView` that inherits a typed array's prototype is not one. A view
counts only over a buffer whose chain holds `ArrayBuffer.prototype` or
`SharedArrayBuffer.prototype`; the model takes the brands and that answer as given, since reading
them observes nothing.

`Types.Atoms` proves that one walk of the prototype chain decides `instanceof` for every listed
constructor, with one `[[GetPrototypeOf]]` read per prototype it passes. It also proves that
ingress recognition splits only the plain-object fallback into atoms; known-kind checks keep the
structural scan. An atom is a `Defs.Value.atom`, so the snapshot, reconcile and produce theorems
about atoms apply to it.

`Types.Ingress` composes the two: one shared prototype read decides both the kind and the atom
split, as the two classifiers would separately, and reads the object once where a separate split
read it twice (`ownReads_shared`); the walk past that read is unchanged (`walkReads_eq`).

`Types.NativeValue` proves the payload policy: mutable publication returns the desired payload,
immutable Temporal compatibility requires equal class, constructor label and exact observation, and
clearing then appending parameter pairs keeps their order and duplicates. Each native object is one
heap node with one atomic payload slot and no child references. These are facet and encoding claims,
not a new instance of the public graph theorems; the URL scalar model has no `searchParams` edge.
`Types.NativeWrites` extends write minimality to these kinds, which the `Spec` model lacks: a kept
URL writes its `href`, and a kept `URLSearchParams` its entries, exactly when the text it compares
differs from `next`'s (`publish_nil_iff`), and a Temporal value is never written: it is kept when
equal and replaced otherwise (`publish_temporal`).
`Types.LazyOwnership` proves that an absent table denotes an empty one under arbitrary writes, and
`Types.OwnedPublication` that bulk replacement equals clear-and-append with identities preserved.

`Types.OwnedNativeChild` models a URL allocated with its `searchParams` child before its source
owner is known. Adoption keeps both identities and the child payload observed first. It keeps a
later captured query only when the child was not mutated and the query decodes to that payload, and
otherwise serializes the payload again (`adopt_consistent`). So when a getter changes the source
URL's query during the call, the parameters captured first win. A mutation that leaves the payload
equal still discards the later query (`net_equal_mutation_normalizes`).

Admission requires the selected child itself, not an equal one (`admitted_iff`), and
`first_prepared_ranked` keeps the first successful preparation in ranked order. In immutable
finalization a changed owner forces its child to be copied (`replay_owned_valid`,
`force_monotone`); an example shows that keeping an earlier equal-child decision after the owner
turns out changed is unsound.

### Serialization: `serialize` and `deserialize`

| Module(s)                  | Key theorems                                                                                                                                                              | Runtime                                                                                                                                                                                                                     | Bridge                    | Obligations                          |
| -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------- | ------------------------------------ |
| `Serialization.Positional` | `decode_encode_relaxed`, `decodeNodes_sound`, `decode_encode_control`, `renumber_first_use`, `typedRef_sound`, `sparse_grow_eq_preallocate`, `sparse_resize_keeps`        | `src/serialization/emit.ts` `slot`, `layout`; `encode.ts` `renumber`, `controlTable`; `decode.ts` `checkControl`; `facets/slots.ts` `runEnd`, `resolve`; `facets/array.ts` `sparseArray`, `place`; `layout.ts`; `frames.ts` | Serialization             | JSON.parse, Native arrays and views  |
| `Serialization.Preorder`   | `preorder_iff`, `check_iff`, `encoder_canonical`                                                                                                                          | `src/serialization/decode.ts` `fill`; `facets/slots.ts` `references`, `enter`                                                                                                                                               | Serialization             | none                                 |
| `Serialization.DFS`        | `recursive_refines_stack`, `entries_unique`, `captured_index_lt_length`                                                                                                   | `src/serialization/encode.ts` `encodeGraph`; array lengths in `frames.ts`                                                                                                                                                   | imported by Serialization | Encoder observations                 |
| `Serialization.Refinement` | `indexed_run_exact`, `leaf_contract`, `leaf_step_refines`                                                                                                                 | `src/serialization/leaf.ts`, `frames.ts`                                                                                                                                                                                    | proof-only                | Encoder observations                 |
| `Serialization.Inline`     | `inline_step_refines`, `inline_run_refines`, `inline_matches_recursive`                                                                                                   | `src/serialization/frames.ts` `advances`                                                                                                                                                                                    | proof-only                | Encoder observations                 |
| `Serialization.ShapeRadix` | `getR_split`, `getR_setR`, `radix_matches_signature`                                                                                                                      | `src/serialization/radix.ts` `lookup`, `intern`, `split`                                                                                                                                                                    | proof-only                | Encoder observations                 |
| `Serialization.Collection` | `resolved_map_trace`, `resolved_map_rows`, `resolved_set_trace`, `resolved_set_keys`, `first_insertion_order`, `last_value`                                               | `src/serialization/facets/collection.ts` `map`, `set`                                                                                                                                                                       | SerializationCollection   | Map and Set equality                 |
| `Serialization.Base64`     | `encode_spec`, `encode_length`                                                                                                                                            | `src/serialization/binary.ts` `encodeTable`                                                                                                                                                                                 | proof-only                | Base64                               |
| `Serialization.Size`       | `accounting_eq_reachable`, `node_count_le_accounting`, `stops_iff`, `accepts_iff_bytes`, `image_sum_le`, `foldMap_length_le`, `json_words_le_text`, `encodeInt_decodeInt` | `src/serialization/size.ts`; `decode.ts` `decodeGraph`, `measureGraph`, `checkShape`; `src/required-max-bytes.ts`; the charges in `facets/*.ts`; bigint text in `emit.ts` and `facets/native.ts`                            | Serialization             | Decoded sizes, Measuring, JSON.parse |

A document is `[literal]` for a JSON-literal root and `[control, payloads]` otherwise. Every value
position is a slot whose kind, literal or reference, comes from its node's layout, never from its
value, so no number or string is reserved. The control table holds each node's layout id, then the
shapes and layouts, each framed by its length (`decode_encode_control`).

The decoder checks meaning, not canonical form: it uses the tables as given, so they may be
reordered, repeated or unused. `decode_encode_relaxed` shows that it inverts the encoder, and
`decodeNodes_sound` states what every accepted document means. `Preorder` proves that the reverse
scan accepts exactly the documents numbered in depth-first entry order from node 0, so every node is
reachable. On the encoder side, `inline_matches_recursive` gives the recursive trace and memo for a
terminating in-place run (termination is not proved), and `radix_matches_signature` shows that the
per-call path-compressed trie assigns first-occurrence ids for any key type, lone surrogates
included.

Map and Set payloads are resolved, then folded with native `set` or `add`; on a failed read the
target is untouched (the `resolved_*` theorems). `encode_spec` covers the table encoder used for
large buffers when `Uint8Array.prototype.toBase64` is missing and `TextDecoder` exists. A sparse
array starts as `new Array(length)` when at least half its elements are present and as `[]`
otherwise, receives its elements in ascending order, then gets its length;
`sparse_grow_eq_preallocate` and `sparse_resize_keeps` prove both starts give the same array with
no element lost, given that every written index is below the length (`runEnd` ensures it); an
example shows that a write at or beyond the length would be removed.

`Size` defines the `maxBytes` limit, and its docstring states what each theorem proves.
`accounting_eq_reachable` is about document nodes, not decoded objects: that the charges cover the
decoded value is the _Decoded sizes_ obligation, and that `requiredMaxBytes` returns the smallest
accepted limit (`accepts_iff_bytes`) is the _Measuring_ obligation. Which words each kind of node
is charged is the runtime's table, which the README states; the theorems hold for any charges that
cover a node's children.

**Encoder-only theorems.** `Positional`'s `decode_encode_document`, `encode_decode_document`,
`intern_canonical`, `canonical_intern` and `sparse_canonical` hold for a decoder that also
requires first-use, duplicate-free tables. They are true of the encoder's output, which
`encode.ts` and `facets/array.ts` cite them for, but not of what `deserialize` accepts.

## Runtime obligations

The proofs assume the following facts. _Intrinsic independence_ applies to every model.

### Heap model and public contracts

- **Capture.** Observations follow the documented order, collections are normalized, descriptor
  operations behave natively, and observations stay stable within a phase. `graph-capture.spec.ts` covers the order of capture's reads.
- **Identity.** Fresh allocations are fresh, each object is its own storage, and each publication
  attempt gets a fresh private token. A proxy is an object of its own: capture, `snapshot`,
  `serialize`, `produce` and identity restoration give it its own node, draft and record, and none
  of them unwraps it. `shared-identity-bug.spec.ts` covers one object at several positions.

### Reference models

- **Spec agreement.** The runtime's result, read back as a graph, equals the reference's on
  identities, values, descriptors, prototypes and extensibility, rejections agree, nothing is
  written before a rejection the reference decides before any write, and `produce` and `snapshot`
  leave `current` unchanged. The bridge checks this on seeded random graphs, so its evidence is for
  the generated cases. The models cover objects, arrays, maps, sets, dates, buffers, views and, for
  `reconcile`, the slots of class prototypes; they do not cover `SharedArrayBuffer`, views that
  track their buffer's length, buffer and view subclasses, URLs, Temporal values or proxies. The
  gate allows no difference: results, rejections, writes before a rejection and the getter counts of
  the current objects `next` does not hold must agree; the getters of an object `next` holds run
  while `next` is read, which the promise leaves out. The gate also runs the `--writes`, `--hazards`
  and `--binary` batches. The `--writes` batch wraps every current object and array in a recording
  proxy and compares the writes and deletions each one receives, over every decision pass, with the
  reference's writes. The `--hazards` batch, also through the proxies, generates more accessors and
  more setters that drop their value than the default batch, so that about one call in nine needs
  more than one decision pass. The `--binary` batches, one per operation, add buffers, some of them
  resizable, with typed arrays and `DataView`s over them; the `reconcile` batch runs through the
  recording proxies.
- **Spec phases.** On the `reconcile` cases, plain, hazard-rich and with buffers and views, the
  runtime's discovery and decisions equal the reference's phases (`SpecOracle.phases`): the visit
  order and the pinning alignment of the nodes that are not pinned, the pinned nodes, each node's
  candidates in decision order with the requirements of their fixed slots, and the decision of
  every pass up to the first that keeps no root. The phase bridge reads them from a bundle of the
  sources that records `publishGraph`'s candidates and each `decide`, so the library carries no
  hook. Capture keeps an object already in place as an atom edge, which has no node, so the bridge
  compares order and alignment over the nodes that are not pinned and checks that every pinned
  node keeps the object it is. The runtime also leaves out a candidate that is an object inside a
  pinned subtree, which the reference keeps in the list but never decides for, since every such
  object is reserved; the bridge's reference list leaves it out too.
- **Spec enumeration.** Every case within the bounds of `scripts/lean-spec-enumerate.ts` agrees with
  the reference, as the outcome bridge compares it, plain and through recording proxies, and, for
  `reconcile`, as the phase bridge compares it. Its universes are objects and arrays of up to two
  nodes and two positions on each side, with sharing, cycles, current objects in place or elsewhere
  and either root inside `next`; a root object with every kind of slot at up to two keys,
  extensible or not; class prototype slots; fixed slots that hold objects, so that a candidate
  demands an object at another node; `Map` and `Set` entries; array holes and integrity levels;
  dates; buffers and views, including a view over another buffer of the same length; and every
  `produce` recipe of up to two operations over the small graphs and over objects and arrays of
  each attribute kind and integrity level, with `snapshot` over every current graph listed. Its
  evidence covers those cases only; a defect that needs a larger graph, such as a demand made
  through a pinned node, is the random bridges' to find.
- **Pass termination.** `publishGraph` in `src/publication/publication-engine.ts` repeats its
  passes with no limit on their number. They end for the reason `blocked_fresh` gives for the
  reference, because the runtime meets both of its premises: a decision keeps no demoted object
  (the runtime's `forbidden` set), and every object a pass finds blocked is one that pass kept.
  Each pass that continues therefore demotes a captured current object for the first time. The
  `forbidden-ignored` mutant keeps demoted objects and `blocked-not-forbidden` demotes nothing; the
  [mutation audit](#runtime-bridges) reports each as `hung`.

### `snapshot`

- **Snapshot memo.** A caller-supplied memo is trusted and can return any object, including the
  source; detachment holds only for a valid memo
  (`graph-capture.spec.ts` keeps a counterexample). A fresh URL built around a memo-supplied child
  must carry matching same-call carrier metadata, or `snapshot` rejects it.
- **Built-in snapshot writer.** Each snapshot facet initializes its writer once and exposes no
  application callback that can reenter the traversal before the copy is recorded. Snapshot facets'
  construction callbacks only create private URL carrier metadata; a new snapshot facet must keep
  this boundary. `url-ownership.spec.ts` covers the memo hits between a URL and its parameters.

### `reconcile`

- **Full capture.** The pinned closure must sit in the current heap at its occupants, be closed and
  separate from captured nodes, have observed buffer extents and receive no write. The runtime walks
  a subtree before pinning it, refuses to pin when the walk meets either root, excludes walked
  objects from other candidates, and pins to itself any captured node the walk met. Each pinned
  slot's edge holds that slot's occupant (`Spec.Reconcile.pinned`). Only plain-object and array slots
  pin, and captured views never pin their buffers.
- **Buffer shape.** An `arrayBuffer` node holds bytes only, and `compatibleShape` compares their
  count. The runtime also keeps a buffer only when it has next's resizability and maximum length,
  which a copy would carry, so a kept buffer differs from next in no property a copy has. `binary-built-ins.spec.ts` covers resizable buffers and views.
- **Property order.** `DeferredOrder` applies only while key storage is private, stable and
  non-escaping, and desired keys are buffered eagerly. A key moved into the requested order is
  deleted, assigned again so that a proxy's `set` trap observes it, and given back its own attributes,
  as `PropertyWrite` keeps them for a key written in place. `property-order.spec.ts` and `reconcile-property-order.spec.ts` cover the cursor and the moved keys.
- **Property writes.** `PropertyWrite` covers one key of an ordinary object, or of a proxy whose
  traps forward to one. The prototype walk in `canPublishProperties`
  must find the descriptor assignment would reach. It reads a descriptor of `Object.prototype` or
  `Array.prototype` only for a key that `in` reports there, and goes past either one only when it
  does not own that key; for any other key it stops there, since `in` has already searched the rest
  of the chain (`src/__tests__/prototype-boundaries.spec.ts`). `deserialize` asks whether
  `Object.prototype` holds a key once per shape, since only built-in code and the global `Temporal`
  run before records are filled. Multi-key order is `PropertyOrder`'s; an own accessor is treated as
  a slot that keeps its place.
- **Write-free readback.** When the first pass wrote nothing to any node, `publishGraph` reads
  nothing back. `WriteFreeReadback` proves that a plain
  object or an array whose publication wrote nothing would read back as accepted, given the same
  observation, and so would a `Map` or `Set` whose publication left its entries as they were
  (`collection_writeFree_matches`, from `CollectionPlan.plan_eq`). A `Date`, buffer, URL,
  `URLSearchParams` or Temporal value reports a write-free publication only when it found its
  contents equal; the runtime must compare them with the same built-in reads at publication and at
  readback. A view writes nothing: candidate discovery checked its shape and bound its buffer,
  which is what readback compares. The runtime supplies that observation: no write means no setter
  or write trap ran, and a repeated read answers as the first did, provided no getter or read trap
  that the call runs, in `current` or in `next`, changes a value the call already read (README:
  _Getters must not change values_). Only the first pass counts, since its targets are the objects
  the preflight read; plain objects must also list exactly their own keys. That pass takes its key
  list and each aligned key's presence and attributes from the preflight's descriptors
  (`publishKnown_eq`).
- **Reads before the first write.** Capture records the value it read at each key of an aligned
  object, and each index of an aligned array (`occupants`), and candidate discovery records the
  same for each other object aligned with a node (`candidateReads`). An object aligned or walked at
  more than one node is read through one table of its reads (`reads`), so no key of it is read
  twice. The preflight of each candidate takes a fixed slot's value from those reads. The first
  publication of the object decides from them whether a key needs a write, without reading it
  again: `publishPre_eq` when the current keys begin in the requested order, so the preflight's
  descriptor gives the attributes, and otherwise, as for an array, `publishSeen_eq`, whose write
  takes the live slot's attributes. A later pass decides each key of a kept object from the value
  the previous pass read back (`publishSeen_eq`), and its preflight reads descriptors again.
  Readback reads every unpinned node again after any write, so a decision that a write in between
  made stale can only block the object (`accepts_readsAs`, `acceptsRetry_readsAs`). The runtime
  supplies only the premise of _Write-free readback_: a repeated read with no write in between
  answers as the first did. An own getter of `current` therefore runs at most once when the call
  writes nothing, twice when it writes, and once more for each demotion pass, apart from reads of
  `next` and of proxy traps (`write-free-readback.spec.ts`); the Spec bridge checks the counts
  against `Spec.Reconcile.run`.
- **Ordinal candidates.** The runtime offers each captured node other than the root the current
  objects aligned with it, at the same key of an object, the same index of an array and the same
  insertion position among `Map` entries (key and value) and `Set` members, inside any candidate of
  any parent, in discovery order; the root gets `current` only; an object some admitted candidate's
  fixed slot requires at a node comes first there (`candidates.ts` `collect`,
  `Spec.Reconcile.discover`, `orderedCandidates`). A current object is a candidate only at its own
  position; another position gets it only as a pinned fixed image (_Full capture_). The Spec bridge
  checks this on random graphs; `readme-publication-semantics.spec.ts` and
  `shared-identity-bug.spec.ts` cover arrays, `Map` and `Set`.
- **Exposed handles.** Readback compares each read with the handle a node is bound to, so a value
  written must read back as that handle; a trap that returns another object for a stored one makes
  readback reject.

### `produce`

- **Special-value decision.** No model covers `chooseSpecial` in `src/graph/provenance.ts`, so
  tests are its only evidence. From the equivalence and provenance facts that finalization reads,
  it decides whether a `Date`, buffer, view, URL, `URLSearchParams` or Temporal value stays itself,
  takes its registered copy or gets a fresh copy; a value that is itself a registered copy can
  instead go back to the original it was made from. Tests include
  `finalization-propagation-regressions.spec.ts`, `url-ownership.spec.ts` and the
  `hardened-kinds.ts` driver that `standard-prototypes.spec.ts` runs.
- **Drafts.** The recipe is isolated from the input, returning the original `current` cancels draft
  changes, and getters are sealed during finalization.
- **Finalization reads.** Reading an object again lists the same children, as `SettledChildren`
  assumes; identity restoration takes an object's children from a finalization walk that visited all
  of them. A draft write keeps the descriptor and value it read for its
  key in the first copy, and a draft observation that reads the object itself counts each data slot
  it read there as backed by the object while the call holds a special-value copy. Every copy comes
  from a draft read; one that a getter makes while finalization observes forces the sealed pass,
  which observes every slot again and runs no getter, as `decisions_gated` assumes. A working copy
  records each symbol written to it, and the session counts each draft it makes and never replaces
  one, as `keys_exact` and `reread_exact` assume. `produce-reads.spec.ts` counts finalization's
  reads.
- **Key order.** `KeyOrder` assumes the engine lists own keys as `OrdinaryOwnPropertyKeys` does and
  that the draft store follows ordinary assignment and `delete`; the KeyOrder bridge checks both.
- **Draft surface.** The runtime refuses new properties on collection drafts and native copies by
  making them non-extensible, and on array drafts in the proxy traps; a getter is deterministic
  between its observation and a later read of the kept object. The DraftSurface bridge checks
  admission and reuse.
- **Draft class.** `Map.prototype`, `Set.prototype` and a subclass's prototype are not modified
  during a call, and the layer the runtime builds holds exactly the draft class's methods, which
  read the original and read and write the working copy with the built-ins, so an override on a
  subclass or the instance never runs. The DraftClass bridge checks resolution and `instanceof`.
- **Draft iteration.** The working copy is a native collection whose iterator follows the
  collection's own insertion order and changes; Lean models entries as an ordered list. The
  DraftIteration bridge checks walks and results on a `Map`.
- **Draft members.** A member's identity is the object its draft drafts, or the object itself;
  reading an element does not change it, which `plain_self` takes as a premise. The DraftMembers
  bridge checks plain arrays, with every element read before the search and with the array
  searched before any element is read.
- **Set methods.** The model assumes an operand whose `has` and `keys` agree and change nothing, and
  whose keys are distinct by identity. The runtime reads `size`, `has` and `keys` and calls them in
  the order the specification gives, walks the draft live, or as a copy for `difference`, and closes
  the key iterator where the specification does; native tests compare the calls, errors and results
  with native `Set` methods on operands that change the set. A native `Set` or `Map` operand is
  asked for each form of a member, which its `has` cannot observe; any other operand's `has`
  receives the draft. The draft's members and size are read with the built-ins, past a subclass's
  iterator and `size`, and the draft runs the built-in algorithm even when the class overrides the
  method. The DraftSetMethods bridge checks results, and that a result holds
  this draft's object members as drafts.
- **Copy prototypes.** A copy takes the source's prototype as read once at capture, and
  `Object.setPrototypeOf` on the fresh copy succeeds. Each kind's standard prototype is its live
  constructor's `prototype`, which does not change during a call. The CopyPrototype bridge checks
  copies and `serialize` acceptance.

### All operations

- **Frozen contents.** `PropertyWrite` takes attributes and extensibility for properties only;
  `CollectionPlan` and the time, bytes and text of dates, buffers, views and URLs have no such
  input, because the built-in methods change them on a frozen value too. The runtime checks a
  frozen built-in's properties, keeps it and updates its contents in place, and a `produce` draft
  changes them in its copy; `standard-prototypes.spec.ts` checks both in each hardened runtime.
- **Intrinsic independence.** The models have no prototypes, so the runtime's own records, tables,
  descriptors, errors and loops must not reach `Object.prototype` or `Array.prototype`; see
  [AGENTS.md](../AGENTS.md) and `src/standard-prototypes.ts`. The `Uint8Array` base64 methods and
  the global `Temporal` are read as own properties. Built-in methods captured when the module
  loads are read through `builtinValue`, which calls the getter a hardened runtime puts in place
  of a method, and are called with an explicit receiver; `standard-prototypes.spec.ts` runs every
  function on every value kind under `node --frozen-intrinsics` and under SES `lockdown()` with
  default and severe override taming, importing the library before and after it, and requires the
  outcomes of an ordinary runtime. A `Set` method operand's keys are stepped as the specification
  steps them and closed in the same way (`closeIterator`), except that a `return`
  only `Object.prototype` holds is neither read nor called. A user array's hole is
  asked of the array itself (`hasElement`) when a standard prototype holds that index; otherwise
  `in` is the only observation. `standard-prototypes.spec.ts` plants each internal and protocol
  name on both prototypes in a child process. An index accessor or read-only index on a standard
  prototype, a built-in method replaced before the module loads, and a replacement, at any time,
  of a built-in method the runtime calls on its own tables are outside this obligation.
- **Built-in contents.** The runtime reads and writes the contents of a `Map`, `Set`, `Date`,
  buffer, view, `URL` or `URLSearchParams` only with the functions captured when the module loads,
  which are assumed to be the built-ins (see _Intrinsic independence_ for one replaced earlier);
  this establishes the built-in insertion premise of `CollectionPlan` and the serialization
  `Collection` model. A `Map` or `Set` is walked with the built-in `forEach`, or with a fresh
  built-in iterator stepped by the built-in `next`. `builtin-contents.spec.ts` checks that no
  override runs, whether a subclass, the instance or a change to a standard prototype after the
  module loads supplies it. The runtime reads
  the global `Temporal` and its `from` in each call that needs them, so a polyfill installed after
  import works; a `Duration` is compared field by field and any other Temporal value with `equals`
  on the copy that `from` returns.

### Native types

- **Recognition.** The runtime performs the same live namespace reads, constructor reads and
  predicate calls in the modelled order, and caches no result across calls; within a call, capture's
  result serves discovery (Ingress). The built-in registries read the prototype once, after the
  `Array.isArray` probe, and decide each constructor probe by the prototype chain from it, never by
  a constructor's `Symbol.hasInstance`. Because of this, and because a repeated read answers as the
  first one did, no constructor probe accepts an object whose prototype is `Object.prototype` or
  `null`. `builtin-recognition.spec.ts` covers the probes.
- **Atoms.** The listed constructors are the live globals, which callers do not modify during a
  call; the runtime decides whether an object is an instance of one by its prototype chain, as
  `instanceof` does with the default `Symbol.hasInstance`. A caller that already read an object's
  prototype, such as `snapshot` and `reconcile` capture, passes it on instead of reading it again.
  The Atoms bridge checks the classification, the read count and each function's treatment of atoms.
- **Ingress.** The prototype that ingress reads serves every reader of that object until the call's
  first write: `reconcile` capture records it, with the kind, for discovery and the preflight's
  inherited-accessor check, and discovery does not check that kind again;
  `produce` uses it for the draft's proxy target and `snapshot` for the copy. A later read must
  answer as the first did, so a getter or trap that changes a prototype before the first write is
  unsupported. Readback and a draft's first copy, which follow the recipe, read the prototype
  again. `ingress-reads.spec.ts` counts the prototype reads.
- **Native values.** Native brands, constructors, capture, cloning, publication and readback are
  faithful, and Temporal labels keep all ten Duration components and each class's calendar, time
  zone and reference-date distinctions. Lean proves neither native parsing nor `.equals`. `temporal.spec.ts` and `url-values.spec.ts` cover the values.
- **Native writes.** `Types.NativeWrites` takes a URL as its `href`, a `URLSearchParams` as its
  serialization and a Temporal value as its class and the fields its comparison reads. `publish` in
  `src/types/url.ts` and `replaceNativeParameters` in `src/types/shared/url-carrier.ts` write only
  after their comparison finds the text different, and a write must leave the value reading
  `next`'s text, which holds for a text read from a native value. `temporalPublication` in
  `src/types/temporal.ts` admits a current Temporal value only when `matches` finds it equal, and
  its `publish` writes nothing. `write-free-readback.spec.ts`, `url-values.spec.ts` and
  `temporal.spec.ts` cover these.
- **Lazy ownership metadata.** Runtime maps stay scoped to their session, phase or attempt;
  construction callbacks still run, and overwriting a shared target clears obsolete metadata.
- **URL ownership.** Ownership is fixed, allocation is fresh, carrier maps are per call, ordered
  pairs are captured faithfully, and force propagates to sealed replay. Preparation fails before
  fresh writes; native exceptions still propagate. The private query marker relies on the URL
  [form parser](https://url.spec.whatwg.org/#concept-urlencoded-parser) ignoring empty fields and on
  every parameter mutator running the native
  [query update](https://url.spec.whatwg.org/#concept-urlsearchparams-update), even for no-ops. Bulk
  publication relies on opaque-path normalization of the empty-list update, which JavaScript tests
  cover. Getter order, method branding and URL parsing are native. Discovery keeps a URL's
  `searchParams` node only with a candidate of its URL node that owns it, and pins the URL node to
  its own object when its `searchParams` stay in place, since a new URL owns new parameters; the
  `Spec` model has no URL, so this rule rests on the decision's requirement chains and
  `url-ownership.spec.ts`, which also covers the owner and child identities.

### Serialization

- **JSON.parse.** `JSON.parse` is trusted to produce the parsed tree; the proofs do not model its
  grammar, number rounding or `-0`. Control integers, Date and Duration values and Temporal
  payloads are checked by runtime code and tests. Bigint text is checked against `Size.lean`'s
  canonical form by a regular expression, and `BigInt` must read `0x` digits as the value
  `ofHex` gives them; tests cover it.
- **Decoded sizes.** Charges use JavaScript's own lengths: `String.prototype.length` in UTF-16
  code units, a view's length times its element size, a decoded URL's `href` and its search
  parameters' entries, and the byte count `decodedSize` predicts before decoding. Each node
  allocates at most one new object and primitive nodes own nothing; a folded `Map` or `Set` and a
  repeated shape key keep entries from among the occurrences charged, so the value is never larger
  than the accounting. A caller-built payload can break this (an array used twice, or extra
  properties on a row returned as the decoded array), which the README forbids; text from
  `JSON.parse` cannot. For `serialize` output of a JSON value, the accounting equals `1 + words`
  of that value. `deserialize-limit.spec.ts` compares the runtime's accounting with an independent
  walk of the decoded value at the exact byte boundary.
- **Measuring.** `measureGraph` runs `decodeGraph`'s checks and charges in the same order, with
  every charge enabled. It writes no reference into the document and allocates no record, `Map` or
  `Set`. It still places sparse arrays, into their new arrays, because placing checks the presence
  runs and the number of values. Without a native base64 decoder, `checkBytes` makes the same `atob`
  call and exact-length check as `decodeBytes` but does not copy the bytes: views are then linked
  and constructed over a zero-filled buffer of the same `byteLength`, and view checks and
  constructors read only the length, never the bytes. For a document with no array at two places, as
  `deserialize` requires, the skipped steps charge nothing and check nothing that the measured steps
  do not; a shared array lets a written reference be read again, as a literal or a reference.
  Because `deserialize` writes record properties as `constructOn` does, no inherited setter or
  read-only property intercepts a write that measuring skips. The exceptions to an exact match are
  those the `requiredMaxBytes` TSDoc lists. The serialization bridge checks that `requiredMaxBytes`
  returns eight bytes per word of the Lean accounting and leaves the document unchanged;
  `deserialize-limit.spec.ts` checks it against the independent walk and checks that it accepts and
  rejects the base64 that `deserialize` does, and `serialization-boundaries.spec.ts` does so through
  a native base64 stand-in.
- **Native arrays and views.** Array lengths stay within `2^32 - 1`, and view offsets, lengths and
  alignment are checked before construction. Native array writes and `length` assignment behave as
  the `NativeArray` model in `Positional` states; view constructors and buffer bytes are outside it. `array-bound.spec.ts` and `sparse-codec.spec.ts` cover array lengths and sparse arrays.
- **Map and Set equality.** `Map.prototype.set` and `Set.prototype.add` use `SameValueZero`,
  canonicalize signed-zero keys and keep the first insertion position of an existing entry
  ([Map.set](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-map.prototype.set),
  [Set.add](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-set.prototype.add)). `collection-normalization.spec.ts` covers signed zeros and `NaN`.
- **Base64.** The encoder's alphabet table and bitwise operators are native; `binary-codec.spec.ts`
  compares it with `btoa`. A native decoder never yields more bytes than `decodedSize` predicts,
  which lets the exact-count check reject skipped whitespace; `serialization-boundaries.spec.ts`
  covers this on the `atob` path and with native stand-ins.
- **Encoder observations.** The traversal models constrain only the order of entering and
  referencing objects, not application reads such as `length` and getters. The encoder iterates
  collections with the built-in iterators, which have no `return` method to call. The runtime
  classifies each child slot (`slot` in `emit.ts`) only where the stack machine would, recognizes
  each object once (`node`), reads a Map entry, URL parameters or a view's buffer before its child,
  and keeps trie nodes fresh per call. `serialization.spec.ts` and
  `serialization-collections.spec.ts` cover representative traces.

## Runtime bridges

`OracleMain` is the oracle executable, `reconcile-oracle`. `RuntimeOracle` reads one JSON request
per line, dispatches it by family to the entry function of that family's oracle module, and ends
each response with a record-separator line. A family's oracle module is `Oracle.<Family>Oracle`, and
its entry function is `run`; `PropertyConstructOn` and `PropertyThroughSetter` instead go to
`PropertyWriteOracle` (`runConstructOn`, `runThroughSetter`).

| Oracle family             | Bridge in `scripts/`                        | Runtime comparison                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| ------------------------- | ------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Contract`                | `lean-captured-bridge.ts`                   | graphs from `reuse-fixtures.json`: values, aliases, cycles, identity restoration                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `PropertyOrder`           | `check-property-order-runtime.ts`           | cursor traces, including cases with strictly less work                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `PropertyWrite`           | `check-property-write-runtime.ts`           | single-key outcomes, run through `reconcile` on ordinary objects and forwarding proxies: status, final descriptor, own and inherited setter calls, and no write before a rejection                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `PropertyPlacement`       | `check-property-placement-runtime.ts`       | pairs of own-key orders with an integer key, names and symbols, and every set of accessors they share: `reconcile` succeeds with the desired order exactly where Lean keeps every accessor, and otherwise writes nothing                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `WriteFreeReadback`       | `check-write-free-readback-runtime.ts`      | `reconcile` of every ordered subset of three keys onto two, and of every array of length up to three onto two requested arrays, through a counting proxy: the readback is elided and nothing is written exactly where Lean finds publication write-free, and every result equals `next`; where the values are objects, each requested key that `current` holds is read once when nothing is written and twice otherwise                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `PropertyConstructOn`     | `check-property-construct-runtime.ts`       | new objects built by `snapshot`, a `produce` rebuild, an object `reconcile` adds and `deserialize`, on a custom prototype or `Object.prototype` holding each kind of descriptor for the key, or on a null prototype, from enumerable and non-enumerable source properties: each holds the own data property with its source's enumerability, no setter on its prototype runs, and `serialize` rejects a non-enumerable one                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `PropertyThroughSetter`   | `check-property-through-setter-runtime.ts`  | assignments of a key the object lacks through a setter on its prototype that defines nothing or the key with each set of attributes, on ordinary objects and `produce` drafts: the draft accepts exactly the definition assignment would make and refuses the others; `standard-prototypes.spec.ts` runs `produce` under `node --frozen-intrinsics`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `KeyOrder`                | `check-key-order-runtime.ts`                | sequences of assignments and deletions on objects with integer keys, names and a symbol: the engine's own keys and `produce`'s result both equal Lean's `ownKeys`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Atoms`                   | `check-atoms-runtime.ts`                    | real built-in prototype chains behind custom prototypes, with proxies counting reads: the runtime walk matches Lean's answer and read count, and each atom is kept by `snapshot`, `reconcile` and `produce` and rejected by `serialize`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Ingress`                 | `check-ingress-runtime.ts`                  | real built-in and listed prototype chains behind custom prototypes, with and without a typed-array brand and with a throwing prototype read: recognition with the prototype read shared and with a separate atom split both match Lean's outcome; the object is read once when shared and as often as Lean counts when not, and its custom prototypes the same number of times either way                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `RecognitionPlain`        | `check-recognition-plain-runtime.ts`        | real built-in prototype chains behind custom prototypes, without a view brand and as a typed array and a `DataView`, each over a recognized buffer and over one whose prototype is `null`, and with a throwing prototype read: built-in recognition and every known-kind check match Lean's result and thrown error; the object is read once, and its custom prototypes as the ordered scan of `recognition-scan.ts` reads them, less the typed-array probe's repeated `DataView` walk                                                                                                                                                                                                                                                                                                                                                                              |
| `DraftSurface`            | `check-draft-surface-runtime.ts`            | draft writes on objects, arrays, maps, typed arrays and dates admitted exactly where the result carries them, and objects and arrays with getters, changed or not, kept exactly where Lean keeps them; a rebuilt object or array holds each returned value as data                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `DraftClass`              | `check-draft-class-runtime.ts`              | names on `Map` and `Set` drafts, built-in and subclass instances, owned by the prototype Lean names, and `instanceof` checks that agree; a subclass method runs on a draft and the result keeps the subclass                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `DraftIteration`          | `check-draft-iteration-runtime.ts`          | scripts of iterations and writes on a `Map` draft: each walk, the result's entries and whether the result keeps the original agree with Lean                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `SettledChildren`         | `check-settled-children-runtime.ts`         | every graph of three objects with child lists of at most two entries, with no object or one object changed through its draft, asked whether object 0 and then object 1 need a copy: each answer, the settled answers, including those settled before their question ended, and the kept child lists equal Lean's                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `DraftMembers`            | `check-draft-members-runtime.ts`            | `includes`, `indexOf` and `lastIndexOf` on an array draft of `[a, b, a, 7]`, for each object as itself and as its draft, another object and numbers, with every element read before the search and with the array searched first: results agree with Lean                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `DraftSetMethods`         | `check-draft-set-methods-runtime.ts`        | the `Set` methods on `Set` drafts, unwritten and with a working copy, over enumerated member and key lists, with each operand form (a `Set` from `current`, a `Set` of drafts, a `Set` draft and a set-like object): the members of each result agree with Lean                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `CopyPrototype`           | `check-copy-prototype-runtime.ts`           | copies by `snapshot`, an object `reconcile` adds and a changed `produce` result, of arrays, maps, sets, dates, data views, URLs and parameters, each as its own instance and as a subclass instance: every copy keeps its source's prototype, and `serialize` accepts only the standard prototype, which `deserialize` restores                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `SeededRequirements`      | `check-seeded-requirements-runtime.ts`      | closure traces, including cases with strictly less work                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `DeferredOrder`           | `check-deferred-order-runtime.ts`           | preflights, demanded checkpoints and original error identities                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `FactRenaming`            | `check-fact-renaming-runtime.ts`            | histories with queries and live cursor reads                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `CompactImmutable`        | `check-compact-immutable-runtime.ts`        | cases and ranked plans, with the construction order of each plan                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `NativeValue`             | `check-native-value-runtime.ts`             | fixtures from `native-value-fixtures.json`: facet compatibility, immutable reuse, publication and readback                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `OwnedNativeChild`        | `check-owned-native-child-runtime.ts`       | production carrier adoption projections: raw and canonical query, ordered entries, owner and child identities; then bulk-versus-sequential parameter publications compared natively, without the oracle                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Serialization`           | `check-serialization-lean.ts`               | `serialize` documents decoded and re-emitted exactly by Lean; malformed documents rejected by both; non-canonical documents decoded to the same graph by both; literal roots; every accepted document accepted at exactly eight bytes per word of Lean's `accounting` and rejected one byte below                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `SerializationCollection` | `check-serialization-collection-runtime.ts` | success and failure traces through the production `map` and `set` facets: reads, ordered contents, untouched target on failure                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Spec`                    | `lean-spec-bridge.ts`                       | seeded random graphs of up to seven objects, arrays, maps, sets, dates, and buffers with views over them, with cycles and sharing, attributes, accessors, non-extensible, sealed and frozen values and prototypes, with data and accessor slots on the class prototypes for `reconcile`: `reconcile` of a mutated `next` that reuses, reorders and moves current objects, `produce` recipes of draft writes, created objects and returned values, and `snapshot`; the results read back as graphs equal the reference's on identities, values, descriptors, prototypes and extensibility, except as _Spec agreement_ allows. Standalone: `pnpm exec tsx scripts/lean-spec-bridge.ts --op produce --seeds 2000`, with `--dump SEED` for one case, `--features` for what the `reconcile` cases exercise, and the flags of the batches that _Spec agreement_ describes |
| `Spec` (phases)           | `lean-spec-phases.ts`                       | the `Spec` bridge's `reconcile` cases, plain, hazard-rich and with buffers and views, on a bundle of the sources that records discovery and each decision pass: visit order, pinning alignment, pinned nodes, candidates in decision order with their fixed-slot requirements, and every pass's decision equal the reference's, as _Spec phases_ describes. Standalone: `pnpm exec tsx scripts/lean-spec-phases.ts --seeds 2000`, with `--hazards`, `--binary`, `--nodes N` and `--dump SEED`                                                                                                                                                                                                                                                                                                                                                                       |
| `Spec` (enumeration)      | `lean-spec-enumerate.ts`                    | every case of the universes _Spec enumeration_ lists, about 52,000 `reconcile` cases, 46,000 `produce` recipes and 800 `snapshot` graphs, compared as the outcome and phase bridges compare them. Standalone: `pnpm exec tsx scripts/lean-spec-enumerate.ts`, with `--only NAME` for one universe and `--count` for the size of each                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |

Read the table with these limits:

- A corpus bounds the test enumeration, not production graphs. "Strictly less work" marks cases
  where the optimized algorithm does less work than the reference, so the optimization is not
  vacuous.
- Comparing traces is stronger evidence than comparing results. The _Runtime comparison_ column
  says which a bridge compares; where a bridge compares results and rejections only, a theorem
  about reads or writes reaches the runtime through native tests that count them, not through the
  bridge.
- The `Serialization` domain is records, null-prototype records, dense and sparse arrays, JSON
  literals and shared scalar nodes. Its hand-written JSON importer uses Lean numbers, so `-0` and
  overflowing literal roots are compared with `JSON.parse` at runtime only.

The _mutation audit_, `pnpm exec tsx scripts/spec-mutants.ts`, checks that the `Spec` bridges
detect runtime defects. It applies one deliberate defect, a _mutant_, at a time to the runtime
sources and runs the bridge without flags, then with `--writes`, then with `--writes --hazards`,
stopping at the first run that reports a difference or does not end. A mutant that only the
runtime's discovery or decisions show runs the phase bridge instead, with `--binary`, then without
flags, then with `--hazards`. It restores the sources after
each mutant. A mutant the bridge does not detect marks a case the generator does not produce or a
difference the comparison does not see; the script lists the mutants it expects to go undetected,
each with the gap it stands for. Run the audit after changing the `Spec` bridge, its generator or
the code its mutants patch, and with nothing else running, since it rewrites the sources. With its
default 1500 seeds it fits the [time budget](development.md#time-budget).

After `pnpm check:lean` has built the oracle, you can run one family by hand. The request needs all
three fields; the reply is the oracle's JSON between record-separator lines, the last carrying
`null` or the error.

```sh
echo '{"family":"Contract","args":["lean/fixtures/reuse-fixtures.json"],"input":""}' \
  | .lake/build/bin/reconcile-oracle
```
