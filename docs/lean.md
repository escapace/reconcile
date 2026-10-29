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
No whole-library correctness, memory or speed claim follows from the proofs. The resource bounds
they prove each cover one function or algorithm, such as the number of `reconcile`'s decision
passes or the `maxBytes` limit on what `deserialize` restores; the [Promises](#promises) rows for
these say which parts are proved.

A _reference model_ is a direct definition that optimized code must agree with: `GraphPolicy`
defines the ranked selection stream that `produce`'s identity restoration refines, and
`Construction` the construction schedule. The `Spec` modules are reference models of the public
functions themselves: executable definitions of `reconcile`, `produce` and `snapshot` over graphs
with descriptors, which the `Spec` bridge compares with the runtime on seeded random graphs, and
about which `Spec.Promises` proves the documented promises.

## The heap model

`Heap/Defs.lean` defines finite heaps of atoms and references: plain objects with ordered fields,
arrays with holes, ordered maps and sets, dates, buffers and views. `Heap.Publication`, immutable
reuse (`Immutable`) and the Contract oracle are stated over these heaps; the graphs the public
functions capture are modelled by `Spec.Graph` instead. Function values are opaque atoms, and so
are objects whose state the library cannot copy, such as a `RegExp`, `Error` or `WeakMap`;
`Types.Atoms` proves how the runtime classifies them.
`Heap/Defs.lean` also defines `HeapWF`, which guarantees that every reference points into the heap,
not that the heap is natively valid. `Heap/WF.lean` defines edges and `SurfaceEq`, equality of two
values at every finite depth, by which `Publication` compares a published heap with its source.

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
   `Oracle/RuntimeOracle.lean`, and call it from a bridge run by `scripts/check/lean.ts`. Write a corpus the
   oracle generates with `Protocol.emitCorpus`, or with `Protocol.emitCheckedCorpus` when a case's
   construction does not ensure a premise, and answer input the bridge sends with
   `Protocol.serveArray`. Check the premises the model's theorems need, not their conclusions. Keep
   hand-written fixtures as JSON in `lean/fixtures/`. Prefer comparing
   production code, and say so when a bridge runs a reference transition. Renaming an oracle
   namespace or a fixture file breaks the bridge that uses it.
6. **Document it** in this guide: the correspondence row, its obligations and a bridge-table row.

## Running the gate

`pnpm check lean` (the _gate_) runs `lake build --wfail`, so a warning fails it, then audits axioms
and runs every bridge against one oracle process.
[Checks and time budget](development.md#checks-and-time-budget) gives its budget and receipt, and
the commands to use while editing.

The `NativeValue` and `SpecialValues` bridges skip Node's native Temporal values, and say so. The
`temporal` round runs the Temporal specs and every bridge again with those values.

`pnpm check lean <bridge>...` builds the proofs and runs only the named bridges, by their file names
in `scripts/check/bridges/`, without the axiom audit, and records no pass. The three `Spec` bridges
run in batches: `--batch` selects one, and for the outcome and phase bridges `--seeds` replaces
each batch's seeds and `--dump` shows each seed's case, the reference's outcome and the comparison;
`--features` instead counts the features of the outcome bridge's `reconcile` cases. A failing batch
prints the command that shows its first failing seed, and `pnpm check --help` lists
the batches. _Spec agreement_, _Spec phases_ and _Spec enumeration_ say what the bridges compare,
and [Runtime bridges](#runtime-bridges) describes the mutation audit and how to query one oracle by
hand.

## Checks and failures

The axiom audit allows only `propext`, `Classical.choice` and `Quot.sound`, so a `sorry` fails it.

When the gate fails:

- **Build or audit.** Fix the warning, register the file or remove the axiom. Never add an axiom.
- **Bridge mismatch.** Decide which side changed. Fix an accidental runtime change in the runtime.
  For a deliberate contract change, change the model first, then the corpus and the bridge. Never
  change an oracle to make it agree with the runtime. Reproduce one family by hand as shown in
  [Runtime bridges](#runtime-bridges).
- **Premise check.** An oracle rejects an input that fails a premise the model's theorems need. Fix
  the input or the generator, never the check.
- **Instrumentation or field-name assertion.** A bridge that rewrites source text names the
  replacement that failed; update its search text and keep the instrumentation at the same points.
  Keep oracle field names and translate in the bridge. See
  [Couplings that fail silently](development.md#couplings-that-fail-silently).
- **Timeout.** See [Checks and time budget](development.md#checks-and-time-budget).

## Correspondence

The tables below map every module in `lakefile.toml` to the runtime code it covers, grouped by
operation. The oracle modules are the exception; [Runtime bridges](#runtime-bridges) names them.
_Key theorems_ lists the statements a reader most needs; each module holds more. In any table,
_(definition)_ or _(definitions)_ marks names that are definitions, not theorems, and _(by
definition)_ marks theorems that only restate their model; for these, the bridge and tests carry
the evidence. A mark applies to every name before it, back to the previous semicolon or the start
of the cell. _Bridge_ names the oracle
family that executes the module's definitions against the runtime; _imported by_ names a family
whose oracle runs them through another module, and _proof-only_ means no oracle runs them. A
proof-only module is still built and audited. _Obligations_ names the [runtime
obligations](#runtime-obligations) the correspondence relies on. The [Promises](#promises) table
instead maps the main promises of the public functions to their theorems, bridges and tests.

### Heap model and public contracts

| Module(s)     | Key theorems                                                                                | Runtime                                                                                                                | Bridge               | Obligations       |
| ------------- | ------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- | -------------------- | ----------------- |
| `Defs`, `WF`  | `HeapWF` (definition)                                                                       | the records of `produce`'s identity restoration (`compileImmutable` and `publishFresh` in `src/restore-identities.ts`) | imported by Contract | Capture           |
| `Publication` | `publishRecords_published`, `checkPublication_sound`, `Published.surface`, `Published.path` | `publishFresh` in `src/restore-identities.ts`                                                                          | imported by Contract | Capture, Identity |

### Reference models

| Module(s)        | Key theorems                                                                                                                                                                                                                                                                                     | Runtime                                                                                                                                                                                                                                                                                                                                            | Bridge            | Obligations                                 |
| ---------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------- | ------------------------------------------- |
| `Spec.Graph`     | `Graph.normalize`, `Obj.copy` (definitions)                                                                                                                                                                                                                                                      | the graphs the bridge builds and reads back                                                                                                                                                                                                                                                                                                        | Spec              | Spec agreement                              |
| `Spec.Reconcile` | `run`, `discover`, `decide`, `demote`, `rounds`, `retainPrefix`, `captureReads`, `keepWalk`, `keepsNext`, `skipped` (definitions)                                                                                                                                                                | `src/reconcile.ts` `reconcile`; the reads of `next` by `AlignedCapture` and its `keep` in `src/publication/capture.ts`                                                                                                                                                                                                                             | Spec, Spec phases | Spec agreement, Spec phases                 |
| `Spec.KeepsNext` | `keepsNext_iff`, `writesOfDecision_keepsNext`, `writesOfDecision_eq_publishedWrites`, `run_allWrites_not_next`, `rounds_dropLast_writes_not_next`, `run_changesNext`, `keepsNextAt_pinned`, `rounds_keepsNext_inPlace`, `own_admitted`, `own_fixedRequirements`; `keepsNext_cur` (by definition) | `keepsNextAt`, `allocate`, `remember` and `skipped`, as `publishPhase` and `readback` use it, in `src/publication/publication-engine.ts`; each node's `source` and the graph's `references` in `src/publication/capture.ts`; `ownCandidate` in `src/publication/candidates.ts` and `ownRequirements` in `src/types/shared/property-publication.ts` | Spec, Spec phases | Spec agreement, Spec phases, Next unchanged |
| `Spec.Produce`   | `run`, `kept`, `rebuild`, `snapshot` (definitions)                                                                                                                                                                                                                                               | `src/produce.ts` `produce`, `src/snapshot.ts` `snapshot`                                                                                                                                                                                                                                                                                           | Spec              | Spec agreement                              |
| `Spec.Promises`  | most theorems in [Promises](#promises)                                                                                                                                                                                                                                                           | the documented promises of `reconcile`, `produce` and `snapshot`                                                                                                                                                                                                                                                                                   | Spec              | Spec agreement                              |
| `Spec.Discovery` | `candidates_eq_aligned`, `offersAligned_needed`, `captureChildren_map`                                                                                                                                                                                                                           | `candidates` in `src/publication/candidates.ts`, `offersOther` in `src/publication/capture.ts`                                                                                                                                                                                                                                                     | Spec phases       | Ordinal candidates                          |

The docstrings of `Spec.Graph`, `Spec.Reconcile`, `Spec.KeepsNext`, `Spec.Produce` and
`Spec.Discovery` state their models and what each theorem proves; `Spec.KeepsNext` also gives the
examples that show each clause of its rule necessary and its first clause conservative.
`Spec.Promises` proves most of the [promises](#promises) about these models; its docstring names
the theorem for each promise.

### Promises

The table maps the main promises of the public functions to the theorems that state them over
the Lean models, the bridges that carry them to the runtime and the tests that check the
runtime directly. In the _Theorems_ column, an unqualified name is in `Spec.Promises`, and a
qualified name gives its module to the unqualified names after it in the same cell. There,
_tested only_ marks a part with no proof, and an italic obligation name, such as _Decoded sizes_,
marks a part that the [runtime obligation](#runtime-obligations) of that name supplies.

| Promise                                                                                                                                                                                                                      | Theorems                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Bridge                                                                                                      | Tests                                                                                                          |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| After a successful `reconcile`, `current` matches `next`: key order, array lengths and holes, entry order, sharing and cycles                                                                                                | `keptObject_attrs` (by definition) for a kept object's properties, in the order `Spec.Reconcile.keptObject` gives them; `CollectionPlan.publish_reaches_next` for a kept Map's or Set's entries; `Types.NativeWrites.result_eq` (by definition) for URLs, URLSearchParams and Temporal values; `WriteFreeReadback.accepts_readsAs` (readback accepts only what reads as `next`); `acceptsRetry_readsAs` (by definition) for a later pass; kept arrays, dates, buffers and views, and the whole graph, tested only | `Spec` (results), `WriteFreeReadback`                                                                       | `reconcile-semantics.spec.ts`                                                                                  |
| Keys and entries keep their place; the retained prefix is the longest                                                                                                                                                        | `retainPrefix_prefix`, `retainPrefix_sublist`, `retainPrefix_longest`, `objectWrites_delete_iff`, `entryWrites_delete_iff`, `CollectionPlan.publish_retained`                                                                                                                                                                                                                                                                                                                                                     | `Spec` (results), `PropertyOrder`, `CollectionWrites` (moves and other writes inside a kept `Map` or `Set`) | `reconcile-property-order.spec.ts`                                                                             |
| An own getter or setter keeps its place in key order; when `next`'s order cannot be reached around it, the object is replaced or, if it is `current` itself, `reconcile` throws                                              | `retainPrefix_feasible_iff`, `PropertyPlacement.feasible_iff`, `reference_keeps_fixed_iff`                                                                                                                                                                                                                                                                                                                                                                                                                        | `PropertyPlacement`, `Spec` (results)                                                                       | `reconcile-accessors.spec.ts`                                                                                  |
| A current object is kept only at its own position, and an object already in place nowhere else                                                                                                                               | `demote_candidate`, `demote_pinned`                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | `Spec` (phases)                                                                                             | `readme-publication-semantics.spec.ts`, `reconcile-semantics.spec.ts`                                          |
| `reconcile` never changes `next`: where matching by position could, it throws `PublicationWouldChangeNext`, before any write when the first decision already could                                                           | `Spec.KeepsNext.run_allWrites_not_next` (a call that succeeds), `rounds_dropLast_writes_not_next` (the passes before a rejection), `run_changesNext` (a rejection by the first decision comes before any pass); that the runtime's check sees every object `next` holds is _Next unchanged_                                                                                                                                                                                                                       | `Spec` (`next` read back after every call; the reason of each rejection), `Spec` (phases)                   | `reconcile-keeps-next-stress.spec.ts`, `readme-publication-semantics.spec.ts`                                  |
| A current object at two positions is kept at the first position read; a node with several candidates keeps the first candidate read unless an admitted candidate's fixed slot needs another                                  | `decide_injective`, `demands_satisfiable`, `demands_pinned`; `Spec.Reconcile.decide`, `orderedCandidates` (definitions) for the order                                                                                                                                                                                                                                                                                                                                                                             | `Spec` (identities)                                                                                         | `reconcile-semantics.spec.ts`, `demanded-candidates.spec.ts`                                                   |
| An own getter of a kept object runs once without writes, twice with them and at most once more per demotion pass                                                                                                             | `get_bound`, `read_once_before_write` (upper bounds)                                                                                                                                                                                                                                                                                                                                                                                                                                                              | `Spec` (getter counts), `WriteFreeReadback`                                                                 | `write-free-readback.spec.ts`                                                                                  |
| Reading `next` runs each getter of an object only `next` holds at most once, and the walk over an object already in place runs each of its getters at most once; an object already in place is neither written nor read back | `freshGets_le_one`, `captureReads_once`, `run_pinned`; two examples in `Spec.Promises` show that a getter of an object `current` and `next` share can run twice while `next` is read                                                                                                                                                                                                                                                                                                                              | `Spec` (getter counts of every object, accessors in `next` included)                                        | `reconcile-pruning.spec.ts`                                                                                    |
| The decision passes are bounded, so no plan is searched                                                                                                                                                                      | `passes_le_cur`, `demote_length_le`, `blocked_fresh`                                                                                                                                                                                                                                                                                                                                                                                                                                                              | `Spec` `reconcile-hazards` (getter counts and writes of every pass)                                         | `public-api-invariants.spec.ts` (hostile setters)                                                              |
| A changed slot is written, an unchanged one left alone, a moved or added one written                                                                                                                                         | `objectWrites_set_iff`, `demote_writesOf_nil_iff`, `CollectionPlan.publish_entryWrites`; `Types.NativeWrites.publish_nil_iff` (by definition)                                                                                                                                                                                                                                                                                                                                                                     | `Spec` `reconcile` (writes to objects and arrays), `NativeValue` (`note.unchanged`)                         | `write-free-readback.spec.ts`, `reconcile-accessors.spec.ts`, `public-api-invariants.spec.ts` (write-free)     |
| A kept property keeps its attributes, and an own getter or setter stays one; an added property other than an array element is writable and configurable with `next`'s enumerability                                          | `keptObject_accessor`; `keptObject_attrs` (by definition); per key, `PropertyWrite.publish_keeps_attrs`, `publish_missing_hide`                                                                                                                                                                                                                                                                                                                                                                                   | `Spec` (descriptors), `PropertyWrite`                                                                       | `public-api-invariants.spec.ts`, `property-enumerability.spec.ts`                                              |
| `reconcile`'s writes, and those that build a new object in `snapshot` and `deserialize`, run no inherited setter and make a `__proto__` key an own data property; `reconcile` never overrides an inherited getter or setter  | `PropertyWrite.reconcileKey_no_inherited_setter`, `publish_missing`, `constructFromOn_data`, `constructFromOn_fresh`; `reconcileKey_rejected` (by definition)                                                                                                                                                                                                                                                                                                                                                     | `PropertyWrite`, `PropertyConstructOn`, `Spec` (no getter or setter of a class prototype runs)              | `reconcile-accessors.spec.ts`, `serialization.spec.ts`                                                         |
| An object that blocks a change is replaced; a pass demotes no other object                                                                                                                                                   | `run_last_unblocked`, `mem_blockedObjects`                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | `Spec` `reconcile-hazards` (results)                                                                        | `publication-readback-boundaries.spec.ts`, `publication-failure-boundaries.spec.ts`                            |
| Added objects are new copies                                                                                                                                                                                                 | `publish_origins`, `publish_fresh` (by definition)                                                                                                                                                                                                                                                                                                                                                                                                                                                                | none; `Spec` identifies only current objects                                                                | `reconcile-semantics.spec.ts`                                                                                  |
| `produce` keeps every unchanged subtree and no changed object                                                                                                                                                                | `kept_closed`, `kept_greatest`, `KeptClosure.kept_iff`                                                                                                                                                                                                                                                                                                                                                                                                                                                            | `Spec` `produce` (results)                                                                                  | `produce-properties.spec.ts`, `public-api-invariants.spec.ts`                                                  |
| `produce` copies a date, buffer, view, URL or `URLSearchParams` when read and keeps the original when the copy is unchanged; a Temporal value the recipe does not replace stays the original                                 | `SpecialValues.resolve_eq_outcome`, `temporal_kept`; `copy_unchanged`, `copy_changed`, `fresh_iff` (by definition); that a copy exists for each value read is _Special-value decision_                                                                                                                                                                                                                                                                                                                            | `SpecialValues` (each slot's object), `SpecialDecision`                                                     | `produce-public-api-coverage.spec.ts`, `url-ownership.spec.ts`, `temporal.spec.ts`                             |
| The result holds copies of a buffer and its views, or of a URL and its `searchParams`, only together, and only when the recipe changes one of them                                                                           | `SpecialValues.coherent`; `view_together`, `url_together` (exactly when one changes, for a view the recipe did not make and a URL the result holds)                                                                                                                                                                                                                                                                                                                                                               | `SpecialValues` (each slot's buffer or `searchParams`)                                                      | `finalization-propagation-regressions.spec.ts`, `url-ownership.spec.ts`                                        |
| `snapshot` is a detached copy, one new object per source object                                                                                                                                                              | `snapshot_size`, `snapshot_copy`, `snapshot_fresh` (by definition)                                                                                                                                                                                                                                                                                                                                                                                                                                                | `Spec` `snapshot` (results)                                                                                 | `public-api-invariants.spec.ts`, `graph-capture.spec.ts`                                                       |
| Each object's prototype is read once before the first write                                                                                                                                                                  | `Types.Ingress.ownReads_shared` (at recognition, by definition); the rest tested only                                                                                                                                                                                                                                                                                                                                                                                                                             | `Ingress`, `RecognitionPlain` (read counts)                                                                 | `builtin-recognition.spec.ts`, `ingress-reads.spec.ts`                                                         |
| `produce` calls each getter of the result once, depth first, and reads each draft once                                                                                                                                       | `GetterOrder.run_reads`, `getters_once` (the getters); reading each draft once tested only                                                                                                                                                                                                                                                                                                                                                                                                                        | `DraftSurface` (results)                                                                                    | `produce-getter-order.spec.ts` (order), `produce-reads.spec.ts`, `finalization-observation-boundaries.spec.ts` |
| `produce` and `snapshot` leave `current` unchanged                                                                                                                                                                           | tested only (the models are pure)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | `Spec` (`current-changed` report)                                                                           | `produce-properties.spec.ts` (`produce`)                                                                       |
| `serialize` calls each getter once, depth first                                                                                                                                                                              | `Serialization.DFS.entries_unique`, `recursive_refines_stack` (each object entered once, depth first); the getter reads are _Encoder observations_                                                                                                                                                                                                                                                                                                                                                                | `Spec` `roundtrip-binary` (each getter once, in the order of the bridge's own depth-first walk)             | `serialization.spec.ts`                                                                                        |
| `deserialize(serialize(value))` through JSON text restores the value, every object new, with its sharing, cycles, key order, holes, entries, dates, buffers and views                                                        | `Serialization.Positional.decode_encode_relaxed` (the document, not the value)                                                                                                                                                                                                                                                                                                                                                                                                                                    | `Spec` `roundtrip-binary` (against `snapshot`)                                                              | `serialization.spec.ts`, `serialization-collections.spec.ts`                                                   |
| `deserialize` restores ordinary, extensible objects                                                                                                                                                                          | `PropertyWrite.constructFromOn_fresh` (each restored property); extensibility tested only                                                                                                                                                                                                                                                                                                                                                                                                                         | `PropertyConstructOn` (descriptors)                                                                         | `public-api-invariants.spec.ts`                                                                                |
| `deserialize` rejects malformed data with `DeserializeInputInvalid`                                                                                                                                                          | `Serialization.Positional.decodeNodes_sound`, `Serialization.Preorder.check_iff` (what the checks accept); the error type tested only                                                                                                                                                                                                                                                                                                                                                                             | `Serialization` (malformed documents)                                                                       | `serialization.spec.ts`, `serialization-boundaries.spec.ts`                                                    |
| A repeated `Map` key in `deserialize`'s data keeps its first position and last value, and a repeated `Set` member its first position                                                                                         | `Serialization.Collection.first_insertion_order`, `last_value`, `resolved_map_rows`, `resolved_set_keys`                                                                                                                                                                                                                                                                                                                                                                                                          | `SerializationCollection`                                                                                   | `serialization-collections.spec.ts`                                                                            |
| `deserialize` restores no value larger than `maxBytes`, each object counted once and each primitive at every occurrence                                                                                                      | `Serialization.Size.stops_iff`, `accounting_eq_reachable`, `image_sum_le`, `foldMap_length_le`, `firstOrder_length_le`; that the charges cover the value is _Decoded sizes_                                                                                                                                                                                                                                                                                                                                       | `Serialization` (accounting)                                                                                | `deserialize-limit.spec.ts`                                                                                    |
| `deserialize` accepts at exactly `requiredMaxBytes` and rejects one byte below                                                                                                                                               | `Serialization.Size.accepts_iff_bytes` (the boundary)                                                                                                                                                                                                                                                                                                                                                                                                                                                             | `Serialization` (the size `requiredMaxBytes` returns), `Spec` `roundtrip-binary`                            | `deserialize-limit.spec.ts`, `public-api-invariants.spec.ts`                                                   |
| `deserialize`'s time and memory are proportional to its input and `maxBytes`                                                                                                                                                 | `Serialization.Size.node_count_le_accounting`, `table_node_count` (a document of records, arrays, literals and bigints has no more nodes than words, so a node count above the limit can be rejected before any table is allocated); the rest tested only                                                                                                                                                                                                                                                         | none                                                                                                        | `deserialize-limit.spec.ts` (rejections before allocation)                                                     |

### `snapshot`

`snapshot` is `Spec.Produce.snapshot` in [Reference models](#reference-models), a new object per
source object with atoms shared; the Spec bridge checks the runtime against it on random graphs.
[The development guide](development.md#couplings-that-fail-silently) lists the walk in
`src/snapshot.ts` as the _Snapshot walk_ coupling. `snapshot`'s runtime obligations are _Snapshot
memo_ and _Built-in snapshot writer_.

### `reconcile`

| Module(s)                     | Key theorems                                                                                                                                                                                                                                                                                                                                                                                                                    | Runtime                                                                                                                                                                                                                                                                                                                                                                                                          | Bridge                                                    | Obligations                                       |
| ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- | ------------------------------------------------- |
| `PropertyOrder`               | `step_equivalence`, `stream_equivalence`, `aligned_mem`                                                                                                                                                                                                                                                                                                                                                                         | `src/types/shared/property-publication.ts` `PropertyOrder`; aligned publication in `src/types/object.ts`                                                                                                                                                                                                                                                                                                         | PropertyOrder                                             | Capture                                           |
| `DeferredOrder`               | `catchUp_eq`, `execute_eq`                                                                                                                                                                                                                                                                                                                                                                                                      | `src/types/shared/property-publication.ts`                                                                                                                                                                                                                                                                                                                                                                       | DeferredOrder                                             | Property order                                    |
| `Descriptor`                  | `Attrs`, `OwnProperty` (definitions)                                                                                                                                                                                                                                                                                                                                                                                            | own property descriptors as `Object.getOwnPropertyDescriptor` reports them; the attributes `defineData` in `src/standard-prototypes.ts` gives                                                                                                                                                                                                                                                                    | imported by PropertyWrite, Spec                           | Property writes                                   |
| `PropertyWrite`               | `reconcileKey_no_inherited_setter`, `publish_missing`, `publish_missing_hide`, `publish_keeps_attrs`, `constructOn_data`, `constructFromOn_data`, `constructOn_fresh`, `constructFromOn_fresh`, `draftSet_eq`, `assignStrict_eq`, `publish_accessor`, `reconcileKey_complete`; `reconcileKey_rejected`, `reconcileKey_sound`, `draftThroughSetter_eq`, `draftThroughSetter_refused`, `draftThroughSetter_tamed` (by definition) | `src/types/shared/property-publication.ts` `canPublishProperties`, `publishProperty`, `writeProperty`; `hide` in `src/standard-prototypes.ts`, as `writeProperties` in `src/types/object.ts` applies it; `src/types/shared/draft-properties.ts` `set`, `defineProperty`; `setOwnProperty` (`src/set-own-property.ts`); `define` in `src/serialization/common.ts`; the fresh-shell write in `src/types/object.ts` | PropertyWrite, PropertyConstructOn, PropertyThroughSetter | Property writes                                   |
| `Retain`, `PropertyPlacement` | `matched_maximal`, `place_matched`, `feasible_iff`, `reference_sectors`, `reference_keeps_fixed_iff`                                                                                                                                                                                                                                                                                                                            | `src/types/shared/property-publication.ts` `canPublishProperties` with `PropertyOrder`                                                                                                                                                                                                                                                                                                                           | PropertyPlacement; `Retain` imported by Spec              | Key order                                         |
| `WriteFreeReadback`           | `object_writeFree_matches`, `array_writeFree_matches`, `collection_writeFree_matches`, `publishKnown_eq`, `publishPre_eq`, `publishSeen_eq`, `accepts_readsAs`; `acceptsRetry_readsAs` (by definition)                                                                                                                                                                                                                          | readback elision, the preflight facts (`PreflightFacts`, `src/types.ts`) and retried publications in `src/publication/publication-engine.ts`; `occupants` in `src/publication/capture.ts`; `publish` in `src/types/object.ts`, `src/types/array.ts` and the other kinds in `src/types/`; `publishKnown`                                                                                                          | WriteFreeReadback                                         | Write-free readback, Reads before the first write |
| `CollectionPlan`              | `publish_result`, `publish_retained`, `publish_deletes`, `publish_puts`, `publish_entryWrites`, `publish_perm_entryWrites`, `publish_reaches_next`, `unchanged_iff`, `put_same`                                                                                                                                                                                                                                                 | `publish` in `src/types/shared/collection.ts`                                                                                                                                                                                                                                                                                                                                                                    | CollectionWrites                                          | Built-in contents, Ordinal candidates             |

Beyond the [Promises](#promises) rows that cite it, `src/__tests__/reconcile-semantics.spec.ts`
tests that a successful call keeps the current root and never merges distinct nodes, and that a kept
plain object keeps its prototype. A failed call throws without rolling back (README: _Not rolled
back_).

Pinning is `Spec.Reconcile.pinned`, and a pinned object is one the README calls _already in
place_. A `next` object is pinned when, at capture's first visit, its parent's aligned current
object holds that same object at the same own-property slot, and the object's subtree reaches
neither root. A pinned object stays as it is with everything inside it, and no other position may
keep it (`pinnedAt`, `demote_pinned`). A buffer or view is never pinned, because construction ties
a buffer to its views and a view to its buffer. The Spec bridge checks pinning on random graphs.

`PropertyOrder` keeps the cursor's decisions while bounding its work. `aligned_mem` proves that when
duplicate-free current keys start with the requested order, a current key is requested exactly when
its position is below the requested count. `DeferredOrder` lets private cursor work wait until
needed, without sharing observations across phases.

The docstrings of `Descriptor`, `PropertyWrite`, `CollectionPlan` and `PropertyPlacement` state
their models and what each theorem proves.

`PropertyWrite` also covers new objects: a new object holds its values as data properties, and
building one runs no setter. `setOwnProperty` (used by `snapshot`), `define` in
`src/serialization/common.ts` and the fresh-shell write assign only a key `Object.prototype` lacks
and define any other (`constructOn`, `constructFromOn`). `constructOn_data` and
`constructFromOn_data` prove the outcome wherever assignment reaches no accessor and no read-only
property, as on an unmodified `Object.prototype`; `constructOn_fresh` and `constructFromOn_fresh`
prove it whatever `Object.prototype` holds. A non-enumerable source property is defined
non-enumerable, and every new property is writable and configurable. `publish_missing` covers a key
an object lacks, which is how `reconcile` fills an object it adds: a key whose assignment would
reach an accessor is defined. `publish_missing_hide` proves, with `publish_missing`, that an added
key takes `next`'s enumerability, and `publish_keeps_attrs` that a key written in place keeps its
attributes.

A `produce` recipe's assignment of a key its object lacks may reach a setter on the prototype,
which receives the draft. A hardened environment's setter, such as those `node --frozen-intrinsics`
and SES put on standard prototypes, defines the key on its receiver as assignment would. The draft
accepts exactly that definition, so the assignment has the object's outcome
(`draftThroughSetter_eq`, `draftThroughSetter_tamed`), and refuses any other definition
(`draftThroughSetter_refused`).

### `produce`

| Module(s)                                                        | Key theorems                                                                                                                          | Runtime                                                                                                                                                                                                                                                                        | Bridge                                       | Obligations                                  |
| ---------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------- | -------------------------------------------- |
| `GraphPolicy`                                                    | `feasiblePlans_exact`, `rankedPlans_exact`, `completion_survives_score_pruning`                                                       | the reference ranked stream, to which `CompactImmutable` relates its masks                                                                                                                                                                                                     | imported by Contract, CompactImmutable       | Selection search                             |
| `SettledChildren`                                                | `check_step`, `needs_settled`, `needs_unchanged`, `needs_complete`, `needs_keeps_complete`, `settled_reach_recorded`, `recorded_getD` | `checkDescendantsForMaterialization` in `src/finalization.ts`; `compileImmutable` in `src/restore-identities.ts`                                                                                                                                                               | SettledChildren                              | Finalization reads                           |
| `FinalizationReads`                                              | `decisions_gated`, `lastSymbol_iff`, `keys_exact`, `reread_exact`                                                                     | `DraftObservation.copies` and `checkState` in `src/finalization.ts`; `PropertyDraftState.keys` in `src/types/shared/draft-properties.ts`                                                                                                                                       | proof-only                                   | Finalization reads                           |
| `SpecialValues`                                                  | `resolve_eq_outcome`, `coherent`, `view_together`, `url_together`, `facts_reachable`, `first_eq_sealed`                               | `chooseSpecial` in `src/graph/provenance.ts`; `specialFacts`, `materializeSpecial`, `forceOwnedChildren` and the special branch of `materializeContainerSlot` in `src/finalization.ts`; `cloneSpecialValueAfterMiss` in `src/draft-session.ts`                                 | SpecialValues, SpecialDecision               | Special-value decision                       |
| `GetterOrder`                                                    | `run_reads`, `getters_once`, `Dfs.slots_iff`, `run_dfs`, `dfs_eq_serialization`                                                       | `needsMaterialization`, `checkState`, `checkDescendantsForMaterialization`, `materializeContainerSlot`, `materializeState`, `readTraversalProperty` and `observeAccessor` in `src/finalization.ts`; `someChild` and `observeDraft` of the object, array, `Map` and `Set` kinds | proof-only                                   | Finalization reads                           |
| `Immutable`                                                      | `selected_published`, `selected_surface`, `selected_storage_distinct`                                                                 | `publishFresh` and `publishFirst` in `src/restore-identities.ts`                                                                                                                                                                                                               | Contract                                     | Identity                                     |
| `KeptClosure`                                                    | `kept_iff`                                                                                                                            | `unavailable` from `compileImmutable` in `src/restore-identities.ts`; the eligibility mask in `immutableHead`                                                                                                                                                                  | proof-only                                   | Identity, Finalization reads, Spec agreement |
| `CompactImmutable`                                               | `feasible_iff`, `ranked_decode`, `ranked_head`, `selected_decode`; `separated_of_injective` (by definition)                           | `src/graph/immutable-selection.ts` `immutableSelections`, `immutableHead`; `publishFirst` in `src/restore-identities.ts`, which publishes the first ranked mask that can be built                                                                                              | CompactImmutable                             | Identity, Selection search                   |
| `KeyOrder`                                                       | `build_nodup`, `ownKeys_ownKeys`, `SameKeys.ownKeys_eq`, `rebuild_preserves`, `produce_key_order`                                     | `preparePropertyCopy` in `src/types/shared/draft-properties.ts`; finalization                                                                                                                                                                                                  | KeyOrder                                     | Key order                                    |
| `DraftSurface`                                                   | `admits_iff_represented`, `refused`, `keeps_iff`, `handle_rebuilds` (by definition)                                                   | `admits` in `src/types/shared/draft-properties.ts`, non-extensible collection drafts and native copies in `src/draft-session.ts`, `reuse` in `src/types/object.ts` and `src/types/array.ts`                                                                                    | DraftSurface                                 | Draft surface                                |
| `DraftClass`                                                     | `draft_instanceOf`, `lookup_other`, `lookup_method`                                                                                   | `draftCollectionBase` and `adoptDraftClass` in `src/types/shared/draft-collection.ts`                                                                                                                                                                                          | DraftClass                                   | Draft class                                  |
| `DraftIteration`                                                 | `iterate_entries`, `iterate_kept`, `write_after_iterate`, `kept_untouched`, `drafted_nodup`                                           | `draftWalk` and `draftCollectionBase` in `src/types/shared/draft-collection.ts`                                                                                                                                                                                                | DraftIteration                               | Draft iteration                              |
| `DraftMembers`                                                   | `includesBy_drafted`, `includesBy_form`, `includesBy_single`, `plain_self`                                                            | `memberIdentity` and `arraySearches` in `src/types/shared/draft-members.ts`                                                                                                                                                                                                    | DraftMembers                                 | Draft members                                |
| `DraftSetMethods`                                                | `mem_union`, `mem_intersection`, `mem_difference`, `mem_symmetricDifference`, `isDisjointFrom_walk`, `intersection_drafted`           | `setMethods` in `src/types/set.ts`                                                                                                                                                                                                                                             | DraftSetMethods                              | Draft members, Set methods                   |
| `CopyPrototype`                                                  | `adopt_eq`, `copy_keeps`, `serializes_iff_restored` (by definition)                                                                   | `adoptPrototype` in `src/types/shared/prototype.ts`; array, `Map`, `Set`, `Date`, `DataView`, URL and Temporal construction; `serialize` recognition and `readView`                                                                                                            | CopyPrototype                                | Copy prototypes                              |
| `Requirements`, `RequirementAdmission`, `RequirementPropagation` | `close_least`, `close_closed`, `close_drains`, `admit_nodup`, `completed_insertion_order`                                             | `src/graph/requirements.ts` `closeRequirements`                                                                                                                                                                                                                                | SeededRequirements; imported by FactRenaming | none                                         |
| `SeededRequirements`                                             | `close_eq`, `run_eq`, `scans_le`                                                                                                      | `compileImmutable` in `src/restore-identities.ts`, `src/finalization.ts`                                                                                                                                                                                                       | SeededRequirements                           | none                                         |
| `ClosureHistory`, `FactRenaming`                                 | `expandUnfolded_eq`, `replay_known`, `execute_eq`, `observations_eq`                                                                  | `src/graph/requirements.ts` `RequirementClosure`                                                                                                                                                                                                                               | FactRenaming                                 | none                                         |
| `Construction`                                                   | `schedule_safe`, `schedule_complete`, `schedule_flat`, `schedule_shells_only`                                                         | `src/graph/construction.ts` `constructionOrder`; `publishFresh` in `src/restore-identities.ts`                                                                                                                                                                                 | CompactImmutable                             | none                                         |

`GraphPolicy` defines domains, storage separation, identity requirements, feasible plans and the
ranked stream, which keeps domain order within equal scores. Identity restoration chooses which
current objects an immutable result reuses. `CompactImmutable` encodes choices as retained bits and
relates them to the ranked stream; `ranked_head` proves that an admissible, separated and closed
eligibility mask is the first ranked mask. Each record is its own storage, so every mask is
separated (`separated_of_injective`) and the runtime search tracks no owners. The unavailable
records are closed over parents, so the eligibility mask is closed, and `immutableHead` checks only
that every fixed record is eligible. `KeptClosure.kept_iff` proves that, over the reference model,
the current objects `produce` keeps are those that the closure of the changed objects over their
parents leaves out.

The docstrings of `SettledChildren`, `FinalizationReads`, `SpecialValues` and `GetterOrder` state
their models and what each theorem proves.

`Requirements` defines `close` as the set the runtime's eager queue admits and proves it the least
closure of the seeds (`close_seeds`, `close_closed`, `close_least`). `replay_known` proves that
after any history of requirements and implications, `RequirementClosure`'s known set is that
closure under the rules received, whatever the arrival order. `SeededRequirements` proves that
dropping implications into seed facts keeps the closure and its trace, which `compileImmutable`
relies on. `FactRenaming` proves that relabeling objects as numbers, as the bridges do, preserves
every closure, query and stream, and `expandUnfolded_eq` equates the runtime's
admit-then-propagate `require` with expanding from the fact.

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

| Module(s)                | Key theorems                                                                                                                       | Runtime                                                                                                                                                                                                                                   | Bridge                                                                            | Obligations                  |
| ------------------------ | ---------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------- | ---------------------------- |
| `Types.RecognitionPlain` | `recognize_eq_scan`, `plain_probes`                                                                                                | `builtinFirstMatch`, `builtinRemainingMatch`, `viewAnswer` and `recognizedBuffer` in `src/types/builtins.ts`, `inChain`; the reference `orderedScan` in `scripts/check/fixtures/recognition-scan.ts`                                      | RecognitionPlain; imported by Ingress                                             | Recognition                  |
| `Types.Atoms`            | `classify_atomic`, `classify_reads`, `ingress_atom_iff`, `ingress_structural`                                                      | `isAtomObject` in `src/object-property.ts`, `recognize` in `src/adapters/recognition.ts`                                                                                                                                                  | Atoms                                                                             | Recognition, Atoms           |
| `Types.Ingress`          | `walkReads_eq`, `viewCopy_once`, `bufferCopy_once`, `typedFirst_once`; `ownReads_shared` (by definition)                           | `recognize` with a `PrototypeRead` in `src/adapters/recognition.ts`; capture's `prototypes`, `createDraft`, the snapshot walk, binary-native copies                                                                                       | Ingress                                                                           | Recognition, Atoms, Ingress  |
| `Types.MapEntries`       | `put_middle`, `put_new`, `remove_middle`                                                                                           | the built-in `Map.prototype.set` and `delete`, which the collection models take as given                                                                                                                                                  | imported by DraftIteration, SerializationCollection                               | Built-in contents            |
| `Types.NativeWrites`     | `publish_nil_iff`, `publish_url`, `publish_parameters`, `publish_temporal`, `temporal_compatible_iff`, `result_eq` (by definition) | `publish`, `matches` and `requirements` in `src/types/url.ts`, `src/types/url-search-parameters.ts` and `src/types/temporal.ts`; `SpecialPolicy.equivalent`; `replaceNativeParameters`                                                    | NativeValue                                                                       | Native values, Native writes |
| `Types.OwnedPublication` | `bulk_equivalent`, `bulk_identity`, `sequential_payload`                                                                           | `src/types/shared/url-carrier.ts`                                                                                                                                                                                                         | imported by NativeValue; native differential check in the OwnedNativeChild bridge | URL ownership                |
| `Types.OwnedNativeChild` | `adopt_consistent`, `admitted_iff`, `first_prepared_ranked`, `replay_owned_valid`                                                  | `src/types/url.ts`, `src/types/url-search-parameters.ts`, `src/types/shared/url-carrier.ts`                                                                                                                                               | OwnedNativeChild                                                                  | URL ownership                |
| `Types.CallTables`       | `lazy_run_eq`, `pending_run_eq`, `filled_run_eq`, `interleave_length`, `interleave_get`, `fill_row`                                | `memoized`, `memo`, `targetOf` and `typedCopy` in `src/snapshot.ts`; `copyTypedFirst` in `src/types/shared/binary-native.ts`; `scalar`, `layout` and `push` in `src/serialization/emit.ts`; `checkShape` in `src/serialization/decode.ts` | proof-only                                                                        | Per-call tables              |

The docstrings of `Types.CallTables`, `Types.RecognitionPlain`, `Types.Atoms`, `Types.Ingress`,
`Types.MapEntries` and `Types.NativeWrites` state their models and what each theorem proves.

`Types.NativeWrites` extends write minimality to URLs, `URLSearchParams` and Temporal values, which
the `Spec` model lacks. Its claims are about one node's contents, not a new instance of the public
graph theorems, and its URL has no `searchParams` edge. `Types.OwnedPublication` proves that bulk
replacement equals clear-and-append with identities preserved (`bulk_equivalent`,
`bulk_identity`).

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

| Module(s)                  | Key theorems                                                                                                                                                                                  | Runtime                                                                                                                                                                                                                     | Bridge                    | Obligations                          |
| -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------- | ------------------------------------ |
| `Serialization.Positional` | `decode_encode_relaxed`, `decodeNodes_sound`, `decode_encode_control`, `renumber_first_use`, `typedRef_sound`, `sparse_grow_eq_preallocate`, `sparse_resize_keeps`                            | `src/serialization/emit.ts` `slot`, `layout`; `encode.ts` `renumber`, `controlTable`; `decode.ts` `checkControl`; `facets/slots.ts` `runEnd`, `resolve`; `facets/array.ts` `sparseArray`, `place`; `layout.ts`; `frames.ts` | Serialization             | JSON.parse, Native arrays and views  |
| `Serialization.Preorder`   | `preorder_iff`, `check_iff`, `encoder_canonical`                                                                                                                                              | `src/serialization/decode.ts` `fill`; `facets/slots.ts` `references`, `enter`                                                                                                                                               | Serialization             | none                                 |
| `Serialization.DFS`        | `recursive_refines_stack`, `entries_unique`, `leaf_contract`, `captured_index_lt_length`                                                                                                      | `src/serialization/encode.ts` `encodeGraph`; `leaf.ts`; array lengths in `frames.ts`                                                                                                                                        | imported by Serialization | Encoder observations                 |
| `Serialization.Inline`     | `inline_step_refines`, `inline_run_refines`, `inline_matches_recursive`                                                                                                                       | `src/serialization/frames.ts` `advances`; `node` in `emit.ts`; `leaf.ts`                                                                                                                                                    | proof-only                | Encoder observations                 |
| `Serialization.ShapeRadix` | `getR_split`, `getR_setR`, `radix_eq_internAll`, `radix_ids_inj`, `radix_renumber`                                                                                                            | `src/serialization/radix.ts` `lookup`, `intern`, `split`; `encode.ts` `renumber`                                                                                                                                            | proof-only                | Encoder observations                 |
| `Serialization.Collection` | `resolved_map_trace`, `resolved_map_rows`, `resolved_set_trace`, `resolved_set_keys`, `first_insertion_order`, `last_value`, `decodeMap_rows`, `decodeSet_keys`                               | `src/serialization/facets/collection.ts` `map`, `set`                                                                                                                                                                       | SerializationCollection   | Map and Set equality                 |
| `Serialization.Base64`     | `encode_spec`, `encode_length`, `groupWord_bytes`, `decode_spec`, `decode_encode`, `decode_in_place`, `wholeGroups_memory`                                                                    | `src/serialization/binary.ts` `encodeTable`, `decodeTable`                                                                                                                                                                  | proof-only                | Base64                               |
| `Serialization.Size`       | `accounting_eq_reachable`, `node_count_le_accounting`, `table_node_count`, `stops_iff`, `accepts_iff_bytes`, `image_sum_le`, `foldMap_length_le`, `json_words_le_text`, `encodeInt_decodeInt` | `src/serialization/size.ts`; `decode.ts` `decodeGraph`, `measureGraph`, `checkShape`; `src/required-max-bytes.ts`; the charges in `facets/*.ts`; bigint text in `emit.ts` and `facets/native.ts`                            | Serialization             | Decoded sizes, Measuring, JSON.parse |

A document is `[literal]` for a JSON-literal root and `[control, payloads]` otherwise. Every value
position is a slot whose kind, literal or reference, comes from its node's layout, never from its
value, so no number or string is reserved. The control table holds each node's layout id, then the
shapes and layouts, each framed by its length (`decode_encode_control`).

The decoder checks meaning, not canonical form: it uses the tables as given, so they may be
reordered, repeated or unused. `decode_encode_relaxed` shows that it inverts the encoder, and
`decodeNodes_sound` states what every accepted document means. `Preorder` proves that the reverse
scan accepts exactly the documents numbered in depth-first entry order from node 0, so every node is
reachable. On the encoder side, `inline_matches_recursive` gives the recursive trace and memo for a
terminating in-place run (termination is not proved). `radix_eq_internAll` shows that the per-call
path-compressed trie assigns `Positional`'s first-use ids (`internAll`) for any key type, lone
surrogates included, and `radix_ids_inj` and `radix_renumber` that those ids meet
`renumber_first_use`'s injectivity premise.

Map and Set payloads are resolved, then folded with native `set` or `add`; on a failed read the
target is untouched, and otherwise it holds the fold (the `resolved_*` theorems). `encode_spec`
covers the table encoder used for large buffers when `Uint8Array.prototype.toBase64` is missing and
`TextDecoder` exists. When `Uint8Array.fromBase64` is missing, the table decoder takes large
buffers: it reads each group's four codes as one little-endian word and writes its three bytes as
one, in place over one buffer, and returns RFC 4648's bytes (`groupWord_bytes`, `decode_in_place`),
the encoder's input among them (`decode_encode`); no write reaches a code still to be read
(`wholeGroups_memory`). A code outside the alphabet sends the text to the `atob` path, which decides
the error. A sparse array starts as `new Array(length)` when at least half its elements are present
and as `[]` otherwise, receives its elements in ascending order, then gets its length;
`sparse_grow_eq_preallocate` and `sparse_resize_keeps` prove both starts give the same array with no
element lost, given that every written index is below the length (`runEnd` ensures it); an example
shows that a write at or beyond the length would be removed.

`Size` defines the `maxBytes` limit, and its docstring states what each theorem proves.
`accounting_eq_reachable` is about document nodes, not decoded objects: that the charges cover the
decoded value is the _Decoded sizes_ obligation, and that `requiredMaxBytes` returns the smallest
accepted limit (`accepts_iff_bytes`) is the _Measuring_ obligation. Which words each kind of node
is charged is the runtime's table, which the README states. For records, arrays, literals and
bigints, `tableCharges` restates that table; the Serialization oracle runs `tableCharges`, and
`table_node_count` proves that it meets `node_count_le_accounting`'s premise for every node it
admits. `Map`, `Set` and the native kinds have no charges in Lean, so for their nodes the runtime
alone meets that premise (_Decoded sizes_). The other theorems hold for any charges that meet
their premises.

**Encoder-only theorems.** `Positional`'s `decode_encode_document`, `encode_decode_document`,
`intern_canonical`, `canonical_intern` and `sparse_canonical` hold for a decoder that also
requires first-use, duplicate-free tables. They are true of the encoder's output, which
`encode.ts` cites `decode_encode_document` for and `facets/array.ts` cites `sparse_canonical`
for, but not of what `deserialize` accepts.

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
  identities, values, descriptors, prototypes and extensibility. Rejections agree, each with the
  reference's reason (`PublicationWouldChangeNext` exactly when the reference reports
  `changesNext`), and nothing is written before a rejection the reference decides before any write.
  After every `reconcile` call, successful or rejected, `next` reads back with the identities and
  contents it had before. `produce` and `snapshot` leave `current` unchanged, and a value sent
  through `serialize`, JSON text and `deserialize` equals the reference's `snapshot`. The bridge
  checks this on seeded random graphs, a `current` of up to seven nodes with cycles, sharing,
  attributes, accessors, prototypes and integrity levels, where `next` reuses, reorders and moves
  current objects, rarely one whose subtree reaches `current`'s root, which makes `next` hold
  `current` and the call reject, and `produce` recipes write drafts, create objects and return
  values, so its evidence is for the generated cases. The models cover objects, arrays, maps, sets,
  dates, buffers, views and, for `reconcile`, the slots of class prototypes; they do not cover
  `SharedArrayBuffer`, views that track their buffer's length, buffer and view subclasses, URLs,
  Temporal values or proxies. The gate allows no difference: results, rejections and writes before a
  rejection must agree, and so must the getter counts of every object on success and of every object
  only `next` holds on rejection. No setter of a `next` object and no getter or setter of a class
  prototype may run. The bridge runs in batches: `reconcile`, plainly and through recording
  proxies; `reconcile-hazards`, `reconcile-binary` and `reconcile-next-accessors`, through the
  proxies; `produce`, `produce-binary`, `snapshot`, `snapshot-binary` and `roundtrip-binary`. The
  plain and hazard batches of the outcome and phase bridges also run the seeds
  `REGRESSION_SEEDS` names in `scripts/check/fixtures/spec-generator.ts`, whose cases once showed the runtime and the
  reference apart past the batches' ranges. The `reconcile` batch also checks twelve fixed cases,
  plainly and through the recording proxies: the six examples
  of `Spec.KeepsNext`, `walkReachesRoot`, and `ownNodeInCapture`, `ownNodeAlignedOnce`,
  `ownNodeInDiscovery`, `ownNodeFixedSlot` and `ownNodeWritableSlot` (_Reads before the first
  write_), each checked to have, in the reference, the outcome the bridge states for it.
  The enumeration never produces `laterPass`, `mapChild` or `walkReachesRoot`, and the gate's random
  graphs almost never do. In `walkReachesRoot`, the walk of an object in place reaches the root of
  `next`, itself an object of `current`, yet the call succeeds: the object's read-only `up` cannot
  take the root's target, so the object is copied. A call that keeps such an object is rejected, and
  getter counts of `current` are compared only on success, so this case alone shows the order of the
  walk's reads. Through the recording proxies, every current object and array is wrapped in a proxy
  that records the writes and deletions it receives, over every decision pass, and they are
  compared with the reference's writes. The `reconcile-hazards` batch generates more accessors and
  more setters that drop their value than the `reconcile` batch, so that about one call in twelve
  needs more than one decision pass. The `-binary` batches add buffers, some of them resizable, with
  typed arrays and `DataView`s over them. The `reconcile-next-accessors` batch adds accessors to the
  objects only `next` holds. The round trip restricts the graphs with buffers and views to what
  `serialize` accepts and uses the `maxBytes` that `requiredMaxBytes` returns; it also checks that
  each getter of the source runs once, depth first, that no setter runs, that one byte less is
  refused and that the source is unchanged.
- **Spec phases.** On the `reconcile` cases, plain, hazard-rich and with buffers and views, the
  runtime's discovery and decisions equal the reference's phases (`SpecOracle.phases`): the visit
  order and the pinning alignment of the nodes that are not pinned, the pinned nodes, each node's
  candidates in decision order with the requirements of their fixed slots, and the decision of every
  pass up to the first that keeps no root or could change `next`. The phase bridge reads them from a
  bundle of the sources that records `publishGraph`'s candidates and each `decide`, so the library
  carries no hook.
- **Spec enumeration.** Every case within the bounds of `scripts/check/bridges/spec-enumeration.ts` agrees with
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
  reference stops, as `publishGraph` does, at the first decision that keeps no root or could
  change `next` (`Spec.Reconcile.rounds`, which both `run` and `SpecOracle.phases` use). The
  reference's budget of one demotion per current object never cuts the passes short
  (`demote_last_unblocked`), and there is at most one more pass than there are current objects
  (`demote_length_le`, `passes_le_cur`). The `forbidden-ignored` mutant keeps demoted objects and
  `blocked-not-forbidden` demotes nothing; the [mutation audit](#runtime-bridges) reports each as
  `hung`.
- **Next unchanged.** `Spec.KeepsNext` proves that a pass whose decision satisfies
  `Spec.Reconcile.keepsNext` writes into no object `next` holds, so the runtime must check the same
  rule at the same point and supply its inputs:
  - _Placement._ After each decision keeps the root, and before its pass allocates or writes,
    `allocate` runs `keepsNextAt` on every kept node; on a failure `publishGraph` returns
    `WOULD_CHANGE_NEXT`, which `reconcile` throws as `PublicationWouldChangeNext`. Pinned nodes
    pass (`keepsNextAt_pinned`).
  - _Objects `next` holds._ Capture sets each node's `source`, the object of `next` it is, in the
    node literal it creates, and keeps its per-call table of the objects of `next` it met
    (`references`); a node is _untouched_ when it keeps its `source`, and a node that keeps another
    object capture met in `next` breaks the rule's first clause. An object inside a subtree kept in
    place is no node's candidate, so it needs no entry. A node's references are its captured
    edges, a view's buffer and a URL's `searchParams` included: a write into a buffer changes its
    views and a write into a URL changes its `searchParams`, and discovery keeps a view's buffer
    or a URL's `searchParams` only with its owner's own object, so the rule sees the linked object
    as a target. A URL that discovery pins because its `searchParams` stay in place keeps the
    object it is.
  - _Skipping._ `skipped` makes publication and readback leave untouched nodes alone, as they
    leave pinned ones (`writesOfDecision_eq_publishedWrites`), and `remember` still records them
    at their nodes, as `writtenPairs` does.
  - _Premise._ The theorems that make skipping and the second clause exact and that show pinned
    and in-place nodes pass (`untouched_writesOf`, `writesOfDecision_eq_publishedWrites`,
    `publishedWrites_child`, `keepsNextAt_pinned`, `rounds_keepsNext_inPlace`) assume that each
    object both arguments share reads the same through both (`Coherent`; README: _Where `next` can
    still change_). The safety theorems do not need it.
  - _Boundary._ The objects `next` holds are those capture reads. README: _Where `next` can still
    change_ lists the objects and changes the rule does not see.

  The `next-held-elsewhere-kept` and `untouched-child-unchecked` mutants each drop one clause of
  the rule, and `untouched-published` publishes and reads back untouched nodes again; the
  [mutation audit](#runtime-bridges) detects each.

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
- **Property order.** `DeferredOrder` applies only while key storage is private, stable and
  non-escaping, and desired keys are buffered eagerly. A key moved into the requested order is
  deleted, assigned again so that a proxy's `set` trap observes it, and given back its own
  attributes (`restoreAttributes`), as `PropertyWrite.publish_keeps_attrs` keeps them for a key
  written in place. No one-key model covers the move; `keptObject_attrs` states the move's result.
  `property-order.spec.ts` and `reconcile-property-order.spec.ts` cover the cursor and the moved
  keys.
- **Property writes.** `PropertyWrite` covers one key of an ordinary object, or of a proxy whose
  traps forward to one. The prototype walk in `canPublishProperties` must find the descriptor
  assignment would reach, reading the standard prototypes as `PropertyWrite`'s docstring states;
  `prototype-boundaries.spec.ts` covers the walk. `deserialize` asks whether `Object.prototype`
  holds a key once per shape, since only built-in code and the global `Temporal` run before records
  are filled. Multi-key order is `PropertyOrder`'s; an own accessor is treated as a slot that keeps
  its place.
- **Write-free readback.** When the first pass wrote nothing to any node, `publishGraph` reads
  nothing back. `WriteFreeReadback` proves that a plain
  object or an array whose publication wrote nothing would read back as accepted, given the same
  observation, and so would a `Map` or `Set` whose publication reports `unchanged`
  (`collection_writeFree_matches`, from `CollectionPlan.unchanged_iff`). A `Date`, buffer, URL,
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
  twice. At the node of `next` that it is, an object of `current` is not read: what capture read
  of it as part of `next` gives each slot, the edge's value, or a node edge's own object, which a
  read returns under `Coherent` (`Spec.Reconcile.capturedKeys`; example `mapOwn` in
  `Spec.Promises`). Those values were not read, so they enter no table, and the object is still
  read once at any other node it is a candidate of, or that capture aligned it with before a later
  walk pinned that node (`Spec.Reconcile.readAt`). There, its preflight reads only the descriptor
  of each slot holding an object, which says whether the slot is fixed: under `Coherent` the object
  passes every other check and requires only that each node one of its fixed slots holds keep the
  object it is (`Spec.KeepsNext.own_admitted`, `own_fixedRequirements`; `ownRequirements`). This
  covers an object and an array with the standard prototype, whose captured elements are all its
  own; another array takes the full preflight. The object is never published there (_Next
  unchanged_), so discovery records no reads of it. The `own-node-walk-read` and
  `own-node-occupant-read` mutants read it at its own node again, and `own-node-walk-shared` and
  `own-node-occupants-shared` let those values enter the table; `own-node-pins-dropped`,
  `own-node-writable-fixed` and `own-node-getter-unpinned` change which slots require an object.
  The bridge's fixed cases `ownNodeInCapture`, `ownNodeAlignedOnce`, `ownNodeInDiscovery`,
  `ownNodeFixedSlot` and `ownNodeWritableSlot` show what the random graphs do not. The
  preflight of any other candidate takes a fixed slot's value from those reads. The first
  publication of the object decides from them whether a key needs a write, without reading it
  again: `publishPre_eq` when the current keys begin in the requested order, so the preflight's
  descriptor gives the attributes, and otherwise, as for an array, `publishSeen_eq`, whose write
  takes the live slot's attributes. A later pass decides each key of a kept object from the value
  the previous pass read back (`publishSeen_eq`), and its preflight reads descriptors again.
  Readback reads every node that is neither pinned nor untouched (_Next unchanged_) again after any
  write, so a decision that a write in between made stale can only block the object
  (`accepts_readsAs`, `acceptsRetry_readsAs`). The runtime supplies only the premise of _Write-free
  readback_: a repeated read with no write in between answers as the first did.
- **Ordinal candidates.** The runtime offers each captured node other than the root the current
  objects aligned with it, at the same key of an object, the same index of an array and the same
  insertion position among `Map` entries (key and value) and `Set` members, inside any candidate of
  any parent, in discovery order; the root gets `current` only, so only `current`'s fixed slots
  make demands there (`keptCandidates`); an object some admitted candidate's fixed slot requires at
  a node comes first there (`candidates.ts` `collect`,
  `Spec.Reconcile.discover`, `orderedCandidates`). A current object is a candidate only at its own
  position; another position gets it only as a pinned fixed image (_Full capture_). The Spec bridge
  checks this on random graphs; `readme-publication-semantics.spec.ts` and
  `shared-identity-bug.spec.ts` cover arrays, `Map` and `Set`. Capture sets `offersOther` for an
  edge of an aligned object without a key or with construction input, and for an edge to a
  captured node whose occupant is an object other than the node's aligned current one. Otherwise
  every edge `collect` would walk meets `OffersAligned`, and a kept subtree is an atom edge it does
  not walk, so `candidates` gives each node its aligned current object alone without walking
  (`candidates_eq_aligned` in `Spec.Discovery`). The `alias-offer-ignored` and
  `entry-offer-ignored` mutants drop each case.

### `produce`

- **Special-value decision.** `SpecialValues` models `chooseSpecial` in `src/graph/provenance.ts`
  and the finalization around it, and assumes these facts, which the runtime must supply:
  `SpecialPolicy.equivalent`
  compares a date's time, a buffer's bytes, a view's shape and its buffer's bytes, a URL's `href`
  and a `URLSearchParams`' text, and finds a Temporal value's copy always equal; a URL's
  `dependencyEquivalent` finds its `searchParams` copy equal exactly when the parameters' text is
  unchanged. A
  copy exists exactly for a value read through a draft and for the buffer or `searchParams` of
  one; a view's copy is over its buffer's copy, and a URL's copy owns its `searchParams`' copy,
  whichever is read first. The sealed pass decides from the values discovery planned to copy
  afresh and from the `searchParams` copy of each URL that the result holds as a copy rather than
  as the original, and discovery reaches every such URL. Given these, `first_eq_sealed` proves that
  discovery's decision of a value it has not yet planned equals the sealed pass's, and
  `resolve_reads_own` that a decision reads no `searchParams` copy the sealed pass forces except
  its own value's. The
  SpecialValues bridge compares `produce` with the model;
  `finalization-propagation-regressions.spec.ts`, `url-ownership.spec.ts` and the
  `hardened-kinds.ts` driver that `standard-prototypes.spec.ts` runs cover more.
- **Finalization reads.** Reading an object again lists the same children, as `SettledChildren`
  and `GetterOrder` assume, and an accessor's result is cached by object and key; identity
  restoration takes an object's children from a finalization walk that visited all of them, and so
  calls no getter. A draft write keeps the descriptor and value it read for its
  key in the first copy, and a draft observation that reads the object itself counts each data slot
  it read there as backed by the object while the call holds a special-value copy. Every copy comes
  from a draft read; one that a getter makes while finalization observes forces the sealed pass,
  which observes every slot again and runs no getter, as `decisions_gated` assumes. A working copy
  records each symbol written to it, and the session counts each draft it makes and never replaces
  one, as `keys_exact` and `reread_exact` assume. `produce-reads.spec.ts` counts finalization's
  reads, and `produce-getter-order.spec.ts` checks the getter order.
- **Selection search.** `immutableSelections` in `src/graph/immutable-selection.ts` must stream
  exactly `CompactImmutable.ranked`, whose masks decode to `GraphPolicy.rankedPlans`
  (`ranked_decode`). No theorem covers its depth-first search, including the edge test, which
  rejects keeping a record when one of its edges leads to an earlier record that is not kept, and
  the `needed` trail, which forbids a fresh copy of a later record that a kept record requires and
  is undone on backtracking. `completion_survives_score_pruning` proves only that the `maximum` and
  `minimum` score bounds keep every completion whose total score is the current `goal`. The
  CompactImmutable bridge checks the whole stream on its 8,195 cases of up to three records.
  `ranked_head` covers the mask `immutableHead` returns, and the search runs only when there is
  none or it cannot be built.
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
  method. `intersection_drafted`, `union_drafted`, `difference_drafted`,
  `symmetricDifference_drafted`, `isSubsetOf_drafted`, `isSupersetOf_drafted` and
  `isDisjointFrom_drafted` prove that a draft holding drafts of its members gives each method's
  result the same identities and answers as one holding the members. The DraftSetMethods bridge
  checks results, and that a result holds this draft's object members as drafts.
- **Copy prototypes.** A copy takes the source's prototype as read once at capture, and
  `Object.setPrototypeOf` on the fresh copy succeeds. Each kind's standard prototype is its live
  constructor's `prototype`, which does not change during a call. A typed array's kind includes the
  element type its brand names. The CopyPrototype bridge checks copies and `serialize` acceptance.

### All operations

- **Per-call tables.** `Types.CallTables` assumes the snapshot walk observes the root first,
  without a lookup, and every other source only after `memoized` misses it, numbering its
  references from 0; that every id serialize assigns is at least
  0; and that deserialize's shape loop reads exactly the count of shapes the control declares, as
  `checkControl` does, so `checkLayout` can bound a shape id by that count. `pending_run_eq` takes
  the buffer getter of a typed array's copy as a function: it answers one object, a fixed-length
  `ArrayBuffer` on `ArrayBuffer.prototype` holding the bytes the source array held when copied
  (`snapshot-binary-observation.spec.ts`).
- **Frozen contents.** `PropertyWrite` takes attributes and extensibility for properties only;
  `CollectionPlan` and the time, bytes and text of dates, buffers, views and URLs have no such
  input, because the built-in methods change them on a frozen value too. The runtime checks a
  frozen built-in's properties, keeps it and updates its contents in place, and a `produce` draft
  changes them in its copy; `standard-prototypes.spec.ts` checks both in each hardened runtime.
- **Intrinsic independence.** The models have no prototypes, so the runtime's own records, tables,
  descriptors, errors and loops must not reach `Object.prototype` or `Array.prototype`.
  [AGENTS.md](../AGENTS.md) states the rule, `src/standard-prototypes.ts` documents the helpers
  that keep it, and `standard-prototypes.spec.ts` checks it under `node --frozen-intrinsics`, under
  SES `lockdown()` and with names planted on both prototypes. An index accessor or read-only index
  on a standard prototype, a built-in method replaced before the module loads, and a replacement,
  at any time, of a built-in method the runtime calls on its own tables are outside this obligation.
- **Built-in contents.** The runtime reads and writes the contents of a `Map`, `Set`, `Date`,
  buffer, view, `URL` or `URLSearchParams` only with the functions captured when the module loads,
  which are assumed to be the built-ins (see _Intrinsic independence_ for one replaced earlier);
  this establishes the built-in `set` and `delete` premise of `Types.MapEntries`, which
  `CollectionPlan`, the serialization `Collection` model and `DraftIteration` share. A `Map` or
  `Set` is walked with the built-in `forEach`, or with a fresh built-in iterator stepped by the
  built-in `next`. `builtin-contents.spec.ts` checks that no override runs, whether a subclass, the
  instance or a change to a standard prototype after the module loads supplies it. The runtime reads
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
  `null`. The runtime walks a view's buffer chain in the `DataView` probe, after the walk for
  `DataView`, unless the prototype already decided the object plain, and a repeated walk must
  answer as the first did.
  `builtin-recognition.spec.ts` covers the probes.
- **Atoms.** The listed constructors are the live globals, which callers do not modify during a
  call; the runtime decides whether an object is an instance of one by its prototype chain, as
  `instanceof` does with the default `Symbol.hasInstance`. A caller that already read an object's
  prototype, such as `snapshot` and `reconcile` capture, passes it on instead of reading it again.
  The Atoms bridge checks the classification, the read count and each function's treatment of atoms.
- **Ingress.** The prototype that ingress reads serves every reader of that object until the call's
  first write: `reconcile` capture records it, with the kind, for discovery and the preflight's
  inherited-accessor check, and discovery does not check that kind again, nor recognize an object
  or an array with the standard prototype at the node of `next` it is, whose kind capture's
  recognition of it as part of `next` decided;
  `produce` uses it for the draft's proxy target and `snapshot` for the copy, a buffer's and a
  view's included. A later read must answer as the first did, so a getter or trap that changes a
  prototype before the first write is unsupported. A view's element type and buffer are fixed when
  the view is made, so one read of the element type serves recognition, the buffer's getter and
  the copy. Readback and a draft's first copy, which follow the recipe, read the prototype
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
  its `publish` writes nothing. A policy reports a write by leaving `note.unchanged` false.
  `write-free-readback.spec.ts`, `url-values.spec.ts` and `temporal.spec.ts` cover these.
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
  compares it with `btoa`. The decoder's tables set the sign bit for a code outside the alphabet,
  `|` adds its disjoint position fields, `encodeInto` writes each ASCII code of the text as one byte
  and, at the first other code, a byte from 0x80 or nothing (leaving a zero), `DataView` reads and
  writes the little-endian words, a `Uint8Array` store keeps a word's low byte, and `transfer` keeps
  the first bytes; `binary-codec.spec.ts` compares the decoder with the `atob` path, errors
  included. A native decoder never yields more bytes than `decodedSize` predicts, which lets the
  exact-count check reject skipped whitespace; `serialization-boundaries.spec.ts` covers this on the
  `atob` path and with native stand-ins.
- **Encoder observations.** The traversal models constrain only the order of entering and
  referencing objects, not application reads such as `length` and getters. The encoder iterates
  collections with the built-in iterators, which have no `return` method to call. The runtime
  classifies each child slot (`slot` in `emit.ts`) only where the stack machine would, recognizes
  each object once (`node`), reads a Map entry, URL parameters or a view's buffer before its child,
  keeps trie nodes fresh per call, and numbers, from a separate first-use table, each layout that
  has no runs, so no two layouts share a provisional id. `serialization.spec.ts` and
  `serialization-collections.spec.ts` cover representative traces.

## Runtime bridges

`OracleMain` is the oracle executable, `reconcile-oracle`. `RuntimeOracle` reads one JSON request
per line, dispatches it by family to the entry function of that family's oracle module, and ends
each response with a record-separator line. A family's oracle module is `Oracle.<Family>Oracle`, and
its entry function is `run`; `PropertyConstructOn` and `PropertyThroughSetter` instead go to
`PropertyWriteOracle` (`runConstructOn`, `runThroughSetter`), and `SpecialDecision` to
`SpecialValuesOracle.runDecision`. Each oracle module's docstring says what its family runs, and
which cases when the oracle generates them; the _Runtime comparison_ column says what the bridge
compares. `Oracle.Protocol` holds what the families share; its docstring states their conventions,
such as a property key crossing as one number (`keyCode`). `Oracle.Enumerate` holds the enumerations
the corpora draw from.

| Oracle family                      | Bridge in `scripts/`                                | Runtime comparison                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| ---------------------------------- | --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `Contract`                         | `scripts/check/bridges/captured.ts`                 | graphs from `reuse-fixtures.json`, which the bridge sends as the request's input: values, aliases, cycles, identity restoration                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `PropertyOrder`                    | `scripts/check/bridges/property-order.ts`           | cursor traces, including cases with strictly less work                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `PropertyWrite`                    | `scripts/check/bridges/property-write.ts`           | single-key outcomes, run through `reconcile` on ordinary objects and forwarding proxies: status, final descriptor, own and inherited setter calls, and no write before a rejection                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `PropertyPlacement`                | `scripts/check/bridges/property-placement.ts`       | pairs of own-key orders with an integer key, names and symbols, and every set of accessors they share: `reconcile` succeeds with the desired order exactly where Lean keeps every accessor, and otherwise writes nothing                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `WriteFreeReadback`                | `scripts/check/bridges/write-free-readback.ts`      | `reconcile` of objects and arrays through a counting proxy: the runtime's readback (`matches`) of `current` before any write answers as Lean's `objectMatches` and `arrayMatches`, the readback is elided and nothing is written exactly where Lean finds publication write-free, and every result equals `next`; where the values are objects, each requested key that `current` holds is read once when nothing is written and twice otherwise                                                                                                                                                                                                                                                                                                                               |
| `CollectionWrites`                 | `scripts/check/bridges/collection-writes.ts`        | `reconcile` of an object holding a `Map` or `Set`, bundled to record each built-in `set`, `add` and `delete` its publication makes and the `unchanged` flag, over every pair of current and next lists of distinct keys from `NaN`, `0`, `'a'` and a function, up to four `Set` members or three `Map` entries valued `0` or `-0`: the writes, in order, and the flag equal `CollectionPlan.publish`'s, every write reaches the kept collection, and it ends holding `next`'s entries                                                                                                                                                                                                                                                                                          |
| `PropertyConstructOn`              | `scripts/check/bridges/property-construct.ts`       | new objects built by `snapshot`, a `produce` rebuild, an object `reconcile` adds and `deserialize`, on a custom prototype or `Object.prototype` holding each kind of descriptor for the key, or on a null prototype, from enumerable and non-enumerable source properties: each holds the own data property with its source's enumerability, no setter on its prototype runs, and `serialize` rejects a non-enumerable one                                                                                                                                                                                                                                                                                                                                                     |
| `PropertyThroughSetter`            | `scripts/check/bridges/property-through-setter.ts`  | assignments of a key the object lacks through a setter on its prototype that defines nothing or the key with each set of attributes, on ordinary objects and `produce` drafts: the draft accepts exactly the definition assignment would make and refuses the others; `standard-prototypes.spec.ts` runs `produce` under `node --frozen-intrinsics`                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `KeyOrder`                         | `scripts/check/bridges/key-order.ts`                | sequences of assignments and deletions on objects with integer keys, names and a symbol: the engine's own keys and `produce`'s result both equal Lean's `ownKeys`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Atoms`                            | `scripts/check/bridges/atoms.ts`                    | real built-in prototype chains behind custom prototypes, with proxies counting reads: the runtime walk matches Lean's answer and read count, and each atom is kept by `snapshot`, `reconcile` and `produce` and rejected by `serialize`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Ingress`                          | `scripts/check/bridges/ingress.ts`                  | recognition with the prototype read shared and with a separate atom split both match Lean's outcome on real prototype chains, for objects without a view brand and for typed arrays over a recognized, a foreign and a raising buffer; an object without the view brand is read once when shared and as often as Lean counts when not, and its custom prototypes the same number of times either way                                                                                                                                                                                                                                                                                                                                                                           |
| `RecognitionPlain`                 | `scripts/check/bridges/recognition-plain.ts`        | built-in recognition and every known-kind check match Lean's result and thrown error on real prototype chains, including views over a recognized, a foreign and a raising buffer; an object without the view brand is read once, and its custom prototypes as the ordered scan of `scripts/check/fixtures/recognition-scan.ts` reads them, less the typed-array probe's repeated `DataView` walk                                                                                                                                                                                                                                                                                                                                                                               |
| `DraftSurface`                     | `scripts/check/bridges/draft-surface.ts`            | draft writes on objects, arrays, maps, typed arrays and dates admitted exactly where the result carries them, and objects and arrays with getters, changed or not, kept exactly where Lean keeps them; a rebuilt object or array holds each returned value as data                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `DraftClass`                       | `scripts/check/bridges/draft-class.ts`              | names on `Map` and `Set` drafts, built-in and subclass instances, owned by the prototype Lean names, and `instanceof` checks that agree; a subclass method runs on a draft and the result keeps the subclass                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `DraftIteration`                   | `scripts/check/bridges/draft-iteration.ts`          | scripts of iterations and writes on a `Map` draft: each walk, the result's entries and whether the result keeps the original agree with Lean                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `SettledChildren`                  | `scripts/check/bridges/settled-children.ts`         | finalization asked whether two objects need a copy, one after the other: each answer, the settled answers, including those settled before their question ended, and the kept child lists equal Lean's                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `SpecialValues`, `SpecialDecision` | `scripts/check/bridges/special-values.ts`           | `chooseSpecial` on all 24 combinations of facts; then `produce`, bundled to record each decision's facts, on 658 scenarios: a date, a standalone `URLSearchParams`, a Temporal value, a buffer with a `Uint8Array`, a `DataView` and a view made over its copy, and a URL with its `searchParams` at either index. Each subset of a buffer and its views is read in index order, and each subset of a URL and its `searchParams` in both orders; each copy is changed, changed and restored, or left; each value is held by up to six slot patterns. Each slot's object (the original, the recipe's copy or a fresh copy) and its buffer or `searchParams` equal Lean's, `current` is unchanged, and the decisions use exactly the eight combinations `facts_reachable` allows |
| `DraftMembers`                     | `scripts/check/bridges/draft-members.ts`            | results of `includes`, `indexOf` and `lastIndexOf` on an array draft agree with Lean                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `DraftSetMethods`                  | `scripts/check/bridges/draft-set-methods.ts`        | the `Set` methods on `Set` drafts, unwritten and with a working copy, over enumerated member and key lists, with each operand form (a `Set` from `current`, a `Set` of drafts, a `Set` draft and a set-like object): the members of each result agree with Lean                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `CopyPrototype`                    | `scripts/check/bridges/copy-prototype.ts`           | copies by `snapshot`, an object `reconcile` adds and a changed `produce` result: every copy keeps its source's prototype, and `serialize` accepts only the standard prototype of the value's own kind, which `deserialize` restores, a typed array given `DataView.prototype` as a `DataView`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `SeededRequirements`               | `scripts/check/bridges/seeded-requirements.ts`      | closure traces, including cases with strictly less work                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `DeferredOrder`                    | `scripts/check/bridges/deferred-order.ts`           | preflights, demanded checkpoints and original error identities                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `FactRenaming`                     | `scripts/check/bridges/fact-renaming.ts`            | histories with queries and live cursor reads                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `CompactImmutable`                 | `scripts/check/bridges/compact-immutable.ts`        | cases and ranked plans, with the construction order of each plan                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `NativeValue`                      | `scripts/check/bridges/native-value.ts`             | fixtures from `native-value-fixtures.json`: whether the preflight keeps the value, immutable reuse, whether a kept value is written (`note.unchanged`), the entries afterwards, and readback                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `OwnedNativeChild`                 | `scripts/check/bridges/owned-native-child.ts`       | production carrier adoption projections: query, ordered entries, owner and child identities; then bulk-versus-sequential parameter publications compared natively, without the oracle                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `Serialization`                    | `scripts/check/bridges/serialization.ts`            | `serialize` documents decoded and re-emitted exactly by Lean; malformed documents rejected by both; non-canonical documents decoded to the same graph by both; literal roots; every accepted document accepted at exactly eight bytes per word of Lean's `accounting` and rejected one byte below, with `Size.lean`'s `tableCharges` admitting every node                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `SerializationCollection`          | `scripts/check/bridges/serialization-collection.ts` | success and failure traces through the production `map` and `set` facets: reads, ordered contents, untouched target on failure                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Spec`                             | `scripts/check/bridges/spec.ts`                     | results, rejections with their reason, `next` read back after every call, and getter counts of every object, `next`'s included, on seeded random graphs and twelve fixed cases, and the `serialize` and `deserialize` round trip against `snapshot`, as _Spec agreement_ describes                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Spec` (phases)                    | `scripts/check/bridges/spec-phases.ts`              | discovery, every pass's decision and whether the call could change `next`, on the `Spec` bridge's random `reconcile` cases, as _Spec phases_ describes                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Spec` (enumeration)               | `scripts/check/bridges/spec-enumeration.ts`         | every case of the universes _Spec enumeration_ lists, about 52,000 `reconcile` cases, 46,000 `produce` recipes and 800 `snapshot` graphs, compared as the outcome and phase bridges compare them                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |

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

The _mutation audit_, `pnpm check mutants`, checks that the `Spec` bridges and the CollectionWrites
bridge detect runtime defects. It works on a copy of the working tree, where it first runs every
bridge it needs on the unmutated sources, which must agree. Then it applies one deliberate defect,
a _mutant_, at a time to the copy's runtime sources and runs the outcome bridge's `reconcile` batch
plainly and through the recording proxies and its `reconcile-hazards` batch at once, and reports the
first of these runs, in that order, that shows a difference. A run that does not end within 30
seconds detects only a mutant marked as one that makes the runtime loop, and a run that crashes, as
by a signal, detects nothing; the audit reports either as unexpected. A mutant that only the
runtime's discovery or decisions show runs the phase bridge's `binary`, `plain` and `hazards`
batches instead. A mutant that only the writes to a kept `Map` or `Set` show runs the
CollectionWrites bridge, once over its fixed corpus. It restores
the copy's sources after each mutant. A mutant the bridge does not detect marks a case the generator
does not produce or a difference the comparison does not see; `scripts/check/mutants.ts` lists the
mutants it expects to go undetected, each with the gap it stands for. `pnpm check mutants <name>...`
runs only the named mutants, and `--seeds` replaces the seeds of each `Spec` bridge run, 1-1500 by
default, with seeds and ranges such as `1-200,10563`; a run given mutant names or `--seeds` records
no pass.

After `pnpm check lean` has built the oracle, you can run one family by hand. The request needs both
fields, `input` empty for a family that reads none; the reply is the oracle's JSON between
record-separator lines, the last carrying `null` or the error.

```sh
echo '{"family":"Atoms","input":""}' | .lake/build/bin/reconcile-oracle
```
