# Finite models and runtime correspondence

This directory holds Lean proofs about the finite algorithms behind `snapshot`,
`reconcile` and `produce`, and the oracles that check the TypeScript runtime against
them. Read it to learn what a proof guarantees, which model covers your code, and how to
add a model. Project-wide commands and budgets are in the
[development workflow](../docs/development.md).

## What the proofs cover

Three kinds of evidence work together, and each has a limit:

- **Proofs** establish properties of finite graph algorithms and of the public contracts
  over a finite heap model. They do not formalize JavaScript.
- **Bridges** run the TypeScript runtime on finite corpora and compare its results with
  Lean oracles. A corpus is evidence for its cases, not a proof for every input.
- **Runtime obligations** are facts the TypeScript code must supply itself, such as the
  order of native reads. Native tests cover them; no proof or axiom does.

A theorem therefore reads: if the runtime supplies these facts, the algorithm produces
this result. The premises matter as much as the conclusion.

## The heap model

[Defs.lean](Defs.lean) and [WF.lean](WF.lean) define finite heaps of atoms and
references: plain objects with ordered fields, arrays with holes, ordered maps and sets,
dates, buffers and views. Functions are opaque atoms. `HeapWF` guarantees that every
reference points into the heap, not that the heap is natively valid.

The model does not derive JavaScript semantics. Capture supplies key order and
normalized atoms, so enumeration order, `SameValue`, `SameValueZero`, byte decoding and
wrapper markers are outside it. So are invalid dates, typed arrays without a valid
constructor tag, non-index array properties and arbitrary exotic objects.

Identity and storage are separate abstract labels; neither describes physical memory.
Two wrappers can share storage, and several views can share one explicit buffer node.
Ownership proofs assume correct labels; they do not discover hidden aliases.

## Runtime obligations

The proofs assume the following. Each is the runtime's responsibility, covered by native
tests rather than Lean.

- **Capture.** Observations follow the documented order, collections are normalized,
  descriptor operations behave natively, and observations stay stable within a phase.
- **Identity and storage.** Fresh allocations are fresh, storage detection is correct,
  and each publication attempt gets a fresh private token.
- **Drafts.** The recipe is isolated from the input, returning the original `current`
  cancels draft changes, and getters are sealed during finalization.
- **Snapshot memo.** A caller-supplied memo is trusted and can return any object,
  including the source. Detachment holds only for a valid memo with native storage
  separation; `graph-capture.spec.ts` keeps a counterexample.
- **Property order.** `DeferredOrder` applies only while key storage is private, stable
  and non-escaping, and desired keys are buffered eagerly.
- **Termination.** The driver's attempt and round bounds assume native operations
  terminate.
- **Pruning.** The runtime establishes `FullCapture` by construction; see
  [Public contracts](#public-contracts).
- **Packaging.** Tree shaking and `Symbol.for` registry identity are packaging
  obligations. `builtin-facets.spec.ts` checks that each operation's facets project the
  same native callbacks.

## Public contracts

These modules state what each operation guarantees, conditional on the obligations above.

- **`reconcile`.** [Publication.lean](Publication.lean) connects local writes to graph
  correspondence. `ReconcileSpec` and [ReconcileSoundness.lean](ReconcileSoundness.lean)
  state that successful object/object publication retains the exact current root
  (`reconcile_root_retained`), preserves sharing and cycles, and never merges distinct
  nodes (`reconcile_no_collapse`). A retained plain object keeps its current prototype.
  Failure is an error and does not promise rollback.
- **Identical-occupant pruning.** [PrunedReconcile.lean](PrunedReconcile.lean) adds pinned
  nodes to the reconcile witness: current objects found at the same own-property slot of
  the aligned current node, kept as fixed images. `PrunedReconcileSpec` certifies the
  captured part as `ReconcileSpec` does, and `pruned_untouched` shows that pinned objects
  stay unchanged. Under `FullCapture`, the pruned result equals publishing the full `next`
  graph (`pruned_full_equivalence`, `pruned_full_soundness`). Its premises: the pinned
  closure sits in the current heap at its occupants, is closed and separate from captured
  nodes, has observed buffer extents and receives no write. The runtime meets them by
  walking a subtree before pinning it, refusing to pin when the walk meets either root,
  excluding walked objects from all other domains, and pinning to itself any captured node
  the walk met. Only plain-object and array slots pin, and captured views never pin their
  buffers (`capturedBuffers`).
- **`snapshot`.** `SnapshotSpec` and [SnapshotSoundness.lean](SnapshotSoundness.lean)
  state graph correspondence and that each copy is fresh relative to its own source.
  `DetachedSnapshotSpec` adds separation from every source node (`SnapshotMemoDisjoint`).
  [SnapshotProjection.lean](SnapshotProjection.lean),
  [SnapshotStream.lean](SnapshotStream.lean) and [SnapshotOwner.lean](SnapshotOwner.lean)
  cover the state projection, streamed map entries and owned shells.
- **`produce`.** [ProduceSpec.lean](ProduceSpec.lean) and
  [ProduceSoundness.lean](ProduceSoundness.lean) describe lazy children, explicit
  deletion, ordinary `undefined` assignment, copy-on-write and finalization.
  `DraftExecSpec` describes the returned graph without a later `reconcile`.
  [ProduceFinalizeCoherence.lean](ProduceFinalizeCoherence.lean) shows that shared draft
  references finalize to one image.
- **Caller composition.** The `RecipePublication*` modules describe
  `reconcile(current, produce(current, recipe))`, combining both stages'
  certificates in `RecipePublicationSpecCore`. Retaining the current root is a claim of
  this composition, not of `produce` alone.

[ContractTest.lean](ContractTest.lean) holds kernel-checked examples, which show that a
specification's premises can hold, and counterexamples, which show why a premise is
needed. Examples include an explicit-replacement draft, shared and moved draft paths, a
detached snapshot, and a spread root over a child that points back to it, which the
runtime must capture rather than pin. Counterexamples include a snapshot that swaps two
equal source nodes under the weaker specification, and a witness that keeps an object
inside a pinned closure.

## Kernel algorithms

Each entry names the runtime code it covers. A model keeps a reference algorithm
separate from the optimized TypeScript, and a bridge compares the two.

- **Selection stream** (`graph/selection.ts` and its helpers).
  [GraphPolicy.lean](GraphPolicy.lean) defines domains, storage separation, identity
  requirements, feasible plans and the ranked stream (`feasiblePlans_exact`); ranking
  keeps domain order within equal scores. Supporting modules prove the state the selector
  maintains: active demands ([ActiveDemands.lean](ActiveDemands.lean)), the future-demand
  guard ([ForwardDemands.lean](ForwardDemands.lean), `search_eq`, `ranked_eq`),
  backtracking ([SelectionUnwind.lean](SelectionUnwind.lean), `unassign_assign`,
  `unwind_assignments`), forced groups
  ([FiniteReachability.lean](FiniteReachability.lean), [ForcedGroups.lean](ForcedGroups.lean),
  [ForcedGroupsReference.lean](ForcedGroupsReference.lean)),
  unsupported-choice removal ([SupportedChoices.lean](SupportedChoices.lean)), and the
  demand summary, checked membership and claim encoding
  ([IncomingConsensus.lean](IncomingConsensus.lean), [DenseChecks.lean](DenseChecks.lean),
  [Claims.lean](Claims.lean)).
- **Immutable selection** (`graph/immutable-selection.ts`, `restore-identities.ts`).
  [CompactImmutable.lean](CompactImmutable.lean) encodes choices as retained bits and
  relates them to the original domains and ranked streams (`feasible_iff`,
  `ranked_decode`, `selected_decode`). [CompactOwners.lean](CompactOwners.lean) bounds the
  score by distinct owners. [Immutable.lean](Immutable.lean) connects selected plans to
  publication (`selected_published`, `selected_storage_distinct`), with
  [ImmutableLabels.lean](ImmutableLabels.lean) and [ReuseClosure.lean](ReuseClosure.lean).
  The compact planner does not replace the general selector.
- **Requirement closure** (`graph/requirements.ts`). [Requirements.lean](Requirements.lean)
  specifies the least closure; [RequirementAdmission.lean](RequirementAdmission.lean) and
  [RequirementPropagation.lean](RequirementPropagation.lean) cover admission, propagation
  and insertion order. [SeededRequirements.lean](SeededRequirements.lean) proves that
  dropping implications into seed facts keeps the closure and its trace, which
  `compileImmutable` relies on. [ClosureHistory.lean](ClosureHistory.lean) and
  [FactRenaming.lean](FactRenaming.lean) prove that relabeling objects as numbers, as the
  bridges do, preserves every closure, query and stream.
- **Construction order** (`graph/construction.ts`). [Construction.lean](Construction.lean)
  defines the schedule; [ConstructionScheduler.lean](ConstructionScheduler.lean) composes
  the other `Construction*` modules into `scheduled_eq_schedule` and
  `countedSchedule_eq_schedule`, including rejection.
- **Execution and retries** (`graph/execution.ts`, `graph/driver.ts`).
  [Execution.lean](Execution.lean) shows that a stale receipt cannot certify a changed
  binding and that finishing requires current readback for the whole domain.
  [Driver.lean](Driver.lean) models attempts and preferred replay, and separates earlier
  observations from fresh certification of the result.
- **Special values** (`graph/provenance.ts`). [Provenance.lean](Provenance.lean) models
  how a special value's identity follows from its provenance and equivalence facts.
- **Property order** (`types/shared/property-publication.ts`).
  [PropertyOrder.lean](PropertyOrder.lean) keeps cursor decisions while bounding work
  (`step_equivalence`, `stream_equivalence`). [DeferredOrder.lean](DeferredOrder.lean)
  proves that private cursor work can wait until needed (`catchUp_eq`, `execute_eq`); it
  does not allow sharing observations across phases.
- **Recognition** (`types/registry.ts`). [Types/Recognition.lean](Types/Recognition.lean)
  models first-match recognition; [Types/Cell.lean](Types/Cell.lean) is an inhabited
  type encoding.

## Runtime bridges

`pnpm check:lean` starts one oracle process, [OracleMain.lean](OracleMain.lean).
[RuntimeOracle.lean](RuntimeOracle.lean) reads one JSON request per line, dispatches it
by family to an oracle module's `run` function, and ends each response with a
record-separator line. [check-lean.ts](../scripts/check-lean.ts) first confirms that bad
requests are rejected, then runs the bridges.

| Oracle family        | Bridge in `scripts/`                   | Runtime comparison                                                                                  |
| -------------------- | -------------------------------------- | --------------------------------------------------------------------------------------------------- |
| `Contract`           | `lean-captured-bridge.ts`              | 10 graphs from `reuse-fixtures.json`: values, aliases, cycles, wrappers, identity restoration       |
| `Policy`             | `lean-policy-bridge.ts`                | 1,557 selection streams, 16 forward-pruned comparisons, closure, construction, execution and driver |
| `Pruned`             | `lean-pruned-bridge.ts`                | 10 graphs from `pruned-fixtures.json`: spread roots, aliases into replaced positions, cycles        |
| `PropertyOrder`      | `check-property-order-runtime.ts`      | 62,800 cursor traces, 18,672 with strictly less work                                                |
| `SeededRequirements` | `check-seeded-requirements-runtime.ts` | 40,966 closure traces, 36,951 with strictly less work                                               |
| `DeferredOrder`      | `check-deferred-order-runtime.ts`      | 566 preflights, 215 demanded checkpoints, 3 original error identities                               |
| `FactRenaming`       | `check-fact-renaming-runtime.ts`       | 41,069 histories with queries and live cursor reads                                                 |
| `CompactImmutable`   | `check-compact-immutable-runtime.ts`   | 40,963 cases and 46,083 ranked plans, including construction rejection                              |
| `SelectionUnwind`    | `check-selection-unwind-runtime.ts`    | 180 admitted prefixes, 1,440 assignment and undo transitions                                        |

The `check-*-runtime.ts` bridges run from `lean-policy-bridge.ts`. Read the table with
these limits:

- Corpus sizes bound the test enumeration, not production graphs.
- "Strictly less work" counts cases where the optimized algorithm does less work than the
  reference, which shows that the optimization is not vacuous.
- The `SelectionUnwind` bridge executes reference transitions with the runtime's
  demand updates, not a production code path.
- The `DeferredOrder` bridge runs a copy of `property-publication.ts` instrumented by exact
  source text, so editing those lines breaks it.
- The `Contract` bridge does not certify every `DraftExecSpec` premise.

After `pnpm check:lean` has built the oracle, you can run one family by hand. The request
needs all three fields. The output is a record-separator line, the oracle's JSON, then a
record-separator line with `null` or the error.

```sh
echo '{"family":"Pruned","args":["lean/pruned-fixtures.json"],"input":""}' \
  | .lake/build/bin/reconcile-oracle
```

## Adding or changing a model

A finite algorithm changes in Lean before it changes in TypeScript. On the Lean side:

1. **Keep existing statements.** Do not weaken or change a retained theorem's statement
   or premises; add a new theorem. A rename that keeps the statement needs no alias.
2. **Show the claim is inhabited.** Add an example whose premises hold and, where a
   premise matters, a counterexample without it, usually in `ContractTest`.
3. **Name the runtime obligations.** State which premises the runtime must establish and
   how, as `FullCapture` does, and list them under
   [Runtime obligations](#runtime-obligations).
4. **Register every file** in `roots` in [lakefile.toml](../lakefile.toml). The axiom audit
   rejects unlisted files.
5. **Add an oracle and a bridge.** Give the oracle a namespaced `run` function, add its
   family to `RuntimeOracle.lean`, and call it from a bridge run by `check-lean.ts` or
   `lean-policy-bridge.ts`. Keep hand-written fixtures as JSON in `lean/`. Prefer
   comparing production code, and say so when a bridge runs a reference transition.
6. **Document it** in this file: the model, a bridge-table row, and any changed counts.

## Checks and failures

Run the complete gate from the repository root:

```sh
pnpm check:lean
```

It builds every module and the oracle with `lake build --wfail`, so a warning fails it,
then audits axioms and runs every bridge within the 295-second budget. The system C
compiler builds the oracle without optimization to save time. While editing, use
`lake build <Module>` and `lake env lean lean/<Module>.lean`; `python3
lean/check-axioms.py` audits a built tree without running bridges. Bridges run only
through `pnpm check:lean`.

[check-axioms.py](check-axioms.py) rejects missing or unlisted Lean files and follows
every owned declaration, including private and generated ones, through its type and
body. Only `propext`, `Classical.choice` and `Quot.sound` are allowed, so a `sorry` fails
the audit. A passing audit says nothing about whether a theorem is useful, inhabited or
matched by the runtime.

When the gate fails:

- **Build or audit.** Fix the warning, register the file or remove the axiom. Never add
  an axiom.
- **Bridge mismatch.** Decide which side changed. Fix an accidental runtime change in the
  runtime. For a deliberate contract change, change the model first, then the corpus and
  the bridge. Never edit expected oracle output to match the runtime.
- **Instrumentation assertion.** A bridge that rewrites source text names the replacement
  that failed. Update its search text and keep the instrumentation at the same points.
- **Field-name mismatch.** Oracle decoders keep their field names; the bridge translates,
  as `lean-policy-bridge.ts` does for the runtime's `tag` field.

## Why some models remain

Reference models stay beside optimized code: `GraphPolicy` defines the ranked stream the
selector must produce, and `Construction` the schedule the scheduler refines.
`SelectionUnwind` stays because its claims apply to ordinary backtracking. The models of
two reverted optimizations, `ArrayBound*` and `Retention*`, are not in the repository; the
[development workflow](../docs/development.md#decisions) records why.
