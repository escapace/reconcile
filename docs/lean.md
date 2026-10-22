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
defines the ranked selection stream, `Construction` the construction schedule, and
`SelectionUnwind` ordinary backtracking.

## The heap model

`Heap/Defs.lean` defines finite heaps of atoms and references: plain objects with ordered fields,
arrays with holes, ordered maps and sets, dates, buffers and views. Functions are opaque atoms, and
so are objects whose state the library cannot copy, such as a `RegExp`, `Error` or `WeakMap`;
`Types.Atoms` proves how the runtime classifies them. `Heap/Defs.lean` also defines `HeapWF`, which
guarantees that every reference points into the heap, not that the heap is natively valid.
`Heap/WF.lean` defines edges, reachability and `SurfaceEq`, equality of two values at every finite
depth, by which the specifications compare results.

The model does not derive JavaScript semantics. Capture supplies key order and normalized atoms, so
enumeration order, `SameValue`, `SameValueZero`, byte decoding and wrapper markers are outside it.
So are invalid dates, typed arrays without a valid constructor tag, non-index array properties and
arbitrary exotic objects.

Identity and storage are separate abstract labels; neither describes physical memory. Two wrappers
can share storage, and several views can share one explicit buffer node. Ownership proofs assume
correct labels; they do not discover hidden aliases.

## Adding or changing a model

[AGENTS.md](../AGENTS.md) sets the order of work and what must be kept. On the Lean side:

1. **Renames.** A rename that keeps a theorem's statement needs no alias.
2. **Examples.** Put an example whose premises hold, and a counterexample for each premise that
   matters, in `ContractTest` or beside the model.
3. **Name the runtime obligations.** State which premises the runtime must establish and how, as
   `FullCapture` does, and list them under [Runtime obligations](#runtime-obligations).
4. **Place and register every file.** A model goes in its area's directory under `lean/`:
   `Heap/`, `Snapshot/`, `Reconcile/`, `Property/`, `Graph/`, `Produce/`, `RecipePublication/`,
   `Types/` or `Serialization/`; its oracle goes in `Oracle/`. List the module in `roots` in
   `lakefile.toml`. The axiom audit rejects unlisted files and roots without a file, so change
   both together.
5. **Add an oracle and a bridge.** Give the oracle a namespaced `run` function, add its family to
   `Oracle/RuntimeOracle.lean`, and call it from a bridge run by `check-lean.ts` or
   `lean-policy-bridge.ts`. Keep hand-written fixtures as JSON in `lean/fixtures/`. Prefer comparing
   production code, and say so when a bridge runs a reference transition. Renaming an oracle
   namespace or a fixture file breaks the bridge that uses it.
6. **Document it** in this guide: the correspondence row, its obligations and a bridge-table row.

## Running the gate

`pnpm check:lean` (the _gate_) runs `lake build --wfail`, so a warning fails it, then audits axioms
and runs every bridge against one oracle process. Its budget and receipt are in
[Time budget](development.md#time-budget).

Extra arguments go to Node. `pnpm check:lean --harmony-temporal` adds Node's native Temporal values
to the `NativeValue` bridge, which otherwise skips them and says so. For the commands to use while
editing, see [Checks and time budget](development.md#checks-and-time-budget). The bridge scripts
have no standalone entry; to query one oracle, see [Runtime bridges](#runtime-bridges).

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
[runtime obligations](#runtime-obligations) the correspondence relies on.

### Heap model and public contracts

| Module(s)      | Key theorems                                                               | Runtime                                                                                                                       | Bridge                                  | Obligations                   |
| -------------- | -------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------- | --------------------------------------- | ----------------------------- |
| `Defs`, `WF`   | `HeapWF` (definition)                                                      | captured graphs: `src/publication/capture.ts` (`reconcile`), the walk in `src/snapshot.ts`, `src/finalization.ts` (`produce`) | imported by Contract, Pruned and Policy | Capture                       |
| `Publication`  | `publishRecords_published`, `checkPublication_sound`                       | `src/publication/*`                                                                                                           | imported by Contract, Pruned and Policy | Capture, Identity and storage |
| `ContractTest` | `swapped_spec`, `fresh_spec`, `spread_full_stale`, `alias_no_full_capture` | none: examples and counterexamples                                                                                            | proof-only                              | none                          |

`ContractTest` holds examples, which show that a specification's premises can hold, and
counterexamples, which show why a premise is needed. For example, a snapshot can satisfy
`SnapshotSpec` while swapping two equal source nodes (`swapped_spec`), which `DetachedSnapshotSpec`
excludes, and a shared child that points back at a spread root must be captured rather than pinned
(`spread_full_stale`).

### `snapshot`

| Module(s)                           | Key theorems                                                                                      | Runtime                                                              | Bridge     | Obligations                                  |
| ----------------------------------- | ------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------- | ---------- | -------------------------------------------- |
| `SnapshotSpec`, `SnapshotSoundness` | `snapshot_detachment`, `snapshot_sharing`, `snapshot_distinctness`, `snapshot_cycle_preservation` | `src/snapshot.ts` `snapshot`                                         | proof-only | Capture, Identity and storage, Snapshot memo |
| `SnapshotProjection`                | `erase_finishing`, `public_result_preserved`                                                      | the snapshot adapters' finishing step (`src/snapshot.ts`)            | proof-only | Built-in snapshot writer                     |
| `SnapshotStream`                    | `run_eq_pairs`, `pending_key_no_write`, `interleaved_agreement`                                   | the pending-key Map writer (`src/types/map.ts`)                      | proof-only | Built-in snapshot writer                     |
| `SnapshotOwner`                     | `memo_edge_agreement`, `interleaved_memo_agreement`                                               | writer state owned by references (`src/snapshot.ts`, `src/types.ts`) | proof-only | Built-in snapshot writer                     |

`SnapshotSpec` states graph correspondence and that each copy is fresh relative to its own source;
`DetachedSnapshotSpec` adds separation from every source node (`SnapshotMemoDisjoint`).
`SnapshotProjection` lets a metadata-only finishing step be omitted, and `SnapshotStream` lets a Map
writer wait for the value edge before writing a pair. `memo_edge_agreement` shows that a canonical
reference can replace a separate memo when both publish the same initialized target. The runtime
uses this only for the exact built-in registry when the caller omits the memo; custom registries
and caller-supplied memos keep their `WeakMap` reads and writes and callback order.

### `reconcile`

| Module(s)                             | Key theorems                                                                                                                                                                                                                                                                                                                                           | Runtime                                                                                                                                                                                                                                                                                       | Bridge                                                    | Obligations                   |
| ------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- | ----------------------------- |
| `ReconcileSpec`, `ReconcileSoundness` | `reconcile_root_retained`, `reconcile_no_collapse`, `reconcile_sharing`, `reconcile_cycle_preservation`                                                                                                                                                                                                                                                | `src/reconcile.ts` `reconcile`                                                                                                                                                                                                                                                                | imported by Pruned                                        | Capture, Identity and storage |
| `PrunedReconcile`                     | `pruned_untouched`, `pruned_full_soundness`, `pruned_full_equivalence` (definition)                                                                                                                                                                                                                                                                    | `src/reconcile.ts`; pinning in `src/publication/capture.ts`, `candidates.ts`                                                                                                                                                                                                                  | Pruned                                                    | Full capture                  |
| `PropertyOrder`                       | `step_equivalence`, `stream_equivalence`, `aligned_mem`                                                                                                                                                                                                                                                                                                | `src/types/shared/property-publication.ts` `PropertyOrder`; aligned publication in `src/types/object.ts`                                                                                                                                                                                      | PropertyOrder                                             | Capture                       |
| `DeferredOrder`                       | `catchUp_eq`, `execute_eq`                                                                                                                                                                                                                                                                                                                             | `src/types/shared/property-publication.ts`                                                                                                                                                                                                                                                    | DeferredOrder (instrumented copy)                         | Property order                |
| `PropertyWrite`                       | `reconcileKey_no_inherited_setter`, `publish_missing`, `construct_data`, `constructFrom_data`, `constructOn_fresh`, `constructOn_eq_construct`, `constructFromOn_fresh`, `draftThroughSetter_eq`, `draftThroughSetter_refused`, `draftThroughSetter_tamed`, `publish_accessor`, `reconcileKey_rejected`, `reconcileKey_sound`, `reconcileKey_complete` | `src/types/shared/property-publication.ts` `canPublishProperties`, `publishProperty`; `src/types/shared/draft-properties.ts` `set`, `defineProperty`; `setOwnProperty` (`src/set-own-property.ts`); `define` in `src/serialization/common.ts`; the fresh-shell write in `src/types/object.ts` | PropertyWrite, PropertyConstructOn, PropertyThroughSetter | Property writes               |
| `PropertyPlacement`                   | `matched_maximal`, `place_matched`, `feasible_iff`, `reference_sectors`, `reference_keeps_fixed_iff`                                                                                                                                                                                                                                                   | `src/types/shared/property-publication.ts` `canPublishProperties` with `PropertyOrder`                                                                                                                                                                                                        | PropertyPlacement                                         | Key order                     |
| `WriteFreeReadback`                   | `object_writeFree_matches`, `array_writeFree_matches`, `unchanged_publish`, `publishKnown_eq`                                                                                                                                                                                                                                                          | readback elision and `PreflightFacts` in `src/publication/publication-engine.ts`; `publish` in `src/types/object.ts` and `src/types/array.ts`; `publishKnown`                                                                                                                                 | WriteFreeReadback                                         | Write-free readback           |

Successful object/object publication retains the exact current root (`reconcile_root_retained`),
preserves sharing and cycles, and never merges distinct nodes (`reconcile_no_collapse`). A retained
plain object keeps its current prototype. Failure is an error and does not promise rollback.
`src/__tests__/reconcile-semantics.spec.ts` tests the contract case by case.

`PrunedReconcile` adds pinned nodes to the _witness_ (`ReconcileWitness`, whose `image` maps each
captured `next` node to its result node): current objects found at the same own-property slot of the
aligned current node, kept as fixed images that stay unchanged (`pruned_untouched`). Under
`FullCapture`, the pruned result equals publishing the full `next` graph: the definition
`pruned_full_equivalence` builds that `ReconcileSpec`, and `pruned_full_soundness` concludes from
it.

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
outcome exactly (`reconcileKey_sound`, `reconcileKey_complete`).

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

### Selection kernel

The selector, its supporting state and the execution driver serve `reconcile` publication
(`publishGraph`); `Provenance` serves `produce` finalization.

| Module(s)                                                     | Key theorems                                                                            | Runtime                                                     | Bridge                                  | Obligations                                           |
| ------------------------------------------------------------- | --------------------------------------------------------------------------------------- | ----------------------------------------------------------- | --------------------------------------- | ----------------------------------------------------- |
| `GraphPolicy`                                                 | `feasiblePlans_exact`, `rankedPlans_exact`, `rankedPreferred_head`                      | `src/graph/selection.ts` `selections`; reference stream     | Policy                                  | Preferred attempts                                    |
| `ActiveDemands`, `ForwardDemands`                             | `maintained_iff_scan`, `search_eq`, `ranked_eq`                                         | `src/graph/selection.ts`                                    | Policy                                  | none                                                  |
| `SelectionUnwind`                                             | `unassign_assign`, `unwind_assignments`                                                 | backtracking in `src/graph/selection.ts`                    | SelectionUnwind (reference transitions) | none                                                  |
| `FiniteReachability`, `ForcedGroups`, `ForcedGroupsReference` | `closure_iff`, `component_forced`, `reference_reaches`                                  | `src/graph/forced-groups.ts`                                | Policy                                  | none                                                  |
| `SupportedChoices`                                            | `completed_exact`, `survivors_fixed`                                                    | `src/graph/supported-choices.ts` `unsupportedChoices`       | Policy                                  | none                                                  |
| `IncomingConsensus`                                           | `foldl_eq`, `summarize_accepts`                                                         | `src/graph/incoming-consensus.ts`, `src/graph/execution.ts` | Policy                                  | none                                                  |
| `DenseChecks`                                                 | `complete_iff_count`, `mark_valid`                                                      | `src/graph/checked.ts` `CheckedNodes`                       | proof-only                              | none                                                  |
| `Claims`                                                      | `has_iff`, `no_alias`                                                                   | `src/graph/claims.ts`                                       | Policy                                  | none                                                  |
| `Execution`, `Driver`                                         | `stale_plan_ignored`, `finish_requires_complete_readback`, `run_certified`, `run_fresh` | `src/graph/execution.ts`, `src/graph/driver.ts` `execute`   | Policy                                  | Identity and storage, Preferred attempts, Termination |
| `Provenance`                                                  | `base_iff`, `source_iff`, `choose_currentBacked`, `untracked_source_iff`                | `src/graph/provenance.ts` `chooseSpecial`                   | Policy                                  | Capture                                               |

`GraphPolicy` defines domains, storage separation, identity requirements,
feasible plans and the ranked stream, which keeps domain order within equal scores.
`rankedPreferred_head` concerns the plan that takes each domain's first choice. When that plan is
feasible, each first choice is retained or its domain offers no retained choice, and the plan's
score marks no domain as preferred, the plan heads the ranked stream, so the driver attempts it
before searching. The other modules prove the state the selector maintains. `Execution` shows that
a stale receipt cannot certify a changed binding and that finishing requires current readback for
the whole domain; `Driver` separates earlier observations from fresh certification of the result.

### `produce`

| Module(s)                                                                                                                                                                                                                | Key theorems                                                                                                                | Runtime                                                                                                                                                            | Bridge                                                                          | Obligations                |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------- | -------------------------- |
| `ProduceDefs`, `ProduceSpec`, `ProduceSoundness`                                                                                                                                                                         | `draft_lazy_child_creation`, `draft_copy_on_write`, `draft_delete_is_explicit`, `draft_finalize_produces_next_graph`        | `src/produce.ts`, `src/draft-session.ts`, `src/finalization.ts`                                                                                                    | proof-only                                                                      | Drafts, Capture            |
| `SettledChildren`                                                                                                                                                                                                        | `check_step`, `needs_settled`, `needs_unchanged`, `settled_reach_recorded`, `recorded_getD`                                 | `checkDescendantsForMaterialization` in `src/finalization.ts`; `compileImmutable` in `src/restore-identities.ts`                                                   | SettledChildren                                                                 | Finalization reads         |
| `ProduceFinalizeCoherence`, `ProduceFinalizeCoherenceSoundness`                                                                                                                                                          | `draft_shared_finalized_image_coherence`, `draft_moved_reference_final_location_correctness`                                | `src/finalization.ts`                                                                                                                                              | proof-only                                                                      | Drafts                     |
| `ReuseClosure`, `Immutable`, `ImmutableLabels`                                                                                                                                                                           | `reuseSurvivors_greatest`, `selected_published`, `selected_storage_distinct`, `fresh_below_native`                          | `src/restore-identities.ts`                                                                                                                                        | Contract (`Immutable`); `ImmutableLabels` proof-only                            | Identity and storage       |
| `FoldedLeaves`                                                                                                                                                                                                           | `feasible_iff`, `dead_iff`, `record_iff`, `score_extend`                                                                    | folding in `compileImmutable`, `src/restore-identities.ts`                                                                                                         | proof-only                                                                      | Folded leaves              |
| `ImmutableAssembly`                                                                                                                                                                                                      | `append_keeps_target`, `completion_agreement`                                                                               | record assembly in `src/restore-identities.ts`                                                                                                                     | proof-only                                                                      | Immutable assembly         |
| `CompactImmutable`, `CompactOwners`                                                                                                                                                                                      | `feasible_iff`, `ranked_decode`, `ranked_head`, `separated_of_distinct`                                                     | `src/graph/immutable-selection.ts` `immutableSelections`                                                                                                           | CompactImmutable                                                                | Preferred attempts         |
| `KeyOrder`                                                                                                                                                                                                               | `build_nodup`, `ownKeys_ownKeys`, `rebuild_preserves`, `produce_key_order`                                                  | `preparePropertyCopy` in `src/types/shared/draft-properties.ts`; finalization                                                                                      | KeyOrder                                                                        | Key order                  |
| `DraftSurface`                                                                                                                                                                                                           | `admits_iff_represented`, `refused`, `keeps_iff`, `handle_rebuilds`                                                         | `admits` in `src/types/shared/draft-properties.ts`, non-extensible collection drafts and native copies in `src/draft-session.ts`, `reuse` in `src/types/object.ts` | DraftSurface                                                                    | Draft surface              |
| `DraftClass`                                                                                                                                                                                                             | `draft_instanceOf`, `lookup_other`, `lookup_method`                                                                         | `draftCollectionBase` and `adoptDraftClass` in `src/types/shared/draft-collection.ts`                                                                              | DraftClass                                                                      | Draft class                |
| `DraftIteration`                                                                                                                                                                                                         | `iterate_entries`, `iterate_kept`, `write_after_iterate`, `kept_untouched`, `drafted_nodup`                                 | `draftWalk` and `draftCollectionBase` in `src/types/shared/draft-collection.ts`                                                                                    | DraftIteration                                                                  | Draft iteration            |
| `DraftRead`                                                                                                                                                                                                              | `read_copied`, `read_not_wrapper`                                                                                           | `get`, `read` and `contains` of `PropertyDraftState` in `src/types/shared/draft-properties.ts`                                                                     | DraftRead                                                                       | Draft reads                |
| `DraftMembers`                                                                                                                                                                                                           | `includes_drafted`, `indexOf_drafted`, `lastIndexOf_drafted`, `includes_form`, `indexOf_form`                               | `memberIdentity` and `arraySearches` in `src/types/shared/draft-members.ts`                                                                                        | DraftMembers                                                                    | Draft members              |
| `DraftSetMethods`                                                                                                                                                                                                        | `mem_union`, `mem_intersection`, `mem_difference`, `mem_symmetricDifference`, `isDisjointFrom_walk`, `intersection_drafted` | `setMethods` in `src/types/set.ts`                                                                                                                                 | DraftSetMethods                                                                 | Draft members, Set methods |
| `CopyPrototype`                                                                                                                                                                                                          | `adopt_eq`, `copy_keeps`, `serializes_iff_restored`                                                                         | `adoptPrototype` in `src/types/shared/prototype.ts`; array, `Map`, `Set`, `Date`, `DataView`, URL and Temporal construction; `serialize` recognition               | CopyPrototype                                                                   | Copy prototypes            |
| `Requirements`, `RequirementAdmission`, `RequirementPropagation`                                                                                                                                                         | `close_least`, `admit_nodup`, `completed_insertion_order`                                                                   | `src/graph/requirements.ts` `closeRequirements`                                                                                                                    | Policy (`Requirements`); SeededRequirements (all three)                         | none                       |
| `SeededRequirements`                                                                                                                                                                                                     | `close_eq`, `run_eq`, `scans_le`                                                                                            | `compileImmutable` in `src/restore-identities.ts`, `src/finalization.ts`                                                                                           | SeededRequirements                                                              | none                       |
| `ClosureHistory`, `FactRenaming`                                                                                                                                                                                         | `expandUnfolded_eq`, `execute_eq`, `observations_eq`                                                                        | `src/graph/requirements.ts` `RequirementClosure`                                                                                                                   | FactRenaming                                                                    | none                       |
| `Construction`                                                                                                                                                                                                           | `schedule_safe`, `schedule_complete`, `schedule_shells_only`                                                                | `src/graph/construction.ts` `constructionOrder`                                                                                                                    | Policy, CompactImmutable                                                        | none                       |
| `ConstructionFrontier`, `ConstructionIncidence`, `ConstructionAdmission`, `ConstructionCompletion`, `ConstructionSetup`, `ConstructionLevels`, `ConstructionBuckets`, `ConstructionRankUpdates`, `ConstructionScheduler` | `scheduled_eq_schedule`, `countedSchedule_eq_schedule`                                                                      | `src/graph/construction.ts`, `src/graph/construction-facts.ts`                                                                                                     | proof-only; Policy and CompactImmutable compare the runtime with `Construction` | none                       |

`ProduceSpec` and `ProduceSoundness` describe lazy children, explicit deletion, ordinary `undefined`
assignment, copy-on-write and finalization. `DraftExecSpec` describes the returned graph without a
later `reconcile`. `ProduceFinalizeCoherence` shows that shared draft references finalize to one
image.

Immutable restoration chooses which current objects an immutable result reuses. `CompactImmutable`
encodes choices as retained bits and relates them to the ranked streams; `ranked_head` proves that
an admissible, separated and closed eligibility mask is the first ranked mask. The compact planner
does not replace the general selector. `ImmutableAssembly` shows that filling one private record
keeps its reserved target and equals allocating a replacement.

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

`FoldedLeaves` lets identity restoration fold the objects inside the unchanged subtrees the result
keeps whole: they are registered after every other node and always kept, so folding them away and
moving their edges to registered nodes onto a fixed node that reaches them leaves the selector the
same choices. When no folded object's storage equals that of a node the result could keep, the
folded problem's masks are exactly the original's with every folded object kept (`feasible_iff`),
scored `m` lower (`score_extend`). The two problems agree on whether some fixed node is unavailable
(`dead_iff`) and otherwise on each record (`record_iff`); a counterexample shows why a clashing
storage must reject the folded problem.

`Requirements` specifies the least closure. `SeededRequirements` proves that dropping implications
into seed facts keeps the closure and its trace, which `compileImmutable` relies on. `FactRenaming`
proves that relabeling objects as numbers, as the bridges do, preserves every closure, query and
stream, and `expandUnfolded_eq` equates the runtime's admit-then-propagate `require` with expanding
from the fact. `ConstructionScheduler` composes the other `Construction*` modules into
`countedSchedule_eq_schedule`, including rejection. Construction order also runs during
`reconcile` publication, in `src/publication/publication-engine.ts`.

### Caller composition

| Module(s)                                                                                                    | Key theorems                                                                                                                                           | Runtime                                                    | Bridge     | Obligations     |
| ------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------- | ---------- | --------------- |
| `RecipePublicationSpec`, `RecipePublicationSoundness`, `RecipePublicationOrder`, `RecipePublicationLocality` | `recipe_publication_root_retained`, `recipe_publication_no_collapse`, `recipe_publication_map_order`, `recipe_publication_untouched_path_preservation` | caller code `reconcile(current, produce(current, recipe))` | proof-only | Drafts, Capture |

These modules combine both stages' certificates in `RecipePublicationSpecCore`. Retaining the
current root is a claim of this composition, not of `produce` alone.
`src/__tests__/recipe-publication.spec.ts` exercises the composition through the public API.

### Native type facets

| Module(s)                                                  | Key theorems                                                                              | Runtime                                                                                                                                             | Bridge                                                                       | Obligations                 |
| ---------------------------------------------------------- | ----------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------- | --------------------------- |
| `Types.Recognition`                                        | `builtinTrace_eq_scanTrace`, `temporalTrace_eq_scanTrace`, `builtinDispatch_eq_scanTrace` | `src/types/builtins.ts`, `src/types/registry.ts`, `src/types/temporal.ts`                                                                           | proof-only                                                                   | Recognition                 |
| `Types.RecognitionPlain`                                   | `recognize_eq_scan`, `plain_probes`                                                       | `builtinFirstMatch` in `src/types/builtins.ts`, `inChain`                                                                                           | RecognitionPlain                                                             | Recognition                 |
| `Types.Atoms`                                              | `classify_atomic`, `classify_reads`, `ingress_atom_iff`, `ingress_structural`             | `isAtomObject` in `src/object-property.ts`, `recognize` in `src/adapters/recognition.ts`                                                            | Atoms                                                                        | Recognition, Atoms          |
| `Types.Ingress`                                            | `ownReads_shared`, `walkReads_eq`                                                         | `recognize` with a `PrototypeRead` in `src/adapters/recognition.ts`; `prototypes` in `src/publication/capture.ts`, `createDraft`, the snapshot walk | Ingress                                                                      | Recognition, Atoms, Ingress |
| `Types.Cell`                                               | `encode_injective`, `child_refs`                                                          | test type in `src/__tests__/fixtures/cell-type.ts`                                                                                                  | proof-only (Policy uses the runtime cell type)                               | none                        |
| `Types.NativeValue`, `Types.NativeValueEncoding`           | `published_payload`, `temporal_compatible_iff`, `clear_append_exact`, `bigint_injective`  | `src/types/temporal.ts`, `src/types/url.ts`, `src/types/url-search-parameters.ts`                                                                   | NativeValue (not `Types.NativeValueEncoding`, which is proof-only)           | Native values               |
| `Types.LazyOwnership`                                      | `lazy_eager_equivalent`, `omit_identity_response`                                         | ownership tables in `src/snapshot.ts` and finalization                                                                                              | imported by OwnedNativeChild                                                 | Lazy ownership metadata     |
| `Types.OwnedPublication`                                   | `bulk_equivalent`, `bulk_identity`, `sealed_owner_sound`                                  | `src/types/shared/url-carrier.ts`                                                                                                                   | OwnedNativeChild; native differential check                                  | URL ownership               |
| `Types.OwnedNativeChild`, `Types.OwnedNativeChildEncoding` | `adopt_consistent`, `admitted_iff`, `first_prepared_ranked`, `replay_owned_valid`         | `src/types/url.ts`, `src/types/url-search-parameters.ts`, `src/types/shared/url-carrier.ts`                                                         | OwnedNativeChild (not `Types.OwnedNativeChildEncoding`, which is proof-only) | URL ownership               |

`Types.Recognition` refines first-match recognition by traces of a fixed prefix of predicate calls.
The traces keep the ranks of the predicates visited, the selected rank and the position of an early
exception.

`Types.RecognitionPlain` proves that the built-in registries may decide an object after one
prototype read: when the prototype is `Object.prototype` or `null` and the object holds no view
brand, every later probe fails, so the plain-object fallback is the scan's result
(`plain_probes`, `recognize_eq_scan`). Any other object takes the scan, each `instanceof` probe
deciding membership from the prototype already read, so the result and a raised error are the
scan's while the object itself is read once.

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
  operations behave natively, and observations stay stable within a phase.
- **Identity and storage.** Fresh allocations are fresh, storage detection is correct, and each
  publication attempt gets a fresh private token.

### `snapshot`

- **Snapshot memo.** A caller-supplied memo is trusted and can return any object, including the
  source; detachment holds only for a valid memo with native storage separation
  (`graph-capture.spec.ts` keeps a counterexample). A fresh URL built around a memo-supplied child
  must carry matching same-call carrier metadata, or `snapshot` rejects it.
- **Built-in snapshot writer.** Each built-in facet initializes its writer once and exposes no
  application callback that can reenter the traversal before the copy is recorded. Built-in
  construction callbacks only read private `ArrayBuffer` layout data or create private URL carrier
  metadata; a new built-in facet must keep this boundary or keep a separate memo.
  `snapshot-construction.spec.ts` covers reinitialization and reentrant caller-memo reads.

### `reconcile`

- **Full capture.** The pinned closure must sit in the current heap at its occupants, be closed and
  separate from captured nodes, have observed buffer extents and receive no write. The runtime walks
  a subtree before pinning it, refuses to pin when the walk meets either root, excludes walked
  objects from other domains, and pins to itself any captured node the walk met. Only plain-object
  and array slots pin, and captured views never pin their buffers.
- **Property order.** `DeferredOrder` applies only while key storage is private, stable and
  non-escaping, and desired keys are buffered eagerly.
- **Property writes.** `PropertyWrite` covers one key of an ordinary object, or of a proxy whose
  traps forward to one, such as a Vue reactive proxy. The prototype walk in `canPublishProperties`
  must find the descriptor assignment would reach. It reads a descriptor of `Object.prototype` or
  `Array.prototype` only for a key that `in` reports there, and goes past either one only when it
  does not own that key; for any other key it stops there, since `in` has already searched the rest
  of the chain (`src/__tests__/prototype-boundaries.spec.ts`). `deserialize` asks whether
  `Object.prototype` holds a key once per shape, since only built-in code and the global `Temporal`
  run before records are filled. Multi-key order is `PropertyOrder`'s; an own accessor is treated as
  a slot that keeps its place.
- **Write-free readback.** When the first publication of an attempt wrote nothing to any node,
  `publishGraph` answers each readback without reading. `WriteFreeReadback` proves that a plain
  object or an array whose publication wrote nothing would read back as accepted, given the same
  observation. The runtime supplies that observation: no write means no setter or write trap ran,
  and a repeated read answers as the first did. Only the first publication counts, since its targets
  are the objects the preflight read, each exposed as it is written; plain objects must also list
  exactly their own keys. That publication of an ordinary target, not a wrapper whose descriptors
  hold its raw contents, takes its key list and each aligned key's presence and attributes from the
  preflight's descriptors and still reads each value (`publishKnown_eq`).

### Selection kernel

- **Preferred attempts.** After attempting the preferred plan (`rankedPreferred_head`), the driver
  skips exactly the stream's first plan. Finalization builds the head eligibility mask
  (`ranked_head`) before searching.
- **Termination.** The driver's attempt and round bounds assume that native operations terminate.

### `produce`

- **Drafts.** The recipe is isolated from the input, returning the original `current` cancels draft
  changes, and getters are sealed during finalization.
- **Finalization reads.** Reading an object again lists the same children, as `SettledChildren`
  assumes; identity restoration takes an object's children from a finalization walk that visited all
  of them, and its storage check the prototype finalization's recognition read, for as long as
  finalization keeps that recognition. A draft write keeps the descriptor and value it read for its
  key in the first copy, and a draft observation that reads the object itself counts each data slot
  it read there as backed by the object.
- **Folded leaves.** A non-strict compile folds the objects a fixed node's walk meets first and
  registers none of them, so they follow every registered node as `FoldedLeaves` orders them; their
  storages join the fixed storages, their edges to registered nodes become the edges of the fixed
  node whose walk met them, and no record points at one. A storage conflict rejects the folded
  problem, and the strict sealed pass compiles without folding.
- **Immutable assembly.** Recursive comparisons read only the pending record's target; edges,
  payload and settled state are consumed after completion. `immutable-assembly.spec.ts` checks these
  boundaries with a cycle and accessor-backed records.
- **Key order.** `KeyOrder` assumes the engine lists own keys as `OrdinaryOwnPropertyKeys` does and
  that the draft store follows ordinary assignment and `delete`; the KeyOrder bridge checks both.
- **Draft surface.** The runtime refuses new properties on collection drafts and native copies by
  making them non-extensible, and on array drafts in the proxy traps; a getter is deterministic
  between its observation and a later read of the kept object. The DraftSurface bridge checks
  admission and reuse.
- **Draft class.** `Map.prototype`, `Set.prototype` and a subclass's prototype are not modified
  during a call, and the layer the runtime builds holds exactly the draft class's methods; a
  subclass override of a collection method behaves on a native collection of its class. The
  DraftClass bridge checks resolution and `instanceof`.
- **Draft iteration.** The working copy is a native collection whose iterator follows the
  collection's own insertion order and changes; Lean models entries as an ordered list. The
  DraftIteration bridge checks walks and results on a `Map`.
- **Draft reads.** `hasOwnProperty` on the object reports its own keys, which a Vue proxy passes
  to its raw object; the DraftRead bridge checks Vue reactive objects and arrays.
- **Draft members.** A member's identity is the raw object a Vue proxy reports through its
  marker, which Vue does not change during a call; the DraftMembers bridge checks plain and Vue
  reactive arrays.
- **Set methods.** The model assumes an operand whose `has` and `keys` agree and change nothing, and
  whose keys are distinct by identity. The runtime reads `size`, `has` and `keys` and calls them in
  the order the specification gives, walks the draft live, or as a copy for `difference`, and closes
  the key iterator where the specification does; native tests compare the calls, errors and results
  with native `Set` methods on operands that change the set. A native `Set` or `Map` operand is
  asked for each form of a member, which its `has` cannot observe; any other operand's `has`
  receives the draft. The draft's members and size are read as the native methods read them, past
  a subclass's iterator and `size`. The DraftSetMethods bridge checks results, and that a result
  holds this draft's object members as drafts.
- **Copy prototypes.** A copy takes the source's prototype as read once at capture, and
  `Object.setPrototypeOf` on the fresh copy succeeds. Each kind's standard prototype is its live
  constructor's `prototype`, which does not change during a call. The CopyPrototype bridge checks
  copies and `serialize` acceptance.

### All operations

- **Intrinsic independence.** The models have no prototypes, so the runtime's own records, tables,
  descriptors, errors and loops must not reach `Object.prototype` or `Array.prototype`; see
  [AGENTS.md](../AGENTS.md) and `src/standard-prototypes.ts`. The `Uint8Array` base64 methods and
  the global `Temporal` are read as own properties. A user collection is walked with the
  `for...of` and destructuring protocol (`stepIterator`, `entryPair`, `closeIterator`), except that
  a `return` only `Object.prototype` holds is neither read nor called; a fresh iterator from a
  built-in `Map` or `Set` method is stepped directly. A user array's hole is asked of the array
  itself (`hasElement`) when a standard prototype holds that index; otherwise `in` is the only
  observation. `standard-prototypes.spec.ts` plants each internal and protocol name on both
  prototypes in a child process. An index accessor or read-only index on a standard prototype, and
  a replaced built-in method, are outside this obligation.

### Native types

- **Recognition.** The runtime performs the same live namespace reads, constructor reads and
  predicate calls in the modelled order, and caches no result across calls; within a call, capture's
  result serves discovery (Ingress). The built-in registries read the prototype once and decide each
  `instanceof` probe from it; a repeated read answers as that one did, and `instanceof` against the
  built-in, `URL` and Temporal constructors uses the default `Symbol.hasInstance`, so no probe
  accepts an object whose prototype is `Object.prototype` or `null`.
- **Atoms.** The listed constructors are the live globals, which callers do not modify during a
  call; `instanceof` against them uses the default `Symbol.hasInstance`. A caller that already read
  an object's prototype, such as `snapshot` and `reconcile` capture, passes it on instead of reading
  it again. The Atoms bridge checks the classification, the read count and each function's
  treatment of atoms.
- **Ingress.** The prototype that ingress reads serves every reader of that object until the call's
  first write: `reconcile` capture records it, with the kind, for discovery, the preflight's
  inherited-accessor check and the Vue marker walk, and discovery does not check that kind again;
  `produce` uses it for the draft's proxy target and `snapshot` for the copy. A later read must
  answer as the first did, so a getter or trap that changes a prototype before the first write is
  unsupported. Readback and a draft's first copy, which follow the recipe, read the prototype
  again.
- **Native values.** Native brands, constructors, capture, cloning, publication and readback are
  faithful, and Temporal labels keep all ten Duration components and each class's calendar, time
  zone and reference-date distinctions. Lean proves neither native parsing nor `.equals`.
- **Lazy ownership metadata.** Runtime maps stay scoped to their session, phase or attempt; custom
  construction callbacks still run, and overwriting a shared target clears obsolete metadata.
- **URL ownership.** Ownership is fixed, allocation is fresh, carrier maps are per call, ordered
  pairs are captured faithfully, and force propagates to sealed replay. Preparation fails before
  fresh writes; native exceptions still propagate. The private query marker relies on the URL
  [form parser](https://url.spec.whatwg.org/#concept-urlencoded-parser) ignoring empty fields and on
  every parameter mutator running the native
  [query update](https://url.spec.whatwg.org/#concept-urlsearchparams-update), even for no-ops. Bulk
  publication relies on opaque-path normalization of the empty-list update, which JavaScript tests
  cover. Getter order, method branding and URL parsing are native.

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
  the `NativeArray` model in `Positional` states; view constructors and buffer bytes are outside it.
- **Map and Set equality.** `Map.prototype.set` and `Set.prototype.add` use `SameValueZero`,
  canonicalize signed-zero keys and keep the first insertion position of an existing entry
  ([Map.set](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-map.prototype.set),
  [Set.add](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-set.prototype.add)).
- **Base64.** The encoder's alphabet table and bitwise operators are native; `binary-codec.spec.ts`
  compares it with `btoa`. A native decoder never yields more bytes than `decodedSize` predicts,
  which lets the exact-count check reject skipped whitespace; `serialization-boundaries.spec.ts`
  covers this on the `atob` path and with native stand-ins.
- **Encoder observations.** The traversal models constrain only the order of entering and
  referencing objects, not application reads such as `length`, getters, iterator `next` and
  `return`, or IteratorClose. The runtime classifies each child slot (`slot` in `emit.ts`) only
  where the stack machine would, recognizes each object once (`node`), reads a Map entry, URL
  parameters or a view's buffer before its child, and keeps trie nodes fresh per call.
  `serialization.spec.ts` and `serialization-collections.spec.ts` cover representative traces.

## Runtime bridges

`OracleMain` is the oracle executable, `reconcile-oracle`. `RuntimeOracle` reads one JSON request
per line, dispatches it by family to the entry function of that family's oracle module, and ends
each response with a record-separator line. A family's oracle module is `Oracle.<Family>Oracle`, and
its entry function is `run`; `PropertyConstructOn` and `PropertyThroughSetter` instead go to
`PropertyWriteOracle` (`runConstructOn`, `runThroughSetter`).

| Oracle family             | Bridge in `scripts/`                        | Runtime comparison                                                                                                                                                                                                                                                                                                                                                                                                         |
| ------------------------- | ------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Contract`                | `lean-captured-bridge.ts`                   | graphs from `reuse-fixtures.json`: values, aliases, cycles, wrappers, identity restoration                                                                                                                                                                                                                                                                                                                                 |
| `Policy`                  | `lean-policy-bridge.ts`                     | complete selection streams, with support, groups and preferred streams on the same fixtures; construction, requirement, consensus, strongly connected component, claim, driver, execution, provenance and forward-pruned cases                                                                                                                                                                                             |
| `Pruned`                  | `lean-pruned-bridge.ts`                     | graphs from `pruned-fixtures.json`: spread roots, aliases into replaced positions, cycles                                                                                                                                                                                                                                                                                                                                  |
| `PropertyOrder`           | `check-property-order-runtime.ts`           | cursor traces, including cases with strictly less work                                                                                                                                                                                                                                                                                                                                                                     |
| `PropertyWrite`           | `check-property-write-runtime.ts`           | single-key outcomes, run through `reconcile` on ordinary objects, forwarding proxies and Vue reactive proxies: status, final descriptor, own and inherited setter calls, and no write before a rejection                                                                                                                                                                                                                   |
| `PropertyPlacement`       | `check-property-placement-runtime.ts`       | pairs of own-key orders with an integer key, names and symbols, and every set of accessors they share: `reconcile` succeeds with the desired order exactly where Lean keeps every accessor, and otherwise writes nothing                                                                                                                                                                                                   |
| `WriteFreeReadback`       | `check-write-free-readback-runtime.ts`      | `reconcile` of every ordered subset of three keys onto two, and of every array of length up to three onto two requested arrays, through a counting proxy: the readback is elided and nothing is written exactly where Lean finds publication write-free, and every result equals `next`                                                                                                                                    |
| `PropertyConstructOn`     | `check-property-construct-runtime.ts`       | new objects built by `snapshot`, a `produce` rebuild, an object `reconcile` adds and `deserialize`, on a custom prototype or `Object.prototype` holding each kind of descriptor for the key, or on a null prototype, from enumerable and non-enumerable source properties: each holds the own data property with its source's enumerability, no setter on its prototype runs, and `serialize` rejects a non-enumerable one |
| `PropertyThroughSetter`   | `check-property-through-setter-runtime.ts`  | assignments of a key the object lacks through a setter on its prototype that defines nothing or the key with each set of attributes, on ordinary objects and `produce` drafts: the draft accepts exactly the definition assignment would make and refuses the others; `standard-prototypes.spec.ts` runs `produce` under `node --frozen-intrinsics`                                                                        |
| `KeyOrder`                | `check-key-order-runtime.ts`                | sequences of assignments and deletions on objects with integer keys, names and a symbol: the engine's own keys and `produce`'s result both equal Lean's `ownKeys`                                                                                                                                                                                                                                                          |
| `Atoms`                   | `check-atoms-runtime.ts`                    | real built-in prototype chains behind custom prototypes, with proxies counting reads: the runtime walk matches Lean's answer and read count, and each atom is kept by `snapshot`, `reconcile` and `produce` and rejected by `serialize`                                                                                                                                                                                    |
| `Ingress`                 | `check-ingress-runtime.ts`                  | real built-in and listed prototype chains behind custom prototypes, with and without a view brand and with a throwing prototype read: recognition with the prototype read shared and with a separate atom split both match Lean's outcome; the object is read once when shared and as often as Lean counts when not, and its custom prototypes the same number of times either way                                         |
| `RecognitionPlain`        | `check-recognition-plain-runtime.ts`        | real built-in prototype chains behind custom prototypes, with and without a view brand and with a throwing prototype read: built-in recognition and every known-kind check match Lean's result and thrown error; the object is read once, and its custom prototypes as the generic scan reads them, less the typed-array probe's repeated `DataView` walk                                                                  |
| `DraftSurface`            | `check-draft-surface-runtime.ts`            | draft writes on objects, arrays, maps, typed arrays and dates admitted exactly where the result carries them, and objects with getters, changed or not, kept exactly where Lean keeps them; a rebuilt object holds each returned value as data                                                                                                                                                                             |
| `DraftClass`              | `check-draft-class-runtime.ts`              | names on `Map` and `Set` drafts, built-in and subclass instances, owned by the prototype Lean names, and `instanceof` checks that agree; a subclass method runs on a draft and the result keeps the subclass                                                                                                                                                                                                               |
| `DraftIteration`          | `check-draft-iteration-runtime.ts`          | scripts of iterations and writes on a `Map` draft: each walk, the result's entries and whether the result keeps the original agree with Lean                                                                                                                                                                                                                                                                               |
| `SettledChildren`         | `check-settled-children-runtime.ts`         | every graph of three objects with child lists of at most two entries, with no object or one object changed through its draft, asked whether object 0 and then object 1 need a copy: each answer, the settled answers, including those settled before their question ended, and the kept child lists equal Lean's                                                                                                           |
| `DraftRead`               | `check-draft-read-runtime.ts`               | reads of Vue reactive object and array drafts, before and after the first write: an owned key gives the child's draft, and Vue's raw-object marker, `hasOwnProperty` and `forEach` come from the prototype, not from Vue's proxy                                                                                                                                                                                           |
| `DraftMembers`            | `check-draft-members-runtime.ts`            | `includes`, `indexOf` and `lastIndexOf` on plain and Vue reactive array drafts of `[a, b, a, 7]`, for each object as itself, its draft and the value Vue reactive state hands out, another object and numbers: results agree with Lean                                                                                                                                                                                     |
| `DraftSetMethods`         | `check-draft-set-methods-runtime.ts`        | the `Set` methods on plain and Vue reactive `Set` drafts, unwritten and with a working copy, over enumerated member and key lists, with each operand form (a `Set` from `current`, a `Set` of drafts, a `Set` draft and a set-like object): the members of each result agree with Lean                                                                                                                                     |
| `CopyPrototype`           | `check-copy-prototype-runtime.ts`           | copies by `snapshot`, an object `reconcile` adds and a changed `produce` result, of arrays, maps, sets, dates, data views, URLs and parameters, each as its own instance and as a subclass instance: every copy keeps its source's prototype, and `serialize` accepts only the standard prototype, which `deserialize` restores                                                                                            |
| `SeededRequirements`      | `check-seeded-requirements-runtime.ts`      | closure traces, including cases with strictly less work                                                                                                                                                                                                                                                                                                                                                                    |
| `DeferredOrder`           | `check-deferred-order-runtime.ts`           | preflights, demanded checkpoints and original error identities                                                                                                                                                                                                                                                                                                                                                             |
| `FactRenaming`            | `check-fact-renaming-runtime.ts`            | histories with queries and live cursor reads                                                                                                                                                                                                                                                                                                                                                                               |
| `CompactImmutable`        | `check-compact-immutable-runtime.ts`        | cases and ranked plans, including construction rejections                                                                                                                                                                                                                                                                                                                                                                  |
| `SelectionUnwind`         | `check-selection-unwind-runtime.ts`         | admitted prefixes with assignment and undo transitions                                                                                                                                                                                                                                                                                                                                                                     |
| `NativeValue`             | `check-native-value-runtime.ts`             | fixtures from `native-value-fixtures.json`: facet compatibility, immutable reuse, publication and readback                                                                                                                                                                                                                                                                                                                 |
| `OwnedNativeChild`        | `check-owned-native-child-runtime.ts`       | production carrier adoption projections: raw and canonical query, ordered entries, owner and child identities; then bulk-versus-sequential parameter publications compared natively, without the oracle                                                                                                                                                                                                                    |
| `Serialization`           | `check-serialization-lean.ts`               | `serialize` documents decoded and re-emitted exactly by Lean; malformed documents rejected by both; non-canonical documents decoded to the same graph by both; literal roots; every accepted document accepted at exactly eight bytes per word of Lean's `accounting` and rejected one byte below                                                                                                                          |
| `SerializationCollection` | `check-serialization-collection-runtime.ts` | success and failure traces through the production `map` and `set` facets: reads, ordered contents, untouched target on failure                                                                                                                                                                                                                                                                                             |

Read the table with these limits:

- A corpus bounds the test enumeration, not production graphs. "Strictly less work" marks cases
  where the optimized algorithm does less work than the reference, so the optimization is not
  vacuous.
- `SelectionUnwind` executes reference transitions with the runtime's demand updates, not a
  production code path. No bridge executes `DraftExecSpec`; the Contract bridge compares
  `produce`'s identity restoration with `Immutable`.
- The `Serialization` domain is records, null-prototype records, dense and sparse arrays, JSON
  literals and shared scalar nodes. Its hand-written JSON importer uses Lean numbers, so `-0` and
  overflowing literal roots are compared with `JSON.parse` at runtime only.

After `pnpm check:lean` has built the oracle, you can run one family by hand. The request needs all
three fields; the reply is the oracle's JSON between record-separator lines, the last carrying
`null` or the error.

```sh
echo '{"family":"Pruned","args":["lean/fixtures/pruned-fixtures.json"],"input":""}' \
  | .lake/build/bin/reconcile-oracle
```
