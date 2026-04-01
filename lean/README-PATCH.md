# Semantic specification for `patch`

`patch` should be modeled as draft execution that produces one finalized next graph and then publishes that graph through one root call to `reconcile`.

That boundary matters because it makes the patch proof story line up with the existing runtime proof base for `snapshot` and `reconcile`: one next graph, one publication witness, one place where topology and order guarantees are discharged.

## Purpose

This document defines the semantic model of `patch` for the default runtime.

The intended operator is a companion to `reconcile`, not a second independent publication system.

- `reconcile(current, next)` publishes a complete next graph.
- `patch(current, recipe)` executes a draft recipe, finalizes one next graph, and publishes that next graph through `reconcile`.

The specification is meant to be precise enough to track the current Lean development in:

- `lean/PatchDraftDefs.lean`
- `lean/PatchDraftSpec.lean`
- `lean/PatchDraftSoundness.lean`
- `lean/PatchSpec.lean`
- `lean/PatchSoundness.lean`
- `lean/PatchOrder.lean`
- `lean/PatchLocality.lean`

There is also one implementation-facing Lean refinement layer:

- `lean/PatchFinalizeCoherence.lean`
- `lean/PatchFinalizeCoherenceSoundness.lean`

That refinement layer does not change the semantic center of this document. It adds a compact proof-facing boundary for finalization coherence in the finalized next graph, covering:

- repeated-reference / cross-reference finalization,
- moved-reference final placement,
- collection-captured draft-value finalization.

It should be read as theorem-level clarification for implementation guidance, not as a change to the semantic core defined here.

## Status and relation to `lean/README.md`

This document is an extension layer over `lean/README.md`, not an independent replacement.

- `lean/README.md` remains the base semantic specification for the supported value domain, `snapshot`, `reconcile`, observational equivalence, and runtime integration.
- This document adds `patch` as a draft-driven operator whose publication step reuses the `reconcile` semantics from `lean/README.md`.

Two consequences follow immediately.

- The semantic domain for patch is exactly the supported runtime value domain already used by `snapshot` and `reconcile`.
- The decisive publication theorems for patch factor through the existing `reconcile` theorem base.

## Scope

This specification covers:

- draft execution as an abstract semantic layer,
- lazy child-draft creation,
- copy-on-write bookkeeping,
- explicit delete semantics,
- root-return replacement,
- finalization to one next graph,
- publication of that next graph via one `reconcile` episode,
- patch soundness,
- patch-wide topology guarantees,
- patch-wide order and shape guarantees in the current retained-root theorem scope,
- patch locality and supported-surface behavioral corollaries,
- implementation-facing finalization-coherence theorems over the finalized next graph,
- the current default-runtime monotonic write policy for proxy-managed draft structures, stated as a runtime-facing semantic note rather than as a separate theorem family.

This specification deliberately excludes:

- full JavaScript proxy-trap semantics,
- engine-level behavior such as hidden classes or garbage collection,
- descriptor-level semantics,
- non-configurable deletion guarantees,
- unsupported exotics outside the supported `snapshot`/`reconcile` surface,
- a result-to-current rebasing relation for trailing-publication theorems,
- a full ECMAScript formalization of object property-order algorithms,
- a full formalization of arbitrary array method behavior beyond the current abstract effect layer,
- callback-order or op-record semantics for how finalization happens internally,
- a requirement that the runtime realize abstract modification propagation through one specific local bookkeeping strategy such as an eagerly propagated concrete `modified` bit on every ancestor node.

## 1 — Semantic domain

`patch` uses the same semantic domain as `reconcile`.

In particular, runtime values remain a finite rooted heap graph over:

- primitives,
- functions as opaque atoms,
- plain objects,
- arrays,
- `Date`,
- `Map`,
- `Set`,
- `ArrayBuffer`,
- `DataView`,
- typed arrays.

The relevant Lean base remains:

- `lean/Defs.lean`
- `lean/WF.lean`
- `lean/SnapshotSpec.lean`
- `lean/SnapshotSoundness.lean`
- `lean/ReconcileSpec.lean`
- `lean/ReconcileSoundness.lean`

So when this document says “next graph,” it means a graph in the same supported semantic domain already used by `reconcile`.

## 2 — Core semantic idea

The semantic center of `patch` is not an instruction language.

It is this factorization:

```text
patch(current, recipe)
= let next := executeDraftRecipe(current, recipe)
  in reconcile(current, next)
```

In Lean-facing terms, the semantic center is the factorization

```text
∃ next,
  DraftExecSpec(current, next)
  ∧ ReconcileSpec(current, next, result)
```

The current proof files package that idea as:

- `DraftExecSpec` in `lean/PatchDraftSpec.lean`
- `PatchSpecCore` and `PatchRootSpec` in `lean/PatchSpec.lean`

The naming split is intentional:

- `PatchSpecCore` is the witness-carrying factorized relation.
- `PatchRootSpec` is the thin root-level proposition exposed as the patch relation.

## 3 — Draft execution layer

The draft layer is intentionally abstract.

It does not attempt to formalize JavaScript proxy traps directly. Instead, it records the proof-relevant effects of draft execution.

### 3.1 — Paths, access, and touch bookkeeping

The draft layer tracks proof-facing paths built from:

- object keys,
- array indices,
- map entry positions,
- set entry positions.

The central bookkeeping witness is `DraftTouchWitness`, which records:

- accessed paths,
- child-draft existence,
- pure reads,
- touched paths and touched current nodes,
- modified nodes,
- copy-allocated nodes,
- parent relations,
- explicit delete sites,
- assignment-of-`undefined` sites,
- abstract array/map/set mutation logs.

The point of this layer is not to model runtime internals. The point is to support theorem statements about:

- lazy child-draft creation,
- copy-on-write,
- delete versus assignment,
- untouched-path preservation,
- abstract collection effects.

### 3.2 — Root return modes

The root patch result has two semantic modes.

- `finalized`
  - the recipe result is the finalized draft graph.
- `replaced(v)`
  - the recipe returned an explicit non-draft value `v`, which becomes the next root.

This is represented by `DraftReturnMode`.

So root replacement is not a marker object and not a separate instruction constructor. It is the return behavior of the draft recipe.

### 3.3 — Lazy child-draft creation

Child drafts exist only at accessed paths.

The current theorem surface exposes this as:

- `draft_lazy_child_creation`

The semantic claim is intentionally modest and proof-facing:

- if a child draft exists at a path, that path was accessed.

### 3.4 — Read non-interference

Pure reads do not directly cause modification or copy allocation of the denoted current node.

The current theorem surface exposes this as:

- `draft_read_non_interference`

### 3.5 — Copy-on-write and modification propagation

Copy-on-write is modeled abstractly at the node level.

The current theorem surface exposes:

- `draft_copy_on_write`
- `draft_parent_modification_propagates`

So the current proof layer establishes:

- copied nodes and modified nodes coincide at the abstract bookkeeping level,
- child modification propagates to ancestors through the parent relation.

That statement should be read as a property of the proof-facing draft witness, not as a requirement that the runtime maintain one identical concrete bookkeeping field at every step. A runtime may realize the same semantic effect either through eager ancestor bookkeeping or through descendant-sensitive finalization checks that force ancestor materialization when a reachable descendant changed elsewhere.

The current default TypeScript runtime uses a monotonic write policy for plain objects, arrays, `Map`, and `Set`:

- pure reads are non-mutating,
- SameValue no-op writes stay no-op,
- the first real mutation permanently marks the affected draft node modified for the rest of the recipe,
- there is no path-level restoration or changed-to-unchanged collapse,
- unmodified ancestors may still finalize to fresh next-side nodes when descendant-sensitive finalization discovers a reachable changed or clone-on-read descendant.

This runtime note clarifies how the current implementation realizes the abstract draft layer. It does not change the factorized patch semantics or the theorem-level meaning of the proof witnesses.

### 3.6 — Delete semantics

Deletion is explicit.

At the semantic level:

- object deletion is tracked as delete,
- assigning `undefined` is tracked as an ordinary assignment,
- those two cases are distinct.

The current theorem surface exposes:

- `draft_delete_is_explicit`
- `draft_undefined_assignment_is_ordinary`

This is the defining deletion rule of the current patch model.

### 3.7 — Finalization witness

Draft finalization carries a current-to-next witness:

```text
preserve : CurId ⇀ NextId
```

Intended meaning:

- `preserve(c) = n` means the finalized next graph contains a node `n` corresponding to current node `c` under finalization.

This witness is used to state untouched-subtree preservation without pretending the current and next namespaces are identical.

The current theorem surface exposes:

- `draft_finalize_produces_next_graph`
- `draft_untouched_preserved`

### 3.8 — Object, array, map, and set effect contracts

The draft layer records object and collection effects abstractly.

Current proof-facing contracts:

- `ObjectDraftNodeSpec`
- `ArrayDraftNodeSpec`
- `MapDraftNodeSpec`
- `SetDraftNodeSpec`

Current extraction theorems:

- `draft_object_effects`
- `draft_array_effects`
- `draft_map_effects`
- `draft_set_effects`

These are intentionally proof-first contracts, not executable semantics for every host-language operation.

## 4 — Root patch semantics

The current root patch relation is packaged by:

- `PatchSpecCore`
- `PatchRootSpec`

with the shape:

```text
PatchSpecCore(current, result)
  = finalized next heap/root
  + DraftExecSpec(current, next)
  + ReconcileSpec(current, next, result)
```

`PatchRootSpec` is intentionally thin:

```text
PatchRootSpec(current, result) := Nonempty (PatchSpecCore(current, result))
```

The patch root therefore does not dispatch over a separate patch instruction language. It packages:

- one finalized next graph,
- one draft execution witness,
- one reconcile publication witness.

## 5 — Observational meaning of `patch`

The main correctness relation remains `SurfaceEq` from `lean/README.md` and `lean/WF.lean`.

So patch correctness is:

- finalize one next graph,
- publish it through `reconcile`,
- obtain a result that is `SurfaceEq` to that next graph.

The current theorem surface exposes this directly as:

- `patch_surface_soundness`

## 6 — Root result theorems

The current root theorem family covers the cases needed by the current patch model.

### 6.1 — Same-atom fast path

If draft execution yields the same atom at the root, patch inherits the ordinary reconcile atom fast path.

The current theorem is:

- `patch_root_fastpath_atom`

### 6.2 — Root replacement publication

If the draft layer returns an explicit replacement root `v`, patch publishes that root through ordinary reconcile root semantics.

The current theorem is:

- `patch_root_replacement_publication`

### 6.3 — Returned atom

If the draft layer returns an atom, the patch result root is that atom.

The current theorem is:

- `patch_root_replaced_atom`

### 6.4 — Returned next reference

If the draft layer returns a next reference, patch root behavior follows the ordinary reconcile root cases:

- direct next-root image under replacement branches,
- retained current-root identity under the same-kind retained branch.

The current theorem is:

- `patch_root_replaced_ref_cases`

## 7 — Patch-wide topology guarantees

The patch publication witness is now packaged directly at patch level.

### 7.1 — Witness packaging

The current proof surface exposes:

- `PatchTopology`
- `patch_topology_bundle`
- `patch_topology_package`

This package records:

- witness existence,
- witness invariants,
- sharing functionality,
- no-collapse,
- current-node injectivity,
- image/reuse consistency.

### 7.2 — One-witness publication

The current theorem is:

- `patch_has_witness`

This is the main topology boundary for patch:

- one finalized next graph,
- one reconcile witness over that next graph and the result graph.

### 7.3 — Sharing, no-collapse, current-node injectivity, buffer aliasing

The current theorem surface exposes:

- `patch_sharing`
- `patch_no_collapse`
- `patch_current_injectivity`
- `patch_buffer_alias`

These are stated directly from `PatchSpecCore`, not from an externally supplied witness.

### 7.4 — Cycle preservation

Cycle preservation is now part of the non-legacy reconcile semantic contract itself.

Current reconcile-side support:

- `ReconcileSpec.cyclePres`
- `reconcile_cycle_preservation`

Current patch-side theorem:

- `patch_cycle_preservation`

So patch now exposes a direct cycle theorem through its own publication witness.

## 8 — Order and shape guarantees

The current order/shape theorem surface is intentionally retained-root scoped.

That is the right boundary for the current proof scope because `ReconcileSpec.nodeSpec` exposes node-shape facts there.

### 8.1 — Plain-object own-key order

For retained plain-object roots, the result own-key order matches the finalized next own-key order.

The current theorem is:

- `patch_object_order_retained_root`

This theorem now quantifies over arbitrary current and next prototype labels.

The theorem is intentionally scoped to retained roots. It does not attempt a full host-language formalization of property-order derivation.

### 8.2 — Array shape and hole semantics

For retained array roots, the result array has:

- the same length as the finalized next array,
- the same hole pattern,
- pointwise transported present entries in index order.

The current theorems are:

- `patch_array_shape_retained_root`
- `patch_array_hole_vs_present_retained_root`

The second theorem is the patch-facing statement of the semantic distinction between:

- holes,
- present slots containing ordinary values.

That includes ordinary values such as `undefined`.

### 8.3 — Map order

For retained map roots, the result entry sequence follows finalized next iteration order pointwise.

The current theorem is:

- `patch_map_order_retained_root`

Implementation note:

- the current TypeScript runtime also finalizes draft-originating object-valued map keys coherently with ordinary object and array paths,
- but the current theorem surface still grounds `mapEntry` paths through entry value positions rather than separate key-position paths,
- so map-key coherence is currently a tested implementation property layered on top of the existing map-order theorem surface, not a separate named key-position theorem family.

### 8.4 — Set order

For retained set roots, the result value sequence follows finalized next iteration order pointwise.

The current theorem is:

- `patch_set_order_retained_root`

## 9 — Locality and supported-surface behavioral corollaries

### 9.1 — Touch locality in the next graph

Untouched regions preserved by the finalization witness remain `SurfaceEq` between the current graph and the finalized next graph.

The current theorem is:

- `patch_touch_locality_next`

### 9.2 — Publication locality

Once the finalized next graph is fixed, patch inherits ordinary reconcile locality for retained nodes.

The current theorem is:

- `patch_publication_locality`

As with `reconcile`, this is not an alias-isolation theorem.

### 9.3 — Delete versus assignment of `undefined`

The patch theorem surface distinguishes:

- explicit delete,
- ordinary assignment of `undefined`.

The current theorems are:

- `patch_delete_is_explicit`
- `patch_undefined_is_ordinary`

### 9.4 — Delete removes key on the supported surface

For retained plain-object roots in the current theorem scope, explicit deletion of key `k` removes `k` from the published result object.

The current theorem is:

- `patch_delete_removes_key_retained_root`

### 9.5 — Untouched key preservation on the supported surface

For retained plain-object roots in the current theorem scope, an untouched key remains present in the finalized next object and in the retained published result.

The current theorem is:

- `patch_untouched_key_preserved_retained_root`

### 9.6 — Modest untouched-path corollary

The current theorem surface also exposes the weaker general corollary:

- `patch_untouched_path_preservation`

This deliberately stops at:

- current-to-next untouched preservation,
- patch surface soundness for publication,

without overstating a direct current-to-result identity theorem across namespaces.

## 10 — How to read the Lean patch proofs

The replacement patch proof tree is easiest to read in this order.

1. `lean/Defs.lean`
2. `lean/WF.lean`
3. `lean/SnapshotSpec.lean`
4. `lean/SnapshotSoundness.lean`
5. `lean/ReconcileSpec.lean`
6. `lean/ReconcileSoundness.lean`
7. `lean/PatchDraftDefs.lean`
8. `lean/PatchDraftSpec.lean`
9. `lean/PatchDraftSoundness.lean`
10. `lean/PatchSpec.lean`
11. `lean/PatchSoundness.lean`
12. `lean/PatchOrder.lean`
13. `lean/PatchLocality.lean`

A useful reading rule is:

- `Snapshot*` and `Reconcile*` define the semantic backend,
- `PatchDraft*` defines draft execution and finalization,
- `Patch*` packages patch as draft execution plus publication and proves the patch-facing corollaries.

## 11 — Properties currently established in Lean

The current replacement proof surface establishes the following theorem families.

### Draft execution

- lazy child-draft creation,
- read non-interference,
- copy-on-write bookkeeping,
- parent-chain modification propagation,
- explicit delete versus assignment-of-`undefined`,
- one finalized next graph,
- untouched-region preservation through the finalization witness,
- object/array/map/set effect contracts,
- root-return replacement.

### Patch root and soundness

- factorized patch root semantics via `PatchSpecCore` and `PatchRootSpec`,
- patch surface soundness,
- root fast-path atom case,
- root replacement publication,
- returned atom theorem,
- returned next-ref root-case theorem.

### Topology

- one patch publication witness,
- patch-level topology packaging,
- sharing,
- no-collapse,
- current-node injectivity,
- image/reuse consistency,
- cycle preservation,
- buffer/view alias preservation.

### Order and shape

- retained-root plain-object key order,
- retained-root array length, hole, and pointwise slot structure,
- retained-root map entry order,
- retained-root set value order,
- explicit hole-versus-present-slot array corollary.

### Locality and supported-surface behavior

- untouched-region preservation into the finalized next graph,
- publication locality,
- delete versus assignment-of-`undefined`,
- retained-root delete-removes-key,
- retained-root untouched-key preservation,
- modest untouched-path preservation corollary.

## 12 — Out of scope for the current theorem tranche

The following remain outside the current patch theorem surface.

- full proxy-trap semantics,
- descriptor-level semantics,
- non-configurable delete guarantees,
- unsupported exotics,
- a full ECMAScript formalization of object key-order derivation,
- a general result-to-current rebasing relation for trailing-publication theorems,
- trailing-reconcile theorems built on such a rebasing relation,
- a broader theorem family beyond the current retained-root scope for node-shape facts,
- separate grounded key-position path theorems for map entries.

These exclusions are deliberate. They keep the patch proof tree aligned with the current supported runtime surface and with the theorem boundaries already present in the non-legacy `reconcile` development.

## 13 — Cost model and optimality target

The patch cost model should be read as:

```text
work = O(
  draft paths accessed
  + draft nodes copied
  + object keys deleted or rewritten during finalization
  + array/map/set structural effects represented in the finalized next graph
  + one reconcile publication of that next graph
  + bytes copied by reconcile-level snapshot or replacement branches
)
```

This is not an edit-script minimization problem.

The semantics are fixed by:

- draft execution,
- finalization,
- one reconcile publication,

not by a search over alternative update scripts.

## 14 — Summary

`patch` is best modeled as a draft-driven operator that produces one finalized next graph and then publishes that graph through one root call to `reconcile`.

The current Lean development now confirms that model directly.

Its main established consequences are:

- patch soundness through `SurfaceEq`,
- one patch-wide publication witness,
- sharing, no-collapse, cycle, and alias guarantees at patch level,
- explicit delete semantics with `undefined` treated as an ordinary value,
- retained-root order and shape theorems for objects, arrays, maps, and sets,
- locality and supported-surface corollaries that match the current proof scope.

That is the semantic object `lean/README-PATCH.md` should specify.
