# Semantic specification for `snapshot` and `reconcile`

## Purpose

This document defines the semantic model of the default context publication runtime implemented in `src/object-kind.ts`, with emphasis on `snapshot` and `reconcile`.

The target is the default runtime used by the interpreter when no custom `snapshotContext` or `reconcileContext` option is supplied. The specification is intended to be precise enough to encode in Lean 4 and to serve as the semantic source of truth for the default `snapshot` and `reconcile` operators.

## Status and relation to adjacent docs

This document is the semantic specification for the default context runtime.

It focuses on `snapshot` and `reconcile` themselves. Narrower documents may build on it for specific operators or proof slices, but this file is the base specification for the default publication runtime.

If a caller injects custom `snapshotContext` or `reconcileContext` functions, this document does not apply unless those functions are themselves observationally equivalent to the semantics below.

## Scope

This specification covers:

- the supported context-value surface for the default runtime,
- detached snapshot semantics at draft creation,
- publication semantics of `reconcile`,
- graph sharing, cycle preservation, and replacement behavior,
- the use of `snapshot` and `reconcile` at runtime publication boundaries.

This specification deliberately excludes:

- JavaScript engines’ hidden classes, garbage collection, or allocation strategy,
- exact property-descriptor preservation,
- accessor and proxy trap semantics,
- arbitrary exotic-object semantics outside the supported surface,
- user-supplied custom context snapshot or reconcile implementations,
- search-based diff, minimum-edit scripts, or global optimal matching.

The operator specified here is a fixed-alignment publication operator, not a general differencing algorithm.

## 1 — Semantic domain

### 1.1 — Values

The semantic domain is a finite rooted heap graph.

A semantic value is either:

```text
Value ::= Atom a | Ref n
```

where:

- `Atom a` is a non-object value or opaque atomic object treated as indivisible by the runtime,
- `Ref n` points to a heap node.

For this specification, atoms include:

- JavaScript primitive values,
- function values, treated as opaque reference atoms,
- symbol values when they appear as property values, map keys, or set elements.

Functions are atoms in this model. They are preserved by reference and are never traversed recursively.

### 1.2 — Supported heap nodes

Each heap node has one of the following kind-tagged payloads:

```text
Node ::=
  PlainObject(protoLabel, orderedKeys, fields)
| Array(length, presentEntries)
| Date(ms)
| Map(entrySeq)
| Set(valueSeq)
| ArrayBuffer(bytes)
| DataView(bufferRef, byteOffset, byteLength)
| TypedArray(ctorTag, bufferRef, byteOffset, length, elements)
```

with the following intended meaning.

- `PlainObject(protoLabel, orderedKeys, fields)`
  - `protoLabel` is an abstract prototype label.
  - `orderedKeys` is the own-key sequence returned by `Reflect.ownKeys` for an ordinary object.
  - `fields` maps each key in `orderedKeys` to a semantic value.
- `Array(length, presentEntries)`
  - `presentEntries` is a partial map from indices `0 .. length-1` to values.
  - Missing indices represent holes.
  - Non-index own properties are not part of the semantic surface.
- `Date(ms)` stores a millisecond timestamp.
- `Map(entrySeq)` stores an insertion-order sequence of key-value pairs.
- `Set(valueSeq)` stores an insertion-order sequence of values.
- `ArrayBuffer(bytes)` stores a byte sequence.
- `DataView(bufferRef, byteOffset, byteLength)` stores view metadata over an `ArrayBuffer` node.
- `TypedArray(ctorTag, bufferRef, byteOffset, length, elements)` stores typed-array metadata and logical element sequence over an `ArrayBuffer` node.

### 1.3 — Object-like values

A value is **object-like** iff it is a `Ref n` in the supported semantic model.

At the JavaScript implementation level, the runtime’s object predicate is `typeof value === 'object' && value !== null`. The semantic model reflects that behavior in one important way:

- functions are not object-like and therefore behave as atoms.

### 1.4 — Kind classification

The semantic kind function classifies supported object-like values into exactly these kinds:

- array,
- date,
- map,
- set,
- array buffer,
- data view,
- typed array,
- plain object.

Within the semantic scope of this document, the plain-object case means ordinary mutable objects only. Unsupported exotics that happen to fall through the implementation’s runtime classifier are outside the first formal specification.

## 2 — Supported and excluded surface

### 2.1 — Supported surface

The default runtime supports the following observable surface.

#### Plain objects

Supported observables:

- own-key sequence in `Reflect.ownKeys` order,
- values at those keys,
- graph topology induced by those values.

Additionally, the construction rules for `snapshot` and for fresh replacement subtrees preserve the source or next prototype label for those fresh nodes. Retained plain objects, however, are mutated in place and keep their current prototype label. Prototype equality with `next` is therefore not part of the generic publication equivalence relation for retained plain-object nodes.

#### Arrays

Supported observables:

- `length`,
- present numeric indices,
- holes,
- values at present numeric indices,
- graph topology induced by indexed entries.

Non-index own properties on arrays are excluded from the semantic surface.

#### `Date`

Supported observable:

- millisecond timestamp.

#### `Map`

Supported observables:

- insertion-order entry sequence,
- recursively reconciled keys and values,
- graph topology induced by keys and values.

The semantic model assumes ordinary JavaScript `Map` behavior:

- logical uniqueness of keys uses `SameValueZero`,
- `-0` is canonicalized to `+0`,
- insertion order is observable.

#### `Set`

Supported observables:

- insertion-order value sequence,
- recursively reconciled values,
- graph topology induced by values.

The semantic model assumes ordinary JavaScript `Set` behavior:

- logical uniqueness uses `SameValueZero`,
- `-0` is canonicalized to `+0`,
- insertion order is observable.

#### `ArrayBuffer`

Supported observables:

- `byteLength`,
- byte contents.

#### `DataView`

Supported observables:

- referenced buffer identity within the result graph,
- `byteOffset`,
- `byteLength`,
- bytes visible through the referenced buffer.

#### Typed arrays

Supported observables:

- constructor tag,
- referenced buffer identity within the result graph,
- `byteOffset`,
- logical length,
- logical element contents.

#### Functions

Functions are supported as opaque atoms only. They are preserved by reference.

### 2.2 — Excluded surface

The first formal specification excludes the following.

- `SharedArrayBuffer`
- views over `SharedArrayBuffer`
- proxies as semantic values
- accessor-dependent object behavior
- values whose correctness depends on descriptor fidelity
- arbitrary exotic non-ordinary objects in the plain-object fallback
- arbitrary extra own properties on `Map`, `Set`, `Date`, `ArrayBuffer`, `DataView`, and typed arrays
- arbitrary non-index own properties on arrays
- active iterator semantics during `Map` or `Set` mutation
- non-configurable deletion behavior
- non-writable-assignment edge cases

The implementation may attempt some of these cases, but this specification does not assign them a proof target.

## 3 — Equality and order primitives

### 3.1 — `SameValue`

The runtime uses JavaScript `Object.is` equality at its fast paths. The semantic equality relation for those paths is therefore ECMAScript `SameValue`.

Relevant consequences:

- `NaN` equals itself,
- `+0` and `-0` are distinct.

Whenever this specification says “equal by fast path,” it means equal under `SameValue`.

### 3.2 — `SameValueZero`

The semantic model for `Map` and `Set` assumes ordinary JavaScript keyed-collection semantics, which use `SameValueZero` for logical uniqueness.

This matters to the resulting container value, but not to the container-retention fast path of `reconcile`, which uses `SameValue` over ordinally aligned reconciled entries.

### 3.3 — Plain-object own-key order

For ordinary objects, `orderedKeys` is the sequence returned by `Reflect.ownKeys`, which in ECMAScript follows `OrdinaryOwnPropertyKeys` order:

1. array-index string keys in ascending numeric order,
2. other string keys in creation order,
3. symbol keys in creation order.

This order is semantically relevant to plain-object publication.

## 4 — Snapshot semantics

`snapshot` creates a detached graph that preserves supported structure from the source graph while preserving functions by reference.

### 4.1 — Snapshot relation

`snapshot(value)` is defined by a recursive traversal with a memo table:

```text
seen : SourceRef ⇀ ResultRef
```

For standalone draft snapshotting, `seen` starts empty. During `reconcile`, the same snapshot operator may be called with a pre-populated `seen` table whose entries are already chosen result images for some next-graph nodes.

The memo table ensures:

- cycles are preserved,
- repeated references in the source graph remain repeated references in the snapshot graph,
- binary aliasing through shared buffers is preserved.

### 4.2 — Snapshot rules

For `snapshot(v, seen)`:

1. If `v` is an atom, return `v` unchanged.
2. If `v = Ref n` and `seen(n)` is defined, return `seen(n)`.
3. Otherwise allocate a fresh result node according to the kind of `n`, store it in `seen(n)`, and then recursively snapshot supported child values.

### 4.3 — Kind-specific snapshot clauses

#### Arrays

For `Array(length, presentEntries)`:

- allocate a fresh array node of the same `length`,
- for each present index `i`, snapshot the entry value recursively,
- preserve holes exactly.

Only indexed structure is preserved.

#### Plain objects

For `PlainObject(protoLabel, orderedKeys, fields)`:

- allocate a fresh plain-object node with the same `protoLabel`,
- copy `orderedKeys` in the same order,
- recursively snapshot each field value in that order.

Descriptor fidelity is not preserved. The semantic payload is keys, values, order, and prototype label only.

#### `Date`

For `Date(ms)`:

- allocate `Date(ms)`.

#### `Map`

For `Map(entrySeq)`:

- allocate a fresh map node,
- for each entry in insertion order, snapshot key and value recursively,
- insert entries in the same order.

#### `Set`

For `Set(valueSeq)`:

- allocate a fresh set node,
- snapshot each value recursively,
- insert values in the same order.

#### `ArrayBuffer`

For `ArrayBuffer(bytes)`:

- allocate a fresh buffer node with copied bytes.

#### `DataView`

For `DataView(bufferRef, byteOffset, byteLength)`:

- first snapshot the referenced buffer,
- allocate a fresh `DataView` node over the snapshotted buffer with the same `byteOffset` and `byteLength`.

#### Typed arrays

For `TypedArray(ctorTag, bufferRef, byteOffset, length, elements)`:

- first snapshot the referenced buffer,
- allocate a fresh typed-array node with the same `ctorTag`, `byteOffset`, and `length` over the snapshotted buffer,
- preserve the logical element sequence.

### 4.4 — Snapshot properties

The specification targets the following snapshot theorems.

- **S1 — Surface preservation.** `snapshot(v)` is observationally equivalent to `v` on the supported surface.
  Additionally, the Lean theorem layer can expose plain-object prototype preservation for snapshotted nodes as a separate theorem, since the generic surface relation intentionally abstracts over plain-object prototype labels during reconcile.
- **S2 — Detachment.** Fresh object-like nodes in the snapshot are distinct from source nodes.
- **S3 — Sharing preservation.** If two source references are equal, their snapshot images are equal.
- **S4 — Distinctness preservation.** Distinct source references remain distinct in the snapshot.
- **S5 — Cycle preservation.** Reachable cycles in the source graph remain cycles in the snapshot graph.

## 5 — Reconcile semantics

`reconcile(current, next)` publishes `next` into the live structure rooted at `current`.

The operator is deterministic and fixed-alignment:

- arrays align by index,
- plain objects align by own-key identity and next own-key order,
- maps align by ordinal entry position,
- sets align by ordinal value position,
- binary views align through backing-buffer publication plus metadata equality.

It is not a search-based matcher.

### 5.1 — Witness relations

The recursive semantics is described using two partial maps.

```text
reuse : CurrentRef ⇀ NextRef
image : NextRef ⇀ ResultRef
```

Intended meaning:

- `reuse(c) = n` means current node `c` has been consumed for alignment against next node `n` and may not be reused for any other distinct next node.
- `image(n) = r` means next node `n` is represented by result node `r`.

A consumed current node is not necessarily the final image of the corresponding next node. For example, the implementation initially consumes matching-kind buffer or view roots before a later compatibility check may force a fresh replacement and overwrite `image(n)`.

Required invariants:

- `reuse` is injective on current nodes: one current node cannot be consumed for two distinct next nodes.
- `image` is functional on next nodes: one next node has one canonical result image.
- if `image(n) = c` for a current node `c`, then `reuse(c) = n`.
- if `n₁ ≠ n₂`, then `image(n₁) ≠ image(n₂)` whenever both are defined object references.
- if `n₁ = n₂`, then `image(n₁) = image(n₂)`.

These maps are semantic witnesses for the no-collapse and sharing properties of publication.

### 5.2 — Root rule

The public root function `reconcileRoot(current, next)` is defined as follows.

```text
reconcileRoot(current, next):
  if SameValue(current, next):
    return current
  if current is not object-like or next is not object-like:
    return next
  if kind(current) ≠ kind(next):
    return next
  return reconcileObjectByKind(current, next, emptyReuse, emptyImage)
```

The direct root return of `next` is semantically important. Nested replacement does not use this rule.

In the Lean model, result roots live in a separate result namespace. Accordingly, the root branches that return `next` directly at the JavaScript level are represented as the canonical result image of `next`: atoms stay unchanged, while next references are re-expressed as fresh result references. This is a representation-layer adaptation, not a change in the intended root semantics.

### 5.3 — Recursive rule

Recursive traversal uses `reconcileValue`, not the public root rule.

```text
reconcileValue(current, next, reuse, image):
  if next is not object-like:
    return next
  if image(next) is defined:
    return image(next)
  if current is not object-like:
    return snapshot(next, image)
  if reuse(current) is defined:
    return snapshot(next, image)
  if kind(current) ≠ kind(next):
    return snapshot(next, image)
  return reconcileObjectByKind(current, next, reuse, image)
```

This is the source of the root-versus-nested asymmetry:

- root primitive or root kind mismatch returns the exact `next` root,
- nested primitive or nested kind mismatch snapshots the next subtree instead.

### 5.4 — Shared-object fast path

When two aligned entries are equal by `SameValue` and are object-like, `reconcile` uses the following rule.

```text
reconcileSharedObject(current, next, reuse, image):
  if image(next) is defined:
    return image(next)
  if reuse(current) is defined:
    return snapshot(next, image)
  reuse(current) := next
  image(next) := current
  return current
```

This preserves equal-next sharing while preventing reuse of one current node for two distinct next nodes.

### 5.5 — Entry rule

For aligned child entries, `reconcileEntry(currentEntry, nextEntry, reuse, image)` is:

```text
if SameValue(currentEntry, nextEntry):
  if nextEntry is object-like:
    return reconcileSharedObject(currentEntry, nextEntry, reuse, image)
  else:
    return currentEntry
else:
  return reconcileValue(currentEntry, nextEntry, reuse, image)
```

### 5.6 — Object-by-kind dispatcher

When kind-specific reconciliation begins for `current` and `next` of the same supported kind:

1. record `reuse(current) := next`,
2. record `image(next) := current`,
3. perform the kind-specific rule below.

If the kind-specific rule later determines that the current node cannot remain the image, it may allocate a replacement and overwrite `image(next)` with that replacement.

## 6 — Kind-specific reconcile rules

### 6.1 — Arrays

Array publication is index-aligned.

Given `current = Array(currentLength, currentEntries)` and `next = Array(nextLength, nextEntries)`:

1. set the current array length to `nextLength`,
2. for each index `i` from `0` to `nextLength - 1`:
   - if `i` is present in `next`, reconcile `current[i]` with `next[i]`,
   - write back only if the reconciled value is not `SameValue` to the current entry,
   - if `i` is absent from `next` and present in `current`, delete index `i`,
3. return the current array.

Consequences:

- holes are preserved,
- trailing indices beyond `nextLength` are removed by the length update,
- array reorder is not solved by matching; correspondence is fixed by index,
- non-index own properties are ignored.

### 6.2 — `Date`

For `Date(currentMs)` and `Date(nextMs)`:

- mutate the current date to `nextMs`,
- return the current date.

### 6.3 — `Map`

Map publication is ordinally aligned by iteration position.

Given `current = Map(currentEntrySeq)` and `next = Map(nextEntrySeq)`:

1. iterate the two entry sequences in lockstep by ordinal position,
2. for each next entry `(nextKey, nextValue)`:
   - read the current entry at the same ordinal position if present,
   - reconcile current key with next key,
   - reconcile current value with next value,
   - store the reconciled pair in a temporary sequence,
3. let `canReturnCurrent` hold iff:
   - `current.size = next.size`, and
   - every next ordinal position had a current ordinal position, and
   - each reconciled key is `SameValue` to the original current key at that position, and
   - each reconciled value is `SameValue` to the original current value at that position,
4. if `canReturnCurrent`, return the current map unchanged,
5. otherwise clear the current map and reinsert the temporary reconciled pairs in next iteration order.

Important semantic point:

- map alignment is by ordinal position, not by associative lookup of matching keys.

### 6.4 — `Set`

Set publication is ordinally aligned by iteration position.

Given `current = Set(currentValueSeq)` and `next = Set(nextValueSeq)`:

1. iterate the two value sequences in lockstep by ordinal position,
2. reconcile each current value with the next value at the same position,
3. let `canReturnCurrent` hold iff:
   - `current.size = next.size`, and
   - every next ordinal position had a current ordinal position, and
   - each reconciled value is `SameValue` to the original current value at that position,
4. if `canReturnCurrent`, return the current set unchanged,
5. otherwise clear the current set and re-add the reconciled values in next iteration order.

Important semantic point:

- set alignment is by ordinal position, not by unordered membership matching.

### 6.5 — `ArrayBuffer`

For `ArrayBuffer(currentBytes)` and `ArrayBuffer(nextBytes)`:

- if `byteLength(currentBytes) ≠ byteLength(nextBytes)`:
  - allocate a fresh buffer copy of `nextBytes`,
  - set `image(next) := replacement`,
  - return the replacement,
- otherwise:
  - overwrite the current buffer bytes with the next buffer bytes,
  - return the current buffer.

Equal-length buffers are copied byte-for-byte even if their contents are already equal. There is no semantic byte-equality fast path.

### 6.6 — `DataView`

Given `current = DataView(currentBuffer, currentOffset, currentLength)` and `next = DataView(nextBuffer, nextOffset, nextLength)`:

1. reconcile `currentBuffer` with `nextBuffer`, obtaining `bufferResult`,
2. if all of the following hold:
   - `bufferResult` is the current buffer,
   - the constructors agree,
   - `currentOffset = nextOffset`,
   - `currentLength = nextLength`,
     then return the current view,
3. otherwise allocate a fresh data-view node over `bufferResult` with `nextOffset` and `nextLength`, set `image(next) := replacement`, and return the replacement.

### 6.7 — Typed arrays

Given matching typed-array kinds, publication follows the same view rule as `DataView`, with constructor tag and metadata interpreted as typed-array metadata:

1. reconcile the backing buffers,
2. if constructor tag, reconciled buffer identity, `byteOffset`, and `byteLength` all match the current typed array, return the current typed array,
3. otherwise allocate a fresh typed array over the reconciled buffer with the next constructor tag, offset, and length, set `image(next) := replacement`, and return the replacement.

### 6.8 — Plain objects

Plain-object publication is key-aligned by exact key identity with next key order authoritative.

Given:

```text
current = PlainObject(currentProto, currentKeys, currentFields)
next    = PlainObject(nextProto,    nextKeys,    nextFields)
```

compute reconciled values for the keys of `next` in `nextKeys` order.

There are two semantic cases.

#### Aligned-key case

If for every index `i < length(nextKeys)`, `currentKeys[i] = nextKeys[i]`, then:

1. for each key `k = nextKeys[i]`, reconcile `current[k]` with `next[k]`,
2. update only those keys whose reconciled values are not `SameValue` to the current value,
3. delete every trailing current own key in positions `length(nextKeys) .. length(currentKeys)-1`,
4. return the current object.

Consequences:

- current key order is retained because it already begins with `nextKeys` in the required order,
- only changed values are rewritten,
- extra trailing current keys are removed.

#### Rebuild case

If there exists a first index `i` with `currentKeys[i] ≠ nextKeys[i]`, then:

1. reconcile every `next[k]` against the corresponding `current[k]` by key identity,
2. store those reconciled values in temporary next-key order,
3. delete every current own key,
4. reassign keys in `nextKeys` order with the temporary reconciled values,
5. return the current object.

Consequences:

- the next own-key order becomes authoritative,
- the current object identity is retained,
- the current object prototype is retained,
- descriptor fidelity is not preserved.

## 7 — Observational equivalence and topology

### 7.1 — Surface equivalence

The main correctness relation is `SurfaceEq(result, next)` over the supported surface.

It is defined recursively as follows.

- **Atoms.** `SurfaceEq(Atom a₁, Atom a₂)` iff `a₁` and `a₂` are equal under the appropriate atomic equality relation. For primitives and functions used by `reconcile`, this is `SameValue`.
- **Arrays.** Same length, same present indices, and recursively `SurfaceEq` at each present index.
- **Plain objects.** Same ordered own-key sequence and recursively `SurfaceEq` for each key value in order.
- **Date.** Same timestamp.
- **Map.** Same insertion-order entry sequence, with recursive `SurfaceEq` on keys and values in each entry.
- **Set.** Same insertion-order value sequence, with recursive `SurfaceEq` on each value.
- **ArrayBuffer.** Same byte length and same bytes.
- **DataView.** Same constructor class, same `byteOffset`, same `byteLength`, and same bytes through the referenced buffer.
- **Typed arrays.** Same constructor tag, same `byteOffset`, same logical length, and same logical element sequence.

`SurfaceEq` intentionally excludes descriptor fidelity and retained plain-object prototype equality. Those are outside the supported semantic surface.

### 7.2 — Topology preservation

Besides surface equivalence, publication must preserve next-graph topology.

Let `Image(nextNode)` be the canonical result node induced by the `image` witness map.

The intended topology properties are:

- **T1 — Sharing preservation.** If two references in `next` are the same node, their images in the result are the same node.
- **T2 — No collapse.** If two references in `next` are distinct nodes, their images in the result are distinct nodes.
- **T3 — Current-node injectivity.** A current node can serve as the result image of at most one next node, and more generally can be consumed for alignment with at most one next node.
- **T4 — Cycle preservation.** Cycles reachable in `next` remain cycles in the result.
- **T5 — Buffer/view alias preservation.** If multiple next views share one next buffer, their result images share one result buffer.

### 7.3 — Locality of replacement

`reconcile` is subtree-local.

When a parent node is kind-compatible and alignable under its kind-specific rule, incompatibility of a child causes replacement of that child subtree only. The parent node is retained whenever its own kind-specific rule allows it.

The main exceptions are container rules whose semantics require full container rebuild after ordinal or key-order divergence:

- map clear-and-reinsert after ordinal mismatch in reconciled entries,
- set clear-and-reinsert after ordinal mismatch in reconciled values,
- plain-object delete-and-reassign after own-key order divergence.

Even in those cases, child values are still obtained by recursive publication before reinsertion.

## 8 — Runtime integration

This section ties the context-runtime specification back to the main machine semantics.

### 8.1 — Draft creation

When the interpreter uses the default runtime, service `draft()` captures the base context by:

```text
baseContext := snapshot(service.context)
```

This applies the snapshot semantics from §§4–5 at the draft-creation boundary for the default implementation.

### 8.2 — Root commit replay

When a draft commits into the live service, each recorded successful reducer step publishes context by:

```text
service.context := reconcile(service.context, reducer(service.context, action))
```

State replay and subscription timing are outside the scope of this document. This section specifies only the context publication operation used at that boundary.

### 8.3 — Child publication during composition

When a composed child transition publishes a new child-context slice into the parent context, the default runtime performs:

```text
parentContext[group] := reconcile(parentContext[group], childReducer(parentContext[group], action))
```

If the child-context value also carries a discriminant field `state`, the runtime may then overwrite that field with the child target state as part of ordinary composition machinery. That state injection belongs to the machine-composition semantics, not to `reconcile` itself.

## 9 — Properties for Lean verification

The following properties describe the theorem-facing contract for the Lean model of this specification.

### R1 — Snapshot soundness

For every supported value `v`, `snapshot(v)` is `SurfaceEq` to `v`.

### R2 — Snapshot topology preservation

`snapshot` preserves sharing, distinctness, and cycles.

### R3 — Reconcile soundness

For every supported `current` and `next` in scope, `reconcile(current, next)` yields a result `r` such that `SurfaceEq(r, next)`.

### R4 — Root fast-path correctness

If `SameValue(current, next)`, then `reconcile(current, next) = current`.

### R5 — Root replacement asymmetry

If the root values are non-object-like on either side, or if their supported kinds differ, then `reconcile(current, next) = next` at the JavaScript level. In the Lean model, the result is the canonical result-namespace image of `next`.

### R6 — Nested replacement via snapshot image

Whenever recursive publication cannot reuse a current subtree because of atom/object mismatch, kind mismatch, or conflicting prior reuse, the result subtree is the fresh result image corresponding to `snapshot(nextSubtree)` modulo the shared `image` relation.

The current Lean relational core proves the fresh-image shape plus the resulting surface and topology obligations. It does not encode a separate explicit snapshot witness inside each nested replacement constructor.

### R7 — Sharing theorem

Equal references in `next` map to equal references in the result.

### R8 — No-collapse theorem

Distinct references in `next` map to distinct references in the result.

### R9 — Current-node injectivity

A current node can be consumed for alignment with at most one next node, and any current node that is actually reused as a result image represents exactly one next node.

### R10 — Locality theorem

If a parent node is kind-compatible and alignable, child incompatibility changes only the necessary child image, not the parent identity.

### R11 — Canonical alignment theorem

The result is determined by the fixed kind-specific alignment rules of this specification. No search over alternative matchings occurs.

### R12 — Buffer/view alias theorem

Publication preserves next aliasing among buffers and views.

### R13 — Ordered-key publication theorem

For supported plain objects, the result’s own-key order is exactly `next` own-key order.

### R14 — Ordinal collection publication theorem

For supported maps and sets, publication is determined by next iteration order, not by unordered matching.

## 10 — Cost model and optimality target

The semantic cost model should stay separate from JavaScript engine costs.

Under the current semantics, a reasonable abstract work measure is:

```text
work = O(
  reachable next nodes visited
  + current keys deleted or rewritten
  + collection entries cleared or reinserted
  + bytes copied
)
```

This specification does not define a minimum-edit objective. Any optimality claim should be relative to the fixed semantics above, not to tree-edit-distance or graph-edit-distance problems.

## 11 — Out of scope for the current proof work

The following are intentionally outside the first Lean formalization.

- `SharedArrayBuffer` and shared-memory concurrency
- full ECMAScript proxy semantics
- accessors and descriptor-preserving publication
- failure behavior of writes or deletes against non-writable or non-configurable properties
- precise iterator invalidation behavior during container mutation
- engine-level performance claims about hidden classes, `delete`, or garbage collection
- custom `snapshotContext` or `reconcileContext` implementations supplied by users
- broadened semantics that allow search-based matching, reordering-aware matching, or global maximal sharing

## 12 — Summary

The default context runtime is best modeled as a deterministic publication operator over a restricted JavaScript heap graph.

Its defining properties are:

- fixed alignment rather than search,
- in-place reuse when kind and metadata permit it,
- snapshot-based nested replacement when reuse would violate next topology,
- preservation of sharing, cycles, and binary aliasing on the supported surface,
- explicit exclusion of descriptor-heavy and exotic JavaScript behavior.

That is the semantic object the Lean model formalizes.
