# @escapace/reconcile

Copy JavaScript objects, arrays, maps and sets, build their next versions, and update them in place, while keeping control of which objects stay the same. `snapshot` makes an independent copy, `produce` builds the next version of a value from ordinary mutations, and `reconcile` updates existing objects in place to match new data. Each function is tree-shakable.

## Install

```sh
pnpm add @escapace/reconcile
```

## Choose a function

| You want to                                                     | Use                                            |
| --------------------------------------------------------------- | ---------------------------------------------- |
| Update objects your code already holds so they match new data   | `reconcile(current, next)`                     |
| Build a new version of a value by writing ordinary mutations    | `produce(current, recipe)`                     |
| Get a copy you can change without affecting the original        | `snapshot(value)`                              |
| Write mutations, then apply them to the objects your code holds | `reconcile(current, produce(current, recipe))` |

The functions differ in what they do with object identity, that is, whether a value in the result is the same object as before or a new one:

| Function                   | Changes the original | Objects in the result                                           |
| -------------------------- | -------------------- | --------------------------------------------------------------- |
| `snapshot(value)`          | No                   | All new                                                         |
| `produce(current, recipe)` | No                   | Unchanged parts are the original objects; changed parts are new |
| `reconcile(current, next)` | Yes, in place        | The original objects, with new contents                         |

```ts
import { produce, reconcile, snapshot } from '@escapace/reconcile'

const state = { user: { name: 'Ada' }, tags: ['a'] }

const copy = snapshot(state) as typeof state // copy.user is a new object
const next = produce(state, (draft) => {
  draft.tags.push('b')
  return draft
}) // next.user is state.user; next.tags is a new array
reconcile(state, next) // state.tags is still the same array, now ['a', 'b']
```

## Update live state

`reconcile(current, next)` changes `current` so that it matches `next`. It keeps the objects that your code, components and watchers already hold.

```ts
const state = { user: { name: 'Ada' }, items: [{ id: 1 }] }
const user = state.user

reconcile(state, { user: { name: 'Grace' }, items: [{ id: 1 }, { id: 2 }] })
// state.user is still `user`, now named 'Grace'; state.items has two items
```

Values are matched by position: object properties by key, array elements by index, and `Map` and `Set` entries by insertion order. An existing object at a matched position is kept and its contents are updated; it also keeps its own prototype. A value of a different kind, such as an array where an object was, replaces it. Values that did not change are not written, so their setters and watchers do not run.

Spread updates are cheap. In `reconcile(state, { ...state, count: 1 })`, every other child of the new object is already in `state`, so `reconcile` reads those children once and writes only `count`.

When both arguments are objects, `reconcile` returns `current`. Otherwise it returns `next` and changes nothing. If `current` cannot be made to match `next`, it throws without undoing earlier writes; see [When something fails](#when-something-fails).

Full contract: [`reconcile`](#function-reconcile-).

## Build the next value

`produce(current, recipe)` gives `recipe` a draft of `current` to change with ordinary code, and returns the next value. `current` is not modified.

```ts
const state = { user: { name: 'Ada' }, items: [{ id: 1 }] }

const next = produce(state, (draft) => {
  draft.items.push({ id: 2 })
  return draft
})
// state.items still has one item; next.user is state.user; next.items is a new array
```

- Return the draft, or any other value, explicitly. A recipe that returns nothing produces `undefined`.
- Unchanged parts of the result are the original objects, so mutating them also changes `current`. Use `snapshot(produce(current, recipe))` when you need a fully independent result.
- Reading a `Date`, `ArrayBuffer`, typed array or `DataView` from the draft gives a writable copy. If the recipe leaves the copy unchanged, the result uses the original.
- If the recipe changes a value and then changes it back, the result keeps the original object.

Full contract: [`produce`](#function-produce-).

## Make an independent copy

`snapshot(value)` returns a deep copy that you can change without affecting the original.

```ts
const state = { user: { name: 'Ada' }, tags: ['a'] }
const copy = snapshot(state) as typeof state

copy.user.name = 'Grace' // state.user.name is still 'Ada'
```

Compared with the built-in `structuredClone`, `snapshot`:

- keeps functions by reference, where `structuredClone` throws;
- copies Vue reactive state, where `structuredClone` throws;
- keeps prototypes, where `structuredClone` returns plain objects;
- keeps properties with symbol keys, which `structuredClone` drops.

Full contract: [`snapshot`](#function-snapshot-).

## Apply a recipe to live state

Combine `produce` and `reconcile` to write changes as mutations and still update the objects your code holds:

```ts
const current = store.state // read once

reconcile(
  current,
  produce(current, (draft) => {
    draft.count += 1
    return draft
  }),
)
```

`produce` finishes before `reconcile` starts, so an error in the recipe leaves `current` untouched. If `current` comes from a getter or a function call, read it once into a variable, as above, and use that variable in both places.

## Vue reactive state

All three functions accept Vue reactive objects, arrays, maps and sets.

```ts
import { reactive } from 'vue'

const store = reactive({ user: { name: 'Ada', role: 'admin' }, items: [] as string[] })

reconcile(store, { user: { name: 'Grace', role: 'admin' }, items: ['a'] })
// store.user is the same reactive object; watchers of name run, watchers of role do not
```

- `reconcile` keeps the reactive objects your components hold.
- `snapshot` returns plain, non-reactive data.
- `produce` keeps unchanged parts as the same reactive objects, while the objects it creates for changed parts are plain. Use `reconcile(store, produce(store, recipe))` to apply the changes to the store.
- `reconcile` never makes two positions share one underlying object through different reactive wrappers.

## Supported values

| Value                                           | `snapshot`                          | `produce`                                             | `reconcile`                                              |
| ----------------------------------------------- | ----------------------------------- | ----------------------------------------------------- | -------------------------------------------------------- |
| Plain objects and arrays                        | Copied                              | Drafted                                               | Updated in place, matched by key or index                |
| `Map` and `Set`                                 | Copied                              | Drafted                                               | Updated in place, matched by entry order                 |
| `Date`, `ArrayBuffer`, typed arrays, `DataView` | Copied                              | Copied when read                                      | Updated in place, or replaced if a buffer's size changes |
| `URL` and `URLSearchParams`                     | Copied with their live relationship | Copied when read; unchanged pairs reuse their source  | Updated while preserving owned parameter identity        |
| Available Temporal values                       | Copied                              | Copied when read; unchanged copies reuse their source | Equal values retained; changed nested values replaced    |
| Class instances                                 | Copied without private fields       | Drafted like plain objects                            | Updated in place like plain objects                      |
| Functions                                       | Kept by reference                   | Kept by reference                                     | Kept by reference                                        |
| Primitives, including `bigint`                  | Returned as is                      | Read and assigned normally                            | Replaced by the next value                               |

All three functions preserve key order, sparse-array holes, shared references, cycles, and the sharing between buffers and their views.

A URL and its `searchParams` remain linked when both appear in the graph, including when parameters appear first. Parameter order, duplicate names and empty names or values are preserved. URL state is read and written through native accessors and methods; instance overrides and extra properties are ignored. Native methods work on draft copies; edits do not affect the source. Query spelling follows native URL behavior: even sorting an already sorted parameter list can change `%20` to `+`. A URL and its owned parameters cannot be retained independently when doing so would break their relationship.

Primitive `bigint` and `BigInt64Array`/`BigUint64Array` already use the primitive and binary paths. Boxed bigint (`Object(1n)`) is not a supported native kind; its internal slot is not copied by the class-instance fallback.

Temporal support is optional and uses the current global `Temporal` namespace: `Duration`, `Instant`, `PlainDate`, `PlainDateTime`, `PlainMonthDay`, `PlainTime`, `PlainYearMonth`, and `ZonedDateTime`. No polyfill is installed or imported. A standards-compatible polyfill can be installed on the global namespace before use; module-only polyfill instances and other realms are not automatically recognized. `Temporal.Now` is not a value kind. Snapshot preserves nanoseconds, calendars, time zones and reference dates. Duration equality compares all ten components, so one second differs from 1,000 milliseconds even if their strings match.

Temporal values are immutable. In a recipe, assign the result of methods such as `add` or `with`. An unchanged read reuses the source; an explicitly created equal value remains a distinct identity. Reconcile can retain an equal Temporal root but rejects a changed one under its existing object-root identity contract. Native kinds follow the existing Date policy for subclasses and extra own properties: copies use native value state, not subclass state or expandos.

## When something fails

Every failure the library detects throws a `ReconcileError`. Its `cause.type` names what happened, and the prefix of the type names where:

| Prefix         | Thrown by                           |
| -------------- | ----------------------------------- |
| `Draft`        | `produce`, while the recipe runs    |
| `Finalization` | `produce`, after the recipe returns |
| `Publication`  | `reconcile`                         |
| `Snapshot`     | `snapshot`                          |

`snapshot` throws `SnapshotURLSearchParamsMemoIncompatible` when a caller-supplied memo provides parameters that cannot be attached to a new URL. Supplying consistent memo entries for both the URL and its parameters remains supported. Errors from your own code, such as getters, setters, proxy traps and iterators, reach you unchanged, as do `RangeError`s for invalid array lengths. `reconcile` does not roll back, so after a failure `current` can hold some of the new values.

```ts
import { isReconcileError, reconcile } from '@escapace/reconcile'

try {
  reconcile(current, next)
} catch (error) {
  if (isReconcileError(error) && error.cause.type === 'PublicationRejected') {
    // current may hold some of the new values
  } else throw error
}
```

Messages may change between versions, so branch on `cause.type`. Every type and its details: [`RECONCILE_ERROR_TYPES`](#const-reconcile_error_types-) and [`ReconcileErrorMetadata`](#interface-reconcileerrormetadata-).

## Limitations

- Iterating a draft `Map` or `Set` with `keys`, `values`, `entries`, `forEach` or `for...of` throws.
- Defining properties on a draft with `Object.defineProperty`, `Object.defineProperties` or `Reflect.defineProperty` throws; use assignment instead.
- Copies and rebuilt objects lose the private fields and other internal state of class instances.
- Storage shared between different wrappers is detected only for Vue reactive wrappers, not for other proxies.
- Results are not frozen.
- A failed `reconcile` is not rolled back.

## Contributing

See the [development workflow](docs/development.md).

# API

## function isReconcileError [↗](src/error.ts#L156-L157 'isReconcileError')

Returns whether `value` is a [ReconcileError](#class-reconcileerror-), narrowing its type.

```typescript
isReconcileError: (value: unknown) => value is ReconcileError
```

### Parameters

| Parameter | Type               | Description                          |
| --------- | ------------------ | ------------------------------------ |
| `value`   | <pre>unknown</pre> | Any value, typically a caught error. |

## function isReconcileErrorOfType [↗](src/error.ts#L165-L168 'isReconcileErrorOfType')

Returns whether `error` has the given `type`, narrowing `cause` to that type's facts.

```typescript
isReconcileErrorOfType: <T extends ReconcileErrorType>(error: ReconcileError, type: T)
  => error is ReconcileError<T>
```

### Parameters

| Parameter | Type                                                                       | Description                                                              |
| --------- | -------------------------------------------------------------------------- | ------------------------------------------------------------------------ |
| `error`   | <pre>[ReconcileError](#class-reconcileerror- 'class ReconcileError')</pre> | An error already known to be a [ReconcileError](#class-reconcileerror-). |
| `type`    | <pre>T</pre>                                                               | The error type to test for.                                              |

## function produce [↗](src/produce.ts#L79-L81 'produce')

Runs `recipe` on a writable draft of `current` and returns the next value, leaving `current` unchanged.

```typescript
export declare function produce<T, R>(current: T, recipe: (draft: T) => R): R
```

### Type Parameters

| Parameter | Description                           |
| --------- | ------------------------------------- |
| `T`       | Type of `current` and of the draft.   |
| `R`       | Type of the value the recipe returns. |

### Parameters

| Parameter | Type                       | Description                                               |
| --------- | -------------------------- | --------------------------------------------------------- |
| `current` | <pre>T</pre>               | The value to start from. It is not modified.              |
| `recipe`  | <pre>(draft: T) => R</pre> | Receives a draft of `current` and returns the next value. |

### Returns

The value the recipe returned, with drafts replaced by ordinary values. A recipe that returns nothing yields `undefined`.

### Throws

1. [ReconcileError](#class-reconcileerror-) while the recipe runs: `DraftIterationUnsupported` for draft `Map` or `Set` iteration, `DraftDefinePropertyUnsupported` for reflective property definition, `DraftArrayLengthRejected` or `DraftArrayIndexRejected` for an exotic array whose descriptors a real array could not have, and `DraftWrapperIdentityChanged` or `DraftWrapperIteratorMismatched` for a misbehaving reactive wrapper.
2. [ReconcileError](#class-reconcileerror-) after the recipe returns: `FinalizationAccessorUnstable` when a getter adds a new getter to the result, and `FinalizationConstructionImpossible` when no consistent result exists. `FinalizationStorageMissing` and `FinalizationChildInvalid` indicate a bug in the library.
3. Errors thrown by the recipe, getters, setters or proxy traps, and native `RangeError`s for invalid array lengths, propagate unchanged.

### Remarks

The draft behaves like `current` but records changes instead of applying them. The recipe returns the next value explicitly: the draft, a part of it, or any other value. Drafts inside the returned value are turned back into ordinary values. If the recipe returns `current` itself, its draft changes are discarded.

The result reuses the parts of `current` the recipe left unchanged where it can, so it is not detached from `current`; use `snapshot(produce(...))` for a detached copy. The result is not frozen. An edit that is later undone restores the original object when its whole subtree ends up equal, including key order, holes, shared references and cycles. A new object the recipe creates stays distinct from an equal existing one.

Plain objects, arrays, `Map` and `Set` become drafts when the recipe reads them. A `Set` draft treats a draft and the object it drafts as the same member. Reading a `Date`, `ArrayBuffer`, `DataView` or typed array gives the recipe a writable copy; an unchanged copy resolves back to the original, and changed copies keep their buffer sharing. URLs and URLSearchParams also copy when read, preserving the URL's live parameter identity in either read order. Native query normalization counts as a change even when parameter entries stay equal. Available Temporal values are copied when read; they are immutable, so assign the value returned by their methods. An unchanged Temporal copy resolves back to the original. Other objects, such as class instances, are drafted like plain objects: an unchanged one is kept, and a changed one is rebuilt with the same prototype and own properties but without private fields or other internal state. Primitives, including bigint, and functions are single values. Vue reactive wrappers that behave like objects, arrays, maps or sets are supported.

Reading a value or writing an equal value back does not count as a change. During the recipe, getters run on every read and assignments call setters with the draft as `this`; `Reflect.set` honors an explicit receiver. Reading descriptors or enumerating keys, for example with `Object.keys`, returns draft values like ordinary reads, so it can create child drafts or copies. Defining properties with `Object.defineProperty`, `Object.defineProperties` or `Reflect.defineProperty` throws; use assignment instead.

After the recipe returns, each getter in the result runs once, in depth-first order, with a temporary draft as `this`. Its value becomes an ordinary data property, so an object with a getter is always rebuilt. Writes the getter makes through `this` become part of the result; changes it makes to other state are not isolated.

Array drafts support normal iteration, including `for...of` and callback methods. Iterating a draft `Map` or `Set` with `keys`, `values`, `entries`, `forEach` or `[Symbol.iterator]` throws.

### Examples

```ts
const current = { todos: [{ done: false }], filter: 'all' }
const next = produce(current, (draft) => {
  draft.todos[0].done = true
  return draft
})
// current is unchanged; next.todos is a new array; next.filter is still 'all'
```

## function reconcile [↗](src/reconcile.ts#L57-L59 'reconcile')

Updates `current` in place to match `next` and returns `current`, keeping existing objects wherever their position and kind allow.

```typescript
export declare function reconcile<T>(current: unknown, next: T): T
```

### Parameters

| Parameter | Type               | Description                                           |
| --------- | ------------------ | ----------------------------------------------------- |
| `current` | <pre>unknown</pre> | The value to update.                                  |
| `next`    | <pre>T</pre>       | The value `current` should match. It is not modified. |

### Returns

`current` when both arguments are objects, otherwise `next`.

### Throws

1. [ReconcileError](#class-reconcileerror-) with type `PublicationRejected` when `current` cannot be made to match `next`. Causes include roots of incompatible kinds, such as an object and an array; a non-writable or non-configurable property, or a non-extensible object, that blocks a change; two kept objects that would share storage; and a write that did not take effect. Writes made before the failure are not rolled back.
2. Errors thrown by getters, setters or proxy traps propagate unchanged, also without rollback.

### Remarks

Values are matched by position: plain-object properties by key, array elements by index, and `Map` and `Set` entries by insertion order. A current object at a matched position is kept and updated when its kind fits the next value; otherwise the next value takes its place. When two positions compete for one object, a deterministic choice keeps it at one of them. Afterwards `current` has the key order, array lengths and holes, entry order, shared references and cycles of `next`. Dates, buffers and views at matched positions take the next value's time or bytes, and buffer sharing follows `next`. URLs and URLSearchParams take the next native state while preserving the URL's owned parameter identity, order and duplicates. Equal Temporal values can retain their identities; changed Temporal values at nested positions are replaced. A changed Temporal root is rejected because an immutable value cannot be changed while retaining the root identity.

`next` is read completely before `current` changes. When both arguments are objects, a successful call returns `current`. When either is not an object, the call returns `next` and changes nothing.

An object in `next` that is already the object at the same property of the matched current object is kept as it is. `reconcile(state, { ...state, count: 1 })` therefore reads the shared children once and writes only the root. Nothing inside a kept object is changed or read back. Other positions never take over an object from inside it, but an object that `next` itself places elsewhere stays that object there. The result equals a full update. A kept object that refers back to either root is updated normally instead.

Vue reactive wrappers are supported. Two kept objects never end up sharing the raw storage behind a wrapper.

### Examples

```ts
const state = { user: { name: 'Ada' }, tags: ['a'] }
const result = reconcile(state, { user: { name: 'Grace' }, tags: ['a', 'b'] })
// result === state; state.user and state.tags are the same objects, updated in place
```

## function snapshot [↗](src/snapshot.ts#L63-L68 'snapshot')

Returns a deep copy of `value` that can be changed without affecting the original.

```typescript
export declare function snapshot(value: unknown, seen?: WeakMap<object, object>): unknown
```

### Parameters

| Parameter | Type                                | Description                                                                                                                                                                                                                                                                                                                                                                                       |
| --------- | ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `value`   | <pre>unknown</pre>                  | The value to copy.                                                                                                                                                                                                                                                                                                                                                                                |
| `seen`    | <pre>WeakMap\<object, object></pre> | Map from source objects already copied to their copies. Entries are used as given, without checking; the copy is detached only if every entry is a detached copy of its source. A supplied parameter copy that a fresh URL would need to adopt raises `SnapshotURLSearchParamsMemoIncompatible`; supply a consistent owner-and-parameters pair or omit those entries. Most callers omit the memo. |

### Returns

A detached copy of `value`, or `value` itself when it is not an object.

### Remarks

The copy keeps plain-object key order and prototypes, sparse-array holes, shared references, cycles, the sharing between buffers and their views, and each URL's owned search parameters. Plain objects, arrays, `Map`, `Set`, `Date`, `ArrayBuffer`, `DataView`, typed arrays and available Temporal values are supported, including Vue reactive wrappers that behave like objects, arrays, maps or sets. Primitives are returned as they are, including bigint, and functions are kept by reference. Temporal support uses the eight value classes on the current global Temporal namespace, without installing a polyfill. Other objects, such as class instances, are copied like plain objects: the copy has the same prototype and own properties but not private fields or other internal state.

### Examples

```ts
const node = { label: 'a', children: [] as unknown[] }
node.children.push(node)
const copy = snapshot(node) as typeof node
// copy !== node; copy.children[0] === copy
```

## class ReconcileError [↗](src/error.ts#L132-L149 'ReconcileError')

The error this library throws when an operation cannot keep its contract.

```typescript
export declare class ReconcileError<T extends ReconcileErrorType = ReconcileErrorType> extends Error
```

### Remarks

Every failure the library detects is a `ReconcileError`. Its `cause` holds a stable `type` and the facts for that type. Its message is for people and may change between versions. Check for it with `instanceof ReconcileError` or [isReconcileError](#function-isreconcileerror-), then branch on `cause.type`.

The library never throws for an outcome that is part of a contract, such as `reconcile` returning `next` when a root is not an object.

Three kinds of errors keep their original identity and are not wrapped: `RangeError` for an invalid array length, as native arrays throw it; errors thrown by application code that the operations reach, such as getters, setters, proxy traps and iterators; and errors the host throws when `reconcile` writes into `current`. When one of them interrupts `reconcile`, earlier writes are not rolled back.

### Examples

```ts
try {
  reconcile(current, next)
} catch (error) {
  if (isReconcileError(error) && error.cause.type === 'PublicationRejected') {
    // current may hold some of the writes; nothing was rolled back
  } else throw error
}
```

### new ReconcileError

Creates an error. The library creates these itself; applications normally only inspect them.

```typescript
constructor(cause: ReconcileErrorCause<T>, message: string);
```

#### Parameters

| Parameter | Type                                                                                        | Description                                                |
| --------- | ------------------------------------------------------------------------------------------- | ---------------------------------------------------------- |
| `cause`   | <pre>[ReconcileErrorCause](#type-reconcileerrorcause- 'type ReconcileErrorCause')\<T></pre> | The error's `type` and the facts for that type.            |
| `message` | <pre>string</pre>                                                                           | A description for people; not part of the stable contract. |

### ReconcileError.cause

The error's `type` and the facts for that type.

```typescript
readonly cause: ReconcileErrorCause<T>;
```

### ReconcileError.name

Always `'ReconcileError'`.

```typescript
readonly name: 'ReconcileError';
```

## const RECONCILE\_ERROR\_TYPES [↗](src/error.ts#L10-L23 'RECONCILE_ERROR_TYPES')

Every error type this library raises, named by the phase that detects it.

```typescript
RECONCILE_ERROR_TYPES: readonly[
  ('DraftArrayIndexRejected',
  'DraftArrayLengthRejected',
  'DraftDefinePropertyUnsupported',
  'DraftIterationUnsupported',
  'DraftWrapperIdentityChanged',
  'DraftWrapperIteratorMismatched',
  'FinalizationAccessorUnstable',
  'FinalizationChildInvalid',
  'FinalizationConstructionImpossible',
  'FinalizationStorageMissing',
  'PublicationRejected',
  'SnapshotURLSearchParamsMemoIncompatible')
]
```

### Remarks

The prefix names the phase. `Draft` types come from `produce` while the recipe runs. `Finalization` types come from `produce` after the recipe returns. `Publication` types come from `reconcile`. `Snapshot` types come from `snapshot`. After the prefix, the name states the subject and the condition, so each type names exactly one situation.

## interface ReconcileErrorMetadata [↗](src/error.ts#L38-L98 'ReconcileErrorMetadata')

The facts each error type carries in `cause`, next to `type`.

```typescript
export interface ReconcileErrorMetadata
```

### Remarks

The facts are values the library already held when it detected the failure. Reporting an error reads nothing more from application objects.

### ReconcileErrorMetadata.DraftArrayIndexRejected

An exotic source array, such as a proxy, reported an index at or beyond a non-writable length, which a real array cannot have. `index` is that index.

```typescript
DraftArrayIndexRejected: {
  index: number
}
```

### ReconcileErrorMetadata.DraftArrayLengthRejected

An exotic source array, such as a proxy, reported a length that its other properties make impossible. `length` is the reported length.

```typescript
DraftArrayLengthRejected: {
  length: number
}
```

### ReconcileErrorMetadata.DraftDefinePropertyUnsupported

The recipe called `Object.defineProperty`, `Object.defineProperties` or `Reflect.defineProperty` on a draft. `property` is the key. Use assignment instead.

```typescript
DraftDefinePropertyUnsupported: {
  property: PropertyKey
}
```

### ReconcileErrorMetadata.DraftIterationUnsupported

The recipe called an iteration method on a draft `Map` or `Set`. `method` names it.

```typescript
DraftIterationUnsupported: {
  method: DraftIterationMethod
}
```

### ReconcileErrorMetadata.DraftWrapperIdentityChanged

A reactive wrapper around a `Map` or `Set` reported an inconsistent chain of raw objects while a draft entry was being inserted.

```typescript
DraftWrapperIdentityChanged: {
}
```

### ReconcileErrorMetadata.DraftWrapperIteratorMismatched

A reactive wrapper around a `Map` or `Set` did not return the value just inserted when it was iterated.

```typescript
DraftWrapperIteratorMismatched: {
}
```

### ReconcileErrorMetadata.FinalizationAccessorUnstable

A getter that ran after the recipe returned put a new getter into the result, which the library found only after it had stopped running getters. `property` is the new getter's key.

```typescript
FinalizationAccessorUnstable: {
  property: PropertyKey
}
```

### ReconcileErrorMetadata.FinalizationChildInvalid

Internal error: a record of the result referred to a child that does not exist. `index` is the record and `child` the invalid reference. This indicates a bug in the library.

```typescript
FinalizationChildInvalid: {
  child: unknown
  index: number
}
```

### ReconcileErrorMetadata.FinalizationConstructionImpossible

No consistent result exists: objects the result must keep would share storage, or the new objects have no valid creation order.

```typescript
FinalizationConstructionImpossible: {
}
```

### ReconcileErrorMetadata.FinalizationStorageMissing

Internal error: an object that could be kept had no storage. `index` identifies its record. This indicates a bug in the library.

```typescript
FinalizationStorageMissing: {
  index: number
}
```

### ReconcileErrorMetadata.PublicationRejected

`reconcile` could not make `current` match `next`. Writes made before the failure are not rolled back.

```typescript
PublicationRejected: {
}
```

### ReconcileErrorMetadata.SnapshotURLSearchParamsMemoIncompatible

A borrowed parameter copy cannot be adopted by a fresh native URL.

```typescript
SnapshotURLSearchParamsMemoIncompatible: {
}
```

## type DraftIterationMethod [↗](src/error.ts#L29 'DraftIterationMethod')

Draft `Map` and `Set` methods that throw; `iterator` stands for `[Symbol.iterator]`.

```typescript
export type DraftIterationMethod = 'entries' | 'forEach' | 'iterator' | 'keys' | 'values'
```

## type ReconcileErrorCause [↗](src/error.ts#L101-L102 'ReconcileErrorCause')

The `cause` of a [ReconcileError](#class-reconcileerror-): its `type` together with that type's facts.

```typescript
export type ReconcileErrorCause<T extends ReconcileErrorType = ReconcileErrorType> = T
  extends ReconcileErrorType ? {
  type: T;
} & ReconcileErrorMetadata[T] : never;
```

## type ReconcileErrorType [↗](src/error.ts#L26 'ReconcileErrorType')

The `type` of a [ReconcileError](#class-reconcileerror-): one of [RECONCILE\_ERROR\_TYPES](#const-reconcile_error_types-).

```typescript
export type ReconcileErrorType = (typeof RECONCILE_ERROR_TYPES)[number]
```
