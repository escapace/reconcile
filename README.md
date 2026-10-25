# @escapace/reconcile

Updates objects in place, builds updated copies from ordinary mutations, makes deep copies and converts values to and from JSON text. Works with plain objects, arrays, `Map`, `Set`, class instances, dates, binary data, URLs and Temporal values and keeps shared references and cycles.

## Install

```sh
pnpm add @escapace/reconcile
```

The package is ESM only, has no dependencies and has no import side effects, so a bundler includes only the imported functions.

## Choose a function

| Task                                                                                                   | Function                                                                               | Compare with                                                  |
| ------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------- | ------------------------------------------------------------- |
| [Update existing objects in place to match a new value](#update-objects-in-place)                      | `reconcile(current, next)`                                                             | Assigning each changed property and deleting each missing one |
| [Build an updated copy by writing ordinary mutations](#build-an-updated-copy)                          | `produce(current, recipe)`                                                             | Spread copies of each object on the path to a change          |
| [Apply ordinary mutations to existing objects, only if the recipe completes](#apply-a-recipe-in-place) | `reconcile(current, produce(current, recipe))`                                         | Mutating `current` directly                                   |
| [Make a deep copy that can be changed without affecting the original](#make-a-deep-copy)               | `snapshot(value)`                                                                      | `structuredClone(value)`                                      |
| [Store or send a value as JSON text and restore it later](#store-or-send-a-value-as-json)              | `JSON.stringify(serialize(value))`, then `deserialize(JSON.parse(text), { maxBytes })` | `JSON.stringify(value)`, then `JSON.parse(text)`              |

`reconcile` changes `current`, and `deserialize` can change its input. `produce`, `snapshot`, `serialize` and [`requiredMaxBytes`](#choose-a-limit) do not change the value they receive; `snapshot` adds entries to its optional `seen` map.

```ts
import { produce, reconcile, snapshot } from '@escapace/reconcile'

const state = { user: { name: 'Ada' }, tags: ['a'] }

const copy = snapshot(state) as typeof state // copy.user is a new object; snapshot returns unknown
const next = produce(state, (draft) => {
  draft.tags.push('b')
  return draft
}) // next.user is state.user; next.tags is a new array
reconcile(state, next) // state.tags is still the same array, now ['a', 'b']
```

Reference: [Supported values](#supported-values), [Object identity](#object-identity), [Size limit](#size-limit), [Errors](#errors) and [Limitations](#limitations).

## Update objects in place

`reconcile(current, next)` updates `current` in place to match `next`. At every depth, it assigns each changed property and deletes each property that `next` lacks. The objects inside `current` stay the same objects, so code that holds them, such as components and watchers, sees the new contents.

```ts
const state = { user: { name: 'Ada' }, items: [{ id: 1 }] }
const user = state.user

reconcile(state, { user: { name: 'Grace' }, items: [{ id: 1 }, { id: 2 }] })
// state.user is still `user`, now named 'Grace'; state.items has two items
```

Values are matched by position: object properties by key, array elements by index, and `Map` and `Set` entries by insertion order. An array element is not matched by an identifier such as `id`, and a `Map` entry is not matched by its key. Inserting an element at the front of an array therefore shifts contents, not objects: each existing element object takes the contents of the element now at its index, so code that holds `items[0]` sees the new first element:

```ts
const state = { items: [{ id: 1 }, { id: 2 }] }
const first = state.items[0]

reconcile(state, { items: [{ id: 0 }, { id: 1 }, { id: 2 }] })
// state.items[0] is still `first`, now { id: 0 }
```

`Map` and `Set` entries work the same way: after a reorder, the first entry's value, key object or `Set` member stays first and takes the contents of the new first entry. To match objects by identifier, store them in a plain object keyed by identifier, not in an array, `Map` or `Set`.

- An existing object at a matched position is kept and its contents are updated. A value of a different type, such as an array where an object was, replaces it. An object that `next` adds is a new copy, except for functions and other [objects kept by reference](#objects-kept-by-reference), such as a `RegExp`.
- Only changed values are written, by ordinary assignment, so setters and watchers run only for values that changed or moved: to reach the key order of `next`, `reconcile` deletes and adds back the properties and the `Map` and `Set` entries that move. `reconcile(state, { ...state, count: 1 })` writes only `count`; [Object identity](#object-identity) gives the rule.

When `next` holds an object of `current` at a different position, the object is matched at its own position: if `next` still has that position, the object stays there and takes the contents that `next` holds there, so `next`, which holds the same object, changes too; otherwise `current` drops it unchanged. An object inside an [object already in place](#object-identity) is the exception: `current` then holds it at both positions.

When both arguments are objects that are not [kept by reference](#objects-kept-by-reference), `reconcile` returns `current`; otherwise it returns `next` and changes nothing. When `current` cannot be made to match `next`, for example because one is an object and the other an array, `reconcile` throws a `ReconcileError` of type `PublicationRejected` (see [Errors](#errors)). A failed call is not rolled back. Objects inside `current` that cannot be changed in place, such as frozen plain objects and arrays, are replaced by copies; see [`reconcile` limitations](#reconcile-limitations).

Full contract: [`reconcile`](#function-reconcile-).

## Build an updated copy

`produce(current, recipe)` passes a draft of `current` to `recipe` and returns the value the recipe returns, with drafts replaced by ordinary values. The draft behaves like `current` but records changes instead of applying them, so `produce` does not modify `current`. As with a value built by hand with spread syntax, such as `{ ...state, items: [...state.items, { id: 2 }] }`, the result shares its unchanged parts with `current`.

```ts
const state = { user: { name: 'Ada' }, items: [{ id: 1 }] }

const next = produce(state, (draft) => {
  draft.items.push({ id: 2 })
  return draft
})
// state.items still has one item; next.user is state.user; next.items is a new array
```

- The recipe must return the next value; a recipe that returns nothing produces `undefined`. It can return the draft, a part of it or any other value. If the recipe returns `current` itself, `produce` returns `current` and discards the draft's changes. The recipe must be synchronous; see [`produce` limitations](#produce-limitations).
- `produce` does not freeze the result. Because the result shares its unchanged parts, it is not detached from `current`: mutating an unchanged part also mutates `current`. `snapshot(produce(current, recipe))` returns a detached result.
- Plain objects, arrays, `Map`, `Set` and class instances become drafts, which the recipe changes by assignment, `delete` and their own methods. For dates, binary data, URLs, Temporal values and functions, see [Supported values](#supported-values).
- A draft is a different object from the one it drafts: `draft.items[0] === item` is false, but `draft.items.includes(item)` is true. See [Object identity](#object-identity).

Some changes cannot be made through a draft, such as changes to the properties of a frozen object; see [`produce` limitations](#produce-limitations).

Full contract: [`produce`](#function-produce-).

## Apply a recipe in place

To change existing objects with a recipe, and only if the recipe completes, pass the result of `produce` to `reconcile`. Only changed and moved values are written.

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

Objects are matched by position, so a recipe that reorders, inserts or removes array elements or `Map` or `Set` entries can give existing objects the contents of other elements or entries instead of moving them; see [Update objects in place](#update-objects-in-place).

`produce` finishes before `reconcile` starts, so an error in the recipe leaves `current` unchanged, apart from changes the recipe makes to objects that have no draft: `Map` key objects and [objects kept by reference](#objects-kept-by-reference). `reconcile` itself is not rolled back if it fails; see [`reconcile` limitations](#reconcile-limitations). When `current` comes from a getter or a function call, read it once into a variable, as above, and pass that variable to both functions, so that both receive the same object.

## Make a deep copy

`snapshot(value)` returns a detached deep copy of `value`: the copy can be changed without affecting the original, apart from functions and other [objects kept by reference](#objects-kept-by-reference), such as a `RegExp`, which are shared with the original, not copied.

```ts
const state = { user: { name: 'Ada' }, tags: ['a'] }
const copy = snapshot(state) as typeof state

copy.user.name = 'Grace' // state.user.name is still 'Ada'
```

`snapshot` differs from the built-in `structuredClone` as follows:

| Value                                                                 | `snapshot`                                                    | `structuredClone`                     |
| --------------------------------------------------------------------- | ------------------------------------------------------------- | ------------------------------------- |
| Class instances                                                       | Copied with the same prototype, without private fields        | Copied as plain objects               |
| Instances of subclasses of `Array`, `Map` and `Set`                   | Copied as instances of the subclass, with only their contents | Copied as instances of the base class |
| Functions                                                             | Kept by reference                                             | Throws                                |
| `URL`, `URLSearchParams` and Temporal values                          | Copied                                                        | Throws                                |
| `RegExp`, `Error`, `Blob` and boxed primitives                        | Kept by reference                                             | Copied                                |
| `Promise`, `WeakMap`, `WeakSet`, `WeakRef` and `FinalizationRegistry` | Kept by reference                                             | Throws                                |
| Properties with symbol keys                                           | Copied                                                        | Dropped                               |
| Non-enumerable properties                                             | Copied, still non-enumerable                                  | Dropped                               |
| Properties other than indexes on arrays, such as `list.label`         | Dropped; see [Limitations › All functions](#all-functions)    | Copied                                |

The rows on symbol keys and non-enumerable properties apply to plain objects and class instances. For private fields and other limits, see [Limitations › All functions](#all-functions).

Full contract: [`snapshot`](#function-snapshot-).

## Store or send a value as JSON

`serialize(value)` returns a JSON-compatible value, made of arrays, strings, finite numbers, booleans and `null`, for `JSON.stringify` to write as text. `deserialize(json, { maxBytes })` restores the value, as new objects, from the result of `JSON.parse`. Unlike `JSON.stringify` and `JSON.parse` alone, the pair preserves shared references and cycles, and supports `Map`, `Set`, `Date`, binary data, `URL`, `URLSearchParams`, Temporal values, `bigint`, `undefined`, `NaN`, `Infinity` and `-0`.

```ts
import { deserialize, serialize } from '@escapace/reconcile'

const user = { name: 'Ada' }
const state = { owner: user, members: new Map([[1, user]]), created: new Date(0), total: 10n }

const text = JSON.stringify(serialize(state))
const copy = deserialize(JSON.parse(text), { maxBytes: 1_000_000 }) as typeof state
// copy.owner === copy.members.get(1); copy.created is a Date; copy.total is 10n
```

- The JSON-compatible value does not have the shape of the original value. Only `deserialize` restores the value from it.
- `serialize` throws for a value it cannot encode, such as a class instance, a function or a property with a symbol key.
- `deserialize` can modify `json`: pass it the result of `JSON.parse` directly, and parse the text again to retry.

For the full list of rejected values, format versions and data not produced by `serialize`, see [`serialize` and `deserialize` limitations](#serialize-and-deserialize-limitations).

Full contract: [`serialize`](#function-serialize-), [`deserialize`](#function-deserialize-) and [`DeserializeOptions`](#interface-deserializeoptions-).

### Untrusted input

`maxBytes` is required. It bounds the size of the value that `deserialize` restores; to choose a limit, see [Size limit](#size-limit). Use `Infinity` only for trusted input.

To read an untrusted message, such as an HTTP request body:

1. Limit the length of the text, then parse it with `JSON.parse`.
2. Pass the result to `deserialize` with a finite `maxBytes`.
3. Validate the restored value with a schema validator.

For example, with [ArkType](https://arktype.io), which implements [Standard Schema](https://standardschema.dev):

```ts
import { type } from 'arktype'
import { deserialize } from '@escapace/reconcile'

const Message = type({ '+': 'delete', 'id': 'number', 'tags': 'string[] <= 16' })

// body is the request text, already limited in length
const result = Message(deserialize(JSON.parse(body), { maxBytes: 64_000 }))
if (result instanceof type.errors) throw new Error(result.summary)
```

`'+': 'delete'` removes keys the schema does not declare; such keys could otherwise hold any supported value, including a cycle. ArkType's `'number'` accepts `Infinity` and `-0`; constrain the type where the application does not accept them.

The validator is needed because `deserialize` checks the format of the data, not its shape: two properties can hold the same object, and any supported type can appear at any position, including values plain JSON cannot carry: `undefined`, `NaN`, `Infinity`, `-0`, a `bigint` or a hole. Choose a validator that checks a shared object once per schema, not once per reference, and that rejects cycles or handles them in bounded time; otherwise a small message that references one object many times can take a long time to validate.

For the errors `deserialize` throws, see [Errors](#errors).

## Supported values

| Value                                                                                                     | `reconcile`                  | `produce`                  | `snapshot`        | `serialize` and `deserialize` |
| --------------------------------------------------------------------------------------------------------- | ---------------------------- | -------------------------- | ----------------- | ----------------------------- |
| Primitives, including `bigint`                                                                            | Replaced by the next value   | Read and assigned normally | Returned as is    | Restored, except symbols      |
| Plain objects, `null`-prototype objects and arrays                                                        | Updated in place             | Drafted                    | Copied            | Restored                      |
| `Map` and `Set`                                                                                           | Updated in place             | Drafted                    | Copied            | Restored                      |
| Class instances                                                                                           | Updated in place             | Drafted                    | Copied            | Rejected                      |
| `Date`, `ArrayBuffer`, typed arrays, `DataView`                                                           | Updated in place or replaced | Copied when read           | Copied            | Restored                      |
| `URL` and `URLSearchParams`                                                                               | Updated in place             | Copied when read           | Copied            | Restored                      |
| Temporal values                                                                                           | Kept if equal, else replaced | Copied when read           | Copied            | Restored                      |
| Functions                                                                                                 | Kept by reference            | Kept by reference          | Kept by reference | Rejected                      |
| `RegExp`, `Error`, `Promise`, `WeakMap` and other [objects kept by reference](#objects-kept-by-reference) | Kept by reference            | Kept by reference          | Kept by reference | Rejected                      |

`reconcile`, `produce`, `snapshot`, `serialize` and `deserialize` preserve key order, sparse-array holes, shared references, cycles and the sharing between buffers and their views. A copy made by `snapshot`, `produce` or `reconcile` keeps its source's prototype, so a class instance stays an instance of its class, and an instance of a subclass of a built-in type, such as `Array` or `Map`, stays one.

### Arrays, `Map` and `Set`

In a recipe, array, `Map` and `Set` drafts work like the collections they draft. A `Map` or `Set` draft is an instance of its source's class, subclasses included. `for...of`, spreading, `forEach`, `keys`, `values` and `entries` yield each object value as its draft. A `Map` draft yields its keys as the `Map` does, not as drafts; see [`produce` limitations](#produce-limitations). `Set` methods such as `union` and `isSubsetOf` work on drafts as on a `Set`. To find an object in a draft, see [Object identity](#object-identity).

### Dates and binary data

`reconcile` updates a `Date` in place to the next time, and a buffer or view, including a `BigInt64Array` or `BigUint64Array`, to the next bytes. It replaces a buffer whose size, resizability or maximum size changes, and a view whose offset, length or type changes or whose buffer it replaces; a view it keeps keeps its own length tracking.

Reading a `Date`, `ArrayBuffer`, typed array or `DataView` from a `produce` draft gives a writable copy. If the recipe does not change a copy, the result holds the original.

A copy of a resizable buffer is resizable to the same maximum, and a view over it is copied with a fixed length. When a recipe shrinks a resizable buffer so that a fixed-length view over it no longer fits, reading that view from the draft afterwards throws a native `RangeError`, and so does `produce` when the result holds a view the recipe did not read. A typed array read before the shrink is out of bounds, with length 0, and `produce` returns it as it is; a `DataView` read before the shrink makes `produce` throw a `TypeError`. Every function that reads the bytes of a detached buffer throws a `TypeError`.

A Node.js `Buffer` is a subclass of `Uint8Array`, so `serialize` rejects it. Pass `new Uint8Array(buffer)`, which copies its bytes. Do not pass a view over `buffer.buffer`: Node.js allocates small buffers from a shared pool, so such a view can encode the whole pool.

### `URL` and `URLSearchParams`

`reconcile` updates a URL in place to the next text. Copies and restored values keep each URL linked to its own `searchParams` object, whichever appears first in the value. Parameter order, duplicate names and empty names or values are preserved.

In a recipe, a URL is copied when read. An unchanged URL and its `searchParams` stay the originals in the result, and a method called on a URL read from the draft changes only the draft, not `current`. Query spelling follows native URL behavior; for example, sorting an already sorted parameter list can change `%20` to `+`.

### Temporal values

The library recognizes Temporal values through the global `Temporal`, when it exists. It does not install or import a polyfill; a standards-compatible polyfill installed globally works. The supported classes are `Duration`, `Instant`, `PlainDate`, `PlainDateTime`, `PlainMonthDay`, `PlainTime`, `PlainYearMonth` and `ZonedDateTime`. Values from a polyfill that is not installed globally, or from another iframe or Node.js `vm` context, are not recognized; see [Limitations › All functions](#all-functions).

Copies preserve nanoseconds, calendars, time zones and reference dates. `reconcile` keeps an equal Temporal value and replaces a changed one. It compares `Duration` values by all ten components, so one second differs from 1,000 milliseconds even when their strings match. When `current` itself is a Temporal value that changed, `reconcile` throws `PublicationRejected`; see [`reconcile` limitations](#reconcile-limitations).

Temporal values are immutable. In a recipe, assign the result of methods such as `add` or `with`. A Temporal value the recipe reads but does not replace stays the original in the result; an equal value that the recipe creates stays a distinct object.

### Objects kept by reference

Some built-in objects hold data that is not stored in properties, so copying their properties cannot copy them. Like functions, they are kept by reference: a `RegExp`, `Error`, `Promise`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Blob` or `SharedArrayBuffer`, a boxed primitive such as `Object(1n)`, and an instance of a subclass of one of them, such as a custom error class. `snapshot` and `produce` keep the original, and `reconcile` assigns the next one when it is a different object. A recipe reads the value itself, so a method that changes it, such as `WeakMap.prototype.set`, changes the original. A view over a `SharedArrayBuffer` is copied over that same buffer, so writing through the copy changes the shared memory.

### Properties and class instances

The table applies to plain objects and class instances; for private fields, and for arrays and other built-in values, see [Limitations › All functions](#all-functions).

| Property                                  | `reconcile`                                                                    | `produce`                                       | `snapshot`                                  | `serialize` and `deserialize`                 |
| ----------------------------------------- | ------------------------------------------------------------------------------ | ----------------------------------------------- | ------------------------------------------- | --------------------------------------------- |
| Symbol keys                               | Updated                                                                        | Drafted                                         | Copied                                      | Rejected                                      |
| Non-enumerable properties                 | Updated; added ones stay non-enumerable                                        | Drafted; stay non-enumerable                    | Copied; stay non-enumerable                 | Rejected                                      |
| Getters and setters on the object         | Setter runs; getter and setter kept; see [limitations](#reconcile-limitations) | Run on each read and write; see below           | Getter runs once; copied as a data property | Getter runs once; restored as a data property |
| Getters and setters on the class          | Never written or overridden                                                    | Run, with the draft as `this`                   | Kept on the prototype                       | Rejected with the instance                    |
| Read-only and non-configurable properties | Attributes kept; see [limitations](#reconcile-limitations)                     | Refuse writes or deletion                       | Copied as writable and configurable         | Restored as writable and configurable         |
| Private fields                            | Kept on objects updated in place; lost on new copies                           | Kept on unchanged objects; lost on changed ones | Lost                                        | Rejected with the instance                    |

Properties that `snapshot` copies and that `reconcile` adds are writable and configurable and keep their source's enumerability, so a non-enumerable property stays hidden from `Object.keys`, spread and `JSON.stringify`. An object updated in place by `reconcile` keeps the attributes of its existing properties. In the result of `produce`, a changed object keeps its extensibility and the attributes of its existing data properties; properties the recipe adds are ordinary writable, enumerable and configurable properties.

During a `produce` recipe, getters run on every read, and assignments call setters with the draft as `this`. After the recipe returns, `produce` calls each getter in the result once. If the recipe did not change an object, and its getters return values that are unchanged in the result and are not drafts (a getter that returns `this.items[0]` returns a draft), the result keeps the original object with its getters. Otherwise it holds a new object, in which each getter is replaced by a data property holding the value it returned.

`reconcile`, `snapshot` and `deserialize` define a `__proto__` key as an own data property, so data never replaces a prototype.

## Object identity

Each function keeps or replaces objects as follows:

| Function                                      | Changes the original | Objects in the result                                                                            |
| --------------------------------------------- | -------------------- | ------------------------------------------------------------------------------------------------ |
| `reconcile(current, next)`                    | Yes, in place        | The original objects, with new contents; added objects are new, except objects kept by reference |
| `produce(current, recipe)`                    | No                   | Unchanged parts are the original objects; changed parts are new                                  |
| `snapshot(value)`                             | No                   | All new, except objects kept by reference                                                        |
| `deserialize(serialize(value), { maxBytes })` | No                   | All new                                                                                          |

- **Objects already in place.** An object in `next` that is already the object at the same position in `current` stays in place. `reconcile` reads its contents once, as part of `next`, and does not change them, so `reconcile(state, { ...state, count: 1 })` writes only `count`. The result is the same as updating it; only work is skipped. `reconcile` does not skip an object that contains `current` or `next` at any depth, or a key, value or member of a `Map` or `Set` that is not itself already in place, or anything inside one: such an object is updated like any other.
- **Drafts and `===`.** A draft is a different object from the one it drafts, and `===` compares references. Searches count a draft as the object it drafts, so they find the object whether they receive the original or its draft: `includes`, `indexOf` and `lastIndexOf` on an array draft, `has`, `add` and `delete` on a `Set` draft, `get`, `has`, `set` and `delete` on a `Map` draft, and `Set` draft methods such as `union` and `isSubsetOf`. A set these methods return holds drafts of the draft's object members.
- **Objects the recipe adds.** A change made through the draft never changes an object the recipe adds. After `draft.items.push(added)`, `draft.items.at(-1)` is a draft of `added`: a change through it goes into a copy in the result, and `added` stays unchanged. If no change is made through the draft, the result holds `added` itself.
- **Undone edits.** In `produce`, an edit that is later undone restores the original object when its whole subtree ends up equal. A new object that the recipe creates stays distinct from an equal existing one.
- **One object at two positions.** When `current` holds one object at two positions and `next` holds different objects there, `reconcile` keeps the object at the first of them in the order it reads `next`, and gives the others new objects.
- **Proxies.** Every function treats a proxy and its target as separate objects. A key that a proxy lists without a descriptor counts as absent, as in `Object.keys`, so copies and `serialize` leave it out.

## Size limit

`deserialize` requires `maxBytes` and throws `DeserializeLimitExceeded` when the value it restores would be larger. The size of a value is a byte count given by a fixed rule, not measured memory: each object counts once, however often it is referenced, and each primitive counts at every occurrence; [How size is counted](#how-size-is-counted) gives the rule.

### Choose a limit

[`requiredMaxBytes`](#function-requiredmaxbytes-) returns the smallest `maxBytes` with which `deserialize` accepts the data; for the output of `serialize`, that is the size of the value. Measure the largest legitimate values and choose a limit above the result.

```ts
const size = requiredMaxBytes(serialize(largestLegitimateState), { maxBytes: Infinity })
```

To estimate the size without `serialize`:

- For a value that holds only plain objects, arrays, strings, finite numbers, booleans and `null`, measure the largest legitimate value with `JSON.stringify`: if its text has _n_ characters, the value fits in 8 × _n_ bytes. Measure the value itself, not the output of `serialize`: that text can write one property key for many objects and omits sparse-array holes, while the size counts every key and every hole.
- For values JSON cannot carry, measure a stand-in the same way: each `Map` as an array of `[key, value]` pairs, each `Set` as an array, each `bigint` as a string, each `BigInt64Array` or `BigUint64Array` as an array of strings and `undefined` as `null`. `JSON.stringify` alone writes a `Map` or `Set` as `{}`, omits `undefined` properties and throws on a `bigint`.
- For an `ArrayBuffer`, `DataView`, `URL`, `URLSearchParams` or Temporal value, add its size from [How size is counted](#how-size-is-counted): its JSON text can be shorter than its size. `JSON.stringify` writes an `ArrayBuffer`, `DataView` or `URLSearchParams` as `{}`.

Test that the largest legitimate values deserialize under the chosen limit.

### What the limit covers

The limit bounds:

- `deserialize` itself: its time and memory are proportional to the size of its input and to `maxBytes`.
- Code that visits each object once, such as a validator that handles shared objects or the other functions of this library: its work is proportional to `maxBytes`. The bound holds for large sparse arrays, several views over one buffer and keys or bigints repeated across many objects.

The limit does not bound:

- `JSON.parse`, which runs before `deserialize`.
- Code that walks the value as a tree, such as `JSON.stringify` of the result or a recursive function without a visited set. Shared objects multiply its work. On a cycle, `JSON.stringify` throws and unguarded recursion exhausts the stack.

### How size is counted

| Part of the value                                                                                                                 | Bytes                                                     |
| --------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- |
| Each slot: the root, each array index (holes included), the key and the value of each property and `Map` entry, each `Set` member | 8                                                         |
| Each object                                                                                                                       | 8                                                         |
| Each string, wherever it occurs, including every property key of every object                                                     | 2 per UTF-16 code unit, rounded up to a multiple of 8     |
| Each `bigint`, wherever it occurs                                                                                                 | 8 per 16 hexadecimal digits of its magnitude, at least 8  |
| Each `ArrayBuffer`, typed array and `DataView`, including the buffer behind a view                                                | its byte length, rounded up to a multiple of 8            |
| Each `Date`                                                                                                                       | 8                                                         |
| Each `URL`                                                                                                                        | its text, as a string; its `searchParams` counts as below |
| Each `URLSearchParams`                                                                                                            | per entry, two slots and the two strings                  |
| Each Temporal value                                                                                                               | its text, as a string; 80 for a `Duration`                |

The rows that apply are added together. A `Date` on its own counts 24 bytes: 8 for its slot, 8 for its object and 8 for its time. Numbers, booleans, `null` and `undefined` fit their 8-byte slot. A shared object is counted once, wherever it is referenced, and a cycle adds only its references.

- A typed array or `DataView` counts its own byte length, and its buffer counts the same bytes again. A buffer with one view therefore counts about twice its byte length, and each further view over the same bytes adds them again.
- A sparse array counts every index up to its length: `a[1_000_000] = x` counts about 8 MB.

## Errors

Every failure the library detects throws a `ReconcileError`. Its `cause.type` names the failure, and the prefix of the type names the function or phase that detected it:

| Prefix         | Thrown by                            |
| -------------- | ------------------------------------ |
| `Publication`  | `reconcile`                          |
| `Draft`        | `produce`, while the recipe runs     |
| `Finalization` | `produce`, after the recipe returns  |
| `Snapshot`     | `snapshot`                           |
| `Serialize`    | `serialize`                          |
| `Deserialize`  | `deserialize` and `requiredMaxBytes` |

```ts
import { isReconcileError, reconcile } from '@escapace/reconcile'

try {
  reconcile(current, next)
} catch (error) {
  if (isReconcileError(error) && error.cause.type === 'PublicationRejected') {
    // current can hold some of the new values
  } else throw error
}
```

Error messages can change between versions; branch on `cause.type`. After `isReconcileError`, `isReconcileErrorOfType(error, type)` also narrows `cause` to that type's properties. For every type and its properties, see [`RECONCILE_ERROR_TYPES`](#const-reconcile_error_types-) and [`ReconcileErrorMetadata`](#interface-reconcileerrormetadata-).

- `reconcile` throws `PublicationRejected` when `current` cannot be made to match `next`; see [`reconcile` limitations](#reconcile-limitations).
- `produce` throws `DraftDefinePropertyUnsupported` when a recipe defines a property on an object or array draft. Its other types are rare; see [`produce`](#function-produce-).
- `snapshot` throws `SnapshotURLSearchParamsMemoIncompatible` when its optional `seen` map holds the `searchParams` of a URL in `value` but not the URL; see [`snapshot`](#function-snapshot-).
- `serialize` throws `SerializeValueUnsupported` for any value listed in [`serialize` and `deserialize` limitations](#serialize-and-deserialize-limitations).
- `deserialize` and `requiredMaxBytes` throw:
  - `DeserializeLimitInvalid` when `maxBytes` is missing or is neither a non-negative safe integer nor `Infinity`.
  - `DeserializeLimitExceeded` when the value would exceed `maxBytes`. `deserialize` can throw it before checking the rest of the data, so the error does not mean that the rest is valid. Data that is both too large and invalid can raise `DeserializeInputInvalid` or a native constructor error instead.
  - `DeserializeInputInvalid` when the data is not in the format that `serialize` produces.
  - A native constructor error, unchanged, such as the `TypeError` that `URL` throws for invalid text.

Errors thrown by recipes, getters, setters, proxy traps and iterators propagate unchanged. Native errors also propagate unchanged: allocation errors, `RangeError`s for invalid array lengths, the engine's error for nesting that exceeds the call stack, and constructor errors. For what a failed `reconcile` leaves in `current`, see [`reconcile` limitations](#reconcile-limitations).

## Limitations

### All functions

- **Built-in values carry only their contents.** Arrays, `Map`, `Set`, dates, binary data, URLs and Temporal values, including instances of their subclasses, carry only their elements, entries, time, bytes or text. Their other own properties, such as `list.label` or a field that a `Map` subclass declares, are not copied, whatever their key or enumerability:
  - `snapshot` drops them.
  - `reconcile` leaves them unchanged on an object it keeps and omits them from a new one.
  - In `produce`, only an array draft shows them. No draft or copy can set or delete them, and a changed value loses them in the result.
  - `serialize` ignores them, including symbol-keyed and non-enumerable ones, and does not call their getters.
- **Freezing does not protect contents.** Freezing a `Map`, `Set`, `Date`, buffer, view, `URL` or `URLSearchParams` value protects its properties, not its entries, time, bytes or text. `reconcile` and `produce` handle such a value as if it were not frozen: `reconcile` updates its contents in `current`, and a recipe changes them in a copy, which the result holds.
- **Overrides of built-in methods do not run.** Every function reads and writes the entries, time, bytes or text of a `Map`, `Set`, `Date`, buffer, view, `URL` or `URLSearchParams` with the built-in methods in place when this library was imported. No function calls a getter or method that a subclass or the instance defines instead of a built-in one, such as a `Map` subclass's `set` or an `entries` method on the instance, and a draft's methods do not call one either. For a change to a standard prototype, see [Standard prototypes](#standard-prototypes).
  - A subclass that keeps its entries elsewhere and overrides the methods that read them, such as an Immer draft of a `Map`, reads as empty in `snapshot`, `reconcile` and `produce`.
  - In a recipe, a method called on a copy of a `Date`, buffer, view, `URL` or `URLSearchParams` is the one the copy inherits, as in any call, so a subclass's override runs.
  - A `Set` draft method, such as `union`, reads its operand's `size`, `has` and `keys` as the built-in method does, so the operand's overrides run; see [`produce` limitations](#produce-limitations).
  - A proxy of a `Map`, `Set`, `Date`, buffer, view, `URL`, `URLSearchParams` or Temporal value has no contents of its own, and neither has an object that inherits from one of their prototypes without being that kind of value, such as `Object.create(Map.prototype)` or a `Map` given `Set.prototype`. The functions throw a `TypeError` when they read the contents. The exceptions: `snapshot`, `reconcile` and `produce` handle such a proxy or object for a typed array as a class instance, and `serialize` throws `SerializeValueUnsupported` for any of these values whose prototype belongs to a subclass, as for any subclass instance.
- **Sparse arrays.** `reconcile`, `produce`, `snapshot` and `serialize` can take time proportional to a sparse array's length, not to the number of elements it holds.
- **Proxies that wrap every read.** A proxy that wraps each object it returns in a new proxy turns a cycle in its data into endless nesting, which `snapshot`, `produce` and `serialize` cannot copy: they exceed the call stack or do not return.
- **Private fields.** `reconcile`, `produce` and `snapshot` lose the private fields of class instances that they rebuild or copy. A getter, setter or method that uses a private field throws on such a copy and on a `produce` draft, which is not the instance that holds the field. The built-in objects listed in [Objects kept by reference](#objects-kept-by-reference) are kept by reference instead.
- **Unrecognized built-in values.** The functions do not recognize the following values and handle them as class instances: a built-in value other than an array created in another JavaScript environment, such as an iframe or a Node.js `vm` context; a Temporal value from a polyfill that is not installed globally; a typed array or `DataView` over a buffer from another environment or with a replaced prototype; and a built-in object that [Supported values](#supported-values) does not list, such as an `Intl.NumberFormat` or a `Headers`. For such a value:
  - `reconcile` can leave the value's entries, time or bytes unchanged without an error, or throw `PublicationRejected`.
  - The value's built-in methods throw on a `produce` draft and on a copy made by `snapshot` or `reconcile`.
  - `serialize` rejects these values and any object from another environment, including plain objects and arrays.
- **Replaced prototypes.** The functions recognize a built-in value by its prototype chain. A `Map`, `Set`, `Date`, buffer, view, `URL`, `URLSearchParams` or Temporal value whose prototype was replaced with `null`, `Object.prototype` or the prototype of a class that is not one of these types or a subclass of one is handled as a plain object or class instance, from its own properties only. For example, `snapshot` copies a `Map` given a `null` prototype as an empty object. Given the prototype of an [object kept by reference](#objects-kept-by-reference), the value is kept by reference. A replaced prototype on a URL's `searchParams` is not supported: any function can then throw or return a wrong result, such as data from `serialize` that `deserialize` rejects.
- **Return type `unknown`.** `snapshot` and `deserialize` return `unknown`; cast the result, as the examples do.

### `reconcile` limitations

- **Matched by position, not by identifier.** Array elements and `Map` and `Set` entries are matched by index and insertion order, even when `next` moves an object of `current`; see [Update objects in place](#update-objects-in-place).
- **Not rolled back.** A failed call is not rolled back: writes made before the failure stay, so `current` can hold some of the new values. This applies to `PublicationRejected` and to errors from getters, setters and proxy traps.
- **`current` itself must be updatable.** `reconcile` throws `PublicationRejected` when it cannot update `current` itself: for example, when `current` and `next` have different types, such as an object and an array, when `current` is a Temporal value that changed, or when `current` blocks a change, as described below. For more causes, see [`reconcile`](#function-reconcile-).
- **Objects that block a change are replaced.** A change to a property is blocked by a frozen or non-extensible object, a read-only non-configurable property, a non-configurable property that `next` lacks, a getter without a setter, a setter that does not store its value, or a proxy trap that refuses an assignment or deletion or does not carry it out. A setter or trap that changes another value during the call can also block a change; `reconcile` then replaces the object that holds the value or the object whose setter made the change. An object inside `current` that blocks a change is replaced by a new copy, so code that holds the old object does not see the change.
- **Getters must not change values.** `reconcile` decides what to write from values it read earlier in the call, and checks the result only when it wrote something. A getter or proxy trap in `current` or `next` that changes a value of `current` during the call can therefore leave `current` different from `next` without an error.
- **Inherited getters and setters.** `reconcile` never writes to or overrides a getter or setter that an object inherits, such as `get fullName()` in a class or one on `Object.prototype`. When `next` has such a key as an own property and the object lacks it, `reconcile` cannot update the object in place: an object inside `current` is replaced by a new copy, and `current` itself makes `reconcile` throw `PublicationRejected` before any write. To apply data through a class setter, assign it in a `produce` recipe and reconcile the result, as in [Apply a recipe in place](#apply-a-recipe-in-place).
- **Getters and setters keep their place in key order.** A getter or setter defined on the object itself keeps its place, because JavaScript can move a property only by deleting and recreating it. Other keys are reordered around it; when the key order of `next` cannot be reached that way, the object is replaced, or `reconcile` throws when it is `current` itself, as for an inherited getter or setter.

### `produce` limitations

- **Synchronous recipes only.** A returned `Promise` is kept as it is, and the draft it resolves to is never finished. A draft kept after the recipe returns still accepts writes, but they reach neither `current` nor the result.
- **Frozen objects and read-only properties.** Because a draft follows its object's property attributes and extensibility, `produce` cannot change a property of a frozen object or a read-only property of `current`, delete a non-configurable property, or add a property to a non-extensible object, such as a sealed one. To change frozen state, pass `snapshot(state)`, whose copies are writable.
- **Assignment only.** Defining a property on an object or array draft with `Object.defineProperty`, `Object.defineProperties` or `Reflect.defineProperty` throws `DraftDefinePropertyUnsupported`; use assignment instead. `Object.freeze`, `Object.seal` and `Object.preventExtensions` throw a `TypeError` on such a draft, as does `Object.setPrototypeOf` with a different prototype.
- **`Map` keys are not drafts.** Iterating a `Map` draft yields each key as the `Map` yields it; only values are drafts. Changing a key object in a recipe changes `current`. To change a key, delete the entry and set a new one; the entry then moves to the end.
- **`Set` methods are fixed at import.** A `Set` draft implements only the `Set` methods that the runtime's `Set` had when this library was imported. A method added to `Set.prototype` later runs with the draft as `this`, so one that calls a built-in `Set` method on `this`, as a polyfill does, throws a `TypeError`; install a polyfill before importing the library.
- **A custom `has` receives drafts.** In `Set` draft methods that look members up in their operand, such as `isSubsetOf` and `difference`, a custom `has` on the operand, such as a subclass override, receives drafts and must recognize them itself. A `Set` or `Map` operand that uses the built-in `has` finds a member whether it holds the object or its draft.
- **Changed dates, buffers and URLs are not extensible.** A `Date`, buffer, view, `URL` or `URLSearchParams` value that a recipe changes is a new, non-extensible copy in the result: adding a property to it throws a `TypeError` in strict-mode code. To add properties, copy it first, for example with `new Date(value)` or `new URL(value)`.

### `serialize` and `deserialize` limitations

- **Supported values only.** `serialize` accepts plain and `null`-prototype objects, arrays, `Map`, `Set`, `Date`, fixed-length `ArrayBuffer`, typed arrays, `DataView`, `URL`, `URLSearchParams`, Temporal values and primitives other than symbols. It throws `SerializeValueUnsupported` for everything else, including:
  - class instances, and instances of subclasses of built-in types, such as a Node.js `Buffer` (see [Dates and binary data](#dates-and-binary-data))
  - symbols, and symbol-keyed or non-enumerable properties of plain and `null`-prototype objects
  - functions and other [objects kept by reference](#objects-kept-by-reference)
  - resizable buffers and views over a `SharedArrayBuffer`
- **No custom codecs or revivers.** Convert other values, such as class instances, to supported values before calling `serialize`.
- **No format version.** The data carries no format version, so both sides must use the same version of this library. Data stored for later use must therefore record the library version or a schema tag.
- **`deserialize` can modify its input.** Pass the result of `JSON.parse` or `serialize` to `deserialize` directly, and do not use it after the call, whether the call returns or throws: `deserialize` can modify it, and the result can share arrays and objects with it. To retry, parse the text again.
- **Data built by other means.** Data that does not come from `JSON.parse` or `serialize` must contain only plain arrays without extra properties and plain objects with only data properties, and must not contain the same array at more than one place. Under a finite `maxBytes`, a value of a type that `JSON.parse` cannot produce, such as `undefined`, a typed array, a `Map` or a `bigint`, is rejected.
- **The limit does not bound everything.** `maxBytes` does not bound `JSON.parse` or code that walks the result as a tree; see [What the limit covers](#what-the-limit-covers).

### Standard prototypes

Apart from the cases below, data properties, getters and setters that other code adds to `Object.prototype` or `Array.prototype` do not change the results, and objects the functions create hold their own data instead of inheriting it. The following changes are not supported:

- **Array indices.** Do not define a getter, setter or read-only property at an array index of either prototype. Native array methods such as `push` run or respect it, so any function can throw or return a wrong result. Data at an index is supported: a hole stays a hole.
- **Replaced methods.** A built-in method replaced before this library is imported takes the built-in's place in the reads and writes that [Overrides of built-in methods do not run](#all-functions) describes. The functions also call built-in methods on their own maps, arrays and strings during each call, such as `Map.prototype.get` and the global `btoa`, so a replacement that behaves differently, installed at any time, can change any result. Do not modify built-ins or prototypes during a call to `serialize` or `deserialize`, including inside getters.

Recipes, options and native code see the prototypes as ordinary JavaScript does. In a recipe, an assignment runs or respects what `Object.prototype` holds for the key, and a native array method such as `splice` reads an index that a prototype holds. Inherited properties of an options object count. Native code and proxies read the prototypes themselves and behave as they do without the library. `reconcile` treats a getter or setter on `Object.prototype` as any [inherited getter or setter](#reconcile-limitations).

**Hardened environments.** SES `lockdown()` and `node --frozen-intrinsics` are supported, and this library can be imported before or after `lockdown()`. They make some properties of `Object.prototype` read-only or replace them with a getter and setter, and an assignment in a recipe then behaves as on an ordinary object:

- **Read-only property**, such as `constructor` after `Object.freeze(Object.prototype)` or after SES `lockdown()` with its default `overrideTaming`: in strict-mode code, such as a module, the assignment throws a `TypeError`. `reconcile` still adds such a key from `next`.
- **Getter and setter**, such as `toString` after SES `lockdown()` or every method under `node --frozen-intrinsics`: the assignment adds the key. `reconcile` treats it as an [inherited getter or setter](#reconcile-limitations), so use the result of `produce` instead of reconciling such a key into `current`.

## License

[Mozilla Public License 2.0](LICENSE).

## Contributing

See the [development guide](docs/development.md) for checks, tests and benchmarks, and the [Lean guide](docs/lean.md) for the proofs and how they correspond to the runtime.

# API

## function deserialize [↗](src/deserialize.ts#L55-L57 'deserialize')

Restores a value from JSON data produced by [serialize](#function-serialize-).

```typescript
export declare function deserialize(json: unknown, options: DeserializeOptions): unknown
```

### Parameters

| Parameter | Type                                                                                           | Description                                                                                                                            |
| --------- | ---------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------- |
| `json`    | <pre>unknown</pre>                                                                             | JSON data produced by [serialize](#function-serialize-) of the same library version. The call can modify it; do not use it afterwards. |
| `options` | <pre>[DeserializeOptions](#interface-deserializeoptions- 'interface DeserializeOptions')</pre> | The size limit; see [DeserializeOptions](#interface-deserializeoptions-).                                                              |

### Returns

The restored value.

### Throws

1. [ReconcileError](#class-reconcileerror-) with type `DeserializeLimitInvalid` when `maxBytes` is invalid, `DeserializeLimitExceeded` when the value would be larger than `maxBytes`, or `DeserializeInputInvalid` when `json` is not in the format that `serialize` produces.
2. Native constructor or allocation errors, unchanged.

### Remarks

Shared references and cycles are restored. For data that `serialize` produces, every object in the result is mutable and distinct from the original value's objects, every property except an array's `length` is a writable, enumerable and configurable data property, and a `__proto__` key is an own data property. A repeated `Map` key keeps its first position and last value, and a repeated `Set` member keeps its first position, as with native insertion. Callers must not modify standard built-ins or prototypes during the call.

Pass the result of `JSON.parse` or [serialize](#function-serialize-) directly, and do not use it after the call, whether the call returns or throws: `deserialize` can modify `json`, and the result can share arrays and objects with it. To retry, parse the text again. Data that does not come from `JSON.parse` or `serialize` must contain only plain arrays without extra properties and plain objects with only data properties, and must not contain the same array at more than one place. Under a finite `maxBytes`, a value of a type that `JSON.parse` cannot produce, such as `undefined`, a typed array, a `Map` or a `bigint`, is rejected. The data carries no format version: both sides must use the same version of this library.

### Examples

```ts
const user = { name: 'Ada' }
const text = JSON.stringify(serialize({ owner: user, members: [user] }))
const copy = deserialize(JSON.parse(text), { maxBytes: 1_000_000 }) as {
  owner: object
  members: object[]
}
// copy.owner === copy.members[0]; copy.owner !== user
```

## function isReconcileError [↗](src/error.ts#L151-L152 'isReconcileError')

Returns whether `value` is a [ReconcileError](#class-reconcileerror-), narrowing its type.

```typescript
isReconcileError: (value: unknown) => value is ReconcileError
```

### Parameters

| Parameter | Type               | Description                          |
| --------- | ------------------ | ------------------------------------ |
| `value`   | <pre>unknown</pre> | Any value, typically a caught error. |

## function isReconcileErrorOfType [↗](src/error.ts#L160-L163 'isReconcileErrorOfType')

Returns whether `error` has the given `type`, narrowing `cause` to that type's properties.

```typescript
isReconcileErrorOfType: <T extends ReconcileErrorType>(error: ReconcileError, type: T)
  => error is ReconcileError<T>
```

### Parameters

| Parameter | Type                                                                       | Description                                                              |
| --------- | -------------------------------------------------------------------------- | ------------------------------------------------------------------------ |
| `error`   | <pre>[ReconcileError](#class-reconcileerror- 'class ReconcileError')</pre> | An error already known to be a [ReconcileError](#class-reconcileerror-). |
| `type`    | <pre>T</pre>                                                               | The error type to test for.                                              |

## function produce [↗](src/produce.ts#L141-L159 'produce')

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

| Parameter | Type                       | Description                                                                                                                   |
| --------- | -------------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| `current` | <pre>T</pre>               | The value to start from. `produce` does not modify it; a recipe can, through `Map` key objects and objects kept by reference. |
| `recipe`  | <pre>(draft: T) => R</pre> | Receives a draft of `current` and returns the next value.                                                                     |

### Returns

The value the recipe returned, with drafts replaced by ordinary values. A recipe that returns nothing yields `undefined`.

### Throws

1. [ReconcileError](#class-reconcileerror-) while the recipe runs: `DraftDefinePropertyUnsupported` for reflective property definition on an object or array draft, `DraftArrayLengthRejected` or `DraftArrayIndexRejected` for an array in `current`, such as a proxy, whose properties a real array could not have.
2. [ReconcileError](#class-reconcileerror-) after the recipe returns: `FinalizationAccessorUnstable` can be thrown when a getter adds a getter to a part of the result that `produce` has already visited, and `FinalizationConstructionImpossible` when no consistent result exists.
3. Errors thrown by the recipe, getters, setters or proxy traps, and native errors, such as a `RangeError` for an invalid array length or the engine's error for nesting that exceeds the call stack, propagate unchanged.

### Remarks

The draft behaves like `current` but records changes instead of applying them. The recipe returns the next value explicitly: the draft, a part of it or any other value. Drafts inside the returned value are turned back into ordinary values. A draft that the result holds only in a prototype, a closure, an object kept by reference such as a function or `Error`, or a property that a built-in value does not carry stays a draft. If the recipe returns `current` itself, its draft changes are discarded. The recipe must be synchronous: a returned `Promise` is kept as it is, and the draft it resolves to is never finished. Writes to a draft after the recipe returns reach neither `current` nor the result.

The result reuses the parts of `current` the recipe left unchanged where it can, so it is not detached from `current`; use `snapshot(produce(...))` for a detached copy. `produce` does not freeze the result. An edit that is later undone restores the original object when its whole subtree ends up equal, including key order, holes, shared references and cycles. A new object the recipe creates stays distinct from an equal existing one. A value the recipe assigns or returns from outside `current` is kept as it is, unless the recipe changes it through the draft. When the recipe assigns or returns an object from `current`, including `current` itself inside another value, the result holds it with the changes made through its draft.

Plain objects, arrays, `Map` and `Set` become drafts when the recipe reads them. Reading a `Date`, `ArrayBuffer`, `DataView` or typed array gives the recipe a writable copy; if the recipe does not change a copy, the result holds the original, and changed copies preserve their buffer sharing. A changed copy is itself the result's value, so changing it after the recipe returns changes the result. `URL` and `URLSearchParams` values are also copied when read; a URL's copy and the copy of its `searchParams` stay linked, whichever the recipe reads first. A buffer and its views, or a URL and its `searchParams`, are copied together only when the recipe changes one of them. A native method that changes the query text, such as `sort` turning `%20` into `+`, counts as a change even when the parameter entries stay equal. Temporal values are copied when read; they are immutable, so assign the value returned by their methods. A Temporal value the recipe reads but does not replace stays the original in the result.

A changed array, `Map`, `Set`, `Date`, buffer, view, URL or `URLSearchParams` value keeps its source's prototype, so an instance of a subclass stays one. Other objects, such as class instances, are drafted like plain objects: an unchanged one is kept, and a changed one is rebuilt with the same prototype and own properties but without private fields. A getter, setter or method that uses a private field throws when it runs on the draft, which is not the instance that holds the field. Primitives, including bigints, and objects kept by reference are not drafted; they are read and assigned as they are, so a method that changes such a value, such as `WeakMap.prototype.set`, changes the original. Objects kept by reference are functions, a `RegExp`, `Error`, `Promise`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Blob` or `SharedArrayBuffer`, a boxed primitive and an instance of a subclass of one of them.

Reading a value or writing an equal value back does not count as a change. During the recipe, getters run on every read and assignments call setters with the draft as `this`; `Reflect.set` with an explicit receiver calls the setter with that receiver as `this`. Reflection, such as `Object.getOwnPropertyDescriptor` or `Object.values`, returns the same draft values as ordinary reads. Defining properties on an object or array draft with `Object.defineProperty`, `Object.defineProperties` or `Reflect.defineProperty` throws `DraftDefinePropertyUnsupported`; use assignment instead. `Object.freeze`, `Object.seal` and `Object.preventExtensions` throw a `TypeError` on such a draft, as does `Object.setPrototypeOf` with a different prototype.

Arrays, `Map`, `Set`, dates, binary data, URLs and Temporal values, including instances of their subclasses, carry only their elements, entries, time, bytes or text. Their drafts and copies refuse to set or delete any other property, such as a field that a subclass declares, as a non-extensible object refuses a new one: in strict-mode code the assignment throws a `TypeError`. An array draft still shows these properties; other drafts and copies do not, and a changed value loses them in the result. A `Date`, buffer, view, URL or `URLSearchParams` value the recipe changes stays non-extensible in the result.

A draft follows its object's property attributes and extensibility: a read-only property refuses writes, a non-configurable one refuses deletion and a non-extensible object, such as a sealed one, refuses new properties, so the properties of a frozen object in `current` cannot be changed through its draft; pass `snapshot(state)` to change frozen state. In the result, a changed object other than a `Date`, buffer, view, URL or `URLSearchParams` value keeps its extensibility, a changed object other than an array keeps the attributes of its existing data properties, and properties the recipe adds are writable, enumerable and configurable. A frozen object other than an array, without getters, that is rebuilt because a child changed is therefore frozen.

After the recipe returns, each own getter in the result is called once, in depth-first order. An object that the recipe did not change, and whose getters returned values the result keeps, stays the original object with its getters; a getter that returns a draft, such as one returning `this.items[0]`, makes its object new even when nothing changed. Otherwise the object is new, and each getter is replaced by a data property that holds the value it returned and has the getter's enumerability, or, in an array, is enumerable. Inside the getter, `this` is a draft of its object: writes through `this` become part of the result, and changes to other objects take effect immediately and are not undone.

A `Map` or `Set` draft is an instance of its source's class: `instanceof`, `Symbol.toStringTag` and `constructor` work as on the source. Its methods read the original until the first change and then read and write a working copy of the same class, always with the built-in methods, so an override on a subclass or on the instance never runs. A method a subclass adds runs with the draft as `this`: it can call the draft's methods, but the subclass's constructor never initializes the draft, so `super` calls to the built-in methods and private fields throw on it, and fields the constructor sets are missing from it. Array, `Map` and `Set` drafts iterate like native collections, including `for...of`, spreading and callback methods: object values come back as drafts, a write during a walk shows up in it, and a walk that changes nothing keeps the original. `Map` keys are not drafts: a walk gives the keys as the `Map` gives them. Changing a key object changes `current`. To change a key, delete its entry and set a new one.

Draft searches count an object and its draft as the same value: `includes`, `indexOf` and `lastIndexOf` on an array draft, key lookup on a `Map` draft, and `has` and methods such as `union` on a `Set` draft. `===` in recipe code compares references, so compare such values with these methods or by a key.

`Set` draft methods return this draft's members as drafts and an operand's values as the operand gives them. An operand whose `has` is the built-in `Set` or `Map` method finds a member whether it holds the object or its draft. Any other operand's `has`, including a subclass override, receives drafts and must recognize them itself. A draft has the `Set` methods that the runtime's `Set` has when this library is imported; install a polyfill for them before importing it.

### Examples

```ts
const current = { todos: [{ done: false }], filter: 'all' }
const next = produce(current, (draft) => {
  draft.todos[0].done = true
  return draft
})
// current is unchanged; next.todos is a new array; next.filter is still 'all'
```

## function reconcile [↗](src/reconcile.ts#L99-L111 'reconcile')

Updates `current` in place to match `next`, keeping each existing object whose position in `next` holds a value of the same type.

```typescript
export declare function reconcile<T>(current: unknown, next: T): T
```

### Parameters

| Parameter | Type               | Description                                                                                                                                                     |
| --------- | ------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `current` | <pre>unknown</pre> | The value to update.                                                                                                                                            |
| `next`    | <pre>T</pre>       | The value `current` should match. `reconcile` does not write to `next` itself, but an object that `next` shares with `current` can change as part of `current`. |

### Returns

`current` when both arguments are objects that are not kept by reference, otherwise `next`.

### Throws

1. [ReconcileError](#class-reconcileerror-) with type `PublicationRejected` when `current` cannot be made to match `next`. Causes include `current` and `next` having different types, such as an object and an array; `current` itself being a changed Temporal value, which is immutable and cannot be updated in place; and `current` itself blocking a change to a property by being non-extensible or by having a read-only non-configurable property, a non-configurable property that `next` lacks, a getter without a setter, a setter that does not store its value, a proxy trap that refuses the assignment, an inherited getter or setter for a key it lacks, an own getter or setter that would have to move to reach the key order of `next`, or a value that another property's setter changes during the call. Inside `current`, such an object is replaced by a new one instead. Writes made before the failure are not rolled back.
2. Errors thrown by getters, setters or proxy traps propagate unchanged, also without rollback.

### Remarks

Values are matched by position: object properties by key, array elements by index, and `Map` and `Set` entries by insertion order. A current object at a matched position is kept and updated when the next value has the same type, such as object, array or `Map`; otherwise the position receives the next value: a primitive or an object kept by reference, such as a function, `RegExp` or `Error`, as it is, and any other object as a new copy. A kept object keeps its prototype: a class instance updated from a plain object stays an instance of its class.

When `current` holds one object at two positions and `next` holds different objects there, the object is kept at the first of them in the order `reconcile` reads `next`, and the others receive new objects. Afterwards `current` has the key order, array lengths and holes, entry order, shared references and cycles of `next`.

When `next` holds one object at two positions and `current` holds different objects there, `reconcile` keeps the current object at the first of them in the order it reads `next`. It keeps the current object at a later position instead when another object of `current` that `reconcile` can keep holds that object in a read-only non-configurable property or a getter without a setter, is a view over it or is the URL whose `searchParams` it is, so that the object holding it can be kept too.

Dates, buffers and views at matched positions take the next value's time or bytes, and buffer sharing follows `next`. A URL or `URLSearchParams` at a matched position takes the next value's text, including parameter order and duplicate names, and a URL keeps its own `searchParams` object. An equal Temporal value is kept, and a changed one at a nested position is replaced. The contents of a `Map`, `Set`, date, buffer, view, URL or `URLSearchParams` are read and written with the built-in methods, so an override on a subclass or on the instance never runs. Arrays, `Map`, `Set`, dates, binary data, URLs and Temporal values carry only their elements, entries, time, bytes or text: their other own properties, such as fields that a subclass declares, are not updated on a kept object and are not copied to a new one.

A changed own property is written by assignment, as application code writes it, so an own setter runs and an own getter or setter is kept; a configurable read-only property is redefined with the next value and keeps its attributes. An own getter or setter keeps its place in the key order, and a getter without a setter must already hold its value. `reconcile` never writes or overrides an inherited getter or setter, such as a class getter or setter. When `next` has an own key that an object lacks, and assigning it would reach such a getter or setter, that object cannot be updated in place: inside `current`, it is replaced by a new object; if it is `current` itself, the call throws before any write. A `__proto__` key is always defined as an own data property, so data never replaces a prototype. A property that `reconcile` adds is writable and configurable and takes the enumerability of the property in `next`, so a non-enumerable one stays hidden from key listing, spread and JSON; a property it keeps has its own attributes.

On an object that `reconcile` keeps and updates, an own getter for a key that `next` also has runs once when the call writes nothing and twice when it writes anything: once when `reconcile` compares its value and again when it checks the result. When the check finds that an object inside `current` blocked a change, for example through a setter that does not store its value, `reconcile` replaces that object and tries again; each retry runs the getter at most once more. These counts leave out reading `next`, which also runs the getters of any object of `current` that `next` holds, and reads that a proxy trap makes.

`next` is read completely before `current` changes. When both arguments are objects that are not kept by reference, a successful call returns `current`. When either is a primitive, a function or another object kept by reference, the call returns `next` and changes nothing.

An object in `next` that is already the object at the same property or index of the matched current object stays in place: `reconcile` reads its contents once, as part of `next`, and does not change them or read them again. `reconcile(state, { ...state, count: 1 })` therefore writes only `count`. Objects inside it stay where they are unless `next` places them elsewhere, and the final state is the same as if it had been updated. This does not apply to an object that refers to `current` or `next` at any depth, or to a key, value or member of a `Map` or `Set` that is not itself in place, or anything inside one; such an object is updated like any other.

### Examples

```ts
const state = { user: { name: 'Ada' }, tags: ['a'] }
const result = reconcile(state, { user: { name: 'Grace' }, tags: ['a', 'b'] })
// result === state; state.user and state.tags are the same objects, updated in place
```

## function requiredMaxBytes [↗](src/required-max-bytes.ts#L45-L50 'requiredMaxBytes')

Returns the smallest `maxBytes` with which [deserialize](#function-deserialize-) accepts JSON data.

```typescript
export declare function requiredMaxBytes(json: unknown, options: DeserializeOptions): number
```

### Parameters

| Parameter | Type                                                                                           | Description                                                                                    |
| --------- | ---------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------- |
| `json`    | <pre>unknown</pre>                                                                             | JSON data, as for [deserialize](#function-deserialize-). It is not modified.                   |
| `options` | <pre>[DeserializeOptions](#interface-deserializeoptions- 'interface DeserializeOptions')</pre> | The largest result to measure up to; see [DeserializeOptions](#interface-deserializeoptions-). |

### Returns

The smallest `maxBytes` that `deserialize` accepts for `json`: a multiple of 8, or `Infinity`.

### Throws

1. [ReconcileError](#class-reconcileerror-) with type `DeserializeLimitInvalid` when `maxBytes` is invalid, `DeserializeLimitExceeded` when the result would be larger than `maxBytes`, or `DeserializeInputInvalid` when `json` is not in the format that `serialize` produces.
2. Native constructor or allocation errors, unchanged.

### Remarks

`requiredMaxBytes` checks and counts `json` as [deserialize](#function-deserialize-) does under a finite `maxBytes`, without restoring the value or modifying `json`. For data that [serialize](#function-serialize-) produces, the result is the size of the restored value. For other data it can be larger, for example when a `Map` key is repeated. The result is `Infinity` when the size is larger than every finite `maxBytes`, which requires `maxBytes: Infinity`.

For data that meets the requirements of `deserialize`, `deserialize` with a finite `maxBytes` returns if and only if `maxBytes` is at least the result. The exceptions: `Object.prototype` or `Array.prototype` has a getter, setter or read-only property at an array index; a built-in method is replaced; or `deserialize` throws a native error, for example for a `Map` or `Set` larger than the engine allows.

Measuring creates each `Date`, `bigint`, view, `URL`, `URLSearchParams`, Temporal value and sparse array in the data, and allocates a buffer for each `ArrayBuffer`; `options.maxBytes` bounds that work as it bounds `deserialize`. Use `maxBytes: Infinity` only for trusted data, such as the output of `serialize`: measuring data that does not come from `JSON.parse` or `serialize` can fail to finish when it contains a cycle. Unlike `deserialize`, `requiredMaxBytes` rejects a value of a type that `JSON.parse` cannot produce, such as `undefined`, even under `Infinity`.

### Examples

```ts
const value = { name: 'Ada', tags: ['a', 'b'] }
const maxBytes = requiredMaxBytes(serialize(value), { maxBytes: Infinity }) // 112
deserialize(serialize(value), { maxBytes }) // restores the value
deserialize(serialize(value), { maxBytes: maxBytes - 1 }) // throws DeserializeLimitExceeded
```

## function serialize [↗](src/serialize.ts#L42-L44 'serialize')

Encodes a value as JSON data that [deserialize](#function-deserialize-) restores, preserving shared references and cycles.

```typescript
export declare function serialize(value: unknown): unknown
```

### Parameters

| Parameter | Type               | Description          |
| --------- | ------------------ | -------------------- |
| `value`   | <pre>unknown</pre> | The value to encode. |

### Returns

New JSON data representing the value.

### Throws

1. [ReconcileError](#class-reconcileerror-) with type `SerializeValueUnsupported` for unsupported values.
2. Errors thrown by getters or proxy traps, and native errors, propagate unchanged.

### Remarks

Plain and null-prototype objects, arrays, `Map`, `Set`, `Date`, fixed-length `ArrayBuffer`, typed arrays, `DataView`, `URL`, `URLSearchParams` and Temporal values are supported. `serialize` rejects objects with other prototypes, such as a class instance, an instance of a subclass of `Array` or a Node.js `Buffer`, because [deserialize](#function-deserialize-) restores only standard prototypes. It also rejects functions and symbols, and the symbol keys and non-enumerable properties of plain and null-prototype objects. Pass `new Uint8Array(buffer)` for a `Buffer`; a view over `buffer.buffer` can encode Node's whole allocation pool. Objects from another iframe or Node.js `vm` context are rejected, plain objects and arrays included.

`serialize` calls each getter once, in depth-first order, with the object being encoded as `this`. An array, `Map` or `Set` is encoded from its elements or entries; its other own properties, whatever their key or enumerability, are not encoded, and their getters are not called. A `Map` or `Set` is read with the built-in methods, never an override on the instance. A `Date`, buffer, view, `URL`, `URLSearchParams` or Temporal value is encoded from its built-in value; its own and overriding properties are not read and are not encoded. Callers must not modify standard built-ins or prototypes during the call, including inside getters.

The result holds only arrays, strings, finite numbers, booleans and `null`, so `JSON.stringify` writes it as text and `JSON.parse` reads it back. Only [deserialize](#function-deserialize-) restores the value from it. It carries no format version, so both sides must use the same version of this library.

### Examples

```ts
const node = { label: 'a', next: undefined as unknown, created: new Date(0) }
node.next = node
const text = JSON.stringify(serialize(node))
const copy = deserialize(JSON.parse(text), { maxBytes: 1_000_000 }) as typeof node
// copy.next === copy; copy.created is a Date
```

## function snapshot [↗](src/snapshot.ts#L103-L108 'snapshot')

Returns a deep copy of `value` that can be changed without affecting the original.

```typescript
export declare function snapshot(
  value: unknown,
  seen?: WeakMap<object, object> | undefined,
): unknown
```

### Parameters

| Parameter | Type                                             | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| --------- | ------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `value`   | <pre>unknown</pre>                               | The value to copy.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `seen`    | <pre>WeakMap\<object, object> \| undefined</pre> | Copies to use for source objects. `snapshot` uses each entry as given, without checking it, and adds an entry for every object it copies. The result is detached only if every supplied entry is a detached copy of its source. Map a URL and its `searchParams` together, to a copy whose `searchParams` is the mapped entry, or map neither. Mapping only the `searchParams` of a URL in `value` throws `SnapshotURLSearchParamsMemoIncompatible`. Mapping only the URL leaves a copy of its `searchParams` elsewhere in the result unlinked from the mapped URL. |

### Returns

A copy of `value`, detached unless `seen` supplies entries that are not, or `value` itself when it is not an object.

### Throws

1. [ReconcileError](#class-reconcileerror-) with type `SnapshotURLSearchParamsMemoIncompatible` when `seen` maps the `searchParams` of a URL in `value` but not the URL.
2. Errors thrown by getters or proxy traps propagate unchanged.

### Remarks

The copy preserves plain-object key order and prototypes, sparse-array holes, shared references, cycles, the link between each URL and its `searchParams` object and the sharing between buffers and their views. Plain objects, arrays, `Map`, `Set`, `Date`, `ArrayBuffer`, `DataView`, typed arrays, `URL`, `URLSearchParams` and Temporal values are supported.

Primitives, including bigints, are returned as they are. Objects kept by reference are shared with the original: functions, a `RegExp`, `Error`, `Promise`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Blob` or `SharedArrayBuffer`, a boxed primitive and an instance of a subclass of one of them. A view over a `SharedArrayBuffer` is copied over that same buffer. Temporal support uses the eight value classes on the current global `Temporal` namespace, without installing a polyfill. Other objects, such as class instances, are copied like plain objects. The copy has the same prototype and own properties, as writable, configurable data properties that keep their enumerability. It has no private fields, so a getter or method that uses one throws on the copy. The entries, time, bytes or text of a `Map`, `Set`, `Date`, buffer, view, URL or `URLSearchParams` are read, and its copy filled, with the built-in methods, so no override on a subclass or on the instance runs, such as a `Map` subclass's `set` or `entries`. A copy of an array, `Map`, `Set`, `Date`, buffer, view, URL, `URLSearchParams` or Temporal value also keeps its source's prototype, so an instance of a subclass stays one, but it holds only the elements, entries, time, bytes or text, without other own properties such as fields that a subclass declares.

A copied object that relies on functions can still run code that belongs to the original. A `__proto__` key is copied as an own data property. Built-in values from another iframe or Node.js `vm` context, such as a `Map`, `Date` or `RegExp`, are not recognized and are copied like class instances, so the copy's built-in methods throw. Arrays from another context are copied as arrays.

### Examples

```ts
const node = { label: 'a', children: [] as unknown[] }
node.children.push(node)
const copy = snapshot(node) as typeof node
// copy !== node; copy.children[0] === copy
```

## class ReconcileError [↗](src/error.ts#L126-L144 'ReconcileError')

The error this library throws for every failure it detects.

```typescript
export declare class ReconcileError<T extends ReconcileErrorType = ReconcileErrorType> extends Error
```

### Remarks

Its `cause` holds a stable `type` and that type's properties. Its message is for people and can change between versions. Check for it with `instanceof ReconcileError` or [isReconcileError](#function-isreconcileerror-), then branch on `cause.type`.

Errors from native constructors and allocation, and errors thrown by application getters, setters, proxy traps, iterators and writes into `current`, propagate unchanged. When an error interrupts `reconcile`, earlier writes are not rolled back.

### Examples

```ts
try {
  reconcile(current, next)
} catch (error) {
  if (isReconcileError(error) && error.cause.type === 'PublicationRejected') {
    // current can hold some of the new values
  } else throw error
}
```

### new ReconcileError

Creates an error. The library creates these errors; applications inspect them.

```typescript
constructor(cause: ReconcileErrorCause<T>, message: string);
```

#### Parameters

| Parameter | Type                                                                                        | Description                                                |
| --------- | ------------------------------------------------------------------------------------------- | ---------------------------------------------------------- |
| `cause`   | <pre>[ReconcileErrorCause](#type-reconcileerrorcause- 'type ReconcileErrorCause')\<T></pre> | The error's `type` and that type's properties.             |
| `message` | <pre>string</pre>                                                                           | A description for people; not part of the stable contract. |

### ReconcileError.cause

The error's `type` and that type's properties.

```typescript
readonly cause: ReconcileErrorCause<T>;
```

### ReconcileError.name

Always `'ReconcileError'`.

```typescript
readonly name: 'ReconcileError';
```

## const RECONCILE\_ERROR\_TYPES [↗](src/error.ts#L12-L24 'RECONCILE_ERROR_TYPES')

Every error type this library throws.

```typescript
RECONCILE_ERROR_TYPES: readonly[
  ('DeserializeInputInvalid',
  'DeserializeLimitExceeded',
  'DeserializeLimitInvalid',
  'DraftArrayIndexRejected',
  'DraftArrayLengthRejected',
  'DraftDefinePropertyUnsupported',
  'FinalizationAccessorUnstable',
  'FinalizationConstructionImpossible',
  'PublicationRejected',
  'SerializeValueUnsupported',
  'SnapshotURLSearchParamsMemoIncompatible')
]
```

### Remarks

The prefix of each name identifies the function or phase that detects the failure. `Draft` types come from `produce` while the recipe runs, `Finalization` types from `produce` after the recipe returns, `Publication` types from `reconcile`, `Snapshot` types from `snapshot`, `Serialize` types from `serialize`, and `Deserialize` types from `deserialize` and `requiredMaxBytes`.

## interface DeserializeOptions [↗](src/deserialize.ts#L5-L12 'DeserializeOptions')

Options for [deserialize](#function-deserialize-).

```typescript
export interface DeserializeOptions
```

### DeserializeOptions.maxBytes

The largest size, in bytes, of the value `deserialize` may return: a non-negative safe integer, or `Infinity` for trusted input only. Each object counts once, however often it is referenced, and each primitive counts at every occurrence.

```typescript
readonly maxBytes: number;
```

## interface ReconcileErrorMetadata [↗](src/error.ts#L35-L97 'ReconcileErrorMetadata')

The properties of `cause` for each error type, in addition to `type`.

```typescript
export interface ReconcileErrorMetadata
```

### Remarks

Creating an error runs no application code, such as getters, setters or proxy traps.

### ReconcileErrorMetadata.DeserializeInputInvalid

The data passed to `deserialize` or `requiredMaxBytes` is not in the format that `serialize` produces. `reason` names the failed check for diagnostics; its values are not part of the API and can change.

```typescript
DeserializeInputInvalid: {
  reason: string
}
```

### ReconcileErrorMetadata.DeserializeLimitExceeded

The value `deserialize` would return is larger than `maxBytes` allows, or `requiredMaxBytes` would return more than `maxBytes`. `maxBytes` is the limit; the error does not report the size of the value.

```typescript
DeserializeLimitExceeded: {
  maxBytes: number
}
```

### ReconcileErrorMetadata.DeserializeLimitInvalid

`maxBytes` is missing, or is neither a non-negative safe integer nor `Infinity`. `maxBytes` is the value received.

```typescript
DeserializeLimitInvalid: {
  maxBytes: unknown
}
```

### ReconcileErrorMetadata.DraftArrayIndexRejected

An array in `current`, such as a proxy, reported an index at or beyond a non-writable length, which a real array cannot have. `index` is that index.

```typescript
DraftArrayIndexRejected: {
  index: number
}
```

### ReconcileErrorMetadata.DraftArrayLengthRejected

An array in `current`, such as a proxy, reported a length that its other properties make impossible. `length` is the reported length.

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

### ReconcileErrorMetadata.FinalizationAccessorUnstable

A getter that ran after the recipe returned added a new getter to a part of the result that `produce` had already visited, so `produce` cannot call it. `property` is the new getter's key.

```typescript
FinalizationAccessorUnstable: {
  property: PropertyKey
}
```

### ReconcileErrorMetadata.FinalizationConstructionImpossible

No consistent result exists: the new objects cannot be created in any order, or a `Map` or `Set` would hold one new object as two keys or members.

```typescript
FinalizationConstructionImpossible: {
}
```

### ReconcileErrorMetadata.PublicationRejected

`reconcile` could not make `current` match `next`. Writes made before the failure are not rolled back.

```typescript
PublicationRejected: {
}
```

### ReconcileErrorMetadata.SerializeValueUnsupported

`serialize` met a value it cannot encode, such as a symbol-keyed property, a function or an object of an unsupported class. `reason` names it for diagnostics; its values are not part of the API and can change.

```typescript
SerializeValueUnsupported: {
  reason: string
}
```

### ReconcileErrorMetadata.SnapshotURLSearchParamsMemoIncompatible

The `seen` map passed to `snapshot` maps the `searchParams` of a URL in the value but not the URL.

```typescript
SnapshotURLSearchParamsMemoIncompatible: {
}
```

## type ReconcileErrorCause [↗](src/error.ts#L100-L101 'ReconcileErrorCause')

The `cause` of a [ReconcileError](#class-reconcileerror-): its `type` and that type's properties.

```typescript
export type ReconcileErrorCause<T extends ReconcileErrorType = ReconcileErrorType> = T
  extends ReconcileErrorType ? {
  type: T;
} & ReconcileErrorMetadata[T] : never;
```

## type ReconcileErrorType [↗](src/error.ts#L27 'ReconcileErrorType')

The `type` of a [ReconcileError](#class-reconcileerror-): one of [RECONCILE\_ERROR\_TYPES](#const-reconcile_error_types-).

```typescript
export type ReconcileErrorType = (typeof RECONCILE_ERROR_TYPES)[number]
```
