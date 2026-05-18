# @escapace/reconcile

Supports three operations over JavaScript objects, arrays, maps, and sets. `snapshot(...)` creates a detached snapshot. `createPatch(...)` runs draft-style code and returns the finalized next value, while `reconcile(...)` applies a next value onto an existing one by reusing compatible structure instead of replacing everything. `patch(...)` is the convenience form that combines `createPatch(...)` with `reconcile(...)`. For supported values, the runtime preserves plain-object key order, sparse-array holes, cycles, shared references, and `ArrayBuffer` or view aliasing. It also supports Vue reactive proxies and alien-deepsignals objects.

## Immer

`createPatch(...)` is the closest match in this package to Immer's `produce(...)`: both run draft-style code and return a next value instead of mutating the current input directly. This package also exposes `snapshot(...)` for detached snapshots and `reconcile(...)` for applying a next value onto existing live structure. Support also extends beyond plain JavaScript objects to common reactive or signal-backed wrappers that behave like objects, arrays, maps, or sets.

| Topic                    | `createPatch(...)`                                                                          | Immer `produce(...)`                                             |
| ------------------------ | ------------------------------------------------------------------------------------------- | ---------------------------------------------------------------- |
| Data structures          | Plain objects, arrays, `Map`, `Set`                                                         | Plain objects, arrays; `Map` and `Set` with `enableMapSet()`     |
| Returned value           | Next value; structural sharing; not frozen; use `snapshot(createPatch(...))` for detachment | Next state; structural sharing; auto-frozen by default           |
| Recipe return            | Draft root, nested draft value, or replacement value                                        | Draft or replacement value; modified child draft return rejected |
| Repeated references      | Supported                                                                                   | Out of scope                                                     |
| Cycles                   | Supported                                                                                   | Out of scope                                                     |
| Primitive `Map` keys     | Supported; ordinary key behavior                                                            | Supported; ordinary key behavior                                 |
| Non-primitive `Map` keys | Update coherently                                                                           | Keys never drafted                                               |
| `Date`                   | Clone-on-read; direct mutation publishes                                                    | Not drafted; replace with a new `Date`                           |
| Binary values            | `ArrayBuffer`, `DataView`, typed arrays; clone-on-read; aliasing preserved                  | Not drafted                                                      |
| Array iteration          | Native iteration works                                                                      | Native iteration works                                           |
| `Map` / `Set` iteration  | Iterator and callback APIs out of scope                                                     | Iterator and callback APIs available with `enableMapSet()`       |

## How `patch(...)` and `reconcile(...)` reuse existing values

`createPatch(...)` computes a next value. `patch(...)` and `reconcile(...)` then apply that next value onto existing JavaScript values, reusing existing objects and collections where possible instead of replacing everything.

| Value                                       | Matched by                | What to expect                                                                                                                                    |
| ------------------------------------------- | ------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| Primitive values and functions              | direct value or reference | Different primitives replace the current value. Functions are kept by reference.                                                                  |
| Plain objects                               | property key              | Key `a` is updated from `next.a`, key `b` from `next.b`, and so on. The result uses the next object's own-key order.                              |
| Arrays                                      | index                     | Index `0` is updated from `next[0]`, index `1` from `next[1]`, and so on. The result uses the next array's length and preserves sparse holes.     |
| `Map`                                       | entry order               | The first current entry is updated from the first next entry, the second from the second, and so on. The result iterates in the next map's order. |
| `Set`                                       | entry order               | The first current value is updated from the first next value, the second from the second, and so on. The result iterates in the next set's order. |
| `Date`                                      | the value itself          | The result matches the next timestamp. Shared `Date` references stay shared.                                                                      |
| `ArrayBuffer`, typed arrays, and `DataView` | the value itself          | The result matches the next bytes, view type, and shared backing-buffer relationships.                                                            |

Reordering follows the kind of JavaScript value being updated: arrays by index, objects by key, and maps and sets by entry order. Existing identities can therefore stay in place while their contents change to match the next value.

Across the whole value:

- Shared references in the next value stay shared in the result.
- Distinct references in the next value stay distinct, even when they look equal.
- Cycles stay intact.
- Buffer and view sharing follows the next value.
- `createPatch(...)` returns a finalized next value, not a detached copy. Use `snapshot(createPatch(...))` when detachment is required.

The same rules apply to wrappers that behave like objects, arrays, maps, or sets, including Vue reactive proxies and alien-deepsignals objects.

# API

## function createPatch [↗](src/patch.ts#L1250-L1281 'createPatch')

Runs `recipe` against a temporary writable draft of `current` and returns the resulting next value without applying it back onto `current`.

```typescript
export declare function createPatch<T, R>(current: T, recipe: (draft: T) => R): R
```

### Parameters

| Parameter | Type                       | Description                                                                   |
| --------- | -------------------------- | ----------------------------------------------------------------------------- |
| `current` | <pre>T</pre>               | Existing value.                                                               |
| `recipe`  | <pre>(draft: T) => R</pre> | Receives a temporary writable draft of `current` and computes the next value. |

### Returns

The next value produced by the recipe.

### Throws

When the recipe calls out-of-scope `Map` or `Set` draft iterator or callback APIs.

### Remarks

`createPatch(...)` is the draft-building half of `patch(...)`. It gives `recipe` a temporary draft that can be mutated like ordinary JavaScript data, then returns the next value produced by that recipe. The recipe may return the draft root, a nested draft value, or any replacement value. Draft values created by this call are turned back into ordinary JavaScript values before return. If a replacement value contains nested draft values created by this call, those nested draft values are also turned back into ordinary JavaScript values before return. A non-draft return wins over draft mutations. Returning `current` by reference discards draft mutations and returns the original value.

Supported values match `snapshot(...)` and `reconcile(current, next)`. Plain objects, arrays, `Map`, and `Set` are drafted structurally. `Set` drafts keep normal set membership behavior within one recipe. When the recipe reads a `Date`, `ArrayBuffer`, `DataView`, or typed array, it sees a writable copy rather than a partially wrapped live value. If that copy is left unchanged, the result reuses the original `Date`, buffer, or view references. If it is changed, the result contains changed copies and preserves `ArrayBuffer` or view aliasing. Primitive values and functions are treated as single values. Other object types, including many class instances or prototype-bearing values, are handled on a best-effort basis rather than rejected up front.

For plain objects, arrays, `Map`, and `Set`, reads do not mark changes, and writing the same value back does not count as a change. Once a real change happens on one draft node, later writes do not restore that node to the original reference, even if the final contents match `current` again.

The returned value is not frozen and it is not guaranteed to be detached from `current`. Untouched subtrees may stay shared. Supported results preserve plain-object key order, sparse-array holes, cycles, shared references, and `ArrayBuffer` or view aliasing. The same behavior also applies to common reactive or signal-backed wrappers when they expose object, array, map, or set behavior.

Array drafts support normal array iteration, including `for...of`, `entries()`, `keys()`, `values()`, and callback-style array methods. `Map` and `Set` draft `keys()`, `values()`, `entries()`, `[Symbol.iterator]()`, and `forEach()` are out of scope and throw when called.

`createPatch(...)` is appropriate when a next value is needed without applying it back onto the existing value. `snapshot(createPatch(...))` produces a detached copy. `patch(...)` applies the result through `reconcile(current, next)`.

## function patch [↗](src/patch.ts#L1320-L1322 'patch')

Runs `recipe` against a temporary writable draft of `current`, then applies the resulting next value back onto `current` through `reconcile(...)`.

```typescript
export declare function patch<T, R>(current: T, recipe: (draft: T) => R): R
```

### Parameters

| Parameter | Type                       | Description                                                                   |
| --------- | -------------------------- | ----------------------------------------------------------------------------- |
| `current` | <pre>T</pre>               | Existing value.                                                               |
| `recipe`  | <pre>(draft: T) => R</pre> | Receives a temporary writable draft of `current` and computes the next value. |

### Returns

The value after the recipe result has been applied through `reconcile(current, next)`.

### Throws

When the recipe calls out-of-scope `Map` or `Set` draft iterator or callback APIs.

### Remarks

`patch(...)` is the convenience wrapper around `createPatch(...)` and `reconcile(current, next)`. It is equivalent to `reconcile(current, createPatch(current, recipe))`. The same recipe return rules as `createPatch(...)` apply: the recipe may return the draft root, a nested draft value, or any replacement value. If a replacement value contains nested draft values created by this call, those nested draft values are turned back into ordinary JavaScript values before publication. A non-draft return wins over draft mutations. Returning `current` by reference discards draft mutations and returns the original value.

Supported values, draft behavior, and exclusions match `createPatch(...)`. Plain objects, arrays, `Map`, and `Set` are drafted structurally. `Date`, `ArrayBuffer`, `DataView`, and typed arrays use the same copy-on-read behavior. Other object types, including many class instances or prototype-bearing values, are handled on a best-effort basis rather than rejected up front. The same behavior also applies to common reactive or signal-backed wrappers when they expose object, array, map, or set behavior. Array drafts support normal array iteration, including `for...of`, `entries()`, `keys()`, `values()`, and callback-style array methods. `Map` and `Set` draft `keys()`, `values()`, `entries()`, `[Symbol.iterator]()`, and `forEach()` are out of scope and throw when called.

After the recipe finishes, `patch(...)` applies the next value through `reconcile(current, next)`. That means existing objects and collections may be kept when they can be updated in place. The result preserves plain-object key order, sparse-array holes, cycles, shared references, and `ArrayBuffer` or view aliasing. Because the next value is applied through `reconcile(current, next)`, `patch(...)` may return `current` even when `createPatch(...)` would return a fresh but equivalent next value.

`createPatch(...)` is appropriate when a next value is needed without applying it back onto the existing value. `snapshot(createPatch(...))` produces a detached copy.

## function reconcile [↗](src/reconcile.ts#L1049-L1082 'reconcile')

Applies `next` onto `current` by updating existing objects and collections when possible.

```typescript
export declare function reconcile<T>(current: unknown, next: T): T
```

### Parameters

| Parameter | Type               | Description                                  |
| --------- | ------------------ | -------------------------------------------- |
| `current` | <pre>unknown</pre> | Existing value to update.                    |
| `next`    | <pre>T</pre>       | Next value to apply onto the existing value. |

### Returns

The updated value. This is usually `current`, but it may be `next` or a replacement subtree when in-place update is not possible.

### Remarks

`reconcile(...)` tries to keep existing identities when the current value can be updated to match the next value. Arrays update by index and preserve sparse holes from `next`. Plain objects update by property key and adopt the next object's own-key order. `Map` and `Set` update by entry order, not by matching keys or values. `Date`, `ArrayBuffer`, `DataView`, and typed arrays update in place only when their published shape stays compatible.

The result matches the observable structure of `next`, including plain-object key order, sparse-array holes, cycles, shared references, and `ArrayBuffer` or view aliasing. When one subtree cannot be updated in place, only that subtree is replaced; surrounding parent values may still be reused.

Supported values include plain JavaScript objects, arrays, maps, sets, `Date`, `ArrayBuffer`, `DataView`, and typed arrays. The same behavior also applies to common reactive or signal-backed wrappers when they expose object, array, map, or set behavior. Descriptor-level details are not preserved on every path; for example, accessors may keep existing behavior, and retained non-configurable keys may not be removed even when `next` does not contain them.

Primitive values are handled directly. If either root is not object-like, or if the root kinds differ, the function returns `next`.

## function snapshot [↗](src/snapshot.ts#L36-L51 'snapshot')

Creates a detached snapshot of `value`.

```typescript
export declare function snapshot(value: unknown, seen?: WeakMap<object, object>): unknown
```

### Parameters

| Parameter | Type                                | Description                                                                                                                    |
| --------- | ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| `value`   | <pre>unknown</pre>                  | Value to snapshot.                                                                                                             |
| `seen`    | <pre>WeakMap\<object, object></pre> | Memoization table that preserves cycles and shared references during recursive traversal. Callers usually omit this parameter. |

### Returns

A detached snapshot that can be mutated without affecting the source value, or the original primitive value when the input is non-object-like.

### Remarks

`snapshot(...)` clones supported objects and collections so the result can be changed without affecting the source value. It preserves plain-object key order, sparse-array holes, cycles, shared references, object prototypes, and `ArrayBuffer` or view aliasing.

Supported values include plain objects, arrays, maps, sets, `Date`, `ArrayBuffer`, `DataView`, and typed arrays. The same behavior also applies to common reactive or signal-backed wrappers when they expose object, array, map, or set behavior. Primitive values are returned unchanged. Function values are kept by reference rather than cloned.
