/** Shared immutable empty facts; callers must never append to this value. */
export const EMPTY_FACTS: readonly never[] = /* @__PURE__ */ Object.freeze([])

/** Replacement decisions for special values that cannot retain their source identity. */
export const SPECIAL_REPLACEMENT = /* @__PURE__ */ Object.freeze({
  // eslint-disable-next-line no-useless-computed-key -- Runtime provenance strings require this key to remain unmangled.
  ['base']: 'copy',
  untracked: 'fresh',
} as const)

/** Marks a slot an own getter answered. A rebuilt object holds its value as a writable,
 * configurable data property with the getter's enumerability; a rebuilt array as an element. */
export const OBSERVED_ACCESSOR = 8

/** The plain-object fallback kind. */
export const OBJECT_KIND = Symbol('object')

/**
 * Kind of an object whose state lives in internal slots that copying own properties loses: a
 * `RegExp`, `Error`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Promise`, boxed
 * primitive, `Blob` or `SharedArrayBuffer`, or an instance of a subclass. Like functions, such atoms are kept by
 * reference and never drafted or copied. Ingress recognition (`recognize` in
 * `src/adapters/recognition.ts`) returns this kind in place of the plain-object fallback; no
 * registry table holds facets for it except `produce`'s leaf entry.
 *
 * @internal
 */
export const ATOM_KIND = Symbol('atom')

/**
 * Marks a slot whose value the call has not read, or whose read no longer holds, as for a key
 * moved before it is published; no value of `current` is this private object.
 */
export const UNREAD: object = /* @__PURE__ */ Object.freeze(Object.create(null) as object)
