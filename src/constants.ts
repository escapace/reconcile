/** Private brand installed by the typed module constructor. */
export const MODULE_BRAND: unique symbol = /* @__PURE__ */ Symbol.for(
  '@escapace/reconcile/type-module',
)

/** Version of the finite identity, storage, and implication vocabulary shared by all modules. */
export const RULE_VOCABULARY = 'identity-storage-requires-v1' as const

/** Shared immutable empty facts; callers must never append to this value. */
export const EMPTY_FACTS: readonly never[] = /* @__PURE__ */ Object.freeze([])

/** Nonnegative signed-integer bits reserved for compact exposure claims. */
export const CLAIM_BIT_COUNT = 31

/** Finite exposure modes admitted by the built-in wrapper adapter. */
export const EXPOSURE_MODES: readonly number[] = /* @__PURE__ */ Object.freeze([
  0, 1, 2, 3, 4, 5, 6, 7, 8,
])

/** Replacement decisions for special values that cannot retain their source identity. */
export const SPECIAL_REPLACEMENT = /* @__PURE__ */ Object.freeze({
  // eslint-disable-next-line no-useless-computed-key -- Runtime provenance strings require this key to remain unmangled.
  ['base']: 'copy',
  untracked: 'fresh',
} as const)
