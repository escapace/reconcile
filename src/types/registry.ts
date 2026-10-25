import type {
  CopyType,
  DraftState,
  DraftStrategy,
  ModuleInput,
  ModuleShape,
  NativePolicy,
  SpecialPolicy,
  StructuralType,
  TypeModule,
  TypeRegistry,
} from '../types'

import { MODULE_BRAND } from '../constants'

/** Copies and freezes typed module facets before registry composition. */
export function defineType<
  L extends { readonly kind: symbol },
  S extends { readonly kind: L['kind'] } & DraftState = { readonly kind: L['kind'] } & DraftState,
>(module: ModuleInput<StructuralType<L, S>>): StructuralType<L, S>
export function defineType<L extends { readonly kind: symbol }>(
  module: ModuleInput<CopyType<L>>,
): CopyType<L>
export function defineType<L extends { readonly kind: symbol }, S extends DraftState = DraftState>(
  module: ModuleInput<TypeModule<L, S>>,
): TypeModule<L, S> {
  const result = Object.freeze({
    ...module,
    draft: Object.freeze(
      module.draft.tag === 'copy'
        ? { ...module.draft, links: Object.freeze({ ...module.draft.links }) }
        : { ...module.draft },
    ),
    [MODULE_BRAND]: true as const,
    policy: Object.freeze({
      ...module.policy,
      bindings: Object.freeze({ ...module.policy.bindings }),
      immutable: Object.freeze(
        module.policy.immutable.tag === 'copy'
          ? {
              ...module.policy.immutable,
              operations: Object.freeze({ ...module.policy.immutable.operations }),
            }
          : { ...module.policy.immutable },
      ),
    }),
    recognition: Object.freeze({ ...module.recognition }),
    requires: Object.freeze([...(module.requires ?? [])]),
  })
  return result
}

/**
 * Composes immutable module facets with ordered recognition and kind-indexed dispatch.
 *
 * @remarks
 * Only this boundary erases native payload types. Known-kind checks evaluate the recognition
 * prefix to preserve precedence; captured kinds dispatch directly without repeating recognition.
 * Composition is trusted internal configuration: tests must establish unique symbol identities, exactly one final fallback, and all declared dependencies.
 * Names and symbol descriptions are diagnostic only. TypeScript checks required operations and matching draft/immutable representations.
 * Native callback semantics remain correspondence obligations; no configuration validation
 * runs here. Copying the array preserves recognition order after caller mutation.
 */
export function registerTypes<const M extends readonly ModuleShape[]>(modules: M) {
  const entries = [...modules]
  const policies: Record<symbol, NativePolicy> = {}
  const drafts: Record<symbol, DraftStrategy> = {}
  const structural: Record<symbol, Extract<NativePolicy['immutable'], { tag: 'structural' }>> = {}
  const specials: Record<symbol, SpecialPolicy | undefined> = {}
  for (const module of entries) {
    const policy = module.policy as NativePolicy
    const draft = module.draft as DraftStrategy
    policies[module.kind] = policy
    if (policy.immutable.tag === 'structural') structural[module.kind] = policy.immutable
    else specials[module.kind] = policy.immutable.operations
    drafts[module.kind] = draft
  }
  return Object.freeze({
    drafts: Object.freeze(drafts),
    policies: Object.freeze(policies),
    specials: Object.freeze(specials),
    structural: Object.freeze(structural),
    ...registerRecognition(entries),
  }) satisfies TypeRegistry
}

/** Preserves ordered predicate observations independently of the native operation facets. */
function registerRecognition<
  const M extends ReadonlyArray<Pick<ModuleShape, 'kind' | 'recognition'>>,
>(entries: M) {
  const positions = new Map(entries.map((module, index) => [module.kind, index]))
  const firstMatch = (value: object, last: number): M[number]['kind'] | undefined => {
    for (let index = 0; index <= last; index += 1) {
      const module = entries[index]
      if (module.recognition.tag === 'fallback' || module.recognition.test(value))
        return module.kind
    }
    return undefined
  }
  return {
    /** Validates a known kind against its recognition prefix, preserving precedence. */
    matches(kind: symbol, value: object): boolean {
      const last = positions.get(kind)
      return last !== undefined && firstMatch(value, last) === kind
    },
    recognize(value: object): M[number]['kind'] | undefined {
      return firstMatch(value, entries.length - 1)
    },
  }
}

/**
 * Explicit development probe; production recognition stops at the first match.
 *
 * @remarks
 * Kept outside the registry object so production bundles do not carry it.
 */
export function diagnoseRecognition<const M extends readonly ModuleShape[]>(
  modules: M,
  value: object,
): { ambiguous: boolean; matches: Array<{ kind: symbol; name: string }>; selected: symbol } {
  const matches = modules
    .filter((module) => module.recognition.tag === 'predicate' && module.recognition.test(value))
    .map((module) => ({ kind: module.kind, name: module.name }))
  return {
    ambiguous: matches.length > 1,
    matches,
    selected: matches[0]?.kind ?? modules.at(-1)!.kind,
  }
}
