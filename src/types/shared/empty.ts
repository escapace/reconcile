import type { BoundEdge } from '../../types'

import { EMPTY_FACTS } from '../../constants'
export const noChildren = (): boolean => false
export const emptyEdges = (): readonly BoundEdge[] => EMPTY_FACTS

export const noDependencies = (): boolean => true

export const noValue = (): undefined => undefined

/** Accepts every candidate; shared by kinds without compatibility work. */
export const yes = (): boolean => true

/** Returns the sealed node unchanged; shared by kinds without derived indexes. */
export const same = <T>(node: T): T => node

/** Shared construction facet for kinds whose fresh targets need no earlier allocations. */
export const independentBindings = /* @__PURE__ */ freeze({ tag: 'independent' } as const)

/** Shared readonly configuration; these objects never contain native values or call state. */
export const ordinaryExposure = /* @__PURE__ */ freeze({ tag: 'ordinary' } as const)
export const independentDraft = /* @__PURE__ */ freeze({
  links: /* @__PURE__ */ freeze({ tag: 'independent' }),
  tag: 'copy',
} as const)

/** Freezes private configuration while keeping its initialization calls independently removable. */
export function freeze<const T>(value: T): Readonly<T> {
  return Object.freeze(value)
}
