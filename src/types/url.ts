import { adoptPrototype } from './shared/prototype'
import { inChain, isObject } from '../object-property'
import { freeze, noValue, same } from './shared/empty'
import { defineType } from './registry'
import { finalizationConstructionImpossible } from '../error'
import {
  URL_KIND,
  adoptURLCarrier,
  carrierFromResponse,
  nativeURLHref,
  nativeURLSearchParameters,
  setNativeURLHref,
} from './shared/url-carrier'
import { URL_SEARCH_PARAMS_KIND } from './url-search-parameters'
import { snapshotURLSearchParametersMemoIncompatible } from '../error'
import type {
  CapturePolicy,
  SnapshotPolicy,
  Recognition,
  ConstructionPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  SpecialPolicy,
  CapturedNode,
  DraftStrategy,
} from '../types'

export { URL_KIND } from './shared/url-carrier'

/** Captures owner serialization and its native parameter-storage carrier. */
export interface URLLayout {
  readonly carrier: URL
  readonly href: string
  readonly kind: typeof URL_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
}

const urlCapture = {
  construction: noValue,
  observe(value, begin, edge, mode) {
    const url = value as URL
    const prototype = Object.getPrototypeOf(url) as object | null
    const href = nativeURLHref(url)
    const response = edge(
      nativeURLSearchParameters(url),
      'searchParams',
      URL_SEARCH_PARAMS_KIND,
      true,
    )
    const carrier =
      carrierFromResponse(response) ??
      (mode !== 'snapshot' &&
      isObject(response) &&
      inChain(Object.getPrototypeOf(response) as object | null, URLSearchParams)
        ? new URL(href)
        : undefined)
    if (carrier === undefined) throw snapshotURLSearchParametersMemoIncompatible()
    adoptPrototype(adoptURLCarrier(carrier, href), prototype, URL.prototype)
    begin({ carrier, href: nativeURLHref(carrier), kind: URL_KIND, prototype })
  },
} satisfies CapturePolicy<URLLayout>

export const urlSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...urlCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(layout, layout.carrier, noValue)
    },
  }))() satisfies SnapshotPolicy<URLLayout>

const urlRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => typeof URL !== 'undefined' && value instanceof URL,
}) satisfies Recognition

function urlBindings(node: Pick<CapturedNode, 'edges'>, current: object) {
  return [
    {
      identity: nativeURLSearchParameters(current as URL),
      node: (node.edges[0] as { node: number }).node,
    },
  ]
}

const urlConstruction = {
  bindings: /* @__PURE__ */ freeze({
    read: urlBindings,
    tag: 'dependent',
    dependencies: (node) => [(node.edges[0] as { node: number }).node],
  }),
  allocate(node, resolve, owners) {
    const parameters = resolve(node.edges[0]) as object
    const carrier = owners?.nativeOwners?.get(parameters) as URL | undefined
    return carrier === undefined
      ? undefined
      : adoptPrototype(
          adoptURLCarrier(carrier, node.layout.href),
          node.layout.prototype,
          URL.prototype,
        )
  },
} satisfies ConstructionPolicy<URLLayout>

export const urlPublication = /* @__PURE__ */ (() =>
  freeze({
    ...urlCapture,
    ...urlConstruction,
    requirements: urlBindings,
    seal: same,
    aligned: (node, current, visit) =>
      visit(
        current === undefined ? undefined : nativeURLSearchParameters(current as URL),
        node.edges[0],
      ),
    matches: (node, current, visit) =>
      nativeURLHref(current as URL) === node.layout.href &&
      visit(nativeURLSearchParameters(current as URL), node.edges[0]),
    publish(node, current, _resolve, _owner, note) {
      const equal = nativeURLHref(current as URL) === node.layout.href
      if (!equal) setNativeURLHref(current as URL, node.layout.href)
      // Its own `searchParams` publishes as a node of its own.
      if (note !== undefined) note.unchanged = equal
      return true
    },
  }))() satisfies PublicationPolicy<URLLayout>

export const urlImmutable = /* @__PURE__ */ (() => ({
  ...urlConstruction,
  freshWrite: noValue,
  immutable: freeze({
    operations: freeze({
      ownsDependencies: true,
      copy(value, resolve, owners) {
        const url = value as URL
        const href = nativeURLHref(url)
        const parameters = resolve(nativeURLSearchParameters(url), URL_SEARCH_PARAMS_KIND)
        const carrier = owners?.nativeOwners?.get(parameters) as URL | undefined
        if (carrier === undefined) throw finalizationConstructionImpossible()
        return adoptPrototype(
          adoptURLCarrier(carrier, href),
          Object.getPrototypeOf(url) as object | null,
          URL.prototype,
        )
      },
      dependencies: (value, visit) =>
        visit(nativeURLSearchParameters(value as URL), URL_SEARCH_PARAMS_KIND),
      dependencyEquivalent(owner, _source, copy, owners) {
        const carrier = owners.nativeOwners?.get(copy) as URL | undefined
        if (carrier === undefined) return false
        const href = nativeURLHref(owner as URL)
        return nativeURLHref(adoptURLCarrier(new URL(nativeURLHref(carrier)), href)) === href
      },
      equivalent: (base, candidate) =>
        nativeURLHref(base as URL) === nativeURLHref(candidate as URL),
    } satisfies SpecialPolicy),
    tag: 'copy',
  }),
  someChild: (source, _read, test) => test(nativeURLSearchParameters(source as URL)),
}))() satisfies ImmutablePolicy<URLLayout>

export const urlDraft = /* @__PURE__ */ freeze({
  links: /* @__PURE__ */ freeze({
    tag: 'dependent',
    register: (source, target, visit) =>
      visit(nativeURLSearchParameters(target as URL), nativeURLSearchParameters(source as URL)),
    writable: () => false,
  }),
  tag: 'copy',
}) satisfies Extract<DraftStrategy, { tag: 'copy' }>
const urlPolicy = /* @__PURE__ */ (() => ({ ...urlSnapshot, ...urlPublication, ...urlImmutable }))()
export const urlType = /* @__PURE__ */ defineType<URLLayout>({
  draft: urlDraft,
  kind: URL_KIND,
  name: 'url',
  policy: urlPolicy,
  recognition: urlRecognition,
  requires: [URL_SEARCH_PARAMS_KIND],
})
