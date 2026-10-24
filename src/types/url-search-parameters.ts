import { adoptPrototype } from './shared/prototype'
import {
  freeze,
  noValue,
  independentBindings,
  yes,
  same,
  emptyEdges,
  noChildren,
  noDependencies,
  independentDraft,
  ordinaryExposure,
} from './shared/empty'
import { defineType } from './registry'
import {
  URL_KIND,
  createURLCarrier,
  nativeURLSearchParameters,
  replaceNativeParameters,
  nativeParametersText,
  urlCarrierResponse,
} from './shared/url-carrier'
import type {
  CapturePolicy,
  SnapshotPolicy,
  Recognition,
  ConstructionPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  SpecialPolicy,
} from '../types'

/** Stable global identity owned by the URLSearchParams module. */
export const URL_SEARCH_PARAMS_KIND = Symbol.for('@escapace/reconcile/url-search-params')

/** Captures ordered parameter values and a private native owner. */
export interface URLSearchParametersLayout {
  readonly carrier: URL
  readonly kind: typeof URL_SEARCH_PARAMS_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
  readonly text: string
}

const urlSearchParametersCapture = {
  construction: (layout) => urlCarrierResponse(layout.carrier),
  observe(value, begin) {
    const prototype = Object.getPrototypeOf(value) as object | null
    const text = nativeParametersText(value as URLSearchParams)
    const carrier = createURLCarrier(text)
    adoptPrototype(nativeURLSearchParameters(carrier), prototype, URLSearchParams.prototype)
    begin({ carrier, kind: URL_SEARCH_PARAMS_KIND, prototype, text })
  },
} satisfies CapturePolicy<URLSearchParametersLayout>

export const urlSearchParametersSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...urlSearchParametersCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(layout, nativeURLSearchParameters(layout.carrier), noValue)
    },
  }))() satisfies SnapshotPolicy<URLSearchParametersLayout>

const urlSearchParametersRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) =>
    typeof URL !== 'undefined' &&
    typeof URLSearchParams !== 'undefined' &&
    value instanceof URLSearchParams,
}) satisfies Recognition

const parametersConstruction = {
  bindings: independentBindings,
  allocate(node, _resolve, owners) {
    const carrier = createURLCarrier(node.layout.text)
    if (owners !== undefined)
      (owners.nativeOwners ??= new WeakMap()).set(nativeURLSearchParameters(carrier), carrier)
    return adoptPrototype(
      nativeURLSearchParameters(carrier),
      node.layout.prototype,
      URLSearchParams.prototype,
    )
  },
} satisfies ConstructionPolicy<URLSearchParametersLayout>

export const urlSearchParametersPublication = /* @__PURE__ */ (() =>
  freeze({
    ...urlSearchParametersCapture,
    ...parametersConstruction,
    aligned: noValue,
    compatible: yes,
    requirements: emptyEdges,
    seal: same,
    matches: (node, current) =>
      nativeParametersText(current as URLSearchParams) === node.layout.text,
    // A publication that wrote nothing found the text equal, as readback, which compares the same
    // text, would.
    publish(node, current, _resolve, owner, note) {
      const wrote = replaceNativeParameters(
        current as URLSearchParams,
        node.layout.text,
        () => owner?.(current, URL_KIND) as URL | undefined,
      )
      if (note !== undefined) note.unchanged = !wrote
      return true
    },
  }))() satisfies PublicationPolicy<URLSearchParametersLayout>

export const urlSearchParametersImmutable = /* @__PURE__ */ (() => ({
  ...parametersConstruction,
  freshWrite: noValue,
  immutable: freeze({
    operations: freeze({
      dependencies: noDependencies,
      copy(value, _resolve, owners) {
        const prototype = Object.getPrototypeOf(value) as object | null
        const carrier = createURLCarrier(nativeParametersText(value as URLSearchParams))
        if (owners !== undefined)
          (owners.nativeOwners ??= new WeakMap()).set(nativeURLSearchParameters(carrier), carrier)
        return adoptPrototype(
          nativeURLSearchParameters(carrier),
          prototype,
          URLSearchParams.prototype,
        )
      },
      equivalent: (base, candidate) =>
        nativeParametersText(base as URLSearchParams) ===
        nativeParametersText(candidate as URLSearchParams),
    } satisfies SpecialPolicy),
    tag: 'copy',
  }),
  someChild: noChildren,
}))() satisfies ImmutablePolicy<URLSearchParametersLayout>

export const urlSearchParametersDraft = independentDraft
export const urlSearchParametersExposure = ordinaryExposure
const parametersPolicy = /* @__PURE__ */ (() => ({
  ...urlSearchParametersSnapshot,
  ...urlSearchParametersPublication,
  ...urlSearchParametersImmutable,
}))()
export const urlSearchParametersType = /* @__PURE__ */ defineType<URLSearchParametersLayout>({
  draft: urlSearchParametersDraft,
  exposure: urlSearchParametersExposure,
  kind: URL_SEARCH_PARAMS_KIND,
  name: 'url-search-params',
  policy: parametersPolicy,
  recognition: urlSearchParametersRecognition,
})
