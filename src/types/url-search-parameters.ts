import {
  freeze,
  noValue,
  independentBindings,
  same,
  emptyEdges,
  noChildren,
  noDependencies,
  independentDraft,
} from './shared/empty'
import {
  URL_KIND,
  nativeURLSearchParameters,
  carriedParameters,
  parametersCarrier,
  replaceNativeParameters,
  nativeParametersText,
  urlCarrierResponse,
} from './shared/url-carrier'
import type {
  CapturePolicy,
  ConstructionPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  SpecialPolicy,
  SnapshotPolicy,
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
    const carrier = parametersCarrier(text, prototype)
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

const parametersConstruction = {
  bindings: independentBindings,
  allocate: (node, _resolve, owners) =>
    carriedParameters(node.layout.text, node.layout.prototype, owners),
} satisfies ConstructionPolicy<URLSearchParametersLayout>

export const urlSearchParametersPublication = /* @__PURE__ */ (() =>
  freeze({
    ...urlSearchParametersCapture,
    ...parametersConstruction,
    aligned: noValue,
    requirements: emptyEdges,
    seal: same,
    someChild: noChildren,
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
  immutable: freeze({
    operations: freeze({
      dependencies: noDependencies,
      copy(value, _resolve, owners) {
        const prototype = Object.getPrototypeOf(value) as object | null
        const text = nativeParametersText(value as URLSearchParams)
        return carriedParameters(text, prototype, owners)
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
