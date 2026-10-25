import { builtinValue, Detached, uncurried } from '../../standard-prototypes'
import { adoptPrototype } from './prototype'
import type { NativeOwners } from '../../types'
/** The URL kind, shared by the URL ownership facets. */
export const URL_KIND = Symbol('url')

/** A built-in method as a function of its receiver, then its arguments. */
type Call<Arguments extends unknown[], Result> = (
  target: unknown,
  ...parameters: Arguments
) => Result

/**
 * The getter or setter of a built-in accessor of `URL`, read when the module loads; undefined where
 * `URL` is missing.
 */
const urlAccessor = <Arguments extends unknown[], Result>(
  key: string,
  part: 'get' | 'set',
): Call<Arguments, Result> =>
  (typeof URL === 'function'
    ? uncurried<Arguments, Result>(
        (
          Object.getOwnPropertyDescriptor(URL.prototype, key) as Partial<
            Record<typeof part, unknown>
          >
        )[part],
      )
    : undefined)!
/** A built-in method of `URLSearchParams`, read when the module loads. */
const parametersMethod = <Arguments extends unknown[], Result>(
  key: PropertyKey,
): Call<Arguments, Result> =>
  (typeof URLSearchParams === 'function'
    ? uncurried<Arguments, Result>(builtinValue(URLSearchParams.prototype, key))
    : undefined)!

const hrefGet = /* @__PURE__ */ (() => urlAccessor<[], string>('href', 'get'))()
const hrefSet = /* @__PURE__ */ (() => urlAccessor<[text: string], unknown>('href', 'set'))()
const searchGet = /* @__PURE__ */ (() => urlAccessor<[], string>('search', 'get'))()
const searchSet = /* @__PURE__ */ (() => urlAccessor<[text: string], unknown>('search', 'set'))()
const parametersGet = /* @__PURE__ */ (() =>
  urlAccessor<[], URLSearchParams>('searchParams', 'get'))()
const parametersText = /* @__PURE__ */ (() => parametersMethod<[], string>('toString'))()
const parametersKeys = /* @__PURE__ */ (() => parametersMethod<[], object>('keys'))()
const parametersEntries = /* @__PURE__ */ (() => parametersMethod<[], object>('entries'))()
const parametersDelete = /* @__PURE__ */ (() =>
  parametersMethod<[name: string], unknown>('delete'))()
const parametersAppend = /* @__PURE__ */ (() =>
  parametersMethod<[name: string, value: string], unknown>('append'))()
const parametersStep = /* @__PURE__ */ (() =>
  (typeof URLSearchParams === 'function'
    ? uncurried<[], IteratorResult<unknown>>(
        builtinValue(Object.getPrototypeOf(new URLSearchParams().keys()) as object, 'next'),
      )
    : undefined)!)()

/** Reads native URL state without consulting application overrides or expandos: every built-in
 * is read when the module loads. */
export function nativeURLHref(value: URL): string {
  return hrefGet(value)
}

export function nativeURLSearchParameters(value: URL): URLSearchParams {
  return parametersGet(value)
}

export function nativeParametersText(value: URLSearchParams): string {
  return parametersText(value)
}

export function setNativeURLHref(value: URL, text: string): void {
  hrefSet(value, text)
}

function nativeURLSearch(value: URL): string {
  return searchGet(value)
}

function setNativeURLSearch(value: URL, text: string): void {
  searchSet(value, text)
}

/** The values a built-in `URLSearchParams` iterator yields, stepped by the built-in `next`. */
function stepAll(iterator: object): unknown[] {
  const values: unknown[] = []
  for (;;) {
    const step = parametersStep(iterator)
    if (step.done === true) return values
    values.push(step.value)
  }
}

/** The `[name, value]` entries of a `URLSearchParams`, in order, read with the built-ins. */
export const nativeParameterEntries = (value: URLSearchParams): unknown[] =>
  stepAll(parametersEntries(value))

/** Replaces native ordered entries, avoiding normalization when no change is needed; returns
 * whether it wrote. */
export function replaceNativeParameters(
  target: URLSearchParams,
  text: string,
  owner?: () => URL | undefined,
): boolean {
  const previous = nativeParametersText(target)
  if (previous === text) return false
  const url = owner?.()
  if (url !== undefined) {
    // Clearing a nonempty list can normalize an opaque path before later appends.
    // An initially empty list must not clear its raw query: it may protect spaces.
    if (previous !== '') setNativeURLSearch(url, '')
    if (text !== '') setNativeURLSearch(url, text)
    return true
  }
  const keys = stepAll(parametersKeys(target))
  for (let index = 0; index < keys.length; index += 1)
    parametersDelete(target, keys[index] as string)
  const entries = stepAll(parametersEntries(new URLSearchParams(text)))
  for (let index = 0; index < entries.length; index += 1) {
    const entry = entries[index] as readonly [string, string]
    parametersAppend(target, entry[0], entry[1])
  }
  return true
}

/** Private construction metadata, distinct from every caller-supplied native memo value. */
class URLCarrierResponse extends Detached {
  declare readonly carrier: URL
  constructor(carrier: URL) {
    super()
    this.carrier = carrier
  }
}

export function urlCarrierResponse(carrier: URL): object {
  return new URLCarrierResponse(carrier)
}

export function carrierFromResponse(value: unknown): URL | undefined {
  return value instanceof URLCarrierResponse ? value.carrier : undefined
}

/** Creates native parameter storage whose owner can be revealed without replacing the child. */
export function createURLCarrier(text: string): URL {
  // The ignored empty query segment records whether a native mutator has serialized the list.
  return new URL(`https://reconcile.invalid/?&${text}`)
}

/** A fresh carrier holding `text`, its `URLSearchParams` on `prototype`. */
export function parametersCarrier(text: string, prototype: object | null): URL {
  const carrier = createURLCarrier(text)
  adoptPrototype(nativeURLSearchParameters(carrier), prototype, URLSearchParams.prototype)
  return carrier
}

/** A fresh `URLSearchParams` holding `text`, on `prototype`, which `owners` maps to its
 * carrier. */
export function carriedParameters(
  text: string,
  prototype: object | null,
  owners: NativeOwners,
): URLSearchParams {
  const carrier = parametersCarrier(text, prototype)
  const parameters = nativeURLSearchParameters(carrier)
  ;(owners.nativeOwners ??= new WeakMap()).set(parameters, carrier)
  return parameters
}

/** `carrier` as the URL `href` names, on `prototype`, keeping its captured parameter list. */
export const ownedURL = (carrier: URL, href: string, prototype: object | null): URL =>
  adoptPrototype(adoptURLCarrier(carrier, href), prototype, URL.prototype)

/** Adopts later-observed owner state while retaining the earlier captured parameter list. */
export function adoptURLCarrier(carrier: URL, href: string): URL {
  const parameters = nativeURLSearchParameters(carrier)
  const text = nativeParametersText(parameters)
  const touched = !nativeURLSearch(carrier).startsWith('?&')
  const observed = new URL(href)
  const preserve = touched || nativeParametersText(nativeURLSearchParameters(observed)) !== text
  setNativeURLHref(carrier, href)
  if (preserve) {
    setNativeURLSearch(carrier, text)
    // Replay the native empty-list update, including native opaque-path normalization.
    if (text === '') parametersDelete(parameters, '')
  }
  return carrier
}
