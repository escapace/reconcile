/** Reads native URL state without consulting application overrides or expandos. */
export function nativeURLHref(value: URL): string {
  return Object.getOwnPropertyDescriptor(URL.prototype, 'href')!.get!.call(value) as string
}

export function nativeURLSearchParameters(value: URL): URLSearchParams {
  return Object.getOwnPropertyDescriptor(URL.prototype, 'searchParams')!.get!.call(
    value,
  ) as URLSearchParams
}

export function nativeParametersText(value: URLSearchParams): string {
  return URLSearchParams.prototype.toString.call(value)
}

export function setNativeURLHref(value: URL, href: string): void {
  Object.getOwnPropertyDescriptor(URL.prototype, 'href')!.set!.call(value, href)
}

function nativeURLSearch(value: URL): string {
  return Object.getOwnPropertyDescriptor(URL.prototype, 'search')!.get!.call(value) as string
}

function setNativeURLSearch(value: URL, text: string): void {
  Object.getOwnPropertyDescriptor(URL.prototype, 'search')!.set!.call(value, text)
}

/** Replaces native ordered entries, avoiding normalization when no change is needed. */
export function replaceNativeParameters(target: URLSearchParams, text: string): void {
  if (nativeParametersText(target) === text) return
  const keys = Array.from(URLSearchParams.prototype.keys.call(target))
  for (const key of keys) URLSearchParams.prototype.delete.call(target, key)
  for (const [key, value] of new URLSearchParams(text))
    URLSearchParams.prototype.append.call(target, key, value)
}

/** Private construction metadata, distinct from every caller-supplied native memo value. */
class URLCarrierResponse {
  declare readonly carrier: URL
  constructor(carrier: URL) {
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
    if (text === '') URLSearchParams.prototype.delete.call(parameters, '')
  }
  return carrier
}
