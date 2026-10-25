import { freeze, same } from './empty'
import type { SpecialPolicy } from '../../types'
import { noValue } from './empty'
import { ARRAY_BUFFER_KIND } from '../array-buffer'
import { bufferEquivalent } from './bytes'
import { atomValue, isNode } from '../../graph/edge'
import {
  bufferByteLength,
  bufferOfView,
  isShared,
  viewByteLength,
  viewElement,
  viewOffset,
} from './binary-native'
import type {
  CapturedNode,
  DraftStrategy,
  CapturePolicy,
  ConstructionPolicy,
  ImmutablePolicy,
  PublicationPolicy,
  NativePolicy,
} from '../../types'

export function viewCapture<K extends symbol>(
  kind: K,
  copy: (value: ArrayBufferView, buffer: ArrayBuffer) => ArrayBufferView,
): CapturePolicy<{ readonly kind: K; readonly sample: ArrayBufferView }> {
  return {
    construction: noValue,
    observe(value, begin, edge) {
      const view = value as ArrayBufferView
      const storage = bufferOfView(view)
      // A `SharedArrayBuffer` is kept by reference, as an atom edge; any other buffer is a node.
      const buffer = edge(
        storage,
        'buffer',
        isShared(storage) ? undefined : ARRAY_BUFFER_KIND,
        true,
      ) as ArrayBuffer
      begin({ kind, sample: copy(view, buffer) })
    },
  }
}

export function viewConstruction<K extends symbol>(
  copy: (value: ArrayBufferView, buffer: ArrayBuffer) => ArrayBufferView,
): ConstructionPolicy<{ readonly kind: K; readonly sample: ArrayBufferView }> {
  return {
    bindings: /* @__PURE__ */ freeze({
      tag: 'dependent',
      dependencies: (node) => (isNode(node.edges[0]) ? [node.edges[0].node] : []),
    } satisfies ConstructionPolicy<{
      readonly kind: K
      readonly sample: ArrayBufferView
    }>['bindings']),
    allocate(node, resolve) {
      const sample = node.layout.sample
      return copy(sample, resolve(node.edges[0]) as ArrayBuffer)
    },
  }
}

// A view's only child is its buffer.
const viewChildren: NativePolicy['someChild'] = (source, _read, test) => test(bufferOfView(source))

export function viewPublication<K extends symbol>(): Omit<
  PublicationPolicy<{ readonly kind: K; readonly sample: ArrayBufferView }>,
  keyof CapturePolicy | keyof ConstructionPolicy
> {
  return {
    seal: same,
    someChild: viewChildren,
    aligned: (node, current, visit) =>
      visit(current === undefined ? undefined : bufferOfView(current), node.edges[0]),
    matches(node, current, visit) {
      const actual = current as ArrayBufferView
      return viewShape(actual, node.layout.sample) && visit(bufferOfView(actual), node.edges[0])
    },
    // A kept view must have next's shape over a buffer of next's length.
    requirements(node, current) {
      const actual = current as ArrayBufferView
      const sample = node.layout.sample
      return viewShape(actual, sample) &&
        bufferByteLength(bufferOfView(actual)) === bufferByteLength(bufferOfView(sample))
        ? viewRequirements(node, current)
        : undefined
    },
    // A view writes nothing: its bytes are its buffer's, and the preflight bound its buffer, which
    // readback compares with its shape.
    publish: (_node, _current, _resolve, _owner, note) => {
      if (note !== undefined) note.unchanged = true
      return true
    },
  }
}

export function viewImmutable<K extends symbol>(
  copy: (value: ArrayBufferView, buffer: ArrayBuffer) => ArrayBufferView,
): {
  readonly immutable: Extract<
    ImmutablePolicy<{ readonly kind: K; readonly sample: ArrayBufferView }>['immutable'],
    { tag: 'copy' }
  >
} & Pick<ImmutablePolicy<{ readonly kind: K; readonly sample: ArrayBufferView }>, 'someChild'> {
  return {
    immutable: /* @__PURE__ */ freeze({
      operations: /* @__PURE__ */ freeze({
        copy: (value, resolve) =>
          copy(
            value as ArrayBufferView,
            resolve(bufferOfView(value), ARRAY_BUFFER_KIND) as ArrayBuffer,
          ),
        dependencies: (value, visit) => visit(bufferOfView(value), ARRAY_BUFFER_KIND),
        equivalent: (base, candidate) =>
          viewShape(base as ArrayBufferView, candidate as ArrayBufferView) &&
          bufferEquivalent(bufferOfView(base), bufferOfView(candidate)),
      } satisfies SpecialPolicy),
      tag: 'copy',
    } satisfies Extract<
      ImmutablePolicy<{ readonly kind: K; readonly sample: ArrayBufferView }>['immutable'],
      { tag: 'copy' }
    >),
    someChild: viewChildren,
  }
}

function viewShape(actual: ArrayBufferView, sample: ArrayBufferView): boolean {
  return (
    Object.getPrototypeOf(actual) === Object.getPrototypeOf(sample) &&
    viewElement(actual) === viewElement(sample) &&
    viewOffset(actual) === viewOffset(sample) &&
    viewByteLength(actual) === viewByteLength(sample)
  )
}

// A view binds its buffer to the buffer's node. A view over a `SharedArrayBuffer` binds nothing,
// and only a view over the same one can stand for it.
function viewRequirements(node: Pick<CapturedNode, 'edges'>, current: object) {
  const edge = node.edges[0]
  if (isNode(edge)) return [{ identity: bufferOfView(current), node: edge.node }]
  return bufferOfView(current) === atomValue(edge) ? [] : undefined
}

/** Views own their backing-store observations, including rereads after constructor execution. */
export const viewDraft: Extract<DraftStrategy, { tag: 'copy' }> = /* @__PURE__ */ freeze({
  links: /* @__PURE__ */ freeze({
    tag: 'dependent',
    register: (source, target, visit) => visit(bufferOfView(target), bufferOfView(source)),
    writable: (value, hasCopy) => hasCopy(bufferOfView(value)),
  } satisfies Extract<DraftStrategy, { tag: 'copy' }>['links']),
  tag: 'copy',
})
