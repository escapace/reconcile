import { freeze, same, yes } from './empty'
import type { SpecialPolicy } from '../../types'
import { noValue } from './empty'
import { ARRAY_BUFFER_KIND } from '../array-buffer'
import { bufferEquivalent } from './bytes'
import type {
  CapturedNode,
  DraftStrategy,
  CapturePolicy,
  ConstructionPolicy,
  SnapshotPolicy,
  PublicationPolicy,
  CopyType,
} from '../../types'

export function viewCapture<K extends symbol>(
  kind: K,
  copy: (value: ArrayBufferView, buffer: ArrayBuffer) => ArrayBufferView,
): CapturePolicy<{ readonly kind: K; readonly sample: ArrayBufferView }> {
  return {
    construction: noValue,
    observe(value, begin, edge) {
      const view = value as ArrayBufferView
      const buffer = edge(view.buffer, 'buffer', ARRAY_BUFFER_KIND, true) as ArrayBuffer
      begin({ kind, sample: copy(view, buffer) })
    },
  }
}

export function viewConstruction<K extends symbol>(
  copy: (value: ArrayBufferView, buffer: ArrayBuffer) => ArrayBufferView,
): ConstructionPolicy<{ readonly kind: K; readonly sample: ArrayBufferView }> {
  return {
    bindings: /* @__PURE__ */ freeze({
      read: viewBindings,
      tag: 'dependent',
      dependencies: (node) => [(node.edges[0] as { node: number }).node],
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

export function viewSnapshot<K extends symbol>(): Pick<
  SnapshotPolicy<{ readonly kind: K; readonly sample: ArrayBufferView }>,
  'snapshot'
> {
  return {
    snapshot(layout, _resolve, writer) {
      writer.initialize(layout, layout.sample, noValue)
    },
  }
}

export function viewPublication<K extends symbol>(): Omit<
  PublicationPolicy<{ readonly kind: K; readonly sample: ArrayBufferView }>,
  keyof CapturePolicy | keyof ConstructionPolicy
> {
  return {
    publish: yes,
    requirements: viewBindings,
    seal: same,
    aligned: (node, current, visit) =>
      visit(current === undefined ? undefined : (current as ArrayBufferView).buffer, node.edges[0]),
    compatible(node, current) {
      const actual = current as ArrayBufferView
      const sample = node.layout.sample
      return viewShape(actual, sample) && actual.buffer.byteLength === sample.buffer.byteLength
    },
    matches(node, current, visit) {
      const actual = current as ArrayBufferView
      return viewShape(actual, node.layout.sample) && visit(actual.buffer, node.edges[0])
    },
  }
}

export function viewImmutable<K extends symbol>(
  copy: (value: ArrayBufferView, buffer: ArrayBuffer) => ArrayBufferView,
): Omit<
  CopyType<{ readonly kind: K; readonly sample: ArrayBufferView }>['policy'],
  'snapshot' | keyof ConstructionPolicy | keyof PublicationPolicy
> {
  return {
    freshWrite: noValue,
    immutable: /* @__PURE__ */ freeze({
      operations: /* @__PURE__ */ freeze({
        copy: (value, resolve) =>
          copy(
            value as ArrayBufferView,
            resolve((value as ArrayBufferView).buffer, ARRAY_BUFFER_KIND) as ArrayBuffer,
          ),
        dependencies: (value, visit) => visit((value as ArrayBufferView).buffer, ARRAY_BUFFER_KIND),
        equivalent: (base, candidate) =>
          viewShape(base as ArrayBufferView, candidate as ArrayBufferView) &&
          bufferEquivalent((base as ArrayBufferView).buffer, (candidate as ArrayBufferView).buffer),
      } satisfies SpecialPolicy),
      tag: 'copy',
    } satisfies CopyType<{
      readonly kind: K
      readonly sample: ArrayBufferView
    }>['policy']['immutable']),
    someChild: (source, _read, test) => test((source as ArrayBufferView).buffer),
  }
}

function viewShape(actual: ArrayBufferView, sample: ArrayBufferView): boolean {
  return (
    actual.constructor === sample.constructor &&
    actual.byteOffset === sample.byteOffset &&
    actual.byteLength === sample.byteLength
  )
}

function viewBindings(node: Pick<CapturedNode, 'edges'>, current: object) {
  return [
    {
      identity: (current as ArrayBufferView).buffer,
      node: (node.edges[0] as { node: number }).node,
    },
  ]
}

/** Views own their backing-store observations, including rereads after constructor execution. */
export const viewDraft: Extract<DraftStrategy, { tag: 'copy' }> = /* @__PURE__ */ freeze({
  links: /* @__PURE__ */ freeze({
    tag: 'dependent',
    register: (source, target, visit) =>
      visit((target as ArrayBufferView).buffer, (source as ArrayBufferView).buffer),
    writable: (value, hasCopy) => hasCopy((value as ArrayBufferView).buffer),
  } satisfies Extract<DraftStrategy, { tag: 'copy' }>['links']),
  tag: 'copy',
})
