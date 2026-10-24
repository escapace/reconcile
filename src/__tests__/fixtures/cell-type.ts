import { isObject } from '../../object-property'
import type { BaseDraftState, NativePolicy } from '../../types'
import { defineType } from '../../types/registry'
import {
  type PropertySurface,
  propertyRequirements,
  propertySlots,
  publishProperty,
  REFUSED,
} from '../../types/shared/property-publication'

// Test-only native surface: one own data slot, encoded as an ordinary object
// with the single key "value" in the existing Lean payload vocabulary.
interface CellLayout<K extends symbol> {
  readonly kind: K
}
interface CellState<K extends symbol> extends BaseDraftState {
  readonly kind: K
}
export class Cell {
  constructor(public value: unknown) {}
}
const write: NativePolicy<CellLayout<symbol>>['freshWrite'] = (node, target, index, resolve) => {
  ;(target as Cell).value = resolve(node.edges[index])
}
/** Builds an extension from an independently owned identity without a central kind catalog. */
export function createCellType<K extends symbol>(kind: K) {
  const surface: PropertySurface<CellLayout<K>> = {
    desired: undefined,
    ordered: false,
    slots: propertySlots,
    compatible: () => true,
    keys: () => ['value'],
  }
  const policy = {
    bindings: { tag: 'independent' },
    freshWrite: write,
    immutable: {
      tag: 'structural',
      observeDraft(source, observer) {
        const { base } = observer
        observer.begin({ kind })
        const value = (source as Cell).value
        observer.edge(value, 'value', base !== undefined && Object.is(value, (base as Cell).value))
      },
      reuse: (node, current, visit) => visit((current as Cell).value, node.edges[0]),
    },
    aligned(node, current, visit) {
      visit((current as Cell | undefined)?.value, node.edges[0])
    },
    allocate: () => new Cell(undefined),
    compatible: () => true,
    construction: () => undefined,
    matches: (node, current, visit) => visit((current as Cell).value, node.edges[0]),
    observe(value, begin, edge) {
      begin({ kind })
      edge((value as Cell).value, 'value')
    },
    publish: (node, target, resolve) =>
      publishProperty(target, 'value', resolve(node.edges[0])) !== REFUSED,
    requirements: (node, current) => propertyRequirements(node, current, surface),
    seal: (node) => node,
    snapshot(layout, resolve, writer) {
      const target = new Cell(undefined)
      writer.initialize(layout, target, (edge) => {
        target.value = resolve(edge)
      })
    },
    someChild: (value, _read, test) => test((value as Cell).value),
  } satisfies NativePolicy<CellLayout<K>>
  return defineType<CellLayout<K>, CellState<K>>({
    draft: {
      tag: 'structural',
      handle(state) {
        return new Proxy(new Cell(undefined), {
          defineProperty: () => false,
          deleteProperty: () => false,
          get(_target, key, receiver) {
            if (key !== 'value') return Reflect.get(state.base, key, receiver) as unknown
            const value = (state.source() as Cell).value
            return isObject(value) ? state.context.materializeChild(value) : value
          },
          set(_target, key, value: unknown) {
            if (key !== 'value') return false
            if (state.context.isSameDraftValue((state.source() as Cell).value, value)) return true
            state.copy ??= new Cell((state.base as Cell).value)
            ;(state.copy as Cell).value = value
            state.modified = true
            return true
          },
        })
      },
      state: (base, context) => ({
        base,
        context,
        copy: undefined,
        handle: undefined,
        kind,
        modified: false,
        properties: undefined,
        source() {
          return this.copy ?? this.base
        },
      }),
    },
    kind,
    name: 'cell',
    policy,
    recognition: { tag: 'predicate', test: (value) => value instanceof Cell },
  })
}

/** Independent extension identity; no built-in numbering agreement is needed. */
export const CELL_KIND = Symbol('cell')
export const cellType = createCellType(CELL_KIND)
