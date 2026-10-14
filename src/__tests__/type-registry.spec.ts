import { createEngine } from '../engine'
import type { CopyType, ModuleInput, NativePolicy, StructuralType, TypeRegistry } from '../types'
import type { DateLayout } from '../types/date'
import { builtinModules } from '../types/builtins'
import { Cell, cellType, createCellType } from './fixtures/cell-type'
import { assert, describe, expect, expectTypeOf, it } from 'vitest'
import { defineType, diagnoseRecognition, registerTypes } from '../types/registry'
import { dateType } from '../types/date'
import { dataViewType } from '../types/data-view'
import { arrayType } from '../types/array'
import { objectType } from '../types/object'

describe('immutable type registration', () => {
  it('keeps explicit recognition precedence and a final property fallback', () => {
    const registry = registerTypes([arrayType, dateType, objectType])
    expect(registry.recognize([])).toBe(arrayType.kind)
    expect(registry.recognize(new Date())).toBe(dateType.kind)
    expect(registry.recognize({})).toBe(objectType.kind)
    expect(registry.policies[dateType.kind]).toBe(dateType.policy)
  })

  it('snapshots configuration without retaining a mutable caller-owned array', () => {
    const modules = [dateType, objectType]
    const registry = registerTypes(modules)
    modules.reverse()
    expect(registry.recognize(new Date())).toBe(dateType.kind)
    expect(Object.isFrozen(registry)).toBe(true)
    expect(Object.isFrozen(registry.policies)).toBe(true)
    expect(Object.isFrozen(registry.drafts)).toBe(true)
    expect(Object.isFrozen(dateType.policy)).toBe(true)
    const immutable = dateType.policy.immutable
    assert(immutable.tag === 'copy')
    expect(Object.isFrozen(immutable.operations)).toBe(true)
  })

  it('isolates custom recognition in a separate registry', () => {
    const selected = new Date()
    const custom = defineType({
      ...dateType,
      name: 'selected-date',
      recognition: { tag: 'predicate', test: (value) => value === selected },
    })
    const customRegistry = registerTypes([custom, objectType])
    const ordinaryRegistry = registerTypes([dateType, objectType])
    const other = new Date()
    expect(customRegistry.recognize(selected)).toBe(dateType.kind)
    expect(customRegistry.recognize(other)).toBe(objectType.kind)
    expect(ordinaryRegistry.recognize(other)).toBe(dateType.kind)
  })
})

it('establishes the composition premises for built-in and extended engines', () => {
  for (const modules of [builtinModules, [cellType, ...builtinModules]]) {
    const kinds: readonly symbol[] = modules.map((module) => module.kind)
    expect(new Set(kinds).size).toBe(modules.length)
    expect(modules.filter((module) => module.recognition.tag === 'fallback')).toEqual([
      modules.at(-1),
    ])
    for (const module of modules) {
      expect(typeof module.kind).toBe('symbol')
      expect(module.requires.every((kind) => kinds.includes(kind))).toBe(true)
      expect(module.policy.immutable.tag).toBe(module.draft.tag)
    }
  }
})

it('enforces required operations, vocabulary and representation through types', () => {
  type Input = ModuleInput<CopyType<DateLayout>>
  expectTypeOf<{ vocabulary: 'custom-rule' } & Omit<Input, 'vocabulary'>>().not.toExtend<Input>()
  expectTypeOf<
    { policy: Omit<Input['policy'], 'observe'> } & Omit<Input, 'policy'>
  >().not.toExtend<Input>()
  expectTypeOf<
    { policy: Omit<Input['policy'], 'snapshot'> } & Omit<Input, 'policy'>
  >().not.toExtend<Input>()
  expectTypeOf<{ draft: typeof objectType.draft } & Omit<Input, 'draft'>>().not.toExtend<Input>()
  expectTypeOf<ReturnType<typeof objectType.draft.state>['kind']>().toEqualTypeOf<
    typeof objectType.kind
  >()
  expectTypeOf<ReturnType<typeof arrayType.draft.state>['kind']>().not.toExtend<
    typeof objectType.kind
  >()
  expectTypeOf<CopyType<DateLayout>['policy']['immutable']>().not.toExtend<
    StructuralType<DateLayout, never>['policy']['immutable']
  >()
})

it('isolates recognition metadata from subsequent caller mutations', () => {
  const recognition = {
    tag: 'predicate' as const,
    test: (value: object): boolean => value instanceof Date,
  }
  const module = defineType({ ...dateType, recognition })
  const registry = registerTypes([module, objectType])
  recognition.test = () => false
  expect(registry.recognize(new Date())).toBe(dateType.kind)
  expect(Object.isFrozen(module.recognition)).toBe(true)
})

it('reports overlapping predicates only through an explicit development probe', () => {
  let probes = 0
  const broad = defineType({
    ...dateType,
    recognition: { tag: 'predicate', test: () => true },
  })
  const array = defineType({
    ...arrayType,
    recognition: {
      tag: 'predicate',
      test: (value: object) => {
        probes += 1
        return Array.isArray(value)
      },
    },
  })
  const registry = registerTypes([broad, array, objectType])
  expect(registry.recognize([])).toBe(dateType.kind)
  expect(probes).toBe(0)
  expect(diagnoseRecognition([broad, array, objectType], [])).toEqual({
    ambiguous: true,
    matches: [
      { kind: dateType.kind, name: dateType.name },
      { kind: arrayType.kind, name: arrayType.name },
    ],
    selected: dateType.kind,
  })
  expect(probes).toBe(1)
})

it('snapshots dependent draft operations before caller mutation', () => {
  const links = {
    tag: 'dependent' as const,
    register: () => undefined,
    writable: () => true,
  }
  const module = defineType({ ...dataViewType, draft: { links, tag: 'copy' } })
  links.writable = () => false
  assert(module.draft.links.tag === 'dependent')
  expect(module.draft.links.writable(new DataView(new ArrayBuffer(0)), () => false)).toBe(true)
  expect(Object.isFrozen(module.draft.links)).toBe(true)
})

it('validates expected kinds with the same precedence as full recognition', () => {
  for (let mask = 0; mask < 4; mask += 1) {
    const array = defineType({
      ...arrayType,
      recognition: { tag: 'predicate', test: () => (mask & 1) !== 0 },
    })
    const date = defineType({
      ...dateType,
      recognition: { tag: 'predicate', test: () => (mask & 2) !== 0 },
    })
    const registry = registerTypes([array, date, objectType])
    const value = {}
    const actual = registry.recognize(value)
    for (const kind of [array.kind, date.kind, objectType.kind, Symbol('unknown')])
      expect(registry.matches(kind, value)).toBe(kind === actual)
  }
})

it('stops expected-kind rejection before unrelated later predicates and revalidates live facts', () => {
  let matches = false
  let laterCalls = 0
  const array = defineType({
    ...arrayType,
    recognition: { tag: 'predicate', test: () => matches },
  })
  const date = defineType({
    ...dateType,
    recognition: {
      tag: 'predicate',
      test: () => {
        laterCalls += 1
        return true
      },
    },
  })
  const registry = registerTypes([array, date, objectType])
  const value = {}
  expect(registry.matches(array.kind, value)).toBe(false)
  expect(laterCalls).toBe(0)
  matches = true
  expect(registry.matches(array.kind, value)).toBe(true)
  expect(registry.matches(date.kind, value)).toBe(false)
  expect(laterCalls).toBe(0)
})

it('keeps independently owned symbols distinct even with equal names and descriptions', () => {
  const firstKind = Symbol('cell')
  const secondKind = Symbol('cell')
  const first = defineType({
    ...createCellType(firstKind),
    recognition: { tag: 'predicate', test: (value) => value instanceof Cell && value.value === 1 },
  })
  const second = createCellType(secondKind)
  const engine = createEngine({ types: [first, second, ...builtinModules] })
  const left = new Cell(1)
  const right = new Cell(2)
  expect(first.name).toBe(second.name)
  expect(firstKind.description).toBe(secondKind.description)
  expect(engine.types.recognize(left)).toBe(firstKind)
  expect(engine.types.recognize(right)).toBe(secondKind)
  expect(engine.types.matches(firstKind, right)).toBe(false)
  expect(engine.types.matches(secondKind, right)).toBe(true)
  expect(engine.types.policies[firstKind]).toBe(first.policy)
  expect(engine.types.policies[secondKind]).toBe(second.policy)
  expect(engine.snapshot([left, right])).toEqual([left, right])
  expect(
    engine.produce(right, (draft) => {
      draft.value = 3
      return draft
    }),
  ).toEqual(new Cell(3))
  expect(engine.reconcile(right, new Cell(4))).toBe(right)
  expect(right.value).toBe(4)
})

it('retains concrete recognition kinds while exposing an explicitly erased core contract', () => {
  const registry = registerTypes([dateType, objectType])
  expectTypeOf(registry).toExtend<TypeRegistry>()
  expectTypeOf(registry.recognize).returns.toEqualTypeOf<
    typeof dateType.kind | typeof objectType.kind | undefined
  >()
  expectTypeOf<TypeRegistry['recognize']>().returns.toEqualTypeOf<symbol | undefined>()
  expectTypeOf<TypeRegistry['policies'][symbol]>().toEqualTypeOf<NativePolicy>()
  expectTypeOf<TypeRegistry['policies'][symbol]>().not.toExtend<typeof dateType.policy>()
})
