import { assert, describe, it } from 'vitest'
import { reactive } from 'vue'
import { produce, reconcile, ReconcileError } from '../index'
import {
  randomSource,
  checkCase,
  graphsEqual,
  mixedGraph,
  graphResult,
  mutateSpecial,
  attributeConfigurations,
  greatestRetainedSubset,
  hasEdge,
  type ReuseGraphNode,
  type TinyNode,
  type AttributeFlags,
} from './fixtures/public-api-fuzz'

// Split from one file so both test workers share the fuzz corpus; every case, seed and
// deadline is unchanged.
describe('deterministic public API fuzz regressions', () => {
  it('preserves aliases across 10,000 replacement graphs', () => {
    const random = randomSource(12_345)
    for (let trial = 0; trial < 10_000; trial += 1) {
      checkCase({ seed: random.seed, trial }, () => {
        const objects: Array<Record<string, unknown>> = Array.from({ length: 8 }, () => ({}))
        const buffer = new ArrayBuffer(4)
        const values = [
          ...objects,
          new Date(1),
          new Date(2),
          buffer,
          new Uint8Array(buffer),
          new DataView(buffer),
        ]
        for (const object of objects)
          for (let index = 0; index < 3; index += 1)
            object[`k${index}`] = values[random.next(values.length)]
        const current = { child: { count: 0 } }
        let expected: Record<string, unknown> = {}
        const result = produce(current, (draft) => {
          expected = { ...objects[0], trigger: draft.child }
          return expected
        })
        expected.trigger = current.child
        assert.isTrue(graphsEqual(expected, result))
        assert.equal(current.child.count, 0)
      })
    }
  }, 60_000)

  it.each(['mixed', 'dates', 'special mutation'] as const)(
    'preserves %s graph topology and finalized values',
    (mode) => {
      const random = randomSource(18_345)
      const trials = mode === 'special mutation' ? 50_000 : 20_000
      for (let trial = 0; trial < trials; trial += 1) {
        checkCase({ mode, seed: random.seed, trial }, () => {
          const { objects, specials, values } = mixedGraph(random, mode === 'dates')
          const edit = random.next(6)
          const root = random.next(6)
          const raw = random.next(values.length)
          const special = random.next(5) + 6
          if (mode === 'special mutation') {
            const touch = random.next(5)
            const changed = random.next(2) === 1
            const returnHandle = random.next(2) === 1
            const current = { objects, specials }
            const result = produce(current, (draft) => {
              draft.objects[edit].count = 1
              const specialDraft = draft.specials[touch]
              if (changed) mutateSpecial(specialDraft)
              return graphResult(
                draft.objects[root],
                values[raw],
                returnHandle ? specialDraft : values[special],
              )
            })
            assert.equal(objects[edit].count, 0)
            objects[edit].count = 1
            if (changed) mutateSpecial(specials[touch])
            assert.isTrue(
              graphsEqual(
                graphResult(
                  objects[root],
                  values[raw],
                  returnHandle ? specials[touch] : values[special],
                ),
                result,
              ),
            )
          } else {
            const result = produce({ objects }, (draft) => {
              draft.objects[edit].count = 1
              return graphResult(draft.objects[root], values[raw], values[special])
            })
            assert.equal(objects[edit].count, 0)
            objects[edit].count = 1
            assert.isTrue(
              graphsEqual(graphResult(objects[root], values[raw], values[special]), result),
            )
          }
        })
      }
    },
    60_000,
  )

  it.each([false, true])(
    'publishes 10,000 overlapping graphs with Vue wrapping = %s or rejects incompatible roots',
    (wrapped) => {
      const random = randomSource(18_345)
      for (let trial = 0; trial < 10_000; trial += 1) {
        checkCase({ seed: random.seed, trial, wrapped }, () => {
          const { values } = mixedGraph(random, false)
          // Vue leaves Date and binary objects raw; wrapping the containing array
          // exercises its actual supported graph surface without pretending otherwise.
          const exposed = wrapped ? reactive(values) : values
          const currentIndex = random.next(values.length)
          const nextIndex = random.next(values.length)
          const current = exposed[currentIndex]
          const next = exposed[nextIndex]
          // This generator authors only raw nodes. Native cloning independently
          // captures their topology, including cycles and shared binary storage.
          const expected = structuredClone(values[nextIndex])
          assert.isTrue(graphsEqual(expected, next))
          if (current.constructor !== next.constructor) {
            const before = structuredClone(values[currentIndex])
            assert.throws(() => reconcile(current, next), ReconcileError)
            assert.isTrue(graphsEqual(before, current))
          } else {
            const result = reconcile(current, next)
            assert.equal(result, current)
            assert.isTrue(graphsEqual(expected, result))
          }
        })
      }
    },
    60_000,
  )

  it('retains the independently computed fixed point in 2,000 twelve-node object/Map graphs', () => {
    const random = randomSource(93_127)
    for (let trial = 0; trial < 2000; trial += 1) {
      checkCase({ seed: random.seed, trial }, () => {
        const size = 12
        const nodes = Array.from(
          { length: size },
          () =>
            Object.fromEntries([
              ['mark', 0],
              ['edges', new Map<string, ReuseGraphNode>()],
            ]) as unknown as ReuseGraphNode,
        )
        const edges: number[][] = nodes.map(() => [])
        const changed = nodes.map(() => random.next(5) === 0)
        for (let from = 0; from < size; from += 1) {
          const degree = random.next(4)
          for (let edge = 0; edge < degree; edge += 1) {
            const to = random.next(size)
            edges[from].push(to)
            nodes[from].edges.set(`e${edge}`, nodes[to])
          }
        }
        const rejected = changed.slice()
        for (let round = 0; round < size; round += 1)
          for (let index = 0; index < size; index += 1)
            rejected[index] ||= edges[index].some((child) => rejected[child])
        const current = { nodes }
        const next = produce(current, (draft) => {
          for (let index = 0; index < size; index += 1) {
            draft.nodes[index].mark = 1
            if (!changed[index]) draft.nodes[index].mark = 0
          }
          return draft
        })
        for (let index = 0; index < size; index += 1) {
          const old = nodes[index]
          const node = next.nodes[index]
          assert.equal(node === old, !rejected[index])
          assert.equal(node.mark, Number(changed[index]))
          assert.equal(old.mark, 0)
          assert.equal(node.edges === old.edges, !edges[index].some((child) => rejected[child]))
          assert.deepEqual([...node.edges.keys()], [...old.edges.keys()])
          edges[index].forEach((child, edge) => {
            assert.equal(node.edges.get(`e${edge}`), next.nodes[child])
            assert.equal(old.edges.get(`e${edge}`), nodes[child])
          })
        }
        assert.equal(next === current, !changed.some(Boolean))
      })
    }
  }, 60_000)

  it('matches exhaustive greatest reuse across 4,096 three-node graph/edit-mask cases', () => {
    let cases = 0
    for (let graph = 0; graph < 512; graph += 1)
      for (let changed = 0; changed < 8; changed += 1) {
        checkCase({ changed, graph }, () => {
          checkTinyGraphReuse(graph, changed)
        })
        cases += 1
      }
    assert.equal(cases, 4096)
  }, 60_000)

  it('preserves 384 native attribute combinations, cyclic aliases, and held-draft isolation', () => {
    const configurations = attributeConfigurations()
    let cases = 0
    for (const prototype of [null, Object.prototype])
      for (const key of ['left', '__proto__', Symbol('left')])
        for (const left of configurations)
          for (const right of configurations) {
            checkCase({ key: String(key), left, nullPrototype: prototype === null, right }, () => {
              const leaf = { n: 0 }
              const current = Object.create(prototype) as Record<PropertyKey, unknown>
              Object.defineProperty(current, key, { ...left, value: leaf })
              Object.defineProperty(current, 'right', { ...right, value: leaf })
              const self = { configurable: false, enumerable: false, writable: false }
              Object.defineProperty(current, 'self', { ...self, value: current })
              let held: typeof current | undefined
              const result = produce(current, (draft) => {
                held = draft
                ;(draft[key] as typeof leaf).n = 1
                return draft
              })
              assert.notEqual(result, current)
              assert.equal(Object.getPrototypeOf(result), prototype)
              assert.equal(result[key], result.right)
              assert.equal(result.self, result)
              assert.equal((result[key] as typeof leaf).n, 1)
              assert.equal(leaf.n, 0)
              const properties: Array<readonly [PropertyKey, AttributeFlags]> = [
                [key, left],
                ['right', right],
                ['self', self],
              ]
              for (const [property, expected] of properties) {
                const actual = Object.getOwnPropertyDescriptor(result, property)!
                assert.deepEqual(
                  {
                    configurable: actual.configurable,
                    enumerable: actual.enumerable,
                    writable: actual.writable,
                  },
                  expected,
                )
                assert.equal(actual.value, result[property])
              }
              ;(result[key] as typeof leaf).n = 2
              assert.equal((held![key] as typeof leaf).n, 1)
              ;(held![key] as typeof leaf).n = 3
              assert.equal((result[key] as typeof leaf).n, 2)
              assert.equal(leaf.n, 0)
            })
            cases += 1
          }
    assert.equal(cases, 384)
  }, 60_000)

  it('preserves array observation semantics in 248 accessor/hole/edit/undo cases', () => {
    let cases = 0
    for (let length = 2; length <= 6; length += 1)
      for (let mask = 0; mask < 1 << length; mask += 2)
        for (const mutate of [false, true])
          for (const undo of [false, true]) {
            checkCase({ length, mask, mutate, undo }, () => {
              checkArrayObservation(length, mask, mutate, undo)
            })
            cases += 1
          }
    assert.equal(cases, 248)
  }, 60_000)
})

function checkTinyGraphReuse(graph: number, changed: number): void {
  const nodes: TinyNode[] = Array.from({ length: 3 }, () => ({ value: 0 }))
  for (let from = 0; from < 3; from += 1)
    for (let to = 0; to < 3; to += 1)
      if (hasEdge(graph, from, to)) nodes[from][`e${to}`] = nodes[to]
  const greatest = greatestRetainedSubset(graph, changed)
  const current = { nodes }
  const result = produce(current, (draft) => {
    for (let index = 0; index < 3; index += 1) {
      draft.nodes[index].value = 1
      if ((changed & (1 << index)) === 0) draft.nodes[index].value = 0
    }
    return draft
  })
  for (let index = 0; index < 3; index += 1) {
    assertTinyNodeReuse(graph, changed, greatest, nodes, result, index)
  }
  if (changed === 0) assert.equal(result, current)
}

function assertTinyNodeReuse(
  graph: number,
  changed: number,
  greatest: number,
  nodes: TinyNode[],
  result: { nodes: TinyNode[] },
  index: number,
): void {
  assert.equal(result.nodes[index] === nodes[index], Boolean(greatest & (1 << index)))
  assert.equal(nodes[index].value, 0)
  assert.equal(result.nodes[index].value, (changed & (1 << index)) !== 0 ? 1 : 0)
  for (let child = 0; child < 3; child += 1)
    if (hasEdge(graph, index, child)) {
      assert.equal(result.nodes[index][`e${child}`], result.nodes[child])
      assert.equal(nodes[index][`e${child}`], nodes[child])
    }
}

function checkArrayObservation(length: number, mask: number, mutate: boolean, undo: boolean): void {
  const { expected, raw, reads } = observedArray(length, mask, mutate, undo)
  const keys: PropertyKey[] = []
  const base = keyRecordingProxy(raw, keys)
  let held: unknown[] | undefined
  const result = produce(base, (draft) => {
    held = draft
    draft[0] = 2
    if (undo) draft[0] = 1
    return draft
  })
  assert.equal(raw[0], 1)
  for (let index = 1; index < length; index += 1)
    assert.equal(reads[index], (mask & (1 << index)) !== 0 ? 1 : 0)
  assert.isTrue(graphsEqual(expected, result))
  // Kept, with its getters, when the recipe changed none of its data: a getter that writes the
  // draft changes it (DraftSurface.keeps).
  assert.equal(result === base, undo && (mask === 0 || !mutate))
  // Native array proxy operations receive string keys, not our numeric
  // traversal indices. Do not freeze incidental internal trap counts.
  assert.isTrue(keys.length > 0 && keys.every((key) => typeof key === 'string'))
  if (result !== base) {
    const old = held![0]
    result[0] = 999
    assert.equal(held![0], old)
    held![0] = 888
    assert.equal(result[0], 999)
    assert.equal(raw[0], 1)
  }
}

// Masked indices get counting accessors that, when mutating, add their index to
// element 0; unmasked odd indices hold plain objects. `expected` is the value each
// element should finalize to.
function observedArray(length: number, mask: number, mutate: boolean, undo: boolean) {
  const raw = new Array<unknown>(length)
  raw[0] = 1
  const reads: number[] = Array.from({ length }, () => 0)
  const expected = new Array<unknown>(length)
  let count = undo ? 1 : 2
  for (let index = 1; index < length; index += 1) {
    if ((mask & (1 << index)) !== 0) {
      Object.defineProperty(raw, index, {
        configurable: true,
        enumerable: true,
        get(this: unknown[]) {
          reads[index] += 1
          if (mutate) this[0] = Number(this[0]) + index
          return index % 2 === 1 ? new Date(index * 100) : { count: this[0] }
        },
      })
      if (mutate) count += index
      expected[index] = index % 2 === 1 ? new Date(index * 100) : { count }
    } else if (index % 2 === 1) {
      raw[index] = { count: index }
      expected[index] = { count: index }
    }
  }
  expected[0] = count
  return { expected, raw, reads }
}

function keyRecordingProxy(raw: unknown[], keys: PropertyKey[]): unknown[] {
  return new Proxy(raw, {
    get(target, key, receiver) {
      keys.push(key)
      return Reflect.get(target, key, receiver) as unknown
    },
    getOwnPropertyDescriptor(target, key) {
      keys.push(key)
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
    has(target, key) {
      keys.push(key)
      return Reflect.has(target, key)
    },
  })
}
