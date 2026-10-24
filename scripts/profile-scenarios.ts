import assert from 'node:assert/strict'
import { ring, type RingNode } from '../src/__tests__/fixtures/ring'
import type { selections } from '../src/graph/selection'
import type * as API from '../src/index'
import type { Domains } from '../src/types'
import {
  flatOperation,
  serializationFixtures,
  serializationOperation,
  smallOperation,
  smallScenarioNames,
  type SmallScenarioName,
  textCodec,
} from './bench-workloads'

export const diagnosticNames = [
  'diag-noop',
  'diag-undo',
  'diag-alias-dag',
  'diag-fanout',
  'diag-sparse',
  'diag-cycle',
  'diag-collections',
  'diag-collection-capture',
  'diag-buffer',
  'diag-views',
  'diag-core-selection',
  'diag-core-requires',
  'diag-shared-cycle',
  'diag-shared-spread',
  'diag-produce-deep',
  'diag-unsupported-cycle',
  'diag-module-date',
  'diag-module-buffer',
  'diag-serialize-graph',
  'diag-deserialize-graph',
  'diag-deserialize-bigints',
  'diag-deserialize-limited',
  'diag-required-max-bytes',
  'diag-tiny-produce',
  'diag-tiny-reconcile',
  'serialize',
  'deserialize',
  ...smallScenarioNames,
] as const
export type DiagnosticName = (typeof diagnosticNames)[number]

/** The operations a diagnostic may call; the harness and the spec pass the same set. */
type Ports = Parameters<typeof createDiagnostic>[1]

/** Fixtures every diagnostic receives; the shared object graph exists before any scenario. */
interface Context {
  readonly alias: { items: Array<{ n: number }> }
  readonly api: Ports
  readonly shared: { n: number }
  readonly size: number
}

interface Scenario {
  readonly layer?: string
  readonly state?: string
  readonly run: () => void
  readonly validate: () => void
}

const identity = (value: object): object => value

/** `size` records with shared children, a `Map`, dates and a cycle back to the first record. */
function serializationGraph(size: number): object {
  const pool = Array.from({ length: 8 }, (_, id) => ({ id, label: `shared-${id}` }))
  const records = Array.from({ length: size }, (_, id): Record<string, unknown> => ({
    id,
    shared: pool[id % pool.length],
    tags: [`t${id % 5}`, id],
    when: new Date(id),
  }))
  records.at(-1)!.next = records[0]
  return { index: new Map(records.map((record, id) => [id, record])), records }
}

/** A ring of frozen nodes with frozen payloads. */
function frozenRing(length: number): RingNode[] {
  const original = ring(length)
  original.forEach((node) => {
    Object.freeze(node.payload)
    Object.freeze(node)
  })
  return original
}

/** Walks `length` links from `root`, checking each payload, and returns the visited nodes. */
function ringMembers(root: RingNode, length: number): RingNode[] {
  const nodes: RingNode[] = []
  let cursor = root
  for (let index = 0; index < length; index += 1) {
    assert.equal(cursor.payload.value, 0)
    nodes.push(cursor)
    cursor = cursor.next!
  }
  assert.equal(cursor, root)
  return nodes
}

function produceAlias({ alias, api, shared }: Context, undo: boolean): Scenario {
  let last: unknown
  return {
    state: 'stable input; expected identity-preserving no-op or write/undo',
    run: () => {
      last = api.produce(alias, (draft) => {
        if (undo) {
          draft.items[0].n += 1
          draft.items[0].n -= 1
        }
        return draft
      })
    },
    validate: () => {
      assert.equal(last, alias)
      assert.equal(shared.n, 0)
    },
  }
}

/** Fixtures are created when a factory runs, before warmup; `run` and `validate` close over them. */
/** The small round's workloads, which ignore the diagnostic size. */
const small =
  (name: SmallScenarioName) =>
  ({ api }: Context): Scenario => ({
    layer: 'small',
    state: 'a flat object of the named number of keys; see smallOperation in bench-workloads.ts',
    ...smallOperation(api, name),
  })

const scenarios: Record<DiagnosticName, (context: Context) => Scenario> = {
  ...(Object.fromEntries(smallScenarioNames.map((name) => [name, small(name)])) as Record<
    SmallScenarioName,
    (context: Context) => Scenario
  >),
  'deserialize': ({ api }) => ({
    layer: 'serialization',
    state: 'decodes the six serialization fixture texts in rotation, one per operation',
    ...serializationOperation(api, 'deserialize'),
  }),
  'diag-alias-dag': ({ alias, api, shared }) => {
    let last: unknown
    const root = { child: shared, left: alias, right: alias }
    return {
      run: () => {
        last = api.snapshot(root)
      },
      validate: () => {
        const output = last as typeof root
        assert.notEqual(output, root)
        assert.equal(output.left, output.right)
        assert(output.left.items.every((item) => item === output.child))
        assert.notEqual(output.child, shared)
      },
    }
  },
  'diag-buffer': ({ api, size }) => {
    let last: unknown
    const input = new ArrayBuffer(size * 1024)
    new Uint8Array(input)[0] = 37
    return {
      run: () => {
        last = api.snapshot(input)
      },
      validate: () => {
        assert.notEqual(last, input)
        assert.equal((last as ArrayBuffer).byteLength, input.byteLength)
        assert.equal(new Uint8Array(last as ArrayBuffer)[0], 37)
      },
    }
  },
  'diag-collection-capture': ({ api, size }) => {
    let last: unknown
    const values = Array.from({ length: size }, (_, n) => ({ n }))
    const input = {
      map: new Map(values.map((value, index) => [index, value])),
      set: new Set(values),
    }
    return {
      run: () => {
        last = api.snapshot(input)
      },
      validate: () => {
        const output = last as typeof input
        assert.equal(output.map.size, size)
        assert.equal(output.set.size, size)
        const members = [...output.set]
        for (let index = 0; index < size; index += 1) {
          assert.equal(output.map.get(index), members[index])
          assert.notEqual(members[index], values[index])
          assert.equal(members[index].n, index)
        }
      },
    }
  },
  'diag-collections': ({ api, shared, size }) => {
    let last: unknown
    const input = {
      map: new Map(Array.from({ length: size }, (_, index) => [index, shared])),
      set: new Set([shared]),
    }
    return {
      run: () => {
        last = api.produce(input, (draft) => {
          draft.map.get(0)!.n += 1
          return draft
        })
      },
      validate: () => {
        const output = last as typeof input
        assert.equal(shared.n, 0)
        assert.equal(output.map.get(0)!.n, 1)
        assert.equal(output.map.get(0), [...output.set][0])
      },
    }
  },
  'diag-core-requires': ({ api, size }) => {
    let last: unknown
    const width = Math.min(size, 32)
    const domains: Domains = [
      Array.from({ length: width }, (_, identity) => ({
        identity,
        required: [{ identity: width + identity, node: 1 }],
        retained: true,
        storage: identity,
      })),
      Array.from({ length: width }, (_, option) => ({
        identity: width + option,
        required: [],
        retained: true,
        storage: width + option,
      })),
    ]
    return {
      layer: 'finite core only',
      state:
        'stable two-domain Requires problem, width capped at 32; complete stream per operation',
      run: () => {
        last = [...api.selections(domains)]
      },
      validate: () => {
        const plans = last as number[][]
        assert.equal(plans.length, width)
        plans.forEach((plan, index) => assert.deepEqual(plan, [index, index]))
      },
    }
  },
  'diag-core-selection': ({ api, size }) => {
    let last: unknown
    const domains: Domains = Array.from({ length: Math.min(size, 6) }, (_, node) => [
      { identity: node, required: [], retained: true, storage: node },
      { identity: node + 10, required: [], retained: false, storage: node + 10 },
    ])
    return {
      layer: 'finite core only',
      state: 'stable finite domains; complete bounded plan stream per operation',
      run: () => {
        last = [...api.selections(domains)]
      },
      validate: () => {
        assert.equal((last as unknown[]).length, 2 ** domains.length)
      },
    }
  },
  'diag-cycle': ({ api, size }) => {
    interface Link {
      next?: Link
    }
    let last: unknown
    const nodes: Link[] = Array.from({ length: size }, () => ({}))
    nodes.forEach((node, index) => {
      node.next = nodes[(index + 1) % size]
    })
    return {
      run: () => {
        last = api.snapshot(nodes[0])
      },
      validate: () => {
        let cursor = last as Link
        assert.notEqual(cursor, nodes[0])
        for (let index = 0; index < size; index += 1) cursor = cursor.next!
        assert.equal(cursor, last)
      },
    }
  },
  'diag-deserialize-bigints': ({ api, size }) => {
    const { decode, encode } = textCodec(api)
    const large = 2n ** 256n
    const text = encode(
      Array.from({ length: size * 8 }, (_, n) => ({
        flag: BigInt(n % 2),
        id: BigInt(n),
        signed: -BigInt(n) * 1_000_003n,
        wide: large + BigInt(n),
      })),
    )
    let last: unknown
    return {
      layer: 'serialization',
      state: 'decodes the JSON text of 8 × size records with four distinct and shared bigints each',
      run: () => {
        last = decode(text)
      },
      validate: () => {
        assert.equal(encode(last), text)
      },
    }
  },
  'diag-deserialize-graph': ({ api, size }) => {
    const { decode, encode } = textCodec(api)
    const text = encode(serializationGraph(size))
    let last: unknown
    return {
      layer: 'serialization',
      state:
        'decodes the JSON text of a size-record graph with shared children, a Map, dates and a cycle',
      run: () => {
        last = decode(text)
      },
      validate: () => {
        assert.equal(encode(last), text)
      },
    }
  },
  'diag-deserialize-limited': ({ api }) => ({
    layer: 'serialization',
    state: 'decodes the six serialization fixture texts in rotation under a limit never reached',
    ...serializationOperation(api, 'deserialize', 2 ** 52),
  }),
  'diag-fanout': ({ api, size }) => {
    let last: unknown
    const current = Array.from({ length: size }, () => ({ n: 0 }))
    const next = [
      Array.from({ length: size }, () => ({ n: 1 })),
      Array.from({ length: size }, () => ({ n: 0 })),
    ]
    let turn = 0
    return {
      state: 'alternating desired values; every operation changes existing leaf values',
      run: () => {
        last = api.reconcile(current, next[turn++ % 2])
      },
      validate: () => {
        assert.equal(last, current)
        assert(current.every((item) => item.n === turn % 2))
      },
    }
  },
  'diag-module-buffer': ({ api, size }) => {
    let last: unknown
    const left = new ArrayBuffer(size * 1024)
    const right = left.slice(0)
    return {
      layer: 'native module only',
      state: 'stable equal byte stores; full extent comparison per operation',
      run: () => {
        last = api.sameBuffer(left, right)
      },
      validate: () => {
        assert.equal(last, true)
      },
    }
  },
  'diag-module-date': ({ api }) => {
    let last: unknown
    const date = new Date(42)
    return {
      layer: 'native module only',
      run: () => {
        last = api.copyDate(date, identity)
      },
      validate: () => {
        assert.notEqual(last, date)
        assert.equal((last as Date).getTime(), 42)
      },
    }
  },
  'diag-noop': (context) => produceAlias(context, false),
  'diag-produce-deep': ({ api, size }) => {
    let last: unknown
    const deep = Array.from({ length: size }, (_, n) => ({
      items: [
        { id: n, tags: [n, n + 1] },
        { id: n + 1, tags: [n + 1, n + 2] },
      ],
      meta: { label: `node-${n}`, nested: { depth: 3, flags: { hot: false } } },
    }))
    const input = { counter: 0, deep }
    return {
      state: 'one leaf changed under a root with n unchanged deep subtrees; input stable',
      run: () => {
        last = api.produce(input, (draft) => {
          draft.counter += 1
          return draft
        })
      },
      validate: () => {
        const output = last as typeof input
        assert.notEqual(output, input)
        assert.equal(output.counter, 1)
        assert.equal(input.counter, 0)
        assert.equal(output.deep, deep)
        for (let n = 0; n < size; n += 1) assert.equal(output.deep[n], deep[n])
      },
    }
  },
  'diag-required-max-bytes': ({ api }) => {
    const { deserialize, requiredMaxBytes } = api
    if (requiredMaxBytes === undefined || deserialize === undefined)
      throw new Error('This source tree has no requiredMaxBytes.')
    // Measuring does not modify a document, so each is parsed once.
    const documents = serializationFixtures(api).map(({ text }) => JSON.parse(text) as unknown)
    const expected = documents.map((json) => {
      const maxBytes = requiredMaxBytes(json, { maxBytes: Infinity })
      deserialize(structuredClone(json), { maxBytes })
      assert.throws(() => deserialize(structuredClone(json), { maxBytes: maxBytes - 1 }))
      return maxBytes
    })
    let turn = 0
    let last = 0
    return {
      layer: 'serialization',
      state: 'measures the six serialization fixture documents in rotation, parsed once',
      run: () => {
        last = requiredMaxBytes(documents[turn++ % documents.length], { maxBytes: Infinity })
      },
      validate: () => {
        assert.equal(last, expected[(turn - 1) % documents.length])
      },
    }
  },
  'diag-serialize-graph': ({ api, size }) => {
    const { encode } = textCodec(api)
    const graph = serializationGraph(size)
    const text = encode(graph)
    let last = ''
    return {
      layer: 'serialization',
      state:
        'encodes a size-record graph with shared children, a Map, dates and a cycle as JSON text',
      run: () => {
        last = encode(graph)
      },
      validate: () => {
        assert.equal(last, text)
      },
    }
  },
  'diag-shared-cycle': ({ api, size }) => {
    let last: unknown
    const length = Math.min(size, 8)
    const original = frozenRing(length)
    const desired = { left: ring(length)[0], right: ring(length)[0] }
    const holder = { left: original[0], right: original[0] }
    return {
      state:
        'two independent desired cycles compete for one frozen ring; holder reset per operation; size capped at 8',
      run: () => {
        holder.left = original[0]
        holder.right = original[0]
        last = api.reconcile(holder, desired)
      },
      validate: () => {
        assert.equal(last, holder)
        const collected = [holder.left, holder.right].map((root) => ringMembers(root, length))
        assert(collected[0].every((node) => !collected[1].includes(node)))
        assert.equal(collected.flat().filter((node) => original.includes(node)).length, length)
      },
    }
  },
  'diag-shared-spread': ({ api, size }) => {
    let last: unknown
    const root: Record<string, unknown> = { counter: 0 }
    const children = Array.from({ length: size }, (_, n) => ({
      n,
      nest: { s: String(n) },
      tags: [n, n + 1],
    }))
    for (const [index, child] of children.entries()) root[`k${index}`] = child
    let counter = 0
    return {
      state: 'spread root over shared children; the root is republished in place each operation',
      run: () => {
        counter += 1
        last = api.reconcile(root, { ...root, counter })
      },
      validate: () => {
        assert.equal(last, root)
        assert.equal(root.counter, counter)
        for (const [index, child] of children.entries()) assert.equal(root[`k${index}`], child)
      },
    }
  },
  'diag-sparse': ({ api, shared, size }) => {
    let last: unknown
    const input: unknown[] = new Array(size * 4)
    input[0] = shared
    input[size] = shared
    input[size * 3] = undefined
    return {
      run: () => {
        last = api.snapshot(input)
      },
      validate: () => {
        const output = last as unknown[]
        assert.equal(output.length, input.length)
        assert.deepEqual(Object.keys(output), Object.keys(input))
        assert.equal(output[0], output[size])
        assert.notEqual(output[0], shared)
      },
    }
  },
  'diag-tiny-produce': ({ api, size }) => ({
    state: 'flat object of n keys; recipes rotate: no change, one key, every key',
    ...flatOperation(api, 'produce', size),
  }),
  'diag-tiny-reconcile': ({ api, size }) => ({
    state: 'flat object of n keys updated in place; rotates unchanged, sparse and full nexts',
    ...flatOperation(api, 'reconcile', size),
  }),
  'diag-undo': (context) => produceAlias(context, true),
  'diag-unsupported-cycle': ({ api, size }) => {
    let last: unknown
    // Larger frozen controls already exhibit expensive failed score-tier searches.
    const length = Math.min(size, 16)
    const original = frozenRing(length)
    const desired = ring(length)
    desired[length - 1].payload.value = 1
    const holder = { start: original[0] }
    return {
      state: 'changed frozen ring payload; mutable holder reset per operation; size capped at 16',
      run: () => {
        holder.start = original[0]
        last = api.reconcile(holder, { start: desired[0] })
      },
      validate: () => {
        assert.equal(last, holder)
        let cursor = holder.start
        for (let index = 0; index < length; index += 1) {
          assert.notEqual(cursor, original[index])
          assert.equal(cursor.payload.value, index === length - 1 ? 1 : 0)
          assert.equal(original[index].payload.value, 0)
          assert.equal(original[index].next, original[(index + 1) % length])
          cursor = cursor.next!
        }
        assert.equal(cursor, holder.start)
      },
    }
  },
  'diag-views': ({ api, size }) => {
    let last: unknown
    const buffer = new ArrayBuffer(size * 16)
    const input = {
      buffer,
      views: Array.from({ length: size }, (_, index) =>
        index % 2 === 0 ? new Uint8Array(buffer, index * 8, 4) : new DataView(buffer, index * 8, 4),
      ),
    }
    return {
      run: () => {
        last = api.snapshot(input)
      },
      validate: () => {
        const output = last as typeof input
        assert.notEqual(output.buffer, buffer)
        assert(output.views.every((view) => view.buffer === output.buffer))
        assert.deepEqual(
          output.views.map((view) => [view.byteOffset, view.byteLength]),
          input.views.map((view) => [view.byteOffset, view.byteLength]),
        )
      },
    }
  },
  'serialize': ({ api }) => ({
    layer: 'serialization',
    state: 'encodes the six serialization fixture graphs as text in rotation, one per operation',
    ...serializationOperation(api, 'serialize'),
  }),
}

/** Fixtures are created before warmup. Validation happens after profiling stops. */
export function createDiagnostic(
  name: DiagnosticName,
  api: {
    produce: typeof API.produce
    reconcile: typeof API.reconcile
    selections: typeof selections
    snapshot: typeof API.snapshot
    copyDate: (value: object, resolve: (child: object) => object) => object
    sameBuffer: (left: ArrayBuffer, right: ArrayBuffer) => boolean
    /** The tree's serialization API, if any; only serialization scenarios need it. */
    deserialize?: typeof API.deserialize
    requiredMaxBytes?: typeof API.requiredMaxBytes
    serialize?: typeof API.serialize
  },
  size: number,
) {
  const shared = { n: 0 }
  const alias = { items: Array.from({ length: size }, () => shared) }
  const { layer = 'full API', run, state, validate } = scenarios[name]({ alias, api, shared, size })
  return {
    metadata: {
      layer,
      name,
      size,
      state: state ?? 'stable input; detached output retained until the next operation',
    },
    run,
    validate,
  }
}
