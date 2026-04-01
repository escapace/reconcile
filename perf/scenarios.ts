import assert from 'node:assert/strict'

import { cloneDeep } from 'es-toolkit'
import { enableMapSet, produce, setAutoFreeze } from 'immer'

import { createPatch } from '../src/index'
import { reconcile } from '../src/reconcile'
import { snapshot } from '../src/snapshot'

export const BATCH_SIZE = 150
const INPUT_COUNT = 64

let sink: unknown

const keepAlive = (value: unknown): void => {
  sink = value
  void sink
}

interface SnapshotInput {
  binary: {
    buffer: ArrayBuffer
    typed: Uint16Array
    view: DataView
  }
  date: Date
  id: number
  list: Array<number | undefined>
  map: Map<string, { score: number; tags: string[] }>
  nested: {
    flags: {
      cold: boolean
      hot: boolean
    }
    order: Record<string, number>
    series: number[]
  }
  set: Set<string>
  sharedLeft: {
    label: string
    values: number[]
  }
  sharedRight: {
    label: string
    values: number[]
  }
  self?: SnapshotInput
}

interface ReconcileTarget {
  binary: {
    buffer: ArrayBuffer
    typed: Uint8Array
    view: DataView
  }
  date: Date
  id: number
  list: Array<number | undefined>
  map: Map<string, { score: number; tag: string }>
  nested: {
    flags: {
      hot: boolean
      warm: boolean
    }
    order: Record<string, number>
    stats: {
      count: number
      total: number
    }
  }
  set: Set<string>
  sharedLeft: {
    label: string
    values: number[]
  }
  sharedRight: {
    label: string
    values: number[]
  }
  add?: {
    code: string
    value: number
  }
  remove?: string
  self?: ReconcileTarget
}

interface ReconcileSlot {
  current: ReconcileTarget
  index: 0 | 1
  targets: readonly [ReconcileTarget, ReconcileTarget]
}

interface PlainObjectTarget {
  flags: {
    hot: boolean
    warm: boolean
    cold?: boolean
  }
  id: number
  nested: {
    info: {
      code: string
      label: string
    }
    order: {
      alpha?: number
      bravo?: number
      charlie?: number
      delta?: number
    }
    stats: {
      count: number
      total: number
    }
  }
  sharedLeft: {
    label: string
    value: number
  }
  sharedRight: {
    label: string
    value: number
  }
  add?: {
    code: string
    value: number
  }
  remove?: string
  self?: PlainObjectTarget
}

interface PlainObjectSlot {
  current: PlainObjectTarget
  index: 0 | 1
  targets: readonly [PlainObjectTarget, PlainObjectTarget]
}

const createSeries = (seed: number, length: number, stride: number): number[] => {
  const values = new Array<number>(length)

  for (let index = 0; index < length; index += 1) {
    values[index] = seed + index * stride
  }

  return values
}

const createSparseArray = (
  length: number,
  entries: ReadonlyArray<readonly [number, number]>,
): Array<number | undefined> => {
  const result = new Array<number | undefined>(length)

  for (const [index, value] of entries) {
    result[index] = value
  }

  return result
}

const createOrderedRecord = (
  entries: ReadonlyArray<readonly [string, number]>,
): Record<string, number> => {
  const result: Record<string, number> = {}

  for (const [key, value] of entries) {
    result[key] = value
  }

  return result
}

const createArrayBuffer = (seed: number, length: number, stride: number): ArrayBuffer => {
  const values = new Uint8Array(length)

  for (let index = 0; index < length; index += 1) {
    values[index] = (seed + index * stride) & 255
  }

  return values.buffer
}

const createSnapshotInput = (seed: number): SnapshotInput => {
  const shared = {
    label: `shared-${seed % 7}`,
    values: createSeries(seed, 4, 2),
  }
  const input: SnapshotInput = {
    binary: {
      buffer: createArrayBuffer(seed * 3 + 1, 24, 7),
      typed: new Uint16Array(createSeries(seed + 2, 8, 3)),
      view: new DataView(createArrayBuffer(seed * 5 + 2, 12, 11)),
    },
    date: new Date(Date.UTC(2024, seed % 12, (seed % 28) + 1, seed % 24, seed % 60, 0)),
    id: seed,
    list: createSparseArray(8, [
      [1, seed],
      [3, seed + 2],
      [6, seed + 5],
    ]),
    map: new Map<string, { score: number; tags: string[] }>([
      [
        `alpha-${seed % 5}`,
        {
          score: seed + 1,
          tags: [`hot-${seed % 3}`, `cold-${seed % 5}`],
        },
      ],
      [
        `beta-${seed % 7}`,
        {
          score: seed + 2,
          tags: [`warm-${seed % 4}`],
        },
      ],
    ]),
    nested: {
      flags: {
        cold: seed % 2 === 0,
        hot: seed % 3 === 0,
      },
      order: createOrderedRecord([
        ['delta', seed + 4],
        ['alpha', seed + 1],
        ['charlie', seed + 3],
        ['bravo', seed + 2],
      ]),
      series: createSeries(seed, 6, 1),
    },
    set: new Set([`group-${seed % 4}`, `kind-${seed % 3}`, `tag-${seed % 7}`]),
    sharedLeft: shared,
    sharedRight: shared,
  }

  input.self = input

  return input
}

const createReconcileTarget = (seed: number, variant: 0 | 1): ReconcileTarget => {
  const shared = {
    label: variant === 0 ? `shared-a-${seed}` : `shared-b-${seed}`,
    values: createSeries(seed + variant, 5, variant === 0 ? 2 : 3),
  }
  const target: ReconcileTarget = {
    ...(variant === 0
      ? { remove: `remove-${seed}` }
      : { add: { code: `add-${seed}`, value: seed * 10 + variant } }),
    binary: {
      buffer: createArrayBuffer(seed * 7 + variant, 24, variant === 0 ? 5 : 9),
      typed: new Uint8Array(createSeries(seed + variant + 1, 16, variant === 0 ? 2 : 4)),
      view: new DataView(createArrayBuffer(seed * 11 + variant, 12, variant === 0 ? 3 : 7)),
    },
    date: new Date(Date.UTC(2025, (seed + variant) % 12, (seed % 28) + 1, variant, seed % 60, 0)),
    id: seed,
    list:
      variant === 0
        ? createSparseArray(8, [
            [1, seed + 1],
            [4, seed + 4],
            [6, seed + 6],
          ])
        : createSparseArray(9, [
            [0, seed + 2],
            [3, seed + 5],
            [7, seed + 8],
          ]),
    map: new Map<string, { score: number; tag: string }>(
      variant === 0
        ? [
            ['alpha', { score: seed + 1, tag: 'cold' }],
            ['beta', { score: seed + 2, tag: 'keep' }],
          ]
        : [
            ['beta', { score: seed + 3, tag: 'keep' }],
            ['gamma', { score: seed + 4, tag: 'hot' }],
          ],
    ),
    nested: {
      flags: {
        hot: variant === 1,
        warm: seed % 2 === 0,
      },
      order:
        variant === 0
          ? createOrderedRecord([
              ['delta', seed + 4],
              ['alpha', seed + 1],
              ['charlie', seed + 3],
              ['bravo', seed + 2],
            ])
          : createOrderedRecord([
              ['bravo', seed + 12],
              ['charlie', seed + 13],
              ['alpha', seed + 11],
              ['delta', seed + 14],
            ]),
      stats: {
        count: seed + variant,
        total: seed * 2 + variant,
      },
    },
    set:
      variant === 0
        ? new Set([`cold-${seed % 3}`, `keep-${seed % 5}`])
        : new Set([`fresh-${seed % 6}`, `hot-${seed % 4}`, `keep-${seed % 5}`]),
    sharedLeft: shared,
    sharedRight: shared,
  }

  target.self = target

  return target
}

const createReconcileSlots = (): ReconcileSlot[] =>
  Array.from({ length: INPUT_COUNT }, (_, index) => {
    const seed = index + 1
    const targetA = createReconcileTarget(seed, 0)
    const targetB = createReconcileTarget(seed, 1)

    return {
      current: cloneDeep(targetA),
      index: 0,
      targets: [targetA, targetB] as const,
    }
  })

function createPlainObjectTarget(seed: number, variant: 0 | 1): PlainObjectTarget {
  // Seed buckets intentionally exercise the main plain-object paths:
  //   0 → aligned, equal-length, value-only updates
  //   1 → aligned across shared prefix, tail add/remove
  //   2 → aligned parent with diverged nested key order
  //   3 → diverged root key order
  const mode = seed % 4
  const shared = {
    label: variant === 0 ? `shared-a-${seed}` : `shared-b-${seed}`,
    value: seed * 10 + variant,
  }
  const flags: PlainObjectTarget['flags'] =
    variant === 0
      ? {
          cold: seed % 2 === 0,
          hot: seed % 3 === 0,
          warm: true,
        }
      : {
          cold: seed % 2 === 0,
          hot: seed % 3 !== 0,
          warm: false,
        }
  const nestedOrder: PlainObjectTarget['nested']['order'] =
    mode === 2
      ? variant === 0
        ? createOrderedRecord([
            ['delta', seed + 4],
            ['alpha', seed + 1],
            ['charlie', seed + 3],
            ['bravo', seed + 2],
          ])
        : createOrderedRecord([
            ['bravo', seed + 12],
            ['charlie', seed + 13],
            ['alpha', seed + 11],
            ['delta', seed + 14],
          ])
      : mode === 1
        ? variant === 0
          ? createOrderedRecord([
              ['alpha', seed + 1],
              ['bravo', seed + 2],
              ['charlie', seed + 3],
            ])
          : createOrderedRecord([
              ['alpha', seed + 11],
              ['bravo', seed + 12],
              ['charlie', seed + 13],
              ['delta', seed + 14],
            ])
        : createOrderedRecord([
            ['alpha', seed + 1 + variant],
            ['bravo', seed + 2 + variant],
            ['charlie', seed + 3 + variant],
            ['delta', seed + 4 + variant],
          ])
  const nested: PlainObjectTarget['nested'] = {
    info: {
      code: variant === 0 ? `code-a-${seed}` : `code-b-${seed}`,
      label: mode === 0 ? 'aligned' : mode === 1 ? 'tail' : mode === 2 ? 'nested' : 'root',
    },
    order: nestedOrder,
    stats: {
      count: seed + variant,
      total: seed * 2 + variant,
    },
  }
  const target: Partial<PlainObjectTarget> = {}

  if (mode === 3 && variant === 0) {
    target.remove = `remove-${seed}`
  }

  target.id = seed
  target.flags = flags
  target.nested = nested
  target.sharedLeft = shared
  target.sharedRight = shared

  if (mode === 1 && variant === 1) {
    target.add = { code: `add-${seed}`, value: seed * 100 + variant }
  }

  if (mode === 3 && variant === 1) {
    target.add = { code: `add-${seed}`, value: seed * 100 + variant }
  }

  target.self = target as PlainObjectTarget

  return target as PlainObjectTarget
}

const createPlainObjectSlots = (): PlainObjectSlot[] =>
  Array.from({ length: INPUT_COUNT }, (_, index) => {
    const seed = index + 1
    const targetA = createPlainObjectTarget(seed, 0)
    const targetB = createPlainObjectTarget(seed, 1)

    return {
      current: cloneDeep(targetA),
      index: 0,
      targets: [targetA, targetB] as const,
    }
  })

const createSnapshotBatchRunner = (
  cloneValue: (value: SnapshotInput) => unknown,
  inputs: readonly SnapshotInput[],
): (() => void) => {
  let cursor = 0

  return () => {
    for (let index = 0; index < BATCH_SIZE; index += 1) {
      keepAlive(cloneValue(inputs[cursor]))
      cursor = (cursor + 1) % inputs.length
    }
  }
}

const createReconcileBatchRunner = (
  reconcileValue: (current: ReconcileTarget, next: ReconcileTarget) => ReconcileTarget,
  slots: ReconcileSlot[],
): (() => void) => {
  let cursor = 0

  return () => {
    for (let index = 0; index < BATCH_SIZE; index += 1) {
      const slot = slots[cursor]
      const nextIndex = slot.index === 0 ? 1 : 0
      const result = reconcileValue(slot.current, slot.targets[nextIndex])

      slot.current = result
      slot.index = nextIndex
      keepAlive(result)
      cursor = (cursor + 1) % slots.length
    }
  }
}

function reconcileRootPlainObjectValue(
  current: PlainObjectTarget,
  next: PlainObjectTarget,
): PlainObjectTarget {
  return reconcile(current, next)
}

export const createContextRuntimeSnapshotBenchmarks = () => {
  const snapshotInputs = Array.from({ length: INPUT_COUNT }, (_, index) =>
    createSnapshotInput(index + 1),
  )

  const baselineSnapshotBatch = createSnapshotBatchRunner(structuredClone, snapshotInputs)
  const runtimeSnapshotBatch = createSnapshotBatchRunner(snapshot, snapshotInputs)

  return {
    baselineSnapshotBatch,
    runtimeSnapshotBatch,
  }
}

export const createContextRuntimeReconcileBenchmarks = () => {
  const baselineReconcileBatch = createReconcileBatchRunner(
    (_current, next) => cloneDeep(next),
    createReconcileSlots(),
  )
  const runtimeReconcileBatch = createReconcileBatchRunner(
    (current, next) => reconcile(current, next),
    createReconcileSlots(),
  )

  return {
    baselineReconcileBatch,
    runtimeReconcileBatch,
  }
}

function createPlainObjectBatchRunner(
  reconcileValue: (current: PlainObjectTarget, next: PlainObjectTarget) => PlainObjectTarget,
  slots: PlainObjectSlot[],
): () => void {
  let cursor = 0

  return () => {
    for (let index = 0; index < BATCH_SIZE; index += 1) {
      const slot = slots[cursor]
      const nextIndex = slot.index === 0 ? 1 : 0
      const result = reconcileValue(slot.current, slot.targets[nextIndex])

      slot.current = result
      slot.index = nextIndex
      keepAlive(result)
      cursor = (cursor + 1) % slots.length
    }
  }
}

export const createContextRuntimeReconcilePlainObjectBenchmarks = () => {
  const baselineReconcilePlainObjectBatch = createPlainObjectBatchRunner(
    (_current, next) => cloneDeep(next),
    createPlainObjectSlots(),
  )
  const runtimeReconcilePlainObjectBatch = createPlainObjectBatchRunner(
    reconcileRootPlainObjectValue,
    createPlainObjectSlots(),
  )

  return {
    baselineReconcilePlainObjectBatch,
    runtimeReconcilePlainObjectBatch,
  }
}

enableMapSet()
setAutoFreeze(false)

/**
 * Shared-surface `createPatch` vs Immer benchmark.
 *
 * Included on purpose:
 * - plain objects
 * - arrays
 * - `Map<string, object>` updates
 * - `Set<string>` membership changes
 * - nested updates plus add/delete/update operations
 *
 * Excluded on purpose because they are not a clean overlap for a fair one-to-one comparison:
 * - cycles or repeated aliases
 * - drafted object-valued map keys
 * - typed-array / `ArrayBuffer` / `DataView` mutation
 * - authoritative nested draft returns
 * - iterator- or callback-based `Map` / `Set` draft APIs
 *
 * Immer is configured with `enableMapSet()` and `setAutoFreeze(false)` so this measures draft
 * update work rather than freeze costs, and both runtimes execute the same toggle recipe.
 */
interface CreatePatchImmerItem {
  done: boolean
  id: string
  nested: {
    label: string
    weight: number
  }
  scores: number[]
}

interface CreatePatchImmerMapValue {
  done: boolean
  meta: {
    label: string
    rank: number
  }
}

interface CreatePatchImmerObjectState {
  counts: {
    active: number
    total: number
  }
  flags: {
    hot: boolean
    warm: boolean
  }
  extra?: {
    code: string
    weight: number
  }
  note?: string
}

interface CreatePatchImmerState {
  id: number
  items: CreatePatchImmerItem[]
  object: CreatePatchImmerObjectState
  phase: 0 | 1
  table: Map<string, CreatePatchImmerMapValue>
  tags: Set<string>
}

interface CreatePatchImmerSlot {
  current: CreatePatchImmerState
}

const createPatchImmerPrimaryItem = (seed: number, phase: 0 | 1): CreatePatchImmerItem => ({
  done: phase === 1,
  id: `primary-${seed}`,
  nested: {
    label: phase === 0 ? `primary-cold-${seed}` : `primary-hot-${seed}`,
    weight: phase === 0 ? seed + 1 : seed + 11,
  },
  scores: phase === 0 ? [seed, seed + 1, seed + 2] : [seed, seed + 11, seed + 2],
})

const createPatchImmerSecondaryItem = (seed: number, phase: 0 | 1): CreatePatchImmerItem =>
  phase === 0
    ? {
        done: false,
        id: `secondary-${seed}`,
        nested: {
          label: `secondary-cold-${seed}`,
          weight: seed + 2,
        },
        scores: [seed + 3, seed + 4, seed + 5],
      }
    : {
        done: true,
        id: `secondary-hot-${seed}`,
        nested: {
          label: `secondary-hot-${seed}`,
          weight: seed + 12,
        },
        scores: [seed + 20, seed + 21],
      }

const createPatchImmerTailItem = (seed: number): CreatePatchImmerItem => ({
  done: false,
  id: `tail-${seed}`,
  nested: {
    label: `tail-${seed}`,
    weight: seed + 13,
  },
  scores: [seed + 30, seed + 31, seed + 32],
})

const createPatchImmerAlphaMapValue = (seed: number, phase: 0 | 1): CreatePatchImmerMapValue => ({
  done: phase === 1,
  meta: {
    label: phase === 0 ? `alpha-cold-${seed}` : `alpha-hot-${seed}`,
    rank: phase === 0 ? seed + 1 : seed + 41,
  },
})

const createPatchImmerBetaMapValue = (seed: number): CreatePatchImmerMapValue => ({
  done: true,
  meta: {
    label: `beta-${seed}`,
    rank: seed + 2,
  },
})

const createPatchImmerGammaMapValue = (seed: number): CreatePatchImmerMapValue => ({
  done: false,
  meta: {
    label: `gamma-${seed}`,
    rank: seed + 42,
  },
})

const createPatchImmerObjectState = (seed: number, phase: 0 | 1): CreatePatchImmerObjectState =>
  phase === 0
    ? {
        counts: {
          active: seed + 1,
          total: seed + 5,
        },
        flags: {
          hot: false,
          warm: true,
        },
        note: `note-${seed}`,
      }
    : {
        counts: {
          active: seed + 2,
          total: seed + 8,
        },
        extra: {
          code: `extra-${seed}`,
          weight: seed + 10,
        },
        flags: {
          hot: true,
          warm: false,
        },
      }

const createPatchImmerItems = (seed: number, phase: 0 | 1): CreatePatchImmerItem[] =>
  phase === 0
    ? [createPatchImmerPrimaryItem(seed, 0), createPatchImmerSecondaryItem(seed, 0)]
    : [
        createPatchImmerPrimaryItem(seed, 1),
        createPatchImmerSecondaryItem(seed, 1),
        createPatchImmerTailItem(seed),
      ]

const createPatchImmerTable = (
  seed: number,
  phase: 0 | 1,
): Map<string, CreatePatchImmerMapValue> =>
  phase === 0
    ? new Map<string, CreatePatchImmerMapValue>([
        ['alpha', createPatchImmerAlphaMapValue(seed, 0)],
        ['beta', createPatchImmerBetaMapValue(seed)],
      ])
    : new Map<string, CreatePatchImmerMapValue>([
        ['alpha', createPatchImmerAlphaMapValue(seed, 1)],
        ['gamma', createPatchImmerGammaMapValue(seed)],
      ])

/* eslint-disable perfectionist/sort-sets */
const createPatchImmerTags = (seed: number, phase: 0 | 1): Set<string> =>
  phase === 0
    ? new Set<string>([`shared-${seed % 3}`, `phase-0-${seed % 5}`])
    : new Set<string>([`shared-${seed % 3}`, `phase-1-${seed % 5}`, `phase-1-extra-${seed % 4}`])
/* eslint-enable perfectionist/sort-sets */

const createPatchImmerState = (seed: number, phase: 0 | 1): CreatePatchImmerState => ({
  id: seed,
  items: createPatchImmerItems(seed, phase),
  object: createPatchImmerObjectState(seed, phase),
  phase,
  table: createPatchImmerTable(seed, phase),
  tags: createPatchImmerTags(seed, phase),
})

const projectCreatePatchImmerState = (state: CreatePatchImmerState) => ({
  id: state.id,
  items: state.items.map((item) => ({
    done: item.done,
    id: item.id,
    nested: {
      label: item.nested.label,
      weight: item.nested.weight,
    },
    scores: [...item.scores],
  })),
  object: {
    counts: {
      active: state.object.counts.active,
      total: state.object.counts.total,
    },
    ...(state.object.extra === undefined
      ? {}
      : {
          extra: {
            code: state.object.extra.code,
            weight: state.object.extra.weight,
          },
        }),
    flags: {
      hot: state.object.flags.hot,
      warm: state.object.flags.warm,
    },
    ...(state.object.note === undefined ? {} : { note: state.object.note }),
  },
  phase: state.phase,
  table: Array.from(state.table.entries(), ([key, value]) => [
    key,
    {
      done: value.done,
      meta: {
        label: value.meta.label,
        rank: value.meta.rank,
      },
    },
  ]),
  tags: Array.from(state.tags.values()),
})

const toggleCreatePatchImmerDraft = (draft: CreatePatchImmerState): CreatePatchImmerState => {
  const seed = draft.id

  if (draft.phase === 0) {
    draft.phase = 1

    draft.object.counts.active = seed + 2
    draft.object.counts.total = seed + 8
    draft.object.flags.hot = true
    draft.object.flags.warm = false
    delete draft.object.note
    draft.object.extra = {
      code: `extra-${seed}`,
      weight: seed + 10,
    }

    draft.items[0].done = true
    draft.items[0].nested.label = `primary-hot-${seed}`
    draft.items[0].nested.weight = seed + 11
    draft.items[0].scores[1] = seed + 11
    draft.items.splice(1, 1, createPatchImmerSecondaryItem(seed, 1), createPatchImmerTailItem(seed))

    const alpha = draft.table.get('alpha')!
    alpha.done = true
    alpha.meta.label = `alpha-hot-${seed}`
    alpha.meta.rank = seed + 41
    draft.table.delete('beta')
    draft.table.set('gamma', createPatchImmerGammaMapValue(seed))

    draft.tags.delete(`phase-0-${seed % 5}`)
    draft.tags.add(`phase-1-${seed % 5}`)
    draft.tags.add(`phase-1-extra-${seed % 4}`)

    return draft
  }

  draft.phase = 0

  draft.object.counts.active = seed + 1
  draft.object.counts.total = seed + 5
  draft.object.flags.hot = false
  draft.object.flags.warm = true
  delete draft.object.extra
  draft.object.note = `note-${seed}`

  draft.items[0].done = false
  draft.items[0].nested.label = `primary-cold-${seed}`
  draft.items[0].nested.weight = seed + 1
  draft.items[0].scores[1] = seed + 1
  draft.items.splice(1, 2, createPatchImmerSecondaryItem(seed, 0))

  const alpha = draft.table.get('alpha')!
  alpha.done = false
  alpha.meta.label = `alpha-cold-${seed}`
  alpha.meta.rank = seed + 1
  draft.table.delete('gamma')
  draft.table.set('beta', createPatchImmerBetaMapValue(seed))

  draft.tags.delete(`phase-1-${seed % 5}`)
  draft.tags.delete(`phase-1-extra-${seed % 4}`)
  draft.tags.add(`phase-0-${seed % 5}`)

  return draft
}

const validateCreatePatchImmerScenario = (): void => {
  for (let seed = 1; seed <= 4; seed += 1) {
    const phaseZero = createPatchImmerState(seed, 0)
    const createPatchPhaseOne = createPatch(phaseZero, toggleCreatePatchImmerDraft)
    const immerPhaseOne = produce(phaseZero, toggleCreatePatchImmerDraft)
    const expectedPhaseOne = createPatchImmerState(seed, 1)

    assert.deepStrictEqual(
      projectCreatePatchImmerState(createPatchPhaseOne),
      projectCreatePatchImmerState(expectedPhaseOne),
    )
    assert.deepStrictEqual(
      projectCreatePatchImmerState(immerPhaseOne),
      projectCreatePatchImmerState(expectedPhaseOne),
    )
    assert.deepStrictEqual(
      projectCreatePatchImmerState(createPatchPhaseOne),
      projectCreatePatchImmerState(immerPhaseOne),
    )

    const createPatchPhaseZero = createPatch(createPatchPhaseOne, toggleCreatePatchImmerDraft)
    const immerPhaseZero = produce(immerPhaseOne, toggleCreatePatchImmerDraft)

    assert.deepStrictEqual(
      projectCreatePatchImmerState(createPatchPhaseZero),
      projectCreatePatchImmerState(phaseZero),
    )
    assert.deepStrictEqual(
      projectCreatePatchImmerState(immerPhaseZero),
      projectCreatePatchImmerState(phaseZero),
    )
    assert.deepStrictEqual(
      projectCreatePatchImmerState(createPatchPhaseZero),
      projectCreatePatchImmerState(immerPhaseZero),
    )
  }
}

validateCreatePatchImmerScenario()

const createPatchImmerSlots = (): CreatePatchImmerSlot[] =>
  Array.from({ length: INPUT_COUNT }, (_, index) => ({
    current: createPatchImmerState(index + 1, 0),
  }))

const createPatchImmerBatchRunner = (
  applyRecipe: (current: CreatePatchImmerState) => CreatePatchImmerState,
  slots: CreatePatchImmerSlot[],
): (() => void) => {
  let cursor = 0

  return () => {
    for (let index = 0; index < BATCH_SIZE; index += 1) {
      const slot = slots[cursor]
      const result = applyRecipe(slot.current)

      slot.current = result
      keepAlive(result)
      cursor = (cursor + 1) % slots.length
    }
  }
}

export const createContextRuntimeCreatePatchImmerBenchmarks = () => {
  const createPatchBatch = createPatchImmerBatchRunner(
    (current) => createPatch(current, toggleCreatePatchImmerDraft),
    createPatchImmerSlots(),
  )
  const immerBatch = createPatchImmerBatchRunner(
    (current) => produce(current, toggleCreatePatchImmerDraft),
    createPatchImmerSlots(),
  )

  return {
    createPatchBatch,
    immerBatch,
  }
}
