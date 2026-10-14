import { assert, describe, it } from 'vitest'
import { isReactive, nextTick, reactive, watch, watchSyncEffect } from 'vue'

import { produce, reconcile, ReconcileError } from '../index'

describe.each(['reconcile', 'produce + reconcile'] as const)('%s Vue observations', (api) => {
  const publish = (current: { first: number; second: number }) =>
    api === 'reconcile'
      ? reconcile(current, { first: 1, second: 2 })
      : reconcile(
          current,
          produce(current, (draft) => {
            draft.first = 1
            draft.second = 2
            return draft
          }),
        )

  it('notifies synchronous watchers through the retained reactive root', () => {
    const current = reactive({ first: 0, second: 0 })
    const observations: number[][] = []
    const stop = watch(
      () => [current.first, current.second],
      (values) => observations.push(values),
      { flush: 'sync' },
    )
    try {
      const result = publish(current)
      assert.equal(result, current)
      assert.isTrue(isReactive(result))
      // This two-property fixture pins non-atomic publication, not a universal
      // notification count for graphs that may require publication repairs.
      assert.deepEqual(observations, [
        [1, 0],
        [1, 2],
      ])
      assert.deepEqual(current, { first: 1, second: 2 })
    } finally {
      stop()
    }
  })

  it('lets Vue batch default watcher callbacks until the next tick', async () => {
    const current = reactive({ first: 0, second: 0 })
    const observations: number[][] = []
    // Watching a reactive object is implicitly deep. Vue, not publication,
    // batches these callbacks; old/new references both name the live root.
    const stop = watch(current, (value, oldValue) => {
      assert.equal(value, current)
      assert.equal(oldValue, current)
      observations.push([value.first, value.second])
    })
    try {
      assert.equal(publish(current), current)
      assert.deepEqual(observations, [])
      assert.deepEqual(current, { first: 1, second: 2 })
      await nextTick()
      assert.deepEqual(observations, [[1, 2]])
    } finally {
      stop()
    }
  })

  it('does not notify watchers for unchanged final values', async () => {
    const current = reactive({ first: 0, second: 0 })
    const synchronous: number[] = []
    const queued: number[] = []
    const stopSync = watch(
      () => current.first,
      (value) => synchronous.push(value),
      { flush: 'sync' },
    )
    const stopQueued = watch(
      () => current.first,
      (value) => queued.push(value),
    )
    try {
      const result =
        api === 'reconcile'
          ? reconcile(current, { first: 0, second: 0 })
          : reconcile(
              current,
              produce(current, (draft) => {
                draft.first = 1
                draft.first = 0
                return draft
              }),
            )
      assert.equal(result, current)
      assert.deepEqual(synchronous, [])
      await nextTick()
      assert.deepEqual(queued, [])
    } finally {
      stopSync()
      stopQueued()
    }
  })

  it('propagates publication failure and leaves earlier reactive writes observable', async () => {
    const failure = new Error('second publication write refused')
    const backing = { first: 0, second: 0 }
    const current = reactive(
      new Proxy(backing, {
        set(target, key, value, receiver) {
          if (key === 'second') throw failure
          return Reflect.set(target, key, value, receiver)
        },
      }),
    )
    assert.isTrue(isReactive(current))
    const synchronous: number[][] = []
    const queued: number[][] = []
    const stopSync = watch(
      () => [current.first, current.second],
      (values) => synchronous.push(values),
      { flush: 'sync' },
    )
    const stopQueued = watch(current, (value) => queued.push([value.first, value.second]))
    try {
      assert.throws(() => publish(current), failure)
      assert.deepEqual(current, { first: 1, second: 0 })
      assert.deepEqual(backing, { first: 1, second: 0 })
      assert.deepEqual(synchronous, [[1, 0]])
      assert.deepEqual(queued, [])
      await nextTick()
      assert.deepEqual(queued, [[1, 0]])
    } finally {
      stopSync()
      stopQueued()
    }
  })

  it('rejects an incompatible reactive root before notifying watchers', async () => {
    const current = reactive({ first: 0, second: 0 })
    const observations: number[] = []
    const stop = watch(
      () => current.first,
      (value) => observations.push(value),
      { flush: 'sync' },
    )
    try {
      assert.throws(
        () =>
          api === 'reconcile'
            ? reconcile(current, [])
            : reconcile(
                current,
                produce(current, () => []),
              ),
        ReconcileError,
      )
      assert.isTrue(isReactive(current))
      assert.deepEqual(current, { first: 0, second: 0 })
      await nextTick()
      assert.deepEqual(observations, [])
    } finally {
      stop()
    }
  })
})

it('produce returns plain changed containers and retains an unchanged reactive branch', async () => {
  const current = reactive({
    changed: { n: 0 },
    list: [] as number[],
    map: new Map<string, number>(),
    set: new Set<number>(),
    stable: { n: 0 },
  })
  const observations: number[][] = []
  const stop = watchSyncEffect(() => {
    observations.push([
      current.changed.n,
      current.list.length,
      current.map.size,
      current.set.size,
      current.stable.n,
    ])
  })
  const queued: number[] = []
  const stopQueued = watch(current, (value) => queued.push(value.stable.n))
  try {
    const result = produce(current, (draft) => {
      draft.changed.n = 1
      draft.list.push(2)
      draft.map.set('key', 3)
      draft.set.add(4)
      return draft
    })
    assert.notEqual(result, current)
    for (const container of [result, result.changed, result.list, result.map, result.set]) {
      assert.isFalse(isReactive(container))
    }
    assert.equal(result.stable, current.stable)
    assert.isTrue(isReactive(result.stable))
    assert.equal(result.changed.n, 1)
    assert.deepEqual(result.list, [2])
    assert.equal(result.map.get('key'), 3)
    assert.isTrue(result.set.has(4))
    assert.deepEqual(observations, [[0, 0, 0, 0, 0]])
    assert.deepEqual(queued, [])
    await nextTick()
    assert.deepEqual(observations, [[0, 0, 0, 0, 0]])
    assert.deepEqual(queued, [])

    result.changed.n = 5
    assert.equal(current.changed.n, 0)
    // Finalized does not mean detached: a retained branch is still shared.
    result.stable.n = 6
    assert.deepEqual(observations, [
      [0, 0, 0, 0, 0],
      [0, 0, 0, 0, 6],
    ])
    await nextTick()
    assert.deepEqual(queued, [6])
  } finally {
    stop()
    stopQueued()
  }
})

it('produce returns the original reactive root after no-op and undone edits', () => {
  const current = reactive({ nested: { n: 0 } })
  const observations: number[] = []
  const stop = watch(
    () => current.nested.n,
    (value) => observations.push(value),
    { flush: 'sync' },
  )
  try {
    assert.equal(
      produce(current, (draft) => draft),
      current,
    )
    const result = produce(current, (draft) => {
      draft.nested.n = 1
      draft.nested.n = 0
      return draft
    })
    assert.equal(result, current)
    assert.isTrue(isReactive(result))
    assert.equal(result.nested, current.nested)
    assert.isTrue(isReactive(result.nested))
    assert.deepEqual(observations, [])
  } finally {
    stop()
  }
})
