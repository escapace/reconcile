import { assert, describe, it } from 'vitest'
import { produce } from '../index'

describe('finalization dependency propagation', () => {
  for (const dataView of [false, true]) {
    for (const reverse of [false, true]) {
      it(`keeps an unchanged outside buffer and the views on it (DataView: ${dataView}, reverse: ${reverse})`, () => {
        const buffer = new ArrayBuffer(4)
        const view = dataView ? new DataView(buffer, 1, 2) : new Uint8Array(buffer, 1, 2)
        const current = { nested: { view } }
        const result = produce(current, (draft) =>
          reverse ? { ...{ root: draft }, buffer } : { buffer, root: draft },
        )
        assert.equal(result.buffer, result.root.nested.view.buffer)
        assert.equal(result.root.nested.view.byteOffset, 1)
        assert.equal(result.root.nested.view.byteLength, 2)
        // Nothing changed, so the result holds the caller's buffer and the original view.
        assert.equal(result.buffer, buffer)
        assert.equal(result.root.nested.view, view)
      })
    }
  }

  it('processes long sharing chains without repeatedly scanning the entire graph', () => {
    const length = 300
    const dates = Array.from({ length: length + 1 }, (_, index) => new Date(index))
    let scans = 0
    const entries = Array.from(
      { length },
      (_, index) =>
        new Proxy(
          {
            left: dates[length - index],
            right: dates[length - index - 1],
          },
          {
            ownKeys(target) {
              scans += 1
              return Reflect.ownKeys(target)
            },
          },
        ),
    )
    const result = produce({ child: {} }, (draft) => ({
      entries,
      seed: dates[0],
      trigger: draft.child,
    }))
    assert.equal(result.seed, result.entries[length - 1].right)
    for (let index = 1; index < length; index += 1) {
      assert.equal(result.entries[index - 1].right, result.entries[index].left)
    }
    assert.equal(result.seed, dates[0])
    // Bound observable graph inspection work rather than machine-dependent elapsed time.
    assert.isBelow(scans, length * 30)
  })
})

const wrapSpecial = {
  array: (value: object): unknown => [value],
  map: (value: object): unknown => new Map([['value', value]]),
  object: (value: object): unknown => ({ value }),
  set: (value: object): unknown => new Set([value]),
}
const readSpecial = {
  array: (value: unknown): object => (value as object[])[0],
  map: (value: unknown): object => (value as Map<string, object>).get('value')!,
  object: (value: unknown): object => (value as { value: object }).value,
  set: (value: unknown): object => [...(value as Set<object>)][0],
}

for (const kind of ['date', 'buffer', 'typed array', 'data view'] as const) {
  for (const container of ['object', 'array', 'map', 'set'] as const) {
    it.each([false, true])(
      `preserves shared ${kind} through ${container} during ownership expansion (reverse: %s)`,
      (reverse) => {
        const buffer = new ArrayBuffer(4)
        const special =
          kind === 'date'
            ? new Date(0)
            : kind === 'buffer'
              ? buffer
              : kind === 'typed array'
                ? new Uint8Array(buffer)
                : new DataView(buffer)
        const raw = { child: wrapSpecial[container](special), n: 0 }
        const result = produce({}, () =>
          reverse ? { ...{ right: raw }, left: raw } : { left: raw, right: raw },
        )
        const left = readSpecial[container](result.left.child)
        const right = readSpecial[container](result.right.child)
        assert.equal(left, right)
        assert.equal(left, special)
        assert.equal(result.left, raw)
        assert.equal(result.right, raw)
      },
    )
  }
}

it('keeps unchanged outside specials and their buffer aliases when another subtree needs ownership expansion', () => {
  const buffer = new ArrayBuffer(4)
  const view = new Uint8Array(buffer, 1, 2)
  const date = new Date(0)
  const raw = { n: 0 }
  const current = { stable: true }
  const result = produce(current, (draft) => ({
    buffer,
    date,
    left: raw,
    repeated: view,
    right: raw,
    trigger: draft,
    view,
  }))
  assert.equal(result.trigger, current)
  assert.equal(result.buffer, buffer)
  assert.equal(result.date, date)
  assert.equal(result.view, view)
  assert.equal(result.view, result.repeated)
  assert.equal(result.view.buffer, result.buffer)
  assert.equal(result.view.byteOffset, 1)
  assert.equal(result.view.byteLength, 2)
  assert.equal(result.left, raw)
  assert.equal(result.right, raw)
})

it('keeps changed draft specials during ownership expansion', () => {
  const buffer = new ArrayBuffer(4)
  const current = { date: new Date(0), view: new Uint8Array(buffer) }
  const raw = { n: 0 }
  const result = produce(current, (draft) => {
    draft.date.setTime(3)
    draft.view[1] = 7
    return { left: raw, right: raw, root: draft }
  })
  assert.equal(result.root.date.getTime(), 3)
  assert.equal(result.root.view[1], 7)
  assert.equal(current.date.getTime(), 0)
  assert.equal(current.view[1], 0)
  result.root.date.setTime(4)
  result.root.view[1] = 8
  assert.equal(current.date.getTime(), 0)
  assert.equal(current.view[1], 0)
  assert.equal(result.left, raw)
  assert.equal(result.right, raw)
})

it('keeps outside dates in a dormant container without extra container reads', () => {
  const events: string[] = []
  class ObservedDate extends Date {
    constructor(
      private readonly label: string,
      time: number,
    ) {
      super(time)
    }
    override getTime(): number {
      events.push(this.label)
      return super.getTime()
    }
  }
  const seed = new ObservedDate('seed', 1)
  const next = new ObservedDate('next', 2)
  const dormant = new Proxy(
    { next, value: seed },
    {
      ownKeys(target) {
        events.push('container')
        return Reflect.ownKeys(target)
      },
    },
  )
  const result = produce({ child: {} }, (draft) => ({
    dormant,
    seed,
    trigger: draft.child,
  }))
  // Unchanged outside dates stay themselves, so no copy reads them, and they cost the container
  // no more reads than plain objects in the same places.
  assert.notInclude(events, 'seed')
  assert.notInclude(events, 'next')
  const plainEvents: string[] = []
  const plain = { t: 1 }
  produce({ child: {} }, (draft) => ({
    dormant: new Proxy(
      { next: { t: 2 }, value: plain },
      {
        ownKeys(target) {
          plainEvents.push('container')
          return Reflect.ownKeys(target)
        },
      },
    ),
    seed: plain,
    trigger: draft.child,
  }))
  assert.equal(events.length, plainEvents.length)
  assert.equal(result.dormant.value, result.seed)
  assert.equal(result.seed, seed)
  assert.equal(result.dormant.next, next)
})
