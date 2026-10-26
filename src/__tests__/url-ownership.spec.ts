/* eslint-disable perfectionist/sort-objects -- Property insertion order exercises owner discovery in both traversal orders. */
import { assert, describe, it } from 'vitest'

import { produce } from '../produce'
import { isReconcileError, ReconcileError } from '../index'
import { reconcile } from '../reconcile'
import { snapshot } from '../snapshot'

function graph(parametersFirst: boolean) {
  const url = new URL('https://example.test/?b=two%20words&a=1&a=2')
  const source = parametersFirst
    ? { params: url.searchParams, url }
    : { url, params: url.searchParams }
  return { ...source, again: source.params, self: undefined as unknown }
}

describe('URL owned search parameters', () => {
  for (const parametersFirst of [true, false]) {
    it(`snapshots native ownership and cycles with params first: ${parametersFirst}`, () => {
      const source = graph(parametersFirst)
      source.self = source
      const copy = snapshot(source) as typeof source
      assert.instanceOf(copy.url, URL)
      assert.instanceOf(copy.params, URLSearchParams)
      assert.notStrictEqual(copy.url, source.url)
      assert.notStrictEqual(copy.params, source.params)
      assert.strictEqual(copy.params, copy.url.searchParams)
      assert.strictEqual(copy.again, copy.params)
      assert.strictEqual(copy.self, copy)
      assert.strictEqual(copy.url.href, source.url.href)
      assert.deepEqual([...copy.params], [...source.params])
      copy.params.append('a', '3')
      assert.deepEqual(copy.url.searchParams.getAll('a'), ['1', '2', '3'])
      assert.deepEqual(source.params.getAll('a'), ['1', '2'])
    })

    it(`drafts preserve ownership with params first: ${parametersFirst}`, () => {
      const source = graph(parametersFirst)
      const result = produce(source, (draft) => {
        draft.params.append('a', '3')
        assert.strictEqual(draft.url.searchParams, draft.params)
        assert.deepEqual(draft.url.searchParams.getAll('a'), ['1', '2', '3'])
        return draft
      })
      assert.strictEqual(result.url.searchParams, result.params)
      assert.strictEqual(result.again, result.params)
      assert.deepEqual(source.params.getAll('a'), ['1', '2'])
      assert.deepEqual(result.params.getAll('a'), ['1', '2', '3'])
    })
  }

  for (const parametersFirst of [true, false]) {
    for (const href of [
      'data:abc   ?',
      'data:abc   ?a=1',
      'data:abc   ?a=1#fragment',
      'https://example.test/?a=1&a=2&=3',
    ]) {
      for (const query of ['', 'x=1&x=2', '=1&=2']) {
        it(`reconciles owned entries without order dependence: ${parametersFirst}, ${href}, ${query}`, () => {
          const url = new URL(href)
          const parameters = url.searchParams
          const source = parametersFirst ? { params: parameters, url } : { url, params: parameters }
          const nextURL = new URL(href)
          nextURL.search = query
          const next = parametersFirst
            ? { params: nextURL.searchParams, url: nextURL }
            : { url: nextURL, params: nextURL.searchParams }
          assert.strictEqual(reconcile(source, next), source)
          assert.strictEqual(source.url, url)
          assert.strictEqual(source.params, parameters)
          assert.strictEqual(source.url.searchParams, parameters)
          assert.strictEqual(source.url.href, nextURL.href)
          assert.deepEqual([...source.params], [...nextURL.searchParams])
        })
      }
    }
  }

  it('reuses a read-only draft after params are observed before their owner', () => {
    const source = graph(true)
    assert.strictEqual(
      produce(source, (draft) => {
        assert.strictEqual(draft.params.get('a'), '1')
        assert.strictEqual(draft.url.searchParams, draft.params)
        return draft
      }),
      source,
    )
  })

  it('exposes owner changes through a previously read child draft', () => {
    const source = graph(true)
    const result = produce(source, (draft) => {
      const parameters = draft.params
      draft.url.search = '?x=1&x=2'
      assert.deepEqual(
        [...parameters],
        [
          ['x', '1'],
          ['x', '2'],
        ],
      )
      assert.strictEqual(parameters, draft.url.searchParams)
      return draft
    })
    assert.strictEqual(result.params, result.url.searchParams)
    assert.deepEqual(
      [...result.params],
      [
        ['x', '1'],
        ['x', '2'],
      ],
    )
    assert.strictEqual(source.url.search, '?b=two%20words&a=1&a=2')
  })

  it('retains native URL normalization even when parameter edits cancel', () => {
    const source = graph(true)
    const result = produce(source, (draft) => {
      draft.params.append('temporary', '1')
      draft.params.delete('temporary')
      return draft
    })
    assert.deepEqual([...result.params], [...source.params])
    assert.notStrictEqual(result.url, source.url)
    assert.strictEqual(result.url.search, '?b=two+words&a=1&a=2')
    assert.strictEqual(source.url.search, '?b=two%20words&a=1&a=2')
    assert.strictEqual(result.params, result.url.searchParams)
  })

  it('preserves native normalization for borrowed sort and absent-name deletion', () => {
    for (const operation of ['sort', 'delete'] as const) {
      const url = new URL('https://example.test/?a=two%20words')
      const source = { params: url.searchParams, url }
      const result = produce(source, (draft) => {
        if (operation === 'sort') URLSearchParams.prototype.sort.call(draft.params)
        else URLSearchParams.prototype.delete.call(draft.params, 'absent')
        return draft
      })
      assert.strictEqual(result.url.href, 'https://example.test/?a=two+words')
      assert.strictEqual(result.params, result.url.searchParams)
      assert.strictEqual(source.url.href, 'https://example.test/?a=two%20words')
    }
  })

  it('retains opaque URL empty-query normalization from a borrowed native mutator', () => {
    const url = new URL('data:text/plain,hello?')
    const source = { params: url.searchParams, url }
    const result = produce(source, (draft) => {
      URLSearchParams.prototype.sort.call(draft.params)
      return draft
    })
    assert.strictEqual(result.url.href, 'data:text/plain,hello')
    assert.strictEqual(source.url.href, 'data:text/plain,hello?')
    assert.strictEqual(result.params, result.url.searchParams)
  })

  it('retains earlier captured parameters when a later owner getter mutates its query', () => {
    const url = new URL('https://example.test/?a=old&a=second')
    let reads = 0
    const source = {
      params: url.searchParams,
      get url() {
        reads += 1
        url.search = '?a=new'
        return url
      },
    }
    const result = snapshot(source) as typeof source
    assert.strictEqual(reads, 1)
    assert.strictEqual(result.url.search, '?a=old&a=second')
    assert.deepEqual(result.params.getAll('a'), ['old', 'second'])
    assert.strictEqual(result.params, result.url.searchParams)
  })

  it('reuses native objects after edits cancel without normalization changes', () => {
    const url = new URL('https://example.test/?a=1&a=2')
    const source = { params: url.searchParams, url }
    assert.strictEqual(
      produce(source, (draft) => {
        draft.params.append('temporary', '1')
        draft.params.delete('temporary')
        return draft
      }),
      source,
    )
  })

  it('rejects external parameter memo entries lacking private ownership metadata', () => {
    const source = graph(true)
    for (const replacement of [new URLSearchParams(source.params), new URL(source.url.href)]) {
      const memo = new WeakMap<object, object>([[source.params, replacement]])
      let caught: unknown
      try {
        snapshot(source, memo)
      } catch (error) {
        caught = error
      }
      assert.instanceOf(caught, ReconcileError)
      assert.strictEqual(caught.cause.type, 'SnapshotURLSearchParamsMemoIncompatible')
    }
  })

  it('trusts consistent prepopulated owner and child memo entries', () => {
    const source = graph(true)
    const replacement = new URL(source.url.href)
    const memo = new WeakMap<object, object>([
      [source.url, replacement],
      [source.params, replacement.searchParams],
    ])
    const result = snapshot(source, memo) as typeof source
    assert.strictEqual(result.url, replacement)
    assert.strictEqual(result.params, replacement.searchParams)
  })

  it('does not invoke an owner getter while first reading a params draft', () => {
    const url = new URL('https://example.test/?a=1')
    let reads = 0
    const source = {
      params: url.searchParams,
      get url() {
        reads += 1
        return url
      },
    }
    produce(source, (draft) => {
      assert.strictEqual(draft.params.get('a'), '1')
      assert.strictEqual(reads, 0)
      assert.strictEqual(draft.url.searchParams, draft.params)
      assert.strictEqual(reads, 1)
      return source
    })
  })

  it('observes enumerable getters once in their existing snapshot order', () => {
    const url = new URL('https://example.test/?a=1')
    const observations: string[] = []
    const source = {
      get params() {
        observations.push('params')
        return url.searchParams
      },
      get url() {
        observations.push('url')
        return url
      },
      get tail() {
        observations.push('tail')
        return 1
      },
    }
    const result = snapshot(source) as typeof source
    assert.deepEqual(observations, ['params', 'url', 'tail'])
    assert.strictEqual(result.params, result.url.searchParams)
  })

  it('keeps distinct equal owners and their children distinct', () => {
    const left = new URL('https://example.test/?a=1')
    const right = new URL(left.href)
    const source = { left, right, leftParams: left.searchParams, rightParams: right.searchParams }
    const result = snapshot(source) as typeof source
    assert.notStrictEqual(result.left, result.right)
    assert.notStrictEqual(result.leftParams, result.rightParams)
    assert.strictEqual(result.left.searchParams, result.leftParams)
    assert.strictEqual(result.right.searchParams, result.rightParams)
  })

  it('reconciles a child alias moving between two owners', () => {
    const left = new URL('https://example.test/left?a=1')
    const right = new URL('https://example.test/right?b=2')
    const current = { left, right, params: left.searchParams }
    const nextLeft = new URL('https://example.test/left?a=3')
    const nextRight = new URL('https://example.test/right?b=4')
    reconcile(current, { left: nextLeft, right: nextRight, params: nextRight.searchParams })
    assert.notStrictEqual(current.left, current.right)
    assert.notStrictEqual(current.left.searchParams, current.right.searchParams)
    assert.strictEqual(current.params, current.right.searchParams)
    assert.strictEqual(current.left.search, '?a=3')
    assert.strictEqual(current.right.search, '?b=4')
  })

  it('preserves raw desired href when publishing equal owned parameter pairs', () => {
    for (const href of ['https://example.test/?a=two%20words', 'https://example.test/?']) {
      for (const parametersFirst of [true, false]) {
        const current = graph(parametersFirst)
        const url = new URL(href)
        const next = parametersFirst
          ? { params: url.searchParams, url }
          : { url, params: url.searchParams }
        reconcile(current, next)
        assert.strictEqual(current.url.href, href)
        assert.strictEqual(current.params, current.url.searchParams)
        assert.deepEqual([...current.params], [...url.searchParams])
      }
      const root = new URL('https://example.test/?old=1')
      const desired = new URL(href)
      assert.strictEqual(reconcile(root, desired), root)
      assert.strictEqual(root.href, href)
    }
  })

  it('pins an identical nested linked pair without changing its native owner', () => {
    const nested = graph(true)
    const current = { count: 0, nested }
    const href = nested.url.href
    assert.strictEqual(reconcile(current, { count: 1, nested }), current)
    assert.strictEqual(current.nested, nested)
    assert.strictEqual(nested.url.href, href)
    assert.strictEqual(nested.params, nested.url.searchParams)
    assert.strictEqual(current.count, 1)
  })

  it('reconciles a linked pair without separating its native child', () => {
    const current = graph(true)
    const currentUrl = current.url
    const currentParameters = current.params
    const next = graph(false)
    next.url.search = '?x=1&x=2'
    assert.strictEqual(reconcile(current, next), current)
    assert.strictEqual(current.url, currentUrl)
    assert.strictEqual(current.params, currentParameters)
    assert.strictEqual(current.params, current.url.searchParams)
    assert.deepEqual(
      [...current.params],
      [
        ['x', '1'],
        ['x', '2'],
      ],
    )
  })

  it('gives a new URL new search parameters when current holds others where next holds them', () => {
    const url = new URL('https://example.test/?q=1')
    const other = new URL('https://other.test/?r=2')
    for (const current of [
      { params: new URLSearchParams('z=9') },
      { url: 'text', params: new URLSearchParams('z=9') },
      { url: new Date(0), params: other.searchParams },
    ] as Array<{ params: URLSearchParams; url?: unknown }>) {
      const kept = current.params
      const result = reconcile(current as object, { url, params: url.searchParams })
      assert.strictEqual(result, current)
      assert.notStrictEqual(result.url, url)
      assert.notStrictEqual(result.params, kept)
      assert.strictEqual(result.params, result.url.searchParams)
      assert.strictEqual(result.url.href, url.href)
    }
  })

  it('keeps the URL whose search parameters stay in place', () => {
    const url = new URL('https://example.test/?q=1')
    const inside = { params: url.searchParams }
    const current: { inside: typeof inside; url: URL | null } = { inside, url: null }
    assert.strictEqual(reconcile(current, { inside, url }), current)
    assert.strictEqual(current.inside, inside)
    assert.strictEqual(current.url, url)
    assert.strictEqual(current.url?.searchParams, inside.params)
  })

  it('rejects in reconcile a URL whose search parameters have a replaced prototype', () => {
    for (const parametersFirst of [true, false]) {
      const url = new URL('https://example.test/?q=1')
      Object.setPrototypeOf(url.searchParams, null)
      const next = parametersFirst
        ? { params: url.searchParams, url }
        : { url, params: url.searchParams }
      let thrown: unknown
      try {
        reconcile({}, next)
      } catch (error) {
        thrown = error
      }
      assert.ok(isReconcileError(thrown) && thrown.cause.type === 'PublicationRejected')
    }
  })

  it('rejects in reconcile a URL whose search parameters were met as another kind', () => {
    // The parameters are met first with an atom's prototype, kept by reference, and have their
    // own prototype again when the URL is read, so the URL has no parameters node to build from.
    const url = new URL('https://example.test/?q=1')
    const parameters = url.searchParams
    Object.setPrototypeOf(parameters, RegExp.prototype)
    const next = new Proxy(
      { a: parameters, b: url },
      {
        get(target, key, receiver) {
          if (key === 'b') Object.setPrototypeOf(parameters, URLSearchParams.prototype)
          return Reflect.get(target, key, receiver) as unknown
        },
      },
    )
    const current = { a: 1, b: new URL('https://other.test/') }
    const before = current.b.href
    let thrown: unknown
    try {
      reconcile(current, next)
    } catch (error) {
      thrown = error
    }
    assert.ok(isReconcileError(thrown) && thrown.cause.type === 'PublicationRejected')
    assert.strictEqual(current.a, 1)
    assert.strictEqual(current.b.href, before)
  })
})
