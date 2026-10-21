import { assert, describe, it } from 'vitest'

import { produce } from '../produce'
import { reconcile } from '../reconcile'
import { snapshot } from '../snapshot'

describe('URL native values', () => {
  it('copies and updates URL roots with native normalized state', () => {
    const current = new URL('https://example.test/old?a=1')
    const next = new URL('https://user:pass@example.test:8443/new?a=2&a=3#fragment')
    const copy = snapshot(next) as URL
    assert.notStrictEqual(copy, next)
    assert.strictEqual(copy.href, next.href)
    assert.strictEqual(reconcile(current, next), current)
    assert.strictEqual(current.href, next.href)
    const produced = produce(current, (draft) => {
      draft.pathname = '/produced'
      return draft
    })
    assert.strictEqual(produced.pathname, '/produced')
    assert.strictEqual(current.pathname, '/new')
  })

  it('preserves standalone parameter order, duplicates and empty names and values', () => {
    const source = new URLSearchParams('b=1&a=2&b=3&=empty&blank=')
    const copy = snapshot(source) as URLSearchParams
    assert.notStrictEqual(copy, source)
    assert.deepEqual([...copy], [...source])
    const current = new URLSearchParams('old=1&old=2&remove=3')
    assert.strictEqual(reconcile(current, source), current)
    assert.deepEqual([...current], [...source])
    const result = produce(source, (draft) => {
      draft.append('b', '4')
      return draft
    })
    assert.deepEqual(result.getAll('b'), ['1', '3', '4'])
    assert.deepEqual(source.getAll('b'), ['1', '3'])
  })

  it('copies intrinsic URL slots without invoking own or subclass overrides', () => {
    class OverriddenURL extends URL {
      override get href(): string {
        throw new Error('Subclass href override')
      }
      override get searchParams(): URLSearchParams {
        throw new Error('Subclass params override')
      }
    }
    const own = new URL('https://example.test/own?a=1')
    Object.defineProperties(own, {
      href: {
        get() {
          throw new Error('Own href override')
        },
      },
      searchParams: {
        get() {
          throw new Error('Own params override')
        },
      },
    })
    const subclass = new OverriddenURL('https://example.test/subclass?b=2')
    const result = snapshot({ own, subclass }) as { own: URL; subclass: URL }
    assert.strictEqual(result.own.href, 'https://example.test/own?a=1')
    assert.deepEqual([...result.own.searchParams], [['a', '1']])
    // The copy keeps the subclass, so read it through the native accessors as the copy did.
    assert.strictEqual(Object.getPrototypeOf(result.subclass), OverriddenURL.prototype)
    const native = (key: 'href' | 'searchParams') =>
      Object.getOwnPropertyDescriptor(URL.prototype, key)!.get!.call(result.subclass) as unknown
    assert.strictEqual(native('href'), 'https://example.test/subclass?b=2')
    assert.deepEqual([...(native('searchParams') as URLSearchParams)], [['b', '2']])
  })

  it('does not merge native owners with misleading own searchParams values', () => {
    const left = new URL('https://example.test/left?a=1')
    const right = new URL('https://example.test/right?b=2')
    const misleading = new URLSearchParams('fake=1')
    Object.defineProperty(left, 'searchParams', { value: misleading })
    Object.defineProperty(right, 'searchParams', { value: misleading })
    const result = snapshot({ left, right }) as { left: URL; right: URL }
    assert.notStrictEqual(result.left, result.right)
    assert.notStrictEqual(result.left.searchParams, result.right.searchParams)
    assert.deepEqual([...result.left.searchParams], [['a', '1']])
    assert.deepEqual([...result.right.searchParams], [['b', '2']])
  })

  it('copies intrinsic parameter state without invoking toString overrides', () => {
    class OverriddenParameters extends URLSearchParams {
      override toString(): string {
        throw new Error('Subclass serialization override')
      }
    }
    const own = new URLSearchParams('a=1&a=2')
    Object.defineProperty(own, 'toString', {
      value() {
        throw new Error('Own serialization override')
      },
    })
    const subclass = new OverriddenParameters('b=1&b=2')
    const result = snapshot({ own, subclass }) as {
      own: URLSearchParams
      subclass: URLSearchParams
    }
    assert.deepEqual(
      [...result.own],
      [
        ['a', '1'],
        ['a', '2'],
      ],
    )
    assert.deepEqual(
      [...result.subclass],
      [
        ['b', '1'],
        ['b', '2'],
      ],
    )
  })

  it('does not read extra properties on native URL or parameters', () => {
    for (const value of [new URL('https://example.test/'), new URLSearchParams('a=1')]) {
      Object.defineProperty(value, 'extra', {
        enumerable: true,
        get() {
          throw new Error('Extra native properties are outside the supported payload')
        },
      })
      const copy = snapshot(value) as object
      assert.strictEqual(Object.hasOwn(copy, 'extra'), false)
    }
  })
})
