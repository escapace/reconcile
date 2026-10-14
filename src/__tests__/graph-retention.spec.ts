import { expect, it } from 'vitest'
import { reactive, shallowReactive } from 'vue'
import { reconcile } from '../reconcile'

it('ranks retention by exposed identities after wrapper normalization', () => {
  const first = { n: 0 }
  const second = { n: 0 }
  const shallow = shallowReactive({ child: first })
  const deep = reactive({ child: second })
  const retained = deep.child
  const current = { a: shallow, b: deep }
  Object.defineProperty(current, 'b', { configurable: false, writable: false })
  const child = { n: 1 }
  const shared = { child }
  expect(reconcile(current, { a: shared, b: shared })).toBe(current)
  expect(current.a).toBe(deep)
  expect(current.b).toBe(deep)
  expect(current.a.child).toBe(retained)
  expect(current.a.child.n).toBe(1)
})
