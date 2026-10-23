import { assert, it } from 'vitest'
import { smallAdd, smallHas, smallSet } from '../graph/small-set'

it('holds the members a Set would, creating one only at the second member', () => {
  const [a, b, c] = [{}, {}, {}]
  const set = smallSet<object>()
  assert.isFalse(smallHas(set, a))
  smallAdd(set, a)
  smallAdd(set, a)
  assert.isTrue(smallHas(set, a))
  assert.isUndefined(set.rest)
  smallAdd(set, b)
  smallAdd(set, a)
  assert.isTrue(smallHas(set, a) && smallHas(set, b))
  assert.isFalse(smallHas(set, c))
  assert.deepEqual([...set.rest!], [b])
})
