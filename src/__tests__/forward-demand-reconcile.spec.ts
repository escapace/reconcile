import { assert, it } from 'vitest'
import { reconcile } from '../reconcile'

it.each([0, 1, 4, 8])('preserves fixed references beyond %s unrelated alternatives', (size) => {
  for (const agrees of [false, true]) {
    const z0 = {}
    const z1 = {}
    const b: Record<string, object> = {}
    const wanted: Record<string, object> = {}
    for (let index = 0; index < size; index += 1) {
      b[`a${index}`] = {}
      wanted[`a${index}`] = {}
    }
    for (let index = 0; index < size; index += 1) {
      b[`b${index}`] = {}
      wanted[`b${index}`] = wanted[`a${index}`]
    }
    Object.defineProperty(b, 'z', { enumerable: true, value: agrees ? z1 : z0 })
    wanted.z = {}
    const current = { b, z: z1 }
    Object.defineProperty(current, 'z', { configurable: false, writable: false })
    const trace: string[] = []
    const next = {
      get b() {
        trace.push('capture b')
        return wanted
      },
      // eslint-disable-next-line perfectionist/sort-objects -- The child must precede the target in capture order.
      z: wanted.z,
    }
    assert.equal(reconcile(current, next), current)
    assert.equal(current.z, z1)
    assert.equal(current.b.z, z1)
    assert.equal(b.z, agrees ? z1 : z0)
    assert.equal(current.b === b, agrees)
    assert.deepEqual(trace, ['capture b'])
    for (let index = 0; index < size; index += 1)
      assert.equal(current.b[`a${index}`], current.b[`b${index}`])
  }
})
