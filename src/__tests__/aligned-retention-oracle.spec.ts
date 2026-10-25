import { assert, describe, it } from 'vitest'
import { produce, reconcile } from '../index'

describe('aligned retention', () => {
  // Exhaustive small fixed-alignment oracle. This decides each target independently of the
  // runtime traversal and never calls snapshot or its graph verifier.
  it('keeps each next object at its first position across all three-slot alias patterns', () => {
    const patterns = Array.from({ length: 27 }, (_, n) => [
      n % 3,
      Math.floor(n / 3) % 3,
      Math.floor(n / 9),
    ])
    for (const before of patterns) {
      for (const after of patterns) {
        const oldNodes = Array.from({ length: 3 }, () => ({ n: 0 }))
        const newNodes = Array.from({ length: 3 }, (_, n) => ({ n: n + 1 }))
        const current = before.map((n) => oldNodes[n])
        const next = after.map((n) => newNodes[n])
        const oldImages = Array.from(current)
        // Each next object, in order of first visit, keeps the first current object at one of
        // its positions, in position order, that no earlier next object kept.
        const targets = [...new Set(after)]
        const used = new Set<number>()
        const expected = targets.map((target) => {
          const kept = before.find((node, slot) => after[slot] === target && !used.has(node))
          if (kept !== undefined) used.add(kept)
          return kept === undefined ? undefined : oldNodes[kept]
        })
        assert.equal(reconcile(current, next), current)
        const actualImages = targets.map((target) => current[after.indexOf(target)])
        assert.deepEqual(
          actualImages.map((node) => (oldImages.includes(node) ? node : undefined)),
          expected,
          `before=${before.join(',')} after=${after.join(',')}`,
        )
        for (let left = 0; left < 3; left += 1) {
          assert.equal(current[left].n, next[left].n)
          for (let right = 0; right < 3; right += 1)
            assert.equal(current[left] === current[right], next[left] === next[right])
        }
      }
    }
  })

  it('restores every unchanged node in cyclic data graphs after undo', () => {
    for (let size = 1; size <= 6; size += 1) {
      for (let edited = 0; edited < size; edited += 1) {
        const nodes: Array<{ n: number; next?: object }> = Array.from({ length: size }, () => ({
          n: 0,
        }))
        for (let index = 0; index < size; index += 1) nodes[index].next = nodes[(index + 1) % size]
        const current = { nodes }
        const oldImages = Array.from(current.nodes)
        const result = produce(current, (draft) => {
          draft.nodes[edited].n = 1
          draft.nodes[edited].n = 0
          return draft
        })
        assert.equal(result, current)
        for (let index = 0; index < size; index += 1) {
          assert.equal(result.nodes[index], oldImages[index])
          assert.equal(nodes[index].n, 0)
        }
      }
    }
  })
})
