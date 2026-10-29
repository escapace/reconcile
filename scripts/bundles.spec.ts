import { describe, expect, it } from 'vitest'
import { sizeTable } from './bundles'

describe('sizeTable', () => {
  const rows = [
    { name: 'kept', values: [1000, 400] },
    { name: 'added', values: [10, 5] },
  ]

  it('tabulates sizes', () => {
    expect(sizeTable(rows, ['Exports', 'Minified', 'Gzip'])).toBe(
      [
        '| Exports | Minified | Gzip |',
        '| --- | ---: | ---: |',
        '| `kept` | 1,000 | 400 |',
        '| `added` | 10 | 5 |',
      ].join('\n'),
    )
  })

  it('tabulates the change from before, with added and removed rows', () => {
    const before = new Map([
      ['dropped', [5, 5]],
      ['kept', [800, 400]],
    ])
    expect(sizeTable(rows, ['Exports', 'Minified', 'Gzip'], before).split('\n').slice(2)).toEqual([
      '| `kept` | 800 → 1,000 | +25.00% | 400 → 400 | +0.00% |',
      '| `added` | new → 10 |  | new → 5 |  |',
      '| `dropped` | removed |  | removed |  |',
    ])
  })
})
