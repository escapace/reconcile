// Positional.lean: a node's layout is [tag, key?, ...runs]. Records and keyed natives carry one
// key field (shape id, view kind, Temporal kind); containers carry the alternating run lengths
// of their slot kinds, literals first, with the last run open. Node tags:
// 0 record, 1 null-prototype record, 2 dense array, 3 sparse array, 4 Map, 5 Set, 6 Date,
// 7 ArrayBuffer, 8 view, 9 URL, 10 URLSearchParams, 11 a URL's own URLSearchParams,
// 12 Temporal, 13 undefined, 14 NaN, 15 Infinity, 16 -Infinity, 17 -0, 18 bigint.
/** The number of node tags. */
export const TAGS = 19
export const keyed = (tag: number): boolean => tag <= 1 || tag === 8 || tag === 12
export const slotted = (tag: number): boolean => tag <= 5
// Positional.lean runsGo / presenceGo: run boundaries, recorded where the kind changes, become
// run lengths in place.
export function lengths(boundaries: number[]): number[] {
  for (let index = boundaries.length - 1; index > 0; index--)
    boundaries[index] -= boundaries[index - 1]
  return boundaries
}
