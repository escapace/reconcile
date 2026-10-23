/** A set that holds its first member inline and creates a `Set` only at its second. */
export interface SmallSet<T> {
  first: T | undefined
  rest: Set<T> | undefined
}

export const smallSet = <T>(): SmallSet<T> => ({ first: undefined, rest: undefined })

export const smallHas = <T>(set: SmallSet<T>, value: T): boolean =>
  set.first === value || set.rest?.has(value) === true

/** Adds `value`, which is never undefined. */
export function smallAdd<T>(set: SmallSet<T>, value: T): void {
  if (set.first === undefined) set.first = value
  else if (set.first !== value) (set.rest ??= new Set()).add(value)
}
