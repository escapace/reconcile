import { produceWith } from './produce'
import { reconcileWith } from './reconcile'
import { snapshotWith } from './snapshot'
import type { EngineOptions } from './types'
import { builtinModules } from './types/builtins'
import { registerTypes } from './types/registry'

/** Internal composition boundary; each engine owns a frozen type registry. */
export function createEngine(options: EngineOptions = {}) {
  const types = registerTypes(options.types ?? builtinModules)
  return Object.freeze({
    types,
    produce<T, R>(current: T, recipe: (draft: T) => R): R {
      return produceWith(types, current, recipe)
    },
    reconcile<T>(current: unknown, next: T): T {
      return reconcileWith(types, current, next)
    },
    snapshot(value: unknown, seen = new WeakMap<object, object>()): unknown {
      return snapshotWith(types, value, seen)
    },
  })
}
