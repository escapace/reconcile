import { setOwnProperty } from './set-own-property'
import { isObject } from 'coastal'

import { cloneBufferView } from './clone-buffer-view'
import {
  OBJECT_KIND_ARRAY,
  OBJECT_KIND_ARRAY_BUFFER,
  OBJECT_KIND_DATA_VIEW,
  OBJECT_KIND_DATE,
  OBJECT_KIND_MAP,
  objectKindOf,
  OBJECT_KIND_PLAIN,
  OBJECT_KIND_SET,
  OBJECT_KIND_TYPED_ARRAY,
} from './object-kind'
import type { ObjectKind } from './object-kind'

/**
 * Creates a detached snapshot of `value`.
 *
 * @remarks
 * `snapshot(...)` clones supported objects and collections so the result can be changed without
 * affecting the source value. It preserves plain-object key order, sparse-array holes, cycles,
 * shared references, object prototypes, and `ArrayBuffer` or view aliasing.
 *
 * Supported values include plain objects, arrays, maps, sets, `Date`, `ArrayBuffer`, `DataView`,
 * and typed arrays. The same behavior also applies to common reactive or signal-backed wrappers
 * when they expose object, array, map, or set behavior. Primitive values are returned unchanged.
 * Function values are kept by reference rather than cloned.
 *
 * @param value - Value to snapshot.
 * @param seen - Memoization table that preserves cycles and shared references during recursive
 * traversal. Callers usually omit this parameter.
 * @returns A detached snapshot that can be mutated without affecting the source value, or the
 * original primitive value when the input is non-object-like.
 */
export function snapshot(
  value: unknown,
  seen: WeakMap<object, object> = new WeakMap<object, object>(),
): unknown {
  if (!isObject(value)) {
    return value
  }

  const sharedResult = seen.get(value)

  if (sharedResult !== undefined) {
    return sharedResult
  }

  return snapshotObjectByKindAfterMiss(objectKindOf(value), value, seen)
}

/** @internal */
function snapshotObjectByKind(
  kind: ObjectKind,
  value: object,
  seen: WeakMap<object, object>,
): object {
  const sharedResult = seen.get(value)

  if (sharedResult !== undefined) {
    return sharedResult
  }

  return snapshotObjectByKindAfterMiss(kind, value, seen)
}

/** @internal */
export function snapshotObjectByKindAfterMiss(
  kind: ObjectKind,
  value: object,
  seen: WeakMap<object, object>,
): object {
  switch (kind) {
    case OBJECT_KIND_ARRAY: {
      const sourceArray = value as unknown[]
      const replacement = new Array<unknown>(sourceArray.length)
      seen.set(value, replacement)

      for (let index = 0; index < sourceArray.length; index += 1) {
        if (index in sourceArray) {
          replacement[index] = snapshot(sourceArray[index], seen)
        }
      }

      return replacement
    }
    case OBJECT_KIND_ARRAY_BUFFER: {
      const replacement = (value as ArrayBuffer).slice(0)
      seen.set(value, replacement)
      return replacement
    }
    case OBJECT_KIND_DATA_VIEW:
    case OBJECT_KIND_TYPED_ARRAY: {
      const sourceView = value as ArrayBufferView
      const replacement = cloneBufferView(
        sourceView,
        snapshotObjectByKind(OBJECT_KIND_ARRAY_BUFFER, sourceView.buffer, seen) as ArrayBuffer,
      )
      seen.set(value, replacement)
      return replacement
    }
    case OBJECT_KIND_DATE: {
      const replacement = new Date((value as Date).getTime())
      seen.set(value, replacement)
      return replacement
    }
    case OBJECT_KIND_MAP: {
      const sourceMap = value as Map<unknown, unknown>
      const replacement = new Map<unknown, unknown>()
      seen.set(value, replacement)

      for (const [key, entry] of sourceMap.entries()) {
        replacement.set(snapshot(key, seen), snapshot(entry, seen))
      }

      return replacement
    }
    case OBJECT_KIND_PLAIN: {
      const sourceObject = value as Record<PropertyKey, unknown>
      // eslint-disable-next-line typescript/no-unsafe-argument
      const replacement = Object.create(Object.getPrototypeOf(sourceObject)) as Record<
        PropertyKey,
        unknown
      >
      const ownNames = Object.getOwnPropertyNames(sourceObject)
      seen.set(value, replacement)

      for (let index = 0; index < ownNames.length; index += 1) {
        const key = ownNames[index]
        setOwnProperty(replacement, key, snapshot(sourceObject[key], seen))
      }

      const ownSymbols = Object.getOwnPropertySymbols(sourceObject)

      if (ownSymbols.length > 0) {
        for (let index = 0; index < ownSymbols.length; index += 1) {
          const key = ownSymbols[index]
          setOwnProperty(replacement, key, snapshot(sourceObject[key], seen))
        }
      }

      return replacement
    }
    case OBJECT_KIND_SET: {
      const sourceSet = value as Set<unknown>
      const replacement = new Set<unknown>()
      seen.set(value, replacement)

      for (const entry of sourceSet.values()) {
        replacement.add(snapshot(entry, seen))
      }

      return replacement
    }
  }
}
