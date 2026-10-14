import { draftIterationUnsupported, type DraftIterationMethod } from '../../error'
import { isObject } from '../../object-property'
import { normalizeCollectionInsertion } from '../../adapters/vue'
import type { BaseDraftState, ExposureFacet } from '../../types'

/**
 * Reads a collection's current working value, using its base until a copy exists.
 *
 * @remarks
 * Object and array callers use their state's descriptor-aware reads instead.
 */
export function draftValue<T extends object>(state: BaseDraftState): T {
  return (state.copy ?? state.base) as T
}

export const PATCH_STATE_SYMBOL = /* @__PURE__ */ Symbol.for('@escapace/reconcile/patch')

// Supply draft identity information; the storage boundary owns collection policy.
export function insertedCollectionValue(
  state: BaseDraftState,
  value: unknown,
  exposure: Extract<ExposureFacet, { tag: 'collection' }>,
  unwrap: boolean,
): unknown {
  return normalizeCollectionInsertion(
    state.base,
    value,
    isObject(value) ? state.context.statesByIdentity.get(value)?.base : undefined,
    exposure,
    unwrap,
  )
}

/** Reports the shared exclusion of collection iteration from the draft surface. */
function unsupported(method: DraftIterationMethod): never {
  throw draftIterationUnsupported(method)
}

/** Keeps every unsupported Map and Set iterator entry point on the same error path. */
export abstract class UnsupportedDraftCollectionIteration {
  // fallow-ignore-next-line unused-class-member -- part of the Map and Set API that recipes call on a draft
  entries(): never {
    return unsupported('entries')
  }

  // fallow-ignore-next-line unused-class-member -- part of the Map and Set API that recipes call on a draft
  forEach(): never {
    return unsupported('forEach')
  }

  // fallow-ignore-next-line unused-class-member -- part of the Map and Set API that recipes call on a draft
  keys(): never {
    return unsupported('keys')
  }

  // fallow-ignore-next-line unused-class-member -- part of the Map and Set API that recipes call on a draft
  values(): never {
    return unsupported('values')
  }

  [Symbol.iterator](): never {
    return unsupported('iterator')
  }
}
