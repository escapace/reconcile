import { defineData } from './standard-prototypes'
/**
 * Every error type this library throws.
 *
 * @remarks
 * The prefix of each name identifies the function or phase that detects the failure. `Draft`
 * types come from `produce` while the recipe runs, `Finalization` types from `produce` after the
 * recipe returns, `Publication` types from `reconcile`, `Snapshot` types from `snapshot`,
 * `Serialize` types from `serialize`, and `Deserialize` types from `deserialize` and
 * `requiredMaxBytes`.
 */
export const RECONCILE_ERROR_TYPES = [
  'DeserializeInputInvalid',
  'DeserializeLimitExceeded',
  'DeserializeLimitInvalid',
  'DraftArrayIndexRejected',
  'DraftArrayLengthRejected',
  'DraftDefinePropertyUnsupported',
  'FinalizationAccessorUnstable',
  'FinalizationChildInvalid',
  'FinalizationConstructionImpossible',
  'FinalizationStorageMissing',
  'PublicationRejected',
  'SerializeValueUnsupported',
  'SnapshotURLSearchParamsMemoIncompatible',
] as const

/** The `type` of a {@link ReconcileError}: one of {@link RECONCILE_ERROR_TYPES}. */
export type ReconcileErrorType = (typeof RECONCILE_ERROR_TYPES)[number]

/**
 * The properties of `cause` for each error type, in addition to `type`.
 *
 * @remarks
 * Creating an error runs no application code, such as getters, setters or proxy traps.
 */
export interface ReconcileErrorMetadata {
  /**
   * The data passed to `deserialize` or `requiredMaxBytes` is not in the format that `serialize`
   * produces. `reason` names the failed check for diagnostics; its values are not part of the API
   * and can change.
   */
  DeserializeInputInvalid: { reason: string }
  /**
   * The value `deserialize` would return is larger than `maxBytes` allows, or `requiredMaxBytes`
   * would return more than `maxBytes`. `maxBytes` is the limit; the error does not report the size
   * of the value.
   */
  DeserializeLimitExceeded: { maxBytes: number }
  /**
   * `maxBytes` is missing, or is neither a non-negative safe integer nor `Infinity`.
   * `maxBytes` is the value received.
   */
  DeserializeLimitInvalid: { maxBytes: unknown }
  /**
   * An array in `current`, such as a proxy, reported an index at or beyond a non-writable length,
   * which a real array cannot have. `index` is that index.
   */
  DraftArrayIndexRejected: { index: number }
  /**
   * An array in `current`, such as a proxy, reported a length that its other properties make
   * impossible. `length` is the reported length.
   */
  DraftArrayLengthRejected: { length: number }
  /**
   * The recipe called `Object.defineProperty`, `Object.defineProperties` or
   * `Reflect.defineProperty` on a draft. `property` is the key. Use assignment instead.
   */
  DraftDefinePropertyUnsupported: { property: PropertyKey }
  /**
   * A getter that ran after the recipe returned added a new getter to a part of the result that
   * `produce` had already visited, so `produce` cannot call it. `property` is the new getter's key.
   */
  FinalizationAccessorUnstable: { property: PropertyKey }
  /**
   * Internal error in `produce`, which indicates a bug in the library. `index` and `child` are
   * diagnostic values for a bug report.
   */
  FinalizationChildInvalid: { child: unknown; index: number }
  /**
   * No consistent result exists: the new objects cannot be created in any order, or a `Map` or
   * `Set` would hold one new object as two keys or members.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  FinalizationConstructionImpossible: {}
  /**
   * Internal error in `produce`, which indicates a bug in the library. `index` is a diagnostic
   * value for a bug report.
   */
  FinalizationStorageMissing: { index: number }
  /**
   * `reconcile` could not make `current` match `next`. Writes made before the failure are not
   * rolled back.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  PublicationRejected: {}
  /**
   * `serialize` met a value it cannot encode, such as a symbol-keyed property, a function or an
   * object of an unsupported class. `reason` names it for diagnostics; its values are not part of
   * the API and can change.
   */
  SerializeValueUnsupported: { reason: string }
  /**
   * The `seen` map passed to `snapshot` maps the `searchParams` of a URL in the value but not the
   * URL.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  SnapshotURLSearchParamsMemoIncompatible: {}
}

/** The `cause` of a {@link ReconcileError}: its `type` and that type's properties. */
export type ReconcileErrorCause<T extends ReconcileErrorType = ReconcileErrorType> =
  T extends ReconcileErrorType ? { type: T } & ReconcileErrorMetadata[T] : never

/**
 * The error this library throws for every failure it detects.
 *
 * @remarks
 * Its `cause` holds a stable `type` and that type's properties. Its message is for people and can
 * change between versions. Check for it with `instanceof ReconcileError` or
 * {@link isReconcileError}, then branch on `cause.type`.
 *
 * Errors from native constructors and allocation, and errors thrown by application getters,
 * setters, proxy traps, iterators and writes into `current`, propagate unchanged. When an error
 * interrupts `reconcile`, earlier writes are not rolled back.
 *
 * @example
 * ```ts
 * try {
 *   reconcile(current, next)
 * } catch (error) {
 *   if (isReconcileError(error) && error.cause.type === 'PublicationRejected') {
 *     // current can hold some of the new values
 *   } else throw error
 * }
 * ```
 */
export class ReconcileError<T extends ReconcileErrorType = ReconcileErrorType> extends Error {
  /** The error's `type` and that type's properties. */
  declare readonly cause: ReconcileErrorCause<T>
  /** Always `'ReconcileError'`. */
  declare readonly name: 'ReconcileError'

  /**
   * Creates an error. The library creates these errors; applications inspect them.
   *
   * @param cause - The error's `type` and that type's properties.
   * @param message - A description for people; not part of the stable contract.
   */
  constructor(cause: ReconcileErrorCause<T>, message: string) {
    super(message)
    // Defined, not assigned, so that nothing Object.prototype holds intercepts either field.
    defineData(this, 'cause', cause)
    defineData(this, 'name', 'ReconcileError')
  }
}

/**
 * Returns whether `value` is a {@link ReconcileError}, narrowing its type.
 *
 * @param value - Any value, typically a caught error.
 */
export const isReconcileError = (value: unknown): value is ReconcileError =>
  value instanceof ReconcileError

/**
 * Returns whether `error` has the given `type`, narrowing `cause` to that type's properties.
 *
 * @param error - An error already known to be a {@link ReconcileError}.
 * @param type - The error type to test for.
 */
export const isReconcileErrorOfType = <T extends ReconcileErrorType>(
  error: ReconcileError,
  type: T,
): error is ReconcileError<T> => error.cause.type === type

const key = (property: PropertyKey): string =>
  typeof property === 'symbol' ? String(property) : JSON.stringify(property)

// One constructor per type keeps each message next to its facts while letting a bundle
// retain only the errors its operations can raise.

export const draftArrayIndexRejected = (index: number) =>
  new ReconcileError(
    { index, type: 'DraftArrayIndexRejected' },
    `An array in current reports index ${index} at or beyond its non-writable length.`,
  )

export const draftArrayLengthRejected = (length: number) =>
  new ReconcileError(
    { length, type: 'DraftArrayLengthRejected' },
    `An array in current reports length ${length}, which its other properties make impossible.`,
  )

export const draftDefinePropertyUnsupported = (property: PropertyKey) =>
  new ReconcileError(
    { property, type: 'DraftDefinePropertyUnsupported' },
    `Draft property ${key(property)} cannot be defined; use assignment instead.`,
  )

export const finalizationAccessorUnstable = (property: PropertyKey) =>
  new ReconcileError(
    { property, type: 'FinalizationAccessorUnstable' },
    `A getter added getter ${key(property)} to a part of the result that produce had already visited.`,
  )

export const finalizationChildInvalid = (index: number, child: unknown) =>
  new ReconcileError(
    { child, index, type: 'FinalizationChildInvalid' },
    `Internal error in produce: record ${index} has invalid child ${String(child)}. This is a bug in @escapace/reconcile.`,
  )

export const finalizationConstructionImpossible = () =>
  new ReconcileError(
    { type: 'FinalizationConstructionImpossible' },
    'produce cannot build a consistent result.',
  )

export const finalizationStorageMissing = (index: number) =>
  new ReconcileError(
    { index, type: 'FinalizationStorageMissing' },
    `Internal error in produce: record ${index} has no storage. This is a bug in @escapace/reconcile.`,
  )

export const publicationRejected = () =>
  new ReconcileError({ type: 'PublicationRejected' }, 'reconcile cannot make current match next.')

export const snapshotURLSearchParametersMemoIncompatible = () =>
  new ReconcileError(
    { type: 'SnapshotURLSearchParamsMemoIncompatible' },
    "The seen map supplies a copy of a URL's searchParams but not of the URL.",
  )

export const deserializeInputInvalid = (reason: string) =>
  new ReconcileError(
    { reason, type: 'DeserializeInputInvalid' },
    `The input is not in the format that serialize produces: ${reason}.`,
  )

export const deserializeLimitExceeded = (maxBytes: number) =>
  new ReconcileError(
    { maxBytes, type: 'DeserializeLimitExceeded' },
    `The deserialized value would exceed maxBytes (${maxBytes}).`,
  )

export const deserializeLimitInvalid = (maxBytes: unknown) =>
  new ReconcileError(
    { maxBytes, type: 'DeserializeLimitInvalid' },
    'maxBytes must be a non-negative safe integer or Infinity.',
  )

export const serializeValueUnsupported = (reason: string) =>
  new ReconcileError(
    { reason, type: 'SerializeValueUnsupported' },
    `serialize cannot encode this value: ${reason}.`,
  )
