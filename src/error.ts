/**
 * Every error type this library raises, named by the phase that detects it.
 *
 * @remarks
 * The prefix names the phase. `Draft` types come from `produce` while the recipe runs.
 * `Finalization` types come from `produce` after the recipe returns. `Publication` types come
 * from `reconcile`. `snapshot` raises no library error. After the prefix, the name states the
 * subject and the condition, so each type names exactly one situation.
 */
export const RECONCILE_ERROR_TYPES = [
  'DraftArrayIndexRejected',
  'DraftArrayLengthRejected',
  'DraftDefinePropertyUnsupported',
  'DraftIterationUnsupported',
  'DraftWrapperIdentityChanged',
  'DraftWrapperIteratorMismatched',
  'FinalizationAccessorUnstable',
  'FinalizationChildInvalid',
  'FinalizationConstructionImpossible',
  'FinalizationStorageMissing',
  'PublicationRejected',
] as const

/** The `type` of a {@link ReconcileError}: one of {@link RECONCILE_ERROR_TYPES}. */
export type ReconcileErrorType = (typeof RECONCILE_ERROR_TYPES)[number]

/** Draft `Map` and `Set` methods that throw; `iterator` stands for `[Symbol.iterator]`. */
export type DraftIterationMethod = 'entries' | 'forEach' | 'iterator' | 'keys' | 'values'

/**
 * The facts each error type carries in `cause`, next to `type`.
 *
 * @remarks
 * The facts are values the library already held when it detected the failure. Reporting an
 * error reads nothing more from application objects.
 */
export interface ReconcileErrorMetadata {
  /**
   * An exotic source array, such as a proxy, reported an index at or beyond a non-writable
   * length, which a real array cannot have. `index` is that index.
   */
  DraftArrayIndexRejected: { index: number }
  /**
   * An exotic source array, such as a proxy, reported a length that its other properties make
   * impossible. `length` is the reported length.
   */
  DraftArrayLengthRejected: { length: number }
  /**
   * The recipe called `Object.defineProperty`, `Object.defineProperties` or
   * `Reflect.defineProperty` on a draft. `property` is the key. Use assignment instead.
   */
  DraftDefinePropertyUnsupported: { property: PropertyKey }
  /** The recipe called an iteration method on a draft `Map` or `Set`. `method` names it. */
  DraftIterationUnsupported: { method: DraftIterationMethod }
  /**
   * A reactive wrapper around a `Map` or `Set` reported an inconsistent chain of raw objects
   * while a draft entry was being inserted.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  DraftWrapperIdentityChanged: {}
  /**
   * A reactive wrapper around a `Map` or `Set` did not return the value just inserted when it
   * was iterated.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  DraftWrapperIteratorMismatched: {}
  /**
   * A getter that ran after the recipe returned put a new getter into the result, which the
   * library found only after it had stopped running getters. `property` is the new getter's key.
   */
  FinalizationAccessorUnstable: { property: PropertyKey }
  /**
   * Internal error: a record of the result referred to a child that does not exist. `index` is
   * the record and `child` the invalid reference. This indicates a bug in the library.
   */
  FinalizationChildInvalid: { child: unknown; index: number }
  /**
   * No consistent result exists: objects the result must keep would share storage, or the new
   * objects have no valid creation order.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  FinalizationConstructionImpossible: {}
  /**
   * Internal error: an object that could be kept had no storage. `index` identifies its record.
   * This indicates a bug in the library.
   */
  FinalizationStorageMissing: { index: number }
  /**
   * `reconcile` could not make `current` match `next`. Writes made before the failure are not
   * rolled back.
   */
  // eslint-disable-next-line typescript/no-empty-object-type
  PublicationRejected: {}
}

/** The `cause` of a {@link ReconcileError}: its `type` together with that type's facts. */
export type ReconcileErrorCause<T extends ReconcileErrorType = ReconcileErrorType> =
  T extends ReconcileErrorType ? { type: T } & ReconcileErrorMetadata[T] : never

/**
 * The error this library throws when an operation cannot keep its contract.
 *
 * @remarks
 * Every failure the library detects is a `ReconcileError`. Its `cause` holds a stable `type` and
 * the facts for that type. Its message is for people and may change between versions. Check for
 * it with `instanceof ReconcileError` or {@link isReconcileError}, then branch on `cause.type`.
 *
 * The library never throws for an outcome that is part of a contract, such as `reconcile`
 * returning `next` when a root is not an object.
 *
 * Three kinds of errors keep their original identity and are not wrapped: `RangeError` for an
 * invalid array length, as native arrays throw it; errors thrown by application code that the
 * operations reach, such as getters, setters, proxy traps and iterators; and errors the host
 * throws when `reconcile` writes into `current`. When one of them interrupts `reconcile`, earlier
 * writes are not rolled back.
 *
 * @example
 * ```ts
 * try {
 *   reconcile(current, next)
 * } catch (error) {
 *   if (isReconcileError(error) && error.cause.type === 'PublicationRejected') {
 *     // current may hold some of the writes; nothing was rolled back
 *   } else throw error
 * }
 * ```
 */
export class ReconcileError<T extends ReconcileErrorType = ReconcileErrorType> extends Error {
  /** The error's `type` and the facts for that type. */
  declare readonly cause: ReconcileErrorCause<T>
  /** Always `'ReconcileError'`. */
  declare readonly name: 'ReconcileError'

  /**
   * Creates an error. The library creates these itself; applications normally only inspect them.
   *
   * @param cause - The error's `type` and the facts for that type.
   * @param message - A description for people; not part of the stable contract.
   */
  constructor(cause: ReconcileErrorCause<T>, message: string) {
    super(message)
    this.cause = cause
    this.name = 'ReconcileError'
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
 * Returns whether `error` has the given `type`, narrowing `cause` to that type's facts.
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
    `Draft array index ${index} exceeds a non-writable length.`,
  )

export const draftArrayLengthRejected = (length: number) =>
  new ReconcileError(
    { length, type: 'DraftArrayLengthRejected' },
    `Draft array length ${length} cannot be applied.`,
  )

export const draftDefinePropertyUnsupported = (property: PropertyKey) =>
  new ReconcileError(
    { property, type: 'DraftDefinePropertyUnsupported' },
    `Draft property ${key(property)} cannot be defined; use assignment instead.`,
  )

export const draftIterationUnsupported = (method: DraftIterationMethod) =>
  new ReconcileError(
    { method, type: 'DraftIterationUnsupported' },
    `Draft Map and Set iteration is not supported: ${method}.`,
  )

export const draftWrapperIdentityChanged = () =>
  new ReconcileError(
    { type: 'DraftWrapperIdentityChanged' },
    'Draft wrapper identity changed during insertion.',
  )

export const draftWrapperIteratorMismatched = () =>
  new ReconcileError(
    { type: 'DraftWrapperIteratorMismatched' },
    'Draft wrapper iterator did not expose the inserted value.',
  )

export const finalizationAccessorUnstable = (property: PropertyKey) =>
  new ReconcileError(
    { property, type: 'FinalizationAccessorUnstable' },
    `Finalization accessor ${key(property)} appeared after sealing.`,
  )

export const finalizationChildInvalid = (index: number, child: unknown) =>
  new ReconcileError(
    { child, index, type: 'FinalizationChildInvalid' },
    `Finalization record ${index} has invalid child ${String(child)}.`,
  )

export const finalizationConstructionImpossible = () =>
  new ReconcileError(
    { type: 'FinalizationConstructionImpossible' },
    'Finalization cannot order construction.',
  )

export const finalizationStorageMissing = (index: number) =>
  new ReconcileError(
    { index, type: 'FinalizationStorageMissing' },
    `Finalization record ${index} has no storage.`,
  )

export const publicationRejected = () =>
  new ReconcileError(
    { type: 'PublicationRejected' },
    'Publication into the current root was rejected.',
  )
