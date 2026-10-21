/**
 * Copy, update and serialize JavaScript object graphs.
 *
 * @remarks
 * {@link snapshot} copies a value deeply. {@link produce} runs a recipe on a draft and returns
 * the next value. {@link reconcile} updates an existing value in place to match another.
 * {@link serialize} encodes a graph as JSON data; {@link deserialize} restores it within a size
 * limit, and {@link requiredMaxBytes} returns the smallest limit for given data.
 * `reconcile(current, produce(current, recipe))` applies a recipe to live state. Every failure
 * the library detects is a {@link ReconcileError}.
 *
 * @packageDocumentation
 */
export {
  isReconcileError,
  isReconcileErrorOfType,
  RECONCILE_ERROR_TYPES,
  ReconcileError,
} from './error'
export type { ReconcileErrorCause, ReconcileErrorMetadata, ReconcileErrorType } from './error'
export { produce } from './produce'
export { reconcile } from './reconcile'
export { snapshot } from './snapshot'

export { deserialize } from './deserialize'
export type { DeserializeOptions } from './deserialize'
export { serialize } from './serialize'
export { requiredMaxBytes } from './required-max-bytes'
