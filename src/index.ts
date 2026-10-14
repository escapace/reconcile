/**
 * Deep copies, draft-based updates and in-place updates for JavaScript object graphs.
 *
 * @remarks
 * {@link snapshot} copies a value deeply. {@link produce} runs a recipe on a draft and returns
 * the next value. {@link reconcile} updates an existing value in place to match another.
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
export type {
  DraftIterationMethod,
  ReconcileErrorCause,
  ReconcileErrorMetadata,
  ReconcileErrorType,
} from './error'
export { produce } from './produce'
export { reconcile } from './reconcile'
export { snapshot } from './snapshot'
