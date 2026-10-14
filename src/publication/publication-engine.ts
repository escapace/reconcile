import { isNode } from '../graph/edge'
import { matchesKind, recognize } from '../adapters/recognition'
import { ExposurePalette, storageIdentity } from '../adapters/vue'
import { EXPOSURE_MODES } from '../constants'
import { isObject } from '../object-property'
import type {
  Binding,
  CapturedGraph,
  Choice,
  Edge,
  Execution,
  PublicationRegistry,
  Readback,
} from '../types'
import { candidates } from './candidates'
import { constructionOrder } from '../graph/construction'
import { constructionDependencies } from '../graph/construction-facts'
import { execute } from '../graph/driver'

/** Reads the live object currently exposed at a node of one attempt. */
const exposed = (state: Execution, index: number): object => state.bindings[index].exposed as object

// The finite driver owns all selection/revision/retry decisions. This adapter
// translates native observations to outcomes without changing an active image.
// Binding labels are the live objects themselves, so no handle table is needed.
// Pinned nodes are retained as they are: no preflight, publication or readback inside.
export function publishGraph(
  types: PublicationRegistry,
  graph: CapturedGraph,
  root: object,
): boolean {
  const records = graph.nodes
  const size = records.length
  const policy = (index: number) => types.policies[records[index].layout.kind]
  const dependencies = records.map((node) => constructionDependencies(types, node))
  // Storage identity is stable for the duration of one call; probe each object once.
  const storages = new Map<object, object>()
  const storage = (value: object): object => {
    let owner = storages.get(value)
    if (owner === undefined) storages.set(value, (owner = storageIdentity(value)))
    return owner
  }
  const domains = candidates(types, records, root, graph, storage)
  const exposure = new ExposurePalette((value) => types.exposures[recognize(types, value)], storage)
  const oldStorage = new Set<unknown>()
  for (const domain of domains)
    for (const choice of domain) if (choice.retained) oldStorage.add(choice.storage)
  // Observes each selected target once and binds it to its choice; undefined when two
  // targets share storage, a fresh target reuses old storage or a construction edge names
  // another target.
  const bind = (choices: readonly Choice[], targets: readonly object[]): Binding[] | undefined => {
    // Fixed identities are the root and everything its selected choices pin transitively.
    const fixed = new Set([0])
    for (const node of fixed) for (const edge of choices[node].required) fixed.add(edge.node)
    const bindings: Binding[] = []
    const owners = new Set<object>()
    for (let index = 0; index < size; index += 1) {
      const target = targets[index]
      const node = records[index]
      const choice = choices[index]
      const observed = exposure.observe(target, types.exposures[node.layout.kind])
      if (
        observed === undefined ||
        owners.has(observed.storage) ||
        (!choice.retained && oldStorage.has(observed.storage))
      )
        return undefined
      owners.add(observed.storage)
      // A retained choice's requirements already name the selected targets; dependent
      // construction extends a copy of them with edges that must name the selected targets.
      const construction = policy(index).bindings
      const read = construction.tag === 'dependent' ? construction.read(node, target) : undefined
      if (read?.some((edge) => edge.identity !== targets[edge.node]) === true) return undefined
      bindings.push({
        choice: choice.identity,
        construction: read === undefined ? choice.required : [...choice.required, ...read],
        exposed: target,
        fixed: fixed.has(index),
        mode: observed.mode,
        palette: EXPOSURE_MODES,
        storage: observed.storage,
        writer: target,
      })
    }
    return bindings
  }
  // Candidate discovery already ran the requirement scan on every retained candidate while no
  // write had happened; it is the preflight. The engine repeats it only after this call's own
  // writes, and never on a fresh target, which is private until it is published.
  let written = false
  const result = execute(domains, {
    prepare(selection) {
      const choices = selection.map((choice, node) => domains[node][choice])
      const order = constructionOrder(
        dependencies,
        choices.map((choice) => choice.retained),
      )
      if (order === undefined) return undefined
      const targets = choices.map((choice) =>
        choice.retained ? (choice.identity as object) : undefined,
      ) as object[]
      const resolve = (edge: Edge): unknown => (isNode(edge) ? targets[edge.node] : edge.value)
      for (const index of order) targets[index] = policy(index).allocate(records[index], resolve)
      return bind(choices, targets)
    },
    publish(state) {
      const resolve = (edge: Edge): unknown =>
        isNode(edge) ? exposed(state, edge.node) : edge.value
      const writer = (index: number): object => state.bindings[index].writer as object
      // After this call's own writes, retained replaceable targets rerun the preflight. A fresh
      // choice is labelled by its node index; a retained one by its object.
      for (let index = 0; index < size; index += 1)
        if (
          written &&
          typeof state.bindings[index].choice !== 'number' &&
          records[index].pinned === undefined &&
          policy(index).requirements(records[index], writer(index)) === undefined
        )
          return { rejected: index }
      written = true
      for (let index = 0; index < size; index += 1) {
        if (records[index].pinned !== undefined) continue
        // Recover only native publication exceptions on replaceable nodes. A
        // fixed receiver's host exception remains a public failure, without rollback.
        try {
          if (!policy(index).publish(records[index], writer(index), resolve))
            return { rejected: index }
        } catch (error) {
          if (state.bindings[index].fixed) throw error
          return { rejected: index }
        }
      }
      return true
    },
    readback(state, index) {
      const node = records[index]
      const target = exposed(state, index)
      if (storage(target) !== state.bindings[index].storage) return { kind: 'reject' }
      if (node.pinned !== undefined) return { kind: 'match' }
      let outcome: Readback = { kind: 'reject' }
      const matches =
        matchesKind(types, target, node.layout.kind) &&
        policy(index).matches(node, target, (actual, wanted) => {
          if (!isNode(wanted)) return Object.is(actual, wanted.value)
          const child = wanted.node
          if (actual === exposed(state, child)) return true
          if (isObject(actual) && storage(actual) === state.bindings[child].storage) {
            const observed = exposure.observe(actual, types.exposures[records[child].layout.kind])
            if (observed !== undefined)
              outcome = {
                exposed: actual,
                kind: 'rebind',
                mode: observed.mode,
                node: child,
                storage: observed.storage,
              }
          }
          return false
        })
      return matches ? { kind: 'match' } : outcome
    },
    retention(state) {
      let score = 0
      for (let index = 0; index < size; index += 1) {
        const target = exposed(state, index)
        if (domains[index].some((choice) => choice.retained && choice.identity === target))
          score += 1
      }
      return score
    },
  })
  return result.kind === 'accepted'
}
