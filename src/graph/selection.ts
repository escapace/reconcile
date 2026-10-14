import type { Choice, Domains, IncomingConsensus, Label, Selection } from '../types'
import { forcedGroups } from './forced-groups'
import { addIncoming } from './incoming-consensus'
import { unsupportedChoices } from './supported-choices'

// fallow-ignore-next-line complexity -- checked for every candidate choice; kept inline for speed
function compatible(
  domains: Domains,
  incoming: readonly IncomingConsensus[],
  selected: readonly number[],
  node: number,
  choice: Choice,
): boolean {
  for (const requirement of choice.required) {
    const domain = domains[requirement.node]
    if (domain === undefined) return false
    if (requirement.node === node) {
      if (choice.identity !== requirement.identity) return false
    } else if (requirement.node < node) {
      if (domain[selected[requirement.node]].identity !== requirement.identity) return false
    } else {
      const demand = incoming[requirement.node]
      if (demand !== undefined && demand !== requirement.identity) return false
      if (!domain.some((candidate) => candidate.identity === requirement.identity)) return false
    }
  }
  const demand = incoming[node]
  return demand === undefined || demand === choice.identity
}

/**
 * Streams every feasible assignment by descending retention and deterministic choice order.
 *
 * @remarks
 * Preferences are captured once per score tier; native failures may change later tiers. Exact
 * stream order matters to the publication driver, not only membership or the first optimum.
 * Backtracking owns one path and builds derived membership only when needed. GraphPolicy's
 * completion_survives_score_pruning and completion_survives_prefix_pruning prove the finite
 * pruning rules. ActiveDemands proves prefix-demand equivalence and exact trail restoration;
 * ForcedGroups proves forced membership and conflict rejection, with disjoint ownership
 * for force restoration. SupportedChoices proves support deletion preserves feasible choices;
 * filtered suffix bounds prune search without changing original preference-callback tiers.
 * Complete-stream bridges check the runtime iterator correspondence.
 */
// fallow-ignore-next-line complexity -- per-step helper calls in this search slowed reconcile 1.5%
export function* selections(
  domains: Domains,
  preferFresh?: (score: number) => ReadonlySet<number>,
): Generator<Selection, void> {
  const size = domains.length
  const incoming = new Array<IncomingConsensus>(size)
  const trail: IncomingConsensus[] = []
  const maximum = new Array<number>(size + 1).fill(0)
  const minimum = new Array<number>(size + 1).fill(0)
  const bounds = (node: number, indices?: readonly number[]): void => {
    const domain = domains[node]
    const count = indices === undefined ? domain.length : indices.length
    let some = false
    let every = true
    for (let position = 0; position < count; position += 1)
      if (domain[indices === undefined ? position : indices[position]].retained) some = true
      else every = false
    maximum[node] = count === 0 ? -Infinity : maximum[node + 1] + Number(some)
    minimum[node] = count === 0 ? Infinity : minimum[node + 1] + Number(every)
  }
  for (let node = size - 1; node >= 0; node -= 1) {
    if (domains[node].length === 0) return
    bounds(node)
  }
  const highest = maximum[0]
  const lowest = minimum[0]
  const removed = unsupportedChoices(domains)
  let ordinary: number[][] | undefined
  const indicesOf = (): number[][] =>
    (ordinary ??= domains.map((domain, node) => {
      const indices = domain.map((_, choice) => choice)
      return removed === undefined
        ? indices
        : indices.filter((choice) => removed[node][choice] === 0)
    }))
  if (removed !== undefined) {
    const admitted = indicesOf()
    for (let node = size - 1; node >= 0; node -= 1) bounds(node, admitted[node])
  }
  const groups = forcedGroups(domains)
  const forced = groups === undefined ? undefined : new Array<number | undefined>(size)
  const selected = new Array<number>(size)
  const next = new Array<number>(size + 1).fill(0)
  const owners = new Set<Label>()
  const freshFirst: number[][] = []
  for (let goal = highest; goal >= lowest; goal -= 1) {
    const preferred = preferFresh?.(goal)
    if (goal > maximum[0] || goal < minimum[0]) continue
    const order =
      preferred === undefined || preferred.size === 0
        ? ordinary
        : indicesOf().map((indices, node) =>
            preferred.has(node)
              ? (freshFirst[node] ??= [
                  ...indices.filter((choice) => !domains[node][choice].retained),
                  ...indices.filter((choice) => domains[node][choice].retained),
                ])
              : indices,
          )
    let node = 0
    let retained = 0
    next[0] = 0
    while (node >= 0) {
      if (node === size) {
        if (retained === goal) yield selected.slice()
      } else {
        const demanded = forced?.[node]
        const position = next[node]++
        const index =
          demanded === undefined
            ? order === undefined
              ? position < domains[node].length
                ? position
                : undefined
              : order[node][position]
            : position === 0
              ? demanded
              : undefined
        const choice = index === undefined ? undefined : domains[node][index]
        if (choice !== undefined) {
          const group = groups?.[node]?.[index!]
          if (group === null) continue
          if (group !== undefined && demanded === undefined) {
            // A follower whose leader was not selected cannot have a feasible completion.
            if (group[0].node !== node) continue
            // Distinct components may compete for future owners. This guard makes each
            // installation own disjoint positions, so undo needs no nested force trail.
            if (group.some((member) => forced![member.node] !== undefined)) continue
          }
          const score = retained + Number(choice.retained)
          if (
            score + minimum[node + 1] <= goal &&
            score + maximum[node + 1] >= goal &&
            !owners.has(choice.storage) &&
            compatible(domains, incoming, selected, node, choice)
          ) {
            // Only a selected prefix choice contributes demands. Outgoing checks
            // already handled self/backward edges and rejected invalid targets.
            for (const edge of choice.required) {
              if (edge.node <= node) continue
              trail.push(incoming[edge.node])
              incoming[edge.node] = addIncoming(incoming[edge.node], edge.identity)
            }
            if (group?.[0].node === node)
              for (let member = 1; member < group.length; member += 1)
                forced![group[member].node] = group[member].choice
            selected[node] = index!
            owners.add(choice.storage)
            retained = score
            node += 1
            next[node] = 0
          }
          continue
        }
      }
      node -= 1
      if (node >= 0) {
        const group = groups?.[node]?.[selected[node]]
        if (group?.[0].node === node)
          for (let member = 1; member < group.length; member += 1)
            forced![group[member].node] = undefined
        const previous = domains[node][selected[node]]
        // Reverse exactly the updates made by this choice, including duplicates.
        for (let edge = previous.required.length - 1; edge >= 0; edge -= 1) {
          const requirement = previous.required[edge]
          if (requirement.node > node) incoming[requirement.node] = trail.pop()
        }
        owners.delete(previous.storage)
        retained -= Number(previous.retained)
      }
    }
  }
}
