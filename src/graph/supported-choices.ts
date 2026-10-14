import type { ChoicePosition, Domains, Label, SupportBucket } from '../types'

function allSupported(domains: Domains): boolean {
  for (let node = 0; node < domains.length; node += 1)
    for (const choice of domains[node])
      for (const edge of choice.required)
        if (
          edge.node === node
            ? edge.identity !== choice.identity
            : !domains[edge.node]?.some((target) => target.identity === edge.identity)
        )
          return false
  return true
}

/**
 * Marks exactly the choice positions removed by unsupported-requirement propagation.
 *
 * @remarks
 * An already-supported domain is a fixed point and returns undefined without worklist state.
 * Otherwise identity buckets count unprocessed supports; processing a deletion decrements
 * its bucket once and wakes dependents only when the last support disappears. Admission
 * marks positions before enqueueing, so duplicate requirements cannot grow the queue past
 * the number of choices. Self requirements use the same position, not a sibling support.
 * SupportedChoices proves finite deletion and bucket laws; the bridge checks the completed
 * mask against independent exhaustive rounds. Domains remain sealed and unmodified.
 */
export function unsupportedChoices(domains: Domains): readonly Uint8Array[] | undefined {
  if (allSupported(domains)) return undefined
  const removed = domains.map((domain) => new Uint8Array(domain.length))
  const queue: ChoicePosition[] = []
  const buckets = domains.map((domain) => {
    const identities = new Map<Label, SupportBucket>()
    for (const choice of domain) {
      const bucket = identities.get(choice.identity)
      if (bucket === undefined) identities.set(choice.identity, { dependents: [], remaining: 1 })
      else bucket.remaining += 1
    }
    return identities
  })
  const admit = (position: ChoicePosition): void => {
    if (removed[position.node][position.choice] !== 0) return
    removed[position.node][position.choice] = 1
    queue.push(position)
  }
  // A choice whose self requirement fails or whose target identity is missing is admitted at
  // once; otherwise it waits in the bucket of every other identity it requires.
  for (let node = 0; node < domains.length; node += 1)
    domains[node].forEach((choice, index) => {
      const position = { choice: index, node }
      for (const edge of choice.required) {
        if (edge.node === node) {
          if (edge.identity !== choice.identity) admit(position)
          continue
        }
        const bucket = buckets[edge.node]?.get(edge.identity)
        if (bucket === undefined) admit(position)
        else bucket.dependents.push(position)
      }
    })
  for (const position of queue) {
    const choice = domains[position.node][position.choice]
    const bucket = buckets[position.node].get(choice.identity)!
    bucket.remaining -= 1
    if (bucket.remaining === 0) for (const dependent of bucket.dependents) admit(dependent)
  }
  return removed
}
