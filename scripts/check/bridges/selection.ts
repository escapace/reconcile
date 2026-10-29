import { UsageError } from '../../framework/command'

/** What a narrowed `pnpm check lean` run asks of a bridge that has batches. */
export interface Selection {
  /** The one batch to run; every batch when absent. */
  readonly batch?: string
  /** Shows each seed's case, the reference's outcome and the comparison, failing on nothing. */
  readonly dump?: boolean
  /** Shows how often each feature of the generated `reconcile` cases occurs, comparing nothing. */
  readonly features?: boolean
  /** The mutation audit's choice of one mode for a batch that runs both plain and through
   * recording proxies. */
  readonly proxies?: boolean
  /** The seeds to run in place of each batch's own. */
  readonly seeds?: readonly number[]
}

/** The batches `selection` selects: the one it names, or all. */
export const selectBatches = <T extends { readonly name: string }>(
  batches: readonly T[],
  { batch }: Selection,
): T[] => batches.filter((candidate) => batch === undefined || candidate.name === batch)

/** The command that shows one seed of a batch, for a failure to print. */
export const reproduce = (family: string, batch: string, seed: number): string =>
  `pnpm check lean ${family} --batch ${batch} --seeds ${seed} --dump`

/** The seeds that `text` lists: single seeds and ranges such as `1-1500`, joined by commas. */
export function parseSeeds(text: string): number[] {
  const seeds = text.split(',').flatMap((part) => {
    const match = /^(\d+)(?:-(\d+))?$/.exec(part.trim())
    const from = Number(match?.[1])
    const to = match?.[2] === undefined ? from : Number(match[2])
    if (match === null || from < 1 || to < from)
      throw new UsageError(`--seeds takes seeds and ranges such as 1-1500,25127, not "${text}"`)
    return Array.from({ length: to - from + 1 }, (_, index) => from + index)
  })
  return [...new Set(seeds)]
}
