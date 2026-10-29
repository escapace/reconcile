import { UsageError } from '../framework/command'
import { rounds, scenarioNames } from '../bench-workloads'
import { diagnosticNames } from './diagnostics'

/** The frozen `perf/` workloads, which run in the measured tree's own harness. Every other
 * scenario runs in the diagnostic overlay, which selects it at run time. */
const FROZEN: readonly string[] = ['snapshot', 'reconcile', 'reconcile-plain-object', 'produce']

/** Every scenario a bench command measures: the default and small workloads, then the
 * diagnostics, which target particular shapes. */
export const SCENARIOS: readonly string[] = [...new Set([...scenarioNames, ...diagnosticNames])]

/** The scenario sets `ab` takes by name. */
export const SETS: Readonly<Record<string, readonly string[]>> = rounds

/** Whether a scenario runs in the diagnostic overlay rather than the frozen harness. */
export const inOverlay = (scenario: string): boolean => !FROZEN.includes(scenario)

/** The scenarios `names` selects, each set expanded and no scenario twice; an unknown name is a
 * usage error. */
export function selectScenarios(names: readonly string[]): string[] {
  const unknown = names.filter((name) => SETS[name] === undefined && !SCENARIOS.includes(name))
  if (unknown.length > 0)
    throw new UsageError(
      `unknown scenarios: ${unknown.join(', ')}; \`pnpm bench --help\` lists the scenarios`,
    )
  return [...new Set(names.flatMap((name) => SETS[name] ?? [name]))]
}
