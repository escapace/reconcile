// The axiom audit: every declaration of every module the Lake library lists, private and
// generated ones included, may depend only on the standard axioms, so a `sorry` fails it. Run it
// after `lake build`; the modules share one imported environment. The control audits four
// modules with no axiom allowed and must be rejected, after it found their private declarations.
import { spawnSync } from 'node:child_process'
import { mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { entry } from '../framework/entry'
import { ROOT } from '../framework/paths'

/** The axioms every declaration may depend on. */
const STANDARD = ['propext', 'Classical.choice', 'Quot.sound']

/** Modules of the control: generated and private declarations, and a proof that depends on
 * another module's. */
const CONTROL = [
  'Graph.GraphPolicy',
  'Property.PropertyOrder',
  'Graph.ClosureHistory',
  'Oracle.FactRenamingOracle',
]

/** The roots of every `[[lean_lib]]` of `lakefile.toml`, which must list each Lean file under
 * `lean/` once and nothing else. A root missing from the parse shows as a coverage mismatch. */
export function configuredModules(root: string): string[] {
  const lakefile = readFileSync(path.join(root, 'lakefile.toml'), 'utf8')
  const modules = lakefile
    .split(/^(?=\[)/m)
    .filter((table) => table.startsWith('[[lean_lib]]'))
    .flatMap((table) => [
      ...(/^roots\s*=\s*\[([^\]]*)\]/m.exec(table)?.[1] ?? '').matchAll(/"([^"]+)"/g),
    ])
    .map((match) => match[1])
  if (modules.length === 0 || new Set(modules).size !== modules.length)
    throw new Error('Empty or duplicate audit roots')
  const sources = readdirSync(path.join(root, 'lean'), { recursive: true })
    .map(String)
    .filter((file) => file.endsWith('.lean'))
    .map((file) => file.slice(0, -'.lean'.length).split(path.sep).join('.'))
  const mismatch = [
    ...sources.filter((source) => !modules.includes(source)),
    ...modules.filter((module) => !sources.includes(module)),
  ]
  if (mismatch.length > 0) throw new Error(`Lake/source coverage mismatch: ${mismatch.join(', ')}`)
  return modules
}

/** Lean name literals, as an array's elements. */
const names = (list: readonly string[]): string => list.map((name) => `\`${name}`).join(', ')

/** The Lean program that audits `modules`, allowing `allowed`; with `requirePrivate`, it first
 * fails unless it found a private declaration. */
export function auditSource(
  modules: readonly string[],
  allowed: readonly string[] = STANDARD,
  requirePrivate = false,
): string {
  return [
    ...modules.map((module) => `import ${module}`),
    'import Lean',
    '',
    'set_option maxHeartbeats 0 in',
    'run_cmd do',
    '  let env ← Lean.getEnv',
    `  let modules : Array Lean.Name := #[${names(modules)}]`,
    '  -- moduleNames maps every import; do not rebuild that array for each declaration.',
    '  let moduleNames := env.header.moduleNames',
    '  let declarations := env.constants.fold (init := #[]) fun names name _ =>',
    '    match env.getModuleIdxFor? name with',
    '    | some idx =>',
    '      if modules.contains moduleNames[idx.toNat]! then names.push name else names',
    '    | none => names',
    '  for module in modules do',
    '    unless declarations.any (fun name =>',
    '        (env.getModuleIdxFor? name).any (fun idx =>',
    '          moduleNames[idx.toNat]! == module)) do',
    '      throwError "No declarations found for configured module {module}"',
    ...(requirePrivate
      ? [
          '  unless declarations.any (fun name => name.toString.startsWith "_private.") do',
          '    throwError "No private declarations were discovered"',
        ]
      : []),
    '  let (_, state) := ((declarations.forM Lean.CollectAxioms.collect).run env).run {}',
    `  let allowed : Array Lean.Name := #[${names(allowed)}]`,
    '  for axiomName in state.axioms do',
    '    unless allowed.contains axiomName do',
    '      throwError "Unexpected axiom: {axiomName}"',
    '  Lean.logInfo m!"Axiom audit passed: {declarations.size} declarations across {modules.size} modules, standard axioms only."',
    '',
  ].join('\n')
}

/** Runs `source` with the project's Lean environment; returns its exit code and output. */
function runLean(source: string, echo: boolean): { output: string; status: number } {
  const directory = mkdtempSync(path.join(tmpdir(), 'reconcile-axioms-'))
  try {
    const file = path.join(directory, 'Audit.lean')
    writeFileSync(file, source)
    const result = spawnSync('lake', ['env', 'lean', file], {
      cwd: ROOT,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    })
    const output = `${result.stdout}${result.stderr}`
    if (echo) process.stdout.write(output)
    return { output, status: result.status ?? 1 }
  } finally {
    rmSync(directory, { force: true, recursive: true })
  }
}

/** The audit, or with `control` the audit that must reject a standard axiom. */
async function main({ control }: { readonly control?: boolean }): Promise<number> {
  if (control !== true)
    return await Promise.resolve(runLean(auditSource(configuredModules(ROOT)), true).status)
  const { output, status } = runLean(auditSource(CONTROL, [], true), false)
  if (status !== 0 && /Unexpected axiom: (?:propext|Classical\.choice|Quot\.sound)/.test(output)) {
    console.log(
      'The audit rejects a standard axiom when none is allowed, after finding private declarations.',
    )
    return 0
  }
  console.error(
    `The control audit was not rejected for a standard axiom (exit ${status}):\n${output}`,
  )
  return 1
}

await entry(import.meta.filename, main)
