import { parseArgs } from 'node:util'

/** One option of a command, with its help text. */
export interface Option {
  readonly description: string
  readonly type: 'boolean' | 'string'
  readonly default?: boolean | string
  readonly multiple?: boolean
  /** How help names the value of a string option, such as `<dir>`. */
  readonly placeholder?: string
  readonly short?: string
}

export interface Parsed {
  readonly positionals: readonly string[]
  readonly values: Readonly<
    Record<string, boolean | string | ReadonlyArray<boolean | string> | undefined>
  >
}

/** A command of the maintainer CLI: a group of subcommands, or a command that runs. */
export interface Command {
  readonly name: string
  readonly summary: string
  readonly usage: string
  readonly commands?: readonly Command[]
  /** Paragraphs help prints after the options. */
  readonly description?: readonly string[]
  readonly examples?: readonly string[]
  readonly options?: Readonly<Record<string, Option>>
  /** Hands the raw arguments to `run` as positionals, for a tool that parses its own. */
  readonly passthrough?: boolean
  /** Flags that no longer exist, each with what replaces it. */
  readonly retired?: Readonly<Record<string, string>>
  readonly run?: (parsed: Parsed) => Promise<number>
  /** Tables help prints before the options, such as the rounds of `check`. */
  readonly sections?: ReadonlyArray<{
    readonly rows: ReadonlyArray<readonly [string, string]>
    readonly title: string
  }>
}

/** A mistake in the command line: exit code 2, with a pointer to the help of the command it was
 * made in. */
export class UsageError extends Error {
  invocation: string | undefined
}

/** A command that cannot run, such as when another round holds the lock or a tool is missing:
 * exit code 3, as for any error of the tooling itself, since nothing was judged. */
export class Blocked extends Error {}

const HELP: Option = { description: 'Show this help.', short: 'h', type: 'boolean' }

const table = (rows: ReadonlyArray<readonly [string, string]>): string[] => {
  const width = Math.max(...rows.map(([left]) => left.length)) + 2
  return rows.map(([left, right]) => `  ${left.padEnd(width)}${right}`)
}

/** A titled block of help, or nothing when it has no lines. */
const block = (title: string, lines: readonly string[]): string[] =>
  lines.length === 0 ? [] : ['', `${title}:`, ...lines]

const optionName = (name: string, option: Option): string =>
  `${option.short === undefined ? '' : `-${option.short}, `}--${name}` +
  (option.type === 'string' ? ` ${option.placeholder ?? '<value>'}` : '')

const optionText = (option: Option): string =>
  option.default === undefined || option.default === false
    ? option.description
    : `${option.description} Default: ${String(option.default)}.`

const optionsOf = (command: Command): Array<[string, Option]> =>
  Object.entries({ ...command.options, help: HELP })

/** The help of `command`, invoked as `invocation`: summary, usage, examples first, then the
 * tables and options. */
export function help(invocation: string, command: Command): string {
  const options =
    command.passthrough === true
      ? []
      : optionsOf(command).map(
          ([name, option]) => [optionName(name, option), optionText(option)] as const,
        )
  const lines = [
    command.summary,
    '',
    `Usage: ${invocation} ${command.usage}`.trimEnd(),
    ...block(
      'Examples',
      (command.examples ?? []).map((example) => `  ${example}`),
    ),
    ...block(
      'Commands',
      table((command.commands ?? []).map((sub) => [sub.name, sub.summary] as const)),
    ),
    ...(command.sections ?? []).flatMap((section) => block(section.title, table(section.rows))),
    ...block('Options', table(options)),
    ...(command.description ?? []).flatMap((paragraph) => ['', paragraph]),
  ]
  return `${lines.join('\n')}\n`
}

/** An option as `parseArgs` takes it, which refuses a field that is present but undefined. */
const parseOption = ({ default: value, multiple, short, type }: Option) => ({
  type,
  ...(value === undefined ? {} : { default: value }),
  ...(multiple === undefined ? {} : { multiple }),
  ...(short === undefined ? {} : { short }),
})

/** Parses `arguments_` against the command's options; a retired or unknown flag is a usage
 * error. */
function parse(command: Command, arguments_: readonly string[]): Parsed {
  for (const argument of arguments_) {
    const flag = argument.split('=')[0]
    const replacement = command.retired?.[flag]
    if (replacement !== undefined) throw new UsageError(`${flag} no longer exists: ${replacement}`)
  }
  const options = Object.fromEntries(
    optionsOf(command).map(([name, option]) => [name, parseOption(option)]),
  )
  try {
    return parseArgs({ allowPositionals: true, args: [...arguments_], options, strict: true })
  } catch (error) {
    throw new UsageError((error as Error).message)
  }
}

const printHelp = (invocation: string, command: Command): number => {
  process.stdout.write(help(invocation, command))
  return 0
}

/** The subcommand of `group` named `name`; any other name is a usage error. */
function subcommand(group: Command, name: string): Command {
  const commands = group.commands ?? []
  const found = commands.find((candidate) => candidate.name === name)
  if (found !== undefined) return found
  throw new UsageError(
    `unknown command "${name}"; the commands are ${commands.map((sub) => sub.name).join(', ')}`,
  )
}

/** Runs a group's subcommand, or prints the help that `help`, `--help` or no argument asks for. */
async function dispatchGroup(
  invocation: string,
  group: Command,
  arguments_: readonly string[],
): Promise<number> {
  const [first, ...rest] = arguments_
  if (first === undefined || first === '--help' || first === '-h')
    return printHelp(invocation, group)
  if (first === 'help') {
    if (rest.length === 0) return printHelp(invocation, group)
    return printHelp(`${invocation} ${rest[0]}`, subcommand(group, rest[0]))
  }
  return await dispatch(`${invocation} ${first}`, subcommand(group, first), rest)
}

/** Runs a command that is not a group, after parsing its options unless it parses its own. */
async function dispatchLeaf(
  invocation: string,
  command: Command,
  arguments_: readonly string[],
): Promise<number> {
  if (command.run === undefined) return printHelp(invocation, command)
  if (command.passthrough === true)
    return await command.run({ positionals: arguments_, values: {} })
  if (arguments_[0] === 'help') return printHelp(invocation, command)
  const parsed = parse(command, arguments_)
  if (parsed.values.help === true) return printHelp(invocation, command)
  return await command.run(parsed)
}

async function dispatch(
  invocation: string,
  command: Command,
  arguments_: readonly string[],
): Promise<number> {
  try {
    return command.commands === undefined
      ? await dispatchLeaf(invocation, command, arguments_)
      : await dispatchGroup(invocation, command, arguments_)
  } catch (error) {
    if (error instanceof UsageError) error.invocation ??= invocation
    throw error
  }
}

/** Reports a usage error, a command that could not run or an error of the tooling itself, and
 * returns its exit code. An unexpected error keeps its stack, to show where the tooling failed. */
function report(error: unknown, invocation: string): number {
  if (error instanceof UsageError) {
    process.stderr.write(
      `error: ${error.message}\nRun "${error.invocation ?? invocation} --help" for usage.\n`,
    )
    return 2
  }
  const text =
    error instanceof Blocked
      ? error.message
      : `the tooling failed: ${error instanceof Error ? (error.stack ?? error.message) : String(error)}`
  process.stderr.write(`error: ${text}\n`)
  return 3
}

/**
 * Runs the command `argv` names, as `pnpm <name> ...`, and returns its exit code: 0 when it
 * passed, 1 when a check failed, 2 for a usage error, 3 when it could not run, 124 when a round's
 * result is incomplete and 130 when it was interrupted.
 */
export async function main(commands: readonly Command[], argv: readonly string[]): Promise<number> {
  const [name, ...arguments_] = argv
  const command = commands.find((candidate) => candidate.name === name)
  if (command === undefined) {
    const known = commands.map((candidate) => candidate.name).join(', ')
    process.stderr.write(`error: unknown command "${name ?? ''}"; the commands are ${known}\n`)
    return 2
  }
  try {
    return await dispatch(`pnpm ${name}`, command, arguments_)
  } catch (error) {
    return report(error, `pnpm ${name}`)
  }
}
