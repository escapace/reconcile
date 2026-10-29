import path from 'node:path'

/**
 * Runs `main` when `file` is the script Node was started with, passing the JSON configuration
 * that the command running it gives as its one argument, and exits with the code it returns.
 * Imported, the module only provides its exports.
 */
export async function entry<T>(file: string, main: (config: T) => Promise<number>): Promise<void> {
  if (path.resolve(process.argv[1] ?? '') !== file) return
  process.exitCode = await main(JSON.parse(process.argv[2] ?? '{}') as T)
}

/** The command line that runs a TypeScript script's `entry` with `config`. */
export const script = (file: string, config: object, flags: readonly string[] = []): string[] => [
  process.execPath,
  ...flags,
  '--import',
  'tsx',
  file,
  JSON.stringify(config),
]
