import { realpathSync } from 'node:fs'

/** The file a path names, through any symbolic link, as Node names the module it runs. */
const real = (file: string): string | undefined => {
  try {
    return realpathSync(file)
  } catch {
    return undefined
  }
}

/**
 * Runs `main` when `file` is the script Node was started with, passing the JSON configuration
 * that the command running it gives as its one argument, and exits with the code it returns.
 * Imported, the module only provides its exports. The paths are compared as files, so that a
 * checkout reached through a symbolic link still runs its scripts rather than passing silently.
 */
export async function entry<T>(file: string, main: (config: T) => Promise<number>): Promise<void> {
  const started = process.argv[1]
  if (started === undefined || real(started) !== real(file)) return
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
