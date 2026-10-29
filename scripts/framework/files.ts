import { renameSync, rmSync, writeFileSync } from 'node:fs'

/** Writes `file` at once: a reader sees the old content or the new, never a part of it. */
function writeAtomic(file: string, text: string): void {
  const staged = `${file}.${process.pid}.tmp`
  try {
    writeFileSync(staged, text)
    renameSync(staged, file)
  } finally {
    rmSync(staged, { force: true })
  }
}

/** Writes `value` as JSON, at once. */
export const writeJson = (file: string, value: unknown): void =>
  writeAtomic(file, `${JSON.stringify(value, undefined, 2)}\n`)
