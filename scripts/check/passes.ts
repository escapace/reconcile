import { mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import type { Inputs } from '../framework/tree'
import { STATE } from '../framework/paths'

/** A round that passed, and the inputs it passed on. */
export interface Pass extends Inputs {
  readonly finishedAt: string
  readonly receipt: string
}

/** How many passes each round keeps, so that switching branches back finds them again. */
const KEPT = 50

const directory = (round: string): string => path.join(STATE, 'passes', round)

const read = (file: string): Pass | undefined => {
  try {
    return JSON.parse(readFileSync(file, 'utf8')) as Pass
  } catch {
    return undefined
  }
}

/** The recorded pass of `round` on exactly these inputs, if any. */
export const findPass = (round: string, hash: string): Pass | undefined =>
  read(path.join(directory(round), `${hash}.json`))

/** The latest recorded pass of `round`, to say what changed since. */
export const latestPass = (round: string): Pass | undefined =>
  read(path.join(directory(round), 'latest.json'))

/** Records that `round` passed on `inputs`, keeping the newest passes of each round. */
export function recordPass(round: string, inputs: Inputs, receipt: string): void {
  const folder = directory(round)
  mkdirSync(folder, { recursive: true })
  const pass: Pass = { ...inputs, finishedAt: new Date().toISOString(), receipt }
  const text = `${JSON.stringify(pass)}\n`
  writeFileSync(path.join(folder, `${inputs.hash}.json`), text)
  writeFileSync(path.join(folder, 'latest.json'), text)
  const recorded = readdirSync(folder)
    .filter((name) => name !== 'latest.json')
    .map((name) => ({ name, time: statSync(path.join(folder, name)).mtimeMs }))
    .sort((left, right) => right.time - left.time)
  for (const { name } of recorded.slice(KEPT)) rmSync(path.join(folder, name), { force: true })
}
