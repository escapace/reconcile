import { mkdirSync, readdirSync, readFileSync, rmSync, statSync, utimesSync } from 'node:fs'
import path from 'node:path'
import { writeJson } from '../framework/files'
import type { Inputs } from '../framework/tree'
import { STATE } from '../framework/paths'

/** A round that passed, and the inputs it passed on: those it left, which include the outputs it
 * rewrote, and the hash of those it started on, which its receipt records. */
export interface Pass extends Inputs {
  readonly finishedAt: string
  readonly receipt: string
  readonly startHash: string
}

/** How many passes each round keeps, so that switching branches back finds them again. */
const KEPT = 50

const directory = (round: string): string => path.join(STATE, 'passes', round)

function read<T>(file: string): T | undefined {
  try {
    return JSON.parse(readFileSync(file, 'utf8')) as T
  } catch {
    return undefined
  }
}

/** Whether the receipt a pass names records a round that passed on the inputs it started on. */
const vouched = (pass: Pass): boolean => {
  const receipt = read<{ inputs?: { hash?: string }; status?: string }>(pass.receipt)
  return receipt?.status === 'passed' && receipt.inputs?.hash === pass.startHash
}

/** The recorded pass of `round` on exactly these inputs, if its receipt vouches for it. Finding
 * it keeps it among the passes the round keeps longest. */
export function findPass(round: string, hash: string): Pass | undefined {
  const file = path.join(directory(round), `${hash}.json`)
  const pass = read<Pass>(file)
  if (pass?.hash !== hash || !vouched(pass)) return undefined
  const now = new Date()
  utimesSync(file, now, now)
  return pass
}

/** The latest recorded pass of `round`, to say what changed since. */
export const latestPass = (round: string): Pass | undefined =>
  read<Pass>(path.join(directory(round), 'latest.json'))

/** Records that `round` passed on `inputs`, keeping the passes of each round used most recently. */
export function recordPass(
  round: string,
  inputs: Inputs,
  receipt: string,
  startHash: string,
): void {
  const folder = directory(round)
  mkdirSync(folder, { recursive: true })
  const pass: Pass = { ...inputs, finishedAt: new Date().toISOString(), receipt, startHash }
  writeJson(path.join(folder, `${inputs.hash}.json`), pass)
  writeJson(path.join(folder, 'latest.json'), pass)
  const recorded = readdirSync(folder)
    .filter((name) => name !== 'latest.json')
    .map((name) => ({ name, time: statSync(path.join(folder, name)).mtimeMs }))
    .sort((left, right) => right.time - left.time)
  for (const { name } of recorded.slice(KEPT)) rmSync(path.join(folder, name), { force: true })
}
