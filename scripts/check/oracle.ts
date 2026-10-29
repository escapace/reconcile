import assert from 'node:assert/strict'
import { spawn } from 'node:child_process'
import { createInterface } from 'node:readline'

export type Oracle = (
  family: string,
  options?: { input?: string; maxBuffer?: number },
) => Promise<string>

const DEFAULT_OUTPUT_LIMIT = 16 * 1024 * 1024

/** Completes a response at its marker line: `null` ends it, a string is the oracle's error. */
function completed(marker: string, output: string[]): string {
  const error: unknown = JSON.parse(marker.slice(1))
  assert(error === null || typeof error === 'string', 'Invalid Lean response marker')
  if (error !== null) throw new Error(error)
  return output.join('\n') + '\n'
}

function request(family: string, input = ''): string {
  return JSON.stringify({ family, input }) + '\n'
}

function logDuration(family: string, started: number): void {
  console.log(`Oracle ${family}: ${((performance.now() - started) / 1000).toFixed(3)}s`)
}

/** Shares one native oracle process across sequential requests; the gate audits axioms first. */
export async function startOracle() {
  const child = spawn('.lake/build/bin/reconcile-oracle', [], {
    stdio: ['pipe', 'pipe', 'inherit'],
  })
  let failure: Error | undefined
  const fail = (error: Error): void => {
    failure ??= error
  }
  child.on('error', fail)
  child.stdin.on('error', fail)
  const exited = new Promise<number | null>((resolve) => child.once('close', resolve))
  const lines = createInterface({ input: child.stdout })[Symbol.asyncIterator]()
  let pending = false
  let closed = false
  let bytes = 0
  let limit = 1024 * 1024
  // Bound bytes before readline can assemble an unexpectedly large single line.
  child.stdout.on('data', (chunk: Buffer) => {
    bytes += chunk.length
    if (bytes > limit) {
      failure = new Error(`Lean oracle output exceeds ${limit} bytes`)
      child.kill('SIGKILL')
    }
  })
  const reply = async (): Promise<string> => {
    const output: string[] = []
    for (;;) {
      const next = await lines.next()
      if (failure !== undefined) throw failure
      assert(next.done !== true, 'Lean oracle exited before completing its response')
      if (next.value.startsWith('\x1e')) return completed(next.value, output)
      output.push(next.value)
    }
  }
  const close = async (): Promise<void> => {
    closed = true
    child.stdin.end()
    const timer = setTimeout(() => child.kill('SIGKILL'), 2000)
    try {
      const code = await exited
      if (failure !== undefined) throw failure
      assert.equal(code, 0, 'Lean oracle did not exit successfully')
    } finally {
      clearTimeout(timer)
    }
  }
  try {
    assert.equal((await reply()).trim(), '', 'Unexpected oracle startup output')
  } catch (error) {
    child.kill('SIGKILL')
    await exited
    throw error
  }
  const run: Oracle = async (family, options = {}) => {
    assert(!closed && !pending, 'Oracle requests require an open, idle session')
    limit = options.maxBuffer ?? DEFAULT_OUTPUT_LIMIT
    assert(Number.isSafeInteger(limit) && limit > 0, 'Invalid oracle output limit')
    bytes = 0
    pending = true
    const started = performance.now()
    try {
      child.stdin.write(request(family, options.input))
      return await reply()
    } finally {
      logDuration(family, started)
      pending = false
    }
  }
  return { close, run }
}

/** Reads a line-per-case response whose first line declares the size of the finite corpus. */
export async function oracleCorpus(
  oracle: Oracle,
  family: string,
  size: number,
  maxBuffer: number,
): Promise<string[]> {
  const lines = (await oracle(family, { maxBuffer })).trim().split('\n')
  assert.equal(Number(lines.shift()), size, 'The finite bridge corpus changed')
  assert.equal(lines.length, size)
  return lines
}

/** Narrows one decoded oracle value to a JSON object. */
export function jsonObject(value: unknown): Record<string, unknown> {
  assert.ok(value !== null && typeof value === 'object' && !Array.isArray(value))
  return value as Record<string, unknown>
}

/** Narrows one decoded oracle value to a boolean. */
export function jsonBoolean(value: unknown): boolean {
  assert.ok(typeof value === 'boolean')
  return value
}

/** Narrows one decoded oracle value to an integer within inclusive bounds. */
export function integerIn(value: unknown, minimum: number, maximum: number): number {
  assert.ok(typeof value === 'number' && Number.isSafeInteger(value))
  assert.ok(value >= minimum && value <= maximum)
  return value
}

/** Checks every corpus row; at least one must witness strictly less work. */
export function strictWitnesses(
  lines: readonly string[],
  check: (row: Record<string, unknown>) => boolean,
): number {
  let witnesses = 0
  for (const line of lines) witnesses += Number(check(jsonObject(JSON.parse(line))))
  assert.ok(witnesses > 0, 'The work theorem needs nontrivial executable witnesses')
  return witnesses
}
