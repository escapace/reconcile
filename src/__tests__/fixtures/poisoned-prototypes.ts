// Setup of the poisoned vitest project: every test runs with a proxy of Object.prototype as the
// prototype of Array.prototype, so that a read of an array key that neither the array nor
// Array.prototype holds, a hole or an index past the end among them, and a write of a named key
// to an array, pass through the proxy. One that library code makes during a call of the public
// API fails the test: a property that other code added to a standard prototype would answer it
// or take the write. The proxy forwards everything, so `in`, descriptors and writes behave as
// without it; a draft forwarding a read of the recipe's is the recipe's read, and test code and
// the test runner read through the proxy freely. Object.prototype itself takes no proxy, so the
// child-process fixture of standard-prototypes.spec.ts covers it.
import { afterAll, afterEach, beforeAll } from 'vitest'

const violations: string[] = []

const OTHER = /\/(?:node_modules|scripts|src\/__tests__)\//
const LIBRARY = /\/(?:lib|src)\//
const DRAFT = /\/src\/(?:draft-session|types\/shared\/draft-[a-z-]+)\.ts$/

interface Site {
  getColumnNumber: () => number | null
  getFileName: () => string | null | undefined
  getFunctionName: () => string | null
  getLineNumber: () => number | null
}

/** The V8 stack trace API of `Error`, which the declaration build's types do not name. */
interface StackTraceApi {
  prepareStackTrace: ((error: Error, sites: Site[]) => unknown) | undefined
  stackTraceLimit: number
  captureStackTrace: (holder: object, above?: (...parameters: never[]) => unknown) => void
}
const v8 = Error as unknown as StackTraceApi
const keepSites = (_: Error, stack: Site[]): unknown => stack

/** The call sites above `note`, innermost first, without native frames; the draft modules and
 * the first frame outside them fit in the few frames taken. */
function sites(): Site[] {
  const prepare = v8.prepareStackTrace
  const limit = v8.stackTraceLimit
  v8.prepareStackTrace = keepSites
  v8.stackTraceLimit = 6
  const holder: { stack?: unknown } = {}
  v8.captureStackTrace(holder, note)
  const stack = holder.stack as Site[]
  v8.prepareStackTrace = prepare
  v8.stackTraceLimit = limit
  const result: Site[] = []
  for (const site of stack) {
    const file = site.getFileName()
    if (file !== null && file !== undefined && file !== '') result.push(site)
  }
  return result
}

const fileOf = (site: Site | undefined): string => site?.getFileName() ?? ''
const isLibrary = (file: string): boolean => LIBRARY.test(file) && !OTHER.test(file)

/** Whether the innermost frames are the draft modules forwarding a read of code outside the
 * library, which called into them. */
function forwarded(frames: readonly Site[]): boolean {
  let index = 0
  while (index < frames.length && DRAFT.test(fileOf(frames[index]))) index += 1
  return index > 0 && !isLibrary(fileOf(frames[index]))
}

/** The library frame that read or wrote for itself, if the innermost code frame is one. */
function offender(): string | undefined {
  const frames = sites()
  const first = frames[0]
  if (first === undefined || !isLibrary(fileOf(first)) || forwarded(frames)) return undefined
  const position = `${fileOf(first)}:${first.getLineNumber()}:${first.getColumnNumber()}`
  return `${first.getFunctionName() ?? '<anonymous>'} (${position})`
}

function note(action: string, key: PropertyKey): void {
  const frame = offender()
  if (frame !== undefined) violations.push(`${action} ${String(key)} of an array at ${frame}`)
}

const isIndex = (key: PropertyKey): boolean =>
  typeof key === 'string' && key !== '' && String(Number(key) >>> 0) === key

/** Object.prototype, forwarding every operation, noting the reads and named writes that reach it. */
const chain = new Proxy(Object.prototype, {
  get(target, key, receiver): unknown {
    note('read', key)
    return Reflect.get(target, key, receiver)
  },
  set(target, key, value, receiver): boolean {
    if (!isIndex(key)) note('wrote', key)
    return Reflect.set(target, key, value, receiver)
  },
})

beforeAll(() => {
  Object.setPrototypeOf(Array.prototype, chain)
})
afterEach(() => {
  if (violations.length === 0) return
  const report = violations.splice(0).join('\n')
  throw new Error(`library code read or wrote through Array.prototype:\n${report}`)
})
afterAll(() => {
  Object.setPrototypeOf(Array.prototype, Object.prototype)
})
