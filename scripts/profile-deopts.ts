type Phase = 'complete' | 'measurement' | 'setup' | 'unmarked' | 'warmup'

interface DeoptEntry {
  count: number
  functionName: string
  parsed: boolean
  phase: Phase
  reason: string
}

const isDeoptEvent = (line: string): boolean =>
  line.includes('[bailout ') || line.includes('[deoptimizing ')

/** Reads the function name; `matched` is false when neither trace shape names a function. */
function deoptFunction(line: string) {
  const matched =
    /<JSFunction ([^(]*)\(sfi =/.exec(line) ?? /\[deoptimizing\s+\([^)]*\):[^<]*<(\S+)>/.exec(line)
  const name = matched?.[1].trim() ?? ''
  return {
    functionName: name === '' ? '(unparsed or anonymous)' : name,
    matched: matched !== null,
  }
}

function deoptReason(line: string) {
  const reasonStart = line.indexOf('reason:')
  const reasonEnd = line.indexOf('): begin.', reasonStart)
  const parsed = reasonStart >= 0 && reasonEnd > reasonStart
  return {
    parsed,
    reason: parsed
      ? line.slice(reasonStart + 'reason:'.length, reasonEnd).trim()
      : 'Unparsed event; inspect the raw trace',
  }
}

/** Keeps every recognized bailout line, including events whose fields cannot be parsed. */
export function parseDeopts(content: string) {
  const entries = new Map<string, DeoptEntry>()
  const coverage = { parsed: 0, total: 0, unparsed: 0 }
  let phase: Phase = 'unmarked'
  for (const line of content.split('\n')) {
    const marker = /^RECONCILE_PHASE (complete|measurement|setup|warmup)$/.exec(line)
    if (marker !== null) phase = marker[1] as Phase
    if (!isDeoptEvent(line)) continue
    const { functionName, matched } = deoptFunction(line)
    const { parsed: reasonParsed, reason } = deoptReason(line)
    const parsed = matched && reasonParsed
    coverage.total += 1
    coverage[parsed ? 'parsed' : 'unparsed'] += 1
    const key = JSON.stringify([functionName, phase, reason, parsed])
    const previous = entries.get(key)
    if (previous === undefined) entries.set(key, { count: 1, functionName, parsed, phase, reason })
    else previous.count += 1
  }
  return { coverage, entries: [...entries.values()].sort((a, b) => b.count - a.count) }
}
