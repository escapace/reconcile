// Reads what V8 reports of a bundled harness: sampled CPU and heap profiles, attributed to source
// frames, and traces of optimizations and deoptimizations.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import type { SourceMap } from 'node:module'
import path from 'node:path'

export interface AttributionFrame {
  readonly functionName: string
  readonly location: string
  readonly scope: 'mapped' | 'project' | 'unmapped'
}

export interface WeightedFrame extends AttributionFrame {
  inclusive: number
  self: number
}

export interface WeightedNode {
  readonly frame: AttributionFrame
  readonly id: number
  readonly weight: number
  readonly parent?: number
}

function aggregateOf(
  frames: Map<string, WeightedFrame>,
  key: string,
  frame: AttributionFrame,
): WeightedFrame {
  let aggregate = frames.get(key)
  if (aggregate === undefined) {
    aggregate = { ...frame, inclusive: 0, self: 0 }
    frames.set(key, aggregate)
  }
  return aggregate
}

/** Charges one node's weight to itself and once to each distinct source frame on its ancestry. */
function charge(
  node: WeightedNode,
  byId: ReadonlyMap<number, WeightedNode>,
  frames: Map<string, WeightedFrame>,
): void {
  const visited = new Set<number>()
  const sources = new Set<string>()
  let current: WeightedNode | undefined = node
  while (current !== undefined) {
    assert(!visited.has(current.id), 'Cyclic profile ancestry')
    visited.add(current.id)
    const { frame } = current
    const key = `${frame.scope}|${frame.functionName}|${frame.location}`
    const aggregate = aggregateOf(frames, key, frame)
    if (current === node) aggregate.self += node.weight
    if (!sources.has(key)) aggregate.inclusive += node.weight
    sources.add(key)
    const parent: number | undefined = current.parent
    current = parent === undefined ? undefined : byId.get(parent)
    assert(parent === undefined || current !== undefined, 'Missing profile parent')
  }
}

/** Attributes a sampled tree without counting a recursive source frame twice per sample. */
export function attribute(nodes: readonly WeightedNode[]) {
  const byId = new Map(nodes.map((node) => [node.id, node]))
  assert.equal(byId.size, nodes.length, 'Duplicate profile node IDs')
  const frames = new Map<string, WeightedFrame>()
  const coverage = { mapped: 0, project: 0, total: 0, unmapped: 0 }
  for (const node of nodes) {
    assert(Number.isFinite(node.weight) && node.weight >= 0, 'Invalid profile weight')
    coverage.total += node.weight
    coverage[node.frame.scope] += node.weight
    charge(node, byId, frames)
  }
  return { coverage, frames: [...frames.values()] }
}

/** A bundle, its source map and the source root that mapped frames are reported against. */
export interface BundleMap {
  readonly bundlePath: string
  readonly root: string
  readonly sourceMap: SourceMap
}

interface CallFrame {
  columnNumber: number
  functionName: string
  lineNumber: number
  scriptId: string
  url: string
}

interface CPUProfileNode {
  callFrame: CallFrame
  hitCount: number
  id: number
  children?: number[]
}

interface CPUProfile {
  endTime: number
  nodes: CPUProfileNode[]
  samples: number[]
  startTime: number
  timeDeltas: number[]
}

interface HeapProfileNode {
  callFrame: CallFrame
  children: HeapProfileNode[]
  id: number
  selfSize: number
}

interface HeapProfile {
  head: HeapProfileNode
  samples: Array<{ nodeId: number; ordinal: number; size: number }>
}

interface ResolvedFrame {
  functionName: string
  originalColumn: number
  originalLine: number
  originalSource: string
}

const displayName = (functionName: string): string =>
  functionName === '' ? '(anonymous)' : functionName

function resolveFrame(
  callFrame: CallFrame,
  { bundlePath, root, sourceMap }: BundleMap,
): ResolvedFrame | undefined {
  if (!callFrame.url.endsWith(path.basename(bundlePath))) {
    return undefined
  }

  const entry = sourceMap.findEntry(callFrame.lineNumber, callFrame.columnNumber)

  if (!('originalSource' in entry) || entry.originalSource === undefined) {
    return undefined
  }

  assert(typeof entry.originalSource === 'string')
  assert(typeof entry.originalLine === 'number')
  assert(typeof entry.originalColumn === 'number')

  const absPath = path.resolve(path.dirname(bundlePath), entry.originalSource)

  return {
    functionName: displayName(callFrame.functionName),
    originalColumn: entry.originalColumn + 1,
    originalLine: entry.originalLine + 1,
    originalSource: path.relative(root, absPath),
  }
}

const unmappedFrame = (frame: CallFrame): AttributionFrame => ({
  functionName: displayName(frame.functionName),
  location: `${frame.url === '' ? '(native)' : frame.url}:${frame.lineNumber + 1}:${frame.columnNumber + 1}`,
  scope: 'unmapped',
})

const mappedFrame = (frame: ResolvedFrame): AttributionFrame => ({
  functionName: frame.functionName,
  location: `${frame.originalSource}:${frame.originalLine}:${frame.originalColumn}`,
  scope: frame.originalSource.startsWith('src/') ? 'project' : 'mapped',
})

function attributionFrame(frame: CallFrame, bundle: BundleMap): AttributionFrame {
  const resolved = resolveFrame(frame, bundle)
  return resolved === undefined ? unmappedFrame(frame) : mappedFrame(resolved)
}

function parentIds(nodes: readonly CPUProfileNode[]): Map<number, number> {
  const parents = new Map<number, number>()
  for (const node of nodes)
    for (const child of node.children ?? []) {
      assert(!parents.has(child), 'Multiple CPU profile parents')
      parents.set(child, node.id)
    }
  return parents
}

function sampleWeights(raw: CPUProfile): Map<number, number> {
  const weights = new Map(raw.nodes.map((node) => [node.id, 0]))
  for (const [index, id] of raw.samples.entries()) {
    const before = weights.get(id)
    assert(before !== undefined, 'CPU sample references missing node')
    weights.set(id, before + raw.timeDeltas[index])
  }
  return weights
}

export function parseCPUProfile(profilePath: string, bundle: BundleMap) {
  const raw = JSON.parse(readFileSync(profilePath, 'utf8')) as CPUProfile
  assert.equal(raw.samples.length, raw.timeDeltas.length, 'CPU sample/delta mismatch')
  const parents = parentIds(raw.nodes)
  const weights = sampleWeights(raw)
  const attribution = attribute(
    raw.nodes.map((node) => ({
      frame: attributionFrame(node.callFrame, bundle),
      id: node.id,
      parent: parents.get(node.id),
      weight: weights.get(node.id)!,
    })),
  )
  const gcTimeUs = raw.nodes.reduce(
    (total, node) =>
      total + (node.callFrame.functionName === '(garbage collector)' ? weights.get(node.id)! : 0),
    0,
  )
  return { attribution, gcTimeUs, totalTime: attribution.coverage.total }
}

export function parseHeapProfile(profilePath: string, bundle: BundleMap) {
  const raw = JSON.parse(readFileSync(profilePath, 'utf8')) as HeapProfile
  const nodes: WeightedNode[] = []
  const visit = (node: HeapProfileNode, parent?: number): void => {
    nodes.push({
      frame: attributionFrame(node.callFrame, bundle),
      id: node.id,
      parent,
      weight: node.selfSize,
    })
    for (const child of node.children) visit(child, node.id)
  }
  visit(raw.head)
  return attribute(nodes)
}

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
