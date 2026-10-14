import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import type { SourceMap } from 'node:module'
import path from 'node:path'
import {
  attribute,
  type AttributionFrame,
  type WeightedFrame,
  type WeightedNode,
} from './profile-attribution'

/** A bundle, its source map and the source root that mapped frames are reported against. */
export interface BundleMap {
  readonly bundlePath: string
  readonly root: string
  readonly sourceMap: SourceMap
}

export interface FrameAggregate {
  functionName: string
  inclusiveTime: number
  location: string
  selfTime: number
}

export interface AllocAggregate {
  allocatedBytes: number
  functionName: string
  inclusiveBytes: number
  location: string
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

/** Keys project-source frames by function and location. */
function projectFrames<T>(
  attribution: { readonly frames: readonly WeightedFrame[] },
  aggregate: (frame: WeightedFrame) => T,
): Map<string, T> {
  const frames = new Map<string, T>()
  for (const frame of attribution.frames)
    if (frame.scope === 'project')
      frames.set(`${frame.functionName}|${frame.location}`, aggregate(frame))
  return frames
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
  const frames = projectFrames(attribution, (frame): FrameAggregate => ({
    functionName: frame.functionName,
    inclusiveTime: frame.inclusive,
    location: frame.location,
    selfTime: frame.self,
  }))
  const gcTimeUs = raw.nodes.reduce(
    (total, node) =>
      total + (node.callFrame.functionName === '(garbage collector)' ? weights.get(node.id)! : 0),
    0,
  )
  return { attribution, frames, gcTimeUs, totalTime: attribution.coverage.total }
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
  const attribution = attribute(nodes)
  const frames = projectFrames(attribution, (frame): AllocAggregate => ({
    allocatedBytes: frame.self,
    functionName: frame.functionName,
    inclusiveBytes: frame.inclusive,
    location: frame.location,
  }))
  return { attribution, frames }
}
