import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import ts from 'typescript'
import { deferredOrderCases } from './deferred-order-cases'
import type { Oracle } from './lean-oracle'

export async function checkDeferredOrderRuntime(oracle: Oracle): Promise<void> {
  const parent = resolve('node_modules/.cache')
  mkdirSync(parent, { recursive: true })
  const temporary = mkdtempSync(join(parent, 'deferred-order-'))
  const moduleUrl = (file: string): string => JSON.stringify(pathToFileURL(resolve(file)).href)
  try {
    const execute = (path: string, label: string): unknown => {
      let source = readFileSync(path, 'utf8')
      const replace = (before: string, after: string): void => {
        assert.equal(source.split(before).length, 2, `Cursor instrumentation: ${before}`)
        source = source.replace(before, after)
      }
      replace("'../../object-property'", moduleUrl('src/object-property.ts'))
      replace("'../../graph/edge'", moduleUrl('src/graph/edge.ts'))
      replace("'../../types'", moduleUrl('src/types.ts'))
      replace("'../../standard-prototypes'", moduleUrl('src/standard-prototypes.ts'))
      replace("'../../constants'", moduleUrl('src/constants.ts'))
      replace(
        '  const previous = surface.keys(current, node)',
        '  const previous = surface.keys(current, node);globalThis.__cursor.start(previous,desiredKeys,surface.ordered)',
      )
      const checkpoint = '    const retained = order?.through(previous, key)'
      replace(checkpoint, `${checkpoint};globalThis.__cursor.fixed(order,retained,key)`)
      replace(
        '  if (order !== undefined) return order.retained === desiredKeys.length',
        '  globalThis.__cursor.final(order);if (order !== undefined) return order.retained === desiredKeys.length',
      )
      const compiled = ts.transpileModule(source, {
        compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ESNext },
        fileName: 'property-publication.ts',
        reportDiagnostics: true,
      })
      assert.deepEqual(compiled.diagnostics, [])
      writeFileSync(join(temporary, `${label}.mjs`), compiled.outputText)
      writeFileSync(
        join(temporary, `${label}-run.mjs`),
        `
import assert from 'node:assert/strict';
import {canPublishProperties} from './${label}.mjs';
import {deferredOrderCases,deferredKeys} from ${moduleUrl('scripts/deferred-order-cases.ts')};
const traces=[];let current;
const key=k=>{if(k==='length')return[1,6];const id=deferredKeys.indexOf(k);assert(id>=0);return[id<2?0:id<4?1:2,id]};
globalThis.__cursor={
 start(previous,desired,ordered){current={previous:[...previous],desired:[...desired],ordered,demands:[],finals:[],observations:[]}},
 fixed(order,kept,key){current.demands.push(current.previous.indexOf(key)+1);current.finals.push(false);current.observations.push(order==null?null:[order.retained,kept])},
 final(order){current.demands.push(current.previous.length);current.finals.push(true);current.observations.push(order===undefined?null:[order.retained,null])}
};
deferredOrderCases(input=>{
 current=undefined;let result,error;
 try{result=canPublishProperties(input.node,input.current,input.surface,[])}catch(caught){error=caught}
 assert.equal(error,input.failure,input.name);assert.ok(current,input.name);
 traces.push({name:input.name,input:{previous:current.previous.map(key),desired:current.desired.map(key),ordered:current.ordered,demands:current.demands,finals:current.finals},observations:current.observations,events:input.events,result:result??null,error:error!==undefined});
});
process.stdout.write(JSON.stringify(traces));
`,
      )
      return JSON.parse(
        execFileSync(process.execPath, ['--import', 'tsx', join(temporary, `${label}-run.mjs`)], {
          encoding: 'utf8',
          maxBuffer: 16 * 1024 * 1024,
          timeout: 120_000,
        }),
      ) as unknown
    }
    const raw = execute('src/types/shared/property-publication.ts', 'current')
    assert.ok(Array.isArray(raw))
    const names: string[] = []
    deferredOrderCases(({ name }) => names.push(name))
    const rows = raw.map((value: unknown) => {
      assert.ok(value !== null && typeof value === 'object')
      const row = value as Record<string, unknown>
      assert.ok(typeof row.name === 'string')
      assert.ok(row.input !== null && typeof row.input === 'object')
      assert.ok(Array.isArray(row.observations) && Array.isArray(row.events))
      assert.ok(typeof row.error === 'boolean')
      return row
    })
    assert.deepEqual(
      rows.map((row) => row.name),
      names,
    )
    const expected: unknown = JSON.parse(
      await oracle('DeferredOrder', [], {
        input: JSON.stringify(rows.map((row) => row.input)),
        maxBuffer: 16 * 1024 * 1024,
      }),
    )
    assert.deepEqual(
      rows.map((row) => row.observations),
      expected,
    )
    console.log(
      `Deferred-order bridge: ${rows.length} actual preflights, ${rows.reduce((sum, row) => sum + (row.observations as unknown[]).length, 0)} demanded checkpoints, ${rows.filter((row) => row.error === true).length} original error identities.`,
    )
  } finally {
    rmSync(temporary, { force: true, recursive: true })
  }
}
