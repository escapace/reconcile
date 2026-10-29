import { mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterAll, describe, expect, it, vi } from 'vitest'

const state = mkdtempSync(path.join(tmpdir(), 'reconcile-check-spec-'))
process.env.RECONCILE_STATE = state
const { main } = await import('../framework/command')
const { inputs } = await import('../framework/tree')
const { check } = await import('./check')
const { recordPass } = await import('./passes')
const { ROUNDS } = await import('./rounds')

/** Runs `pnpm check` with `argv` and returns its exit code with what it wrote. */
async function cli(...argv: string[]): Promise<{ code: number; stderr: string; stdout: string }> {
  let stdout = ''
  let stderr = ''
  vi.spyOn(process.stdout, 'write').mockImplementation((text) => {
    stdout += String(text)
    return true
  })
  vi.spyOn(process.stderr, 'write').mockImplementation((text) => {
    stderr += String(text)
    return true
  })
  try {
    return { code: await main([check], ['check', ...argv]), stderr, stdout }
  } finally {
    vi.restoreAllMocks()
  }
}

afterAll(() => {
  rmSync(state, { force: true, recursive: true })
})

describe('pnpm check', () => {
  it('refuses an unknown round, and names or narrowing options a round does not take', async () => {
    const unknown = await cli('nothing')
    expect(unknown.code).toBe(2)
    expect(unknown.stderr).toContain('the rounds are static, test, lib, temporal, lean, mutants')
    const refusals: Array<[string[], string]> = [
      [['lean', 'no-such-bridge'], 'unknown bridges: no-such-bridge'],
      [['static', '--seeds', '10'], 'only the lean and mutants rounds take'],
      [['--dump'], 'only the lean and mutants rounds take'],
      [['mutants', '--seeds', '0'], '--seeds takes seeds and ranges'],
      [['mutants', 'no-such-mutant'], 'unknown mutants: no-such-mutant'],
      [['mutants', '--batch', 'reconcile'], 'mutant names and --seeds only'],
      [['lean', '--batch', 'reconcile'], 'narrow one bridge that has batches'],
      [['lean', 'captured', '--seeds', '1'], 'narrow one bridge that has batches'],
      [['lean', 'spec', '--batch', 'nothing'], 'spec has no batch "nothing"'],
      [['lean', 'spec-phases', '--features'], 'spec-phases takes no --features'],
      [['lean', 'spec', '--dump'], '--dump needs --seeds'],
    ]
    for (const [argv, message] of refusals) {
      const refused = await cli(...argv)
      expect(refused.code).toBe(2)
      expect(refused.stderr).toContain(message)
    }
  })

  it('prints its help for `help` as for `--help`', async () => {
    const help = await cli('help')
    expect(help.code).toBe(0)
    expect(help.stdout).toContain('Rounds:')
    expect(help.stdout).toContain('lean spec-phases       --batch plain, hazards, binary')
  })

  it('plans to run every round without a recorded pass, and to reuse one with a pass', async () => {
    const before = await cli('--plan')
    expect(before.code).toBe(0)
    for (const round of ROUNDS)
      expect(before.stdout).toMatch(new RegExp(`${round.name} +run +no pass recorded`))
    recordPass('static', inputs(ROUNDS[0].exclude), 'receipt.json')
    expect((await cli('static', '--plan')).stdout).toMatch(/static +reuse +passed/)
    expect((await cli('static', '--plan', '--fresh')).stdout).toMatch(/static +run +--fresh/)
  })

  it('records no pass for a narrowed run', async () => {
    const narrowed = [
      ['mutants', 'readback-skipped'],
      ['mutants', '--seeds', '1-1500'],
      ['lean', 'spec'],
      ['lean', 'spec', '--batch', 'reconcile-hazards', '--seeds', '10563', '--dump'],
      ['lean', 'spec', '--batch', 'reconcile', '--features'],
    ]
    for (const argv of narrowed)
      expect((await cli(...argv, '--plan')).stdout).toContain('narrowed run')
    expect((await cli('lean', '--plan')).stdout).not.toContain('narrowed run')
  })
})
