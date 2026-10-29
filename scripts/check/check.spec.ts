import { mkdtempSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { describe, expect, it, vi } from 'vitest'

process.env.RECONCILE_STATE = mkdtempSync(path.join(tmpdir(), 'reconcile-check-spec-'))
const { main } = await import('../framework/command')
const { inputs } = await import('../framework/fingerprint')
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

describe('pnpm check', () => {
  it('refuses an unknown round, and mutant names or seeds for any round but mutants', async () => {
    const unknown = await cli('nothing')
    expect(unknown.code).toBe(2)
    expect(unknown.stderr).toContain('the rounds are static, test, lib, temporal, lean, mutants')
    expect((await cli('lean', 'some-mutant')).stderr).toContain(
      'only the mutants round takes names',
    )
    expect((await cli('static', '--seeds', '10')).stderr).toContain('--seeds applies only')
    expect((await cli('mutants', '--seeds', '0')).stderr).toContain('positive integer')
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

  it('records no pass for a narrowed mutants run', async () => {
    expect((await cli('mutants', 'some-mutant', '--plan')).stdout).toContain('narrowed run')
    expect((await cli('mutants', '--seeds', '10', '--plan')).stdout).toContain('narrowed run')
    expect((await cli('mutants', '--seeds', '1500', '--plan')).stdout).not.toContain('narrowed run')
  })
})
