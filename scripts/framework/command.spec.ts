import { afterEach, describe, expect, it, vi } from 'vitest'
import { help, main, type Command } from './command'

const ran: Array<Record<string, unknown>> = []

const sub: Command = {
  examples: ['pnpm tool run --size 3'],
  name: 'run',
  options: { size: { default: '1', description: 'How many.', placeholder: '<n>', type: 'string' } },
  retired: { '--count': 'use --size' },
  summary: 'Runs it.',
  usage: '[options]',
  async run({ positionals, values }) {
    ran.push({ positionals, values })
    return await Promise.resolve(0)
  },
}

const tool: Command = { commands: [sub], name: 'tool', summary: 'A tool.', usage: '<command>' }

/** Runs the CLI and returns its exit code with what it wrote. */
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
  const code = await main([tool], argv)
  vi.restoreAllMocks()
  return { code, stderr, stdout }
}

afterEach(() => {
  ran.length = 0
})

describe('help', () => {
  it('leads with the summary, usage and examples, then the options with their defaults', () => {
    const text = help('pnpm tool run', sub)
    expect(text.indexOf('Runs it.')).toBe(0)
    expect(text.indexOf('Usage: pnpm tool run [options]')).toBeLessThan(text.indexOf('Examples:'))
    expect(text.indexOf('Examples:')).toBeLessThan(text.indexOf('Options:'))
    expect(text).toContain('--size <n>')
    expect(text).toContain('Default: 1.')
    expect(text).toContain('-h, --help')
  })
})

describe('main', () => {
  it('runs a subcommand with its parsed options', async () => {
    expect((await cli('tool', 'run', '--size', '3', 'x')).code).toBe(0)
    expect(ran).toEqual([{ positionals: ['x'], values: { size: '3' } }])
  })

  it('prints help for a group, `help <command>` and `--help` without running anything', async () => {
    expect((await cli('tool')).stdout).toContain('Commands:')
    expect((await cli('tool', 'help', 'run')).stdout).toContain('Runs it.')
    expect((await cli('tool', 'run', '--help')).stdout).toContain('Runs it.')
    expect(ran).toEqual([])
  })

  it('exits 2 for an unknown command, an unknown flag or a retired one, naming the fix', async () => {
    expect((await cli('nothing')).code).toBe(2)
    const unknown = await cli('tool', 'walk')
    expect(unknown.code).toBe(2)
    expect(unknown.stderr).toContain('the commands are run')
    expect((await cli('tool', 'run', '--sise', '3')).code).toBe(2)
    const retired = await cli('tool', 'run', '--count=3')
    expect(retired.code).toBe(2)
    expect(retired.stderr).toContain('--count no longer exists: use --size')
    expect(retired.stderr).toContain('Run "pnpm tool run --help"')
    expect(ran).toEqual([])
  })
})
