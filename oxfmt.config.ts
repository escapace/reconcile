import { defineConfig } from 'oxfmt'

export default defineConfig({
  arrowParens: 'always',
  bracketSameLine: false,
  bracketSpacing: true,
  htmlWhitespaceSensitivity: 'strict',
  // Prettier formatted no TOML, and ESLint keeps its own TOML style.
  ignorePatterns: ['**/*.toml', 'pnpm-lock.yaml'],
  printWidth: 100,
  quoteProps: 'consistent',
  semi: false,
  singleQuote: true,
  sortPackageJson: false,
  tabWidth: 2,
  trailingComma: 'all',
})
