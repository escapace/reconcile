// The maintainer CLI: `pnpm check` asks whether a change is correct and `pnpm bench` whether it
// is faster or smaller. `pnpm check --help` and `pnpm bench --help` list their commands.
import { bench } from './bench/bench'
import { check } from './check/check'
import { main } from './framework/command'
import { finish, handleInterrupts } from './framework/interrupt'

handleInterrupts()
finish(await main([check, bench], process.argv.slice(2)))
