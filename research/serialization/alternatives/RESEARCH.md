# Existing-library adoption findings

Recommendation before shared performance measurements: with performance prioritized above readability, evaluate **devalue 6.0.3 first**, rather than committing to a new codec. It already preserves the most difficult required semantics: object/collection cycles and identities, sparse holes, invalid Dates, special numeric values, BigInt, null prototypes, and binary view identities/offsets/shared backing stores. It is a published codec with a dedicated parser and explicit validation. These are correctness observations, not speed claims.

Versions tested: devalue 6.0.3, flatted 3.4.4, superjson 2.2.6; pinned transitively and exactly by `package-lock.json`. Run `npm ci --ignore-scripts --cache /tmp/reconcile-research-npm`, then `node probe.mjs > probe-results.json`. `adapters.mjs` exports the common `{name,stringify,parse}` array. Tests are small semantic probes; the parent harness supplies fair benchmarks and a common correctness corpus. No benchmarks were run in this subtask.

## Contract comparison

| Property | devalue | flatted | superjson | superjson dedupe |
|---|---|---|---|---|
| JSON.parse accepts encoded text | yes | yes | yes | yes |
| Plain root object remains visible at JSON.parse root | no, table | no, table | under `json` | under `json` |
| Object cycles/shared identity | pass | pass | pass | pass |
| Our Map/Set mutual cycle fixture | pass | loses types | loses back-edge | pass |
| Repeated Date identity | pass | loses type | pass | pass |
| Invalid Date | pass | null | null | null |
| undefined/NaN/infinities/-0/BigInt | pass | BigInt throws | pass | pass |
| Sparse array holes/trailing length | pass | loses holes | loses holes/length | loses holes/length |
| Null prototype | pass | loses | loses | loses |
| Own `__proto__` key | rejects | pass | rejects | rejects |
| Own `constructor` / `prototype` keys | pass | pass | rejects | rejects |
| Shared ArrayBuffer, DataView, typed view and offsets | pass | loses | loses | loses |
| Float64Array NaN/infinities/-0 | pass | loses type | loses values | loses values |
| BigInt64Array | pass | throws | throws | throws |
| Functions and local symbols | rejects | loses | loses | loses |
| Extra enumerable array/Date props | loses | loses | loses | loses |

A pass denotes the explicit predicate in `probe.mjs`, not a universal proof. In particular, these codecs do not promise descriptor/prototype/function closure fidelity. Arbitrary function/local-symbol identity cannot be self-contained portable JSON without an out-of-band registry. Reconcile snapshot handles a wider runtime domain than any portable codec can honestly reproduce. Serializing arbitrary prototypes likewise needs a declared registry, not names guessed from constructors.

Superjson source transforms typed arrays with `[...v]` and reconstructs `new ctor(v)`, so backing buffers and offsets cannot survive. Float special values inside those transformed arrays are not recursively annotated and turn into JSON null/zero. Its constructor whitelist omits BigInt typed arrays and DataView. A custom binary transformer alone cannot fix graph-wide backing-store identity without a coordinated prepass or registry, at which point much of a graph codec is being built anyway.

Flatted's contract explicitly limits it to JSON-compatible data plus references. Rich-type adapters would create a new wire protocol, collision handling, and graph reconstruction on top. That undercuts adopting it to avoid maintaining a codec.

Devalue does not silently support all reconcile objects: it rejects own `__proto__`, enumerable symbol keys, functions, and non-plain unregistered instances; it drops extra properties on specialized builtins/arrays. Node Buffer is deliberately normalized to independent Uint8Array storage for each distinct Buffer, retaining repeated reference identity but not shared pools. Ordinary ArrayBuffer-backed views preserve the entire backing buffer, including bytes outside the visible view. Decide whether Node Buffer belongs to the serialization domain; do not promise its prototype or pool aliasing. Devalue's custom operation hooks can avoid getters or support foreign runtimes, but using them requires its own contract review.

## Raw JSON and interpretation

For `{name:'Ada',count:2}`:

- devalue: `[{"name":1,"count":2},"Ada",2]`
- flatted: `[{"name":"1","count":2},"Ada"]`
- superjson: `{"json":{"name":"Ada","count":2}}`

For `x={name:'Ada'}; x.self=x`:

- devalue: `[{"name":1,"self":0},"Ada"]`
- flatted: `[{"name":"1","self":"0"},"Ada"]`
- superjson: `{"json":{"name":"Ada","self":null},"meta":{"referentialEqualities":[["self"]],"v":1}}`

JSON.parse returns the literal arrays/indices or envelope/null placeholder above; it cannot restore types or cycles. Each library's parse restores the original graph for this fixture. No ordinary JSON document can directly contain a cycle; accepting text and restoring graphs are separate capabilities.

For `{b,u,v,again:u}` with one 16-byte ArrayBuffer, Uint8Array offset 2 length 3, and DataView offset 1 byteLength 5, devalue gives:

```json
[{"b":1,"u":2,"v":3,"again":2},["ArrayBuffer","AQIDBAAAAAAAAAAAAAAAAA=="],["Uint8Array",1,2,3],["DataView",1,1,5]]
```

## Specific SuperJSON failure

```js
const k = {}, m = new Map(), s = new Set();
m.set(k, s); s.add(m);
const x = SuperJSON.parse(SuperJSON.stringify({k,m,s}));
x.m.get(x.k) === x.s; // true
x.s.has(x.m); // false (expected true)
```

Default encoding duplicates a set at `s`; referential-equality restoration patches `m.0.1.0` before replacing `m.0.1` with canonical `s`, losing the patched edge. `new SuperJSON({dedupe:true})` passes this fixture by retaining first occurrence as canonical. This is a reproducible case, not a blanket claim about all collection cycles. No issue or upstream change was published.

## Adoption scope and remaining questions

Devalue explicitly makes human readability AND cross-version format stability non-goals. Human readability is a tradeoff now that performance wins; format stability is a separate product decision. Matched-version transport can simply pin versions. Durable persisted data needs explicit codec/version identification, a compatibility policy and fixtures/migrations; pinning a package alone is not a perpetual compatibility guarantee.

Do not wrap devalue as a full-fidelity clone of reconcile's snapshot API. Either expose a deliberately narrower portable-data domain and reject unsupported inputs before silent property loss, or define additional protocol requirements and accept custom implementation cost. A wrapper validation traversal adds encode cost and should be measured if adopted. If all lawful own keys, array extra properties or extremely deep iterative traversal are mandatory, custom codecs may win on correctness despite devalue's maturity. No framework should be added until those boundaries and the common measurements establish desirability.

Primary sources inspected on 2026-10-15:

- https://github.com/sveltejs/devalue (features, binary policy, explicit non-goals)
- https://github.com/sveltejs/devalue/blob/main/src/stringify.js
- https://github.com/sveltejs/devalue/blob/main/src/parse.js
- https://github.com/sveltejs/devalue/blob/main/src/operations.js
- https://github.com/ravionhq/superjson (current upstream; former flightcontrolhq URL redirects)
- https://github.com/ravionhq/superjson/blob/main/src/transformer.ts
- https://github.com/ravionhq/superjson/blob/main/src/plainer.ts
- https://github.com/WebReflection/flatted (JSON-only contract, table representation)

Published-package sources under `node_modules` and the lockfile are the exact evidence for executable results; moving upstream branches can later differ.
