# Native collection reconstruction repair

Release review found that a native Map or Set iterator can revisit an item when a
descendant getter deletes and reinserts it. The encoder correctly captured every
visit, but the decoder rejected the repeated resolved key or member. This made
`parse(stringify(value))` fail for otherwise supported input. Overridden collection
iterators can expose the same issue.

The authorized repair removes only the two duplicate-membership guards in
`src/serialization/facets/collection.ts`. Every token is still decoded in order,
including an overwritten Map value. Native `Map.set` and `Set.add` retain first
insertion order, last Map values and one Set member, matching existing snapshot
semantics. Token grammar, layout A, capture observations, IteratorClose, native
allocation, and the core graph operations are unchanged. Repeated collection rows
are intentionally accepted now.

The source and accepted consumer bundle were frozen before the runtime edit. The
counted-work consequence is one fewer native `has` call and conditional per Map
pair or Set member, with no new allocation or encoder work. This is not a measured
performance claim. The requested performance comparison is separate from correctness
validation.

## Proof and regression evidence

The [scoped collection proof](../../lean/Serialization/COLLECTION.md) was compiled
warning-free before production was edited. Its first successful complete proof
round took 13.669 seconds. All existing theorem statements remain unchanged. The
separate native bridge compares actual production facets with the finite oracle,
including ordered partial results, every read prefix and exception identity.

The new public regressions cover native iterator revisits, custom duplicate
iterators, SameValueZero, aliases/cycles/distinct equal objects, malformed repeated
and overwritten values, bigint key normalization and abrupt cleanup. Before the
repair, the initial regression suite had six expected failures at duplicate guards;
typecheck passed. The earlier URL ownership test was separately corrected to
actually cover both discovery orders and passed source/built tests.

Standard built-ins and prototypes remain a documented native correspondence
boundary. This repair does not change prototype setter behavior or inherited
`toJSON` handling.

## Final validation

The complete gate passed in **263.572 seconds**, including descendant shutdown,
under its 295-second budget. It covered typecheck, package build, 1,447 passing
source tests (with the retained one expected failure and 39 skips), 21 built-codec
tests, Fallow, scoped ESLint, filename lint, formatting checks, full Lean build and
all runtime bridges. Scoped ESLint had zero errors and one existing missing-message
warning in the legacy-token test.

The axiom audit checked 7,240 declarations across 91 modules with standard axioms
only. The new bridge passed 430 success/error traces. The existing serialization
bridge retained its 99 graphs, eight malformed documents and scalar checks; all
native ownership and Temporal checks also passed. The package and minified consumer
each passed 205 independent A-wire checks.

The browser-target combined consumer is 12,870 minified bytes and 4,972 gzip bytes
(level 9), compared with accepted A's 12,939 and 4,998 bytes. Rebuilding the baseline
with the same esbuild 0.28.2 package-consumer options first reproduced its exact
accepted SHA-256. The repaired consumer SHA-256 is
`09ffefd239e243f3e8662b7858b6ed331187088830a21659cfe69de5e2735940`.

See the [complete gate receipt](validation/collection-fold-validation.json),
[proof-first receipt](validation/collection-fold-proof.json),
[consumer correspondence](validation/collection-fold-bundle.json) and
[validated input hashes](validation/collection-fold-inputs.json). Historical
adoption and measurement records describe their original source; they are not
evidence that this repaired bundle is byte-identical or universally
performance-neutral. Correctness validation makes no latency claim.
