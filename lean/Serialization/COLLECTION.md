# Native collection sequence reconstruction

The encoder preserves the ordered iterator-yield sequence. A native Map or Set
iterator can revisit an element deleted and reinserted during a descendant getter.
Overridden collection iterators can also yield repeated entries. The codec must
still traverse every yielded child in its original order. The decoder now folds
that captured sequence through native `Map.set` / `Set.add`, matching the core
snapshot writer and collection publication normalization: first insertion position,
last Map value, and one Set member.

This deliberately broadens accepted transport rows to include repeated resolved
Map keys and Set members. It does not change token grammar, encoder capture,
iterator stepping/closing, or core snapshot/reconcile/produce. A Map value is
always parsed even when a later entry will overwrite it. No validation pass or
collection tracking structure is added to production.

## Checked finite scope

`Collection.lean` uses canonical **resolved key identities**, not wire-token
syntax. `put` updates the first existing pair in place or appends a new pair.
`remember` preserves the first occurrence of a key. The checked statements are:

- `keys_put` / `first_insertion_order`: Map key order equals first-occurrence order.
- `lookup_put` / `last_value`: lookup returns the last supplied value for that key,
  or the initial lookup result when no entry targets it.
- `fold_unique`, `set_unique`: reconstruction from an empty collection has no
  duplicate keys/members.
- `remember_existing`: an existing Set member does not move or duplicate.
- `map_reads_every_occurrence`, `set_reads_every_occurrence`: the complete attempted
  read trace and first read failure equal an independent left-to-right validation
  traversal, irrespective of the accumulated collection contents. This is a
  specification comparison, not a runtime prevalidation pass.
- `successful_map_fold`, `successful_set_fold`: when reads succeed, the inline
  read-and-update decoder equals the ordered finite fold and records every read.

Executable witnesses distinguish first-value retention, moving repeated keys to
the end, rejecting repeats, raw signed-zero equality, and skipping a malformed
value that is followed by another occurrence of its key. Failure results also
retain the already constructed prefix collection, which the native bridge checks.

The proof was compiled with warnings treated as errors before removing either
production duplicate guard. All theorem statements in other modules are retained.

## Actual-facet bridge

`CollectionOracle.lean` adds the separate `SerializationCollection` oracle family.
It runs the proved inline decoders with finite token indexes, resolved-value codes
and an optional failed-read position. It does not enlarge `Serialization.Oracle`'s
historical object/array domain or its narrower bigint lexical model.

`scripts/check-serialization-collection-runtime.ts` invokes the actual production
collection `allocate` and `fill` functions. Its instrumented `context.read` records
every attempted token and can throw a unique sentinel at each occurrence. It
compares the native ordered result, partial result on error, complete read prefix
and original exception identity against the Lean oracle. Successful and failed
prefixes cover undefined, null, booleans, NaN, signed zero, infinities, positive and
negative numbers, bigint, strings, two distinct equal objects, aliases and the
actual destination collection itself.

The bridge has separate value codes for -0 and +0, merges them only for keys, and
checks that a Map **value** can remain -0. Object codes 14 and 15 are fresh distinct
objects and code 16 is the collection being filled; repeated codes resolve to the
same object. This exercises native SameValueZero and self-reference without
assuming equal-looking objects have the same identity.

## Native correspondence and limits

- Native Map/Set implement SameValueZero key equality, canonicalize signed-zero
  keys and preserve first insertion order on updating an existing key/member.
  These are explicit ECMAScript premises, exercised by the bridge rather than
  proved in Lean. See [Map.set](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-map.prototype.set),
  [Set.add](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-set.prototype.add),
  [Map iteration](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-createmapiterator)
  and [Set iteration](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-createsetiterator).
- Token decoding supplies resolved values and stable object identities. Native
  allocation freshness, intended URL-owner aliases, JSON parsing and scalar/BigInt
  grammar remain their existing runtime/proof obligations. Do not compare fresh
  wire arrays or textual bigint spellings as collection identities.
- The finite reader is deterministic over a private parsed transport tree and
  an already allocated identity table. Public tests additionally exercise actual
  parse/stringify, dynamic native iterator revisits, getter traces, malformed
  overwritten values, native error propagation and IteratorClose.
- Native insertion is represented as a total finite update. Allocation/resource
  failures, tampered constructors/prototypes and property-get side effects are
  outside that theorem. Production keeps the original `target.set(key,
context.read(valueToken))` and `target.add(child)` expressions; it removes only
  the duplicate-membership guards. It does not move native method lookup or value
  reading. Previously rejected duplicate rows intentionally have a different
  success/error boundary; an invalid value on such a row must now be read and
  rejected at that read.
- The bridge uses a handwritten finite-code projection, not extraction of the
  TypeScript parser into Lean. It checks actual facet behavior but does not prove
  whole-JavaScript correctness, unbounded mutation termination or performance.

Static production cost change is one fewer native `has` call and conditional per
Map pair / Set member, with no added allocation. This is not a measured speed
claim. Encoder canonicalization instead would require per-collection identity
tracking and still capture every occurrence; it was not selected.
