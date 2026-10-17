# Prior art for the graph-preserving JSON codec: engine source, specifications and papers

Review date: 2026-10-17. Codec source read at `b629990` (`src/serialization/`). No files in the
repository were changed and no benchmarks were run. Engine claims come from V8 source as shipped
in **Node v24.22.0 (V8 13.6.233.17)**, the measured runtime, unless stated otherwise. I compared it
with V8 `main` and the V8 copies in Node 25.0.0 (V8 14.1) and 26.0.0 (V8 14.6). Blog posts are
marked _(blog)_. "Analogy" means the source's assumptions do not hold here, so the source can
suggest a direction but supplies no evidence.

Link prefixes used below:

- `N24` = `https://github.com/nodejs/node/blob/v24.22.0/deps/v8/`
- `V8M` = `https://github.com/v8/v8/blob/main/` (mirror of chromium.googlesource.com/v8/v8, read 2026-10-17)

---

## 0. Findings that change how the measurements should be read

1. **The Node 24 measurements did not use the new JSON.stringify fast path.** In V8 13.6, as
   bundled with Node 24.22.0, `json_stringify_fast_path` defaults to **false**
   (`N24src/flags/flag-definitions.h#L758`: `DEFINE_BOOL(json_stringify_fast_path, false, ...)`,
   enabled only through `--future`). Node 25.0.0 (V8 14.1) and Node 26.0.0 (V8 14.6) default it
   to **true**, and so does V8 main (`V8Msrc/flags/flag-definitions.h`, around line 881). The
   "9–28% native share" was therefore measured on the old recursive `JsonStringifier`. On
   Node ≥ 25 and Chrome ≥ 138, the native share for the same transport tree should be smaller,
   so JS capture becomes an even larger fraction. The fast path can be tested on Node 24 with
   `node --json-stringify-fast-path`.
2. **On the new fast path, one cons-string or sliced-string value anywhere in the document
   restarts serialization from the beginning on the slow path.**
   `FastJsonStringifier::TrySerializeSimpleObject` lists only sequential, external, thin and
   internalized string types. `CONS_*` and `SLICED_*` strings reach `default: return SLOW_PATH`
   (`N24src/json/json-stringifier.cc#L2517-L2595`; the same in V8M). `FastJsonStringify` then runs
   a fresh `JsonStringifier` from the root (`#L3531`: `// TODO(pthier): Resume instead of
restarting.`). The v8.dev post says the same ("Strings like ConsString may need flattening ...
   fall back to the slower path") _(blog, https://v8.dev/blog/json-stringify, 2025-08-04)_. User
   strings built with `+`, template literals, `slice` or `substring` are often ropes or slices.
   Benchmark fixtures built from literals therefore measure a different path from real inputs.
3. **The rows built in JS do not fall off the fast path.** `[root, shapes, nodes]` contains only
   arrays, Smis, HeapNumbers, `true`, `false`, `null` and strings. Holey arrays stay on the fast
   path while the `NoElements` protector is intact (`SerializeJSArray`, `#L2899`). `JSON.rawJSON`
   values do **not** stay on it: `JS_RAW_JSON_TYPE` reaches `default: SLOW_PATH` in the fast
   path.
4. **Execution-history sensitivity has a source-level explanation.** V8 keeps at most one
   `FeedbackCell` per function literal per native context (`N24src/objects/feedback-cell.h`, header
   comment). The inner closures that `encodeGraph`/`decodeGraph` create on each call (`token`,
   `objectToken`, `read`) therefore share one feedback vector across calls and fixtures.
   Polymorphic inline caches hold at most 4 maps (`DEFAULT_MAX_POLYMORPHIC_MAP_COUNT 4`,
   `N24src/flags/flag-definitions.h#L2681`). Beyond that, access goes megamorphic and uses the
   global stub cache, which has 2^11 primary and 2^9 secondary entries
   (`N24src/ic/stub-cache.h#L88-L91`). TurboFan inlines at most 4 call targets per site
   (`kMaxCallPolymorphism = 4`, `N24src/compiler/js-inlining-heuristic.h#L66`). See §1.6 for how the
   `Frame` objects exceed these limits.
5. **The `hasBuffers` encode path returns a rope.** `'[' + ... + ',[' + parts.join(',') + ']]'`
   produces a `ConsString`. The result is flattened, with a full-length copy, only when it is
   first consumed (§1.4). This is the "return-only gains disappeared once the string was
   consumed" effect: return-only timing omits the flatten. Measurements should consume the whole
   string.
6. **Side finding (robustness, not speed): the decoder can be made to allocate a large array
   from a few bytes of input.** `sparseArray.allocate` runs `new Array(length)` with `length`
   taken from the wire. In V8 13.6, setting a length on an array with no backing store presizes
   the store to exactly that length (`N24src/objects/elements.cc#L864`: "assume we are setting
   the length to presize"). Only lengths above `kMaxFastArrayLength` = 32 Mi
   (`N24src/objects/js-array.h#L136`) switch to dictionary elements. A 20-byte row
   `[3,33554432]` therefore allocates about 128 MiB of holes. devalue 6.x fixed the same problem
   by forcing dictionary mode before setting the length (`src/operations.js`,
   `createSparseArray`; CHANGELOG "fix: force sparse arrays to allocate sparsely", 206ca67).
   Dense rows are not affected, because the arity check ties their length to the size of the
   input.

---

## 1. V8 internals

### 1.1 JSON.stringify

| Item                                      | Source                                                                                                                                                                                 | Mechanism and preconditions                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Applicability                                                                                                                                                                                    |
| ----------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Fast-path gate                            | `N24src/json/json-stringifier.cc#L3466-L3555` (`CanUseFastStringifier`, `FastJsonStringify`)                                                                                           | Used only when the flag is on **and** `replacer` and `space` are both undefined. Two templated stringifiers (one-byte and two-byte). The first two-byte string switches to the two-byte stringifier, which resumes from the saved continuation stack; the two outputs are concatenated.                                                                                                                                                                                                           | The codec calls stringify without a replacer or space, so it qualifies. The flag is off on Node 24 (§0.1).                                                                                       |
| Fall-off conditions                       | Same file: `CanFastSerializeJSObjectFastPath` (#L2314), `CanFastSerializeJSArrayFastPath`, `TrySerializeSimpleObject` (#L2517), `SerializeJSPrimitiveWrapper`                          | Objects need fast properties, no elements (`empty_fixed_array` or empty dictionary), no "interesting properties" (`toJSON`) on the map, and the initial prototype from the same native context. Arrays need the initial `Array.prototype`. Holey kinds need the `NoElements` protector. Accessors (`location() != kField`) fall back. Cons and sliced strings, BigInt (inside wrappers), raw JSON and any other instance type fall back. **Every fall-off restarts the whole document** (#L3531). | The codec's transport tree is arrays of primitives and flat strings, so it stays on the fast path unless a user string is a rope or a slice (§0.2).                                              |
| Per-call map cache                        | `map_cache_(&zone_)` (#L2339) and `ResumeJSObject<kWithMapCache>`                                                                                                                      | The first time a hidden class is seen in a call, its keys are checked for escaping and its symbols and non-enumerable properties are recorded. Later objects with the same map copy their keys without checks. V8 main moved this to a persistent bit on the map ("fast-json-iterable") _(blog)_.                                                                                                                                                                                                 | Not used by this wire, which has no JSON objects. It is relevant only if records are emitted as JSON objects (D2, §4). It is also an engine example of per-call interning keyed by hidden class. |
| Old (Node 24) stringifier                 | `JsonStringifier::Serialize_` (#L924ff), `SerializeJSArray` (#L1113), `SerializeFixedArrayWithPossibleTransitions`                                                                     | Recursive. Every value gets a `StackLimitCheck` and interrupt check. `PACKED_ELEMENTS` arrays create a handle per element and re-check `length` and `ElementsKind` on each iteration. Strings are `String::Flatten`ed (#L1714), which allocates for a cons string. Cycle detection is a linear scan, but only after nesting passes 10 or a `toJSON` call is seen (`StackPush`, #L754).                                                                                                            | The wire nests at most four deep, so no cycle scans. The per-element overhead of `PACKED_ELEMENTS` rows dominates the native share on Node 24.                                                   |
| Number formatting                         | Node 24: `base::DoubleToAscii` (Grisu-based, `N24src/numbers/conversions.cc#L944-L967`). Node 25 and later: Dragonbox (`third_party/dragonbox` present in v25.0.0, absent in v24.22.0) | Shortest round-trip conversion of doubles to strings.                                                                                                                                                                                                                                                                                                                                                                                                                                             | Number-heavy arrays, where native stringify is 50–90% of encode time, should get faster on Node ≥ 25 with no codec change.                                                                       |
| SIMD/SWAR escaping, segmented zone buffer | _(blog)_ v8.dev/blog/json-stringify; `AppendStringSIMD` in the N24 source (compiled in but behind the flag)                                                                            | Escape scanning works on whole words or vectors and copies unescaped runs in bulk. The output buffer grows by adding segments instead of reallocating.                                                                                                                                                                                                                                                                                                                                            | Explains why JS-level emitters (rejected designs 1 and 2) lose on strings, and why that gap grows on Node ≥ 25.                                                                                  |

**Per-call overhead of tiny stringify calls.** `JSON.stringify` and `JSON.parse` are C++
builtins (`BUILTIN(JsonStringify)` in `N24src/builtins/builtins-json.cc`), and neither TurboFan
(`js-call-reducer.cc`) nor Maglev (`maglev-graph-builder.cc`) reduces them. Each call therefore
enters C++, opens a handle scope, constructs a stringifier and allocates a result string. The
per-record `JSON.stringify(keys)` in `context.shape` pays this fixed cost for every record. The
result is a fresh string whose hash `Map.get` must compute over the whole signature, and a lookup
hit then compares the full contents. Rejected design 3 (one stringify per node) pays the same
fixed cost for every node.

### 1.2 JSON.parse

- **Parser.** Iterative, with its own continuation stack, since V8 7.6 _(blog, v8.dev/blog/v8-release-76:
  "up to 2.7× faster")_; `N24src/json/json-parser.cc` `ParseJsonValue`.
- **Arrays** (`BuildJsonArray`, `#L1356`). Elements are buffered on `element_stack_` and the
  array is allocated **once at exact length**. Its kind is `PACKED_SMI` if every element is a
  Smi, `PACKED_DOUBLE` if any element is a HeapNumber and there is no other heap object, and
  `PACKED_ELEMENTS` otherwise. Decoded rows are therefore never holey but come in three elements
  kinds. A row like `[2,3,0.5,1]` is a `FixedDoubleArray`, and generic code that reads its
  elements boxes a new HeapNumber on each read.
- **Objects** (`BuildJsonObject`, `JSDataObjectBuilder`). Properties are buffered, the object is
  allocated with exactly that many in-object fields (up to 128), and map _feedback_ is taken
  from the previous object in the same array (`#L1611`, `#L1859`), using
  `TransitionsAccessor::ExpectedTransition` on the raw key bytes. Keys are always internalized.
- **String values** (`#L2248`). A value is internalized only if the source is one-byte and the
  value is **shorter than 10 characters**. Shape key names are array _values_ in this wire, so
  keys of 10 or more characters, and every key in a document containing any non-Latin-1
  character, arrive as non-internalized strings. The first keyed store with such a key
  internalizes it.
- **Applicability.** JSON.parse is 30–90% of decode time. Its cost grows with the number of
  arrays allocated (one JSArray plus one FixedArray per row, and one more per `[-7,x]` or
  `[-6,"…"]` token) and with the text length. The decoder controls neither except through the
  wire format.

### 1.3 Elements kinds, preallocation and dictionary elements

| Fact                                                                                                                                                                                                                                                                                                                                                          | Source                                                                                                      |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| Growth policy: `new_capacity = old + old/2 + 16`. An array literal `[a, b]` has capacity 2, so its first `push` grows it to 19, then to 44, 82 and so on, copying each time.                                                                                                                                                                                  | `NewElementsCapacity`, `N24src/objects/js-objects.h#L652`                                                   |
| `new Array(n)` with `0 < n < kInitialMaxFastElementArray` allocates exactly n elements and transitions to a HOLEY kind. The limit is about 16 K elements: (`kMaxRegularHeapObjectSize` − headers) / 8, and `kMaxRegularHeapObjectSize` is 128 KiB with 256 KiB pages. Larger n takes `SetLength`, which presizes exactly up to `kMaxFastArrayLength` = 32 Mi. | `N24src/objects/elements.cc#L5601`, `#L864`; `js-array.h#L136-L146`; `objects.cc` `SetLengthWouldNormalize` |
| A write past capacity converts to dictionary elements when the gap is ≥ `kMaxGap` = 1024, or when the store would exceed 500 elements (old space) or 5000 (young space) and the dictionary would be smaller.                                                                                                                                                  | `ShouldConvertToSlowElements`, `N24src/objects/js-objects-inl.h#L1057`; `js-objects.h#L931-L939`            |
| Kind transitions go one way only (packed to holey, Smi to double to tagged). A holey array stays holey forever.                                                                                                                                                                                                                                               | _(blog)_ https://v8.dev/blog/elements-kinds                                                                 |

**Applicability.** (a) Encoder rows grow by `push` from a two-element literal, so every record
and collection row pays at least one reallocation, and dense array rows are copied twice: once
into `entries`, then again by `[2, len, ...entries]`. (b) Holey rows are fine for both
stringifiers. On the new fast path, though, they make the whole call depend on the `NoElements`
protector. (c) Decoder output arrays made with `new Array(n)` are holey forever, which slows the
_consumer's_ later accesses. Building them by `push` would keep them packed but cost
reallocations.

### 1.4 Strings: ropes and flattening

- **Cons strings.** `ConsString::kMinLength = 13` and `SlicedString::kMinLength = 13`
  (`N24src/objects/string.h`, around lines 1029 and 1130). A concatenation whose result is at
  least 13 characters long creates a cons string without copying.
- **Flattening.** `String::SlowFlatten` (`N24src/objects/string-inl.h#L714`) allocates a flat
  sequential string of the full length (in old space if the cons string is old), copies both
  halves, then rewrites the cons string as (flat, empty). Every native consumer that needs flat
  characters pays this once: `JSON.parse`, the old stringifier, `TextEncoder`, and so on. The new
  JSON fast path does not flatten; it restarts on the slow path (§0.2).
- **`Array.prototype.join`.** The Torque `BufferJoin` (`N24src/builtins/array-join.tq#L287`)
  sums the string lengths, allocates **one** flat one-byte or two-byte string and copies into
  it. It produces flat output with no rope.
- **Applicability.** Building the document with `+=` or `+` defers the copy to the consumer
  (rejected design 3, and §0.5). `parts.join(',')` is the right primitive for one final
  assembly, but the `'[' + … + ']'` wrapping around it puts a rope back on top.

### 1.5 Identity memo: `Map<object, number>`

- **Hash storage.** The identity hash is stored in the object's `properties_or_hash` slot. It
  is a Smi when the object has no out-of-line properties, and otherwise lives in the
  `PropertyArray` or dictionary header. Creating it allocates no new object
  (`SetHashAndUpdateProperties`, `JSReceiver::SetIdentityHash`,
  `N24src/objects/js-objects.cc#L745-L816`). The first hash of an object is randomly generated and
  then persists, so later calls reuse it.
- **Table growth** (`OrderedHashTable::EnsureCapacityForAdding`,
  `N24src/objects/ordered-hash-table.cc#L77`). Capacity starts at 4, a full table **doubles**, and
  every growth allocates a new table and rehashes all entries. Each entry is 3 tagged words (key,
  value, chain), plus one bucket per two entries.
- **JIT treatment.** `Map.prototype.get` and `has` are inlined by TurboFan (`js-call-reducer.cc`
  around line 5040) and by Maglev (`TryReduceMapPrototypeGet`, around line 9599). `Map.prototype.set`
  is not reduced by either, so it always calls the CSA builtin.
- **V8 ValueSerializer.** Uses an address-keyed `IdentityMap` allocated in a zone
  (`N24src/objects/value-serializer.cc#L300`) with `FindOrInsert`, one probe per object (`#L584`).
  JS code has no equivalent. The closest it can get is to avoid a second probe, but `Map` has no
  get-or-insert in all target engines (TC39 "upsert" is not universally shipped, so it fails the
  portability constraint).
- **Applicability.** The memo costs a `get` miss plus a `set` per new object and one `get` per
  repeat. No portable mechanism found reduces this. `WeakMap` uses an ephemeron table, which adds
  GC work, so it is not a candidate.

### 1.6 Property access, shapes and the `Frame` objects

- **Literal sizing.** An object literal with _n_ properties gets a map with _n_ in-object fields
  (`Factory::ObjectLiteralMapFromCache` and `Map::Create`, `N24src/heap/factory.cc` around line
  4069). The empty literal `{}` uses the Object function's initial map, which has 4 in-object
  fields (`kInitialGlobalObjectUnusedPropertiesCount = 4`, `js-objects.h#L943`;
  `init/bootstrapper.cc` around line 911). Further properties go to an out-of-line `PropertyArray`
  that grows by `kFieldsAdded = 3` (`js-objects.h#L954`), reallocating each time.
- **Codec observation (from reading `encode.ts` and `frames.ts`).** Every `Frame` starts as the
  same 6-property literal `{detail,id,input,phase,tag,value}`. Each kind then adds different
  fields in a different order:
  - record: `keys`, `row`, `index`, `child`
  - array: `length`, `index`, `count`, `dense`, `entries`, `child`, `row`
  - Map: `row`, `iterator`, `next`, `active`, `child`, `mapValue`
  - Set, view and URL: further variants

  Each order is a separate transition chain, so a mixed graph creates at least five frame maps.
  `row`, `child` and `input` sit at **different offsets** in each map, out of line, behind
  `PropertyArray` growth. The driver loop's `frame.tag`, `frame.row`, `frame.child` and
  `frame.input` accesses then exceed the 4-map polymorphic limit, become megamorphic, and stay
  that way for the life of the process because feedback is shared (§0.4). `advances[frame.tag](…)`
  is likewise an indirect call site with up to 6 distinct targets, above the inlining limit of 4.

- **Kind results.** `recognize()` returns a **fresh object literal** for every object visited,
  in two shapes: `{tag}` and `{detail, tag}`. Escape analysis can remove an allocation only if
  the allocation is inlined into the consumer and does not escape. TurboFan has `--turbo-escape`;
  Maglev has `maglev_escape_analysis` ("avoid inlined allocation of objects that cannot escape",
  `N24src/flags/flag-definitions.h#L1396`). `recognize` calls `nativeKind`, which returns its own
  object, and its two return shapes make `kind.detail` loads polymorphic, so escape analysis
  cannot be relied on.
- **`Reflect.get(o, k)`.** TurboFan lowers the two-argument form to a call to the generic
  `GetProperty` builtin, with **no inline-cache feedback** (`ReduceReflectGet`,
  `N24src/compiler/js-call-reducer.cc#L3396`). Maglev in 13.6 has no `Reflect.get` reduction. The
  builtin (`N24src/builtins/reflect.tq#L64`) runs `GetPropertyWithReceiver`, a full lookup on every
  call. `o[k]` instead uses a `KeyedLoadIC`, which is monomorphic or polymorphic for inline field
  loads and megamorphic for stub-cache handlers. **The two have the same semantics** for an object
  receiver: both perform `o.[[Get]](k, o)`, so proxy `get` traps and getters run with the same
  arguments.
- **`Object.getOwnPropertyNames`** (`N24src/builtins/builtins-object-gen.cc#L748`). When the
  map's enum cache is valid and every own property is enumerable, CSA copies the cached keys into
  a new `PACKED_ELEMENTS` array without a runtime call. Objects with elements, dictionary-mode
  objects and custom receivers such as proxies take the runtime path.
- **`Object.getOwnPropertySymbols`.** A C++ builtin (`builtins-object.cc` around line 293) using
  `KeyAccumulator`. It returns early when `MayHaveSymbols()` is false
  (`N24src/objects/keys.cc#L477`): a fast-mode map whose enum length equals its descriptor count.
  For **dictionary-mode** objects `MayHaveSymbols()` always returns true, so every call does a
  full key collection. Dictionary-mode objects include all `Object.create(null)` objects and
  null-proto literals: `ObjectCreate` uses `slow_object_with_null_prototype_map` and a property
  dictionary (`builtins-object-gen.cc#L1273`), and so does `runtime-literals.cc#L386`.
- **Per-record cost.** A record therefore costs: `getOwnPropertyNames` (CSA fast path), then
  `JSON.stringify(keys)` (C++ entry), then `Map.get` on a new string, then _k_ calls to
  `Reflect.get` (generic builtin, no inline cache), then `getOwnPropertySymbols` (C++ entry).
  Merging the two key queries into one `Reflect.ownKeys` call would halve the proxy `ownKeys`
  trap calls, which is an observable change and therefore **forbidden**.

### 1.7 Allocation lifetime and pretenuring

- **Allocation mementos.** V8 tracks allocation sites for array and object literals and for
  Array-constructor sites. It decides to pretenure a site once at least `kMinMementoCount = 100`
  mementos exist and the scavenger survival ratio reaches 0.85
  (`N24src/heap/pretenuring-handler.cc#L26-L29`; states in `objects/allocation-site.h#L28-L33`).
- **Applicability.** Encoder rows all stay alive until the final stringify. On large documents
  they survive scavenges and get copied and promoted, which is the case pretenuring targets.
  V8 decides this by itself, with no portable control. Arrays produced by spread or growth may
  not carry the literal's site. This can only be observed with `--trace-pretenuring`, not tuned
  directly (see §4, Clifford et al.).

---

## 2. Structured clone and V8 ValueSerializer

**HTML StructuredSerializeInternal** (https://html.spec.whatwg.org/multipage/structured-data.html):

- Step 2 returns `memory[value]` if it exists. Step 27 sets `memory[value]` _before_ step 28
  serializes children, which is preorder identity assignment, as in this codec.
- Arrays record `[[Length]]` together with their enumerable own properties.
- Objects use `EnumerableOwnProperties` followed by `HasOwnProperty` and `[[Get]]` for each key
  (step 28.4).
- Map and Set **copy** `[[MapData]]`/`[[SetData]]` into a list before serializing children
  (step 28.1/28.2), so they never use the iterator protocol.

**V8 `ValueSerializer`** (`N24src/objects/value-serializer.cc`):

- `WriteJSReceiver` (`#L581`) assigns ids in preorder with one `IdentityMap::FindOrInsert`.
- `WriteJSObject` (`#L683`): for fast-property objects without elements, it walks the map's
  descriptors and reads fields directly with `RawFastPropertyAt` _while the map is unchanged_. It
  falls back to `LookupIterator` and `GetProperty` once a getter has changed the map.
- `WriteJSArray` (`#L747`): an array is dense if `HasFastElements && !HasHoleyElements`, and
  "sparse" otherwise. The choice is made by elements kind, without counting. `PACKED_SMI`,
  `PACKED_DOUBLE` and `PACKED_ELEMENTS` each have an element loop. The `PACKED_ELEMENTS` loop
  re-checks `length` and the elements kind on every element and falls back if a side effect
  changed them.
- `ReadJSObjectProperties` (`#L2538`) builds objects by following existing **map transitions**
  matched on the raw key bytes (`ExpectedTransition`). It buffers the values and commits them all
  at once. Dense arrays are preallocated `HOLEY_ELEMENTS` at their length.

**What transfers to a pure-JS encoder:**

- Preorder ids before children: already done.
- Interning by hidden class: only an approximation is possible in JS, by interning on key
  _sequences_ (§5, E1).
- Building objects via expected transitions: the JS analogues are template cloning (D1) or
  letting JSON.parse build the objects (D2).

**What does not transfer:**

- Direct field reads guarded by "map unchanged" (an engine privilege).
- Address-keyed identity maps.
- Snapshotting Map and Set contents: the codec's observable contract uses the iterator protocol
  and `IteratorClose`, so snapshotting would change the observations.

---

## 3. Other JS graph serializers

| Library (version read)                                            | Traversal / identity                                                                                                                                                                                     | String building                                                                                                                                                                                                                                                                             | Rationale on record                                                                                                                                                                                                                                                                                                                                                                         | Lesson for this codec                                                                                                                                                                                                                                                            |
| ----------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **devalue 6.0.3** (`src/stringify.js`, `parse.js`)                | Recursive `flatten`, `Map` from object to index, preorder ids. Records on the wire are JSON objects (`{"k":idx}`); null-proto records are `["null",k,v,…]`.                                              | Each node becomes a JS string built with `+=` and templates. Node strings go into an array, and the result is `` `[${stringified.join(',')}]` ``. Strings with no escapes are wrapped in quotes after `needs_escape.test(str) && isWellFormed()`; otherwise it calls `JSON.stringify(str)`. | CHANGELOG: "perf: use native JSON.stringify for strings that need escaping, instead of a per-character loop" (5cd712a); "skip per-character escaping for strings with nothing to escape" (6156b2e); "cache quoted property names" (6156b2e, a **persistent module-level cache** of up to 1024 keys, which this codec's rules forbid); "force sparse arrays to allocate sparsely" (206ca67). | Independent confirmation that escaping in JS loses to native. Its decoder lets JSON.parse build record objects, then assigns `object[key] = hydrate(value[key])` with keys from `Object.keys(value)` (`parse.js` around line 300). Its sparse-array DoS fix applies here (§0.6). |
| **flatted 3.4.4** (`esm/index.js`)                                | `Map` from value to index string. A work list of objects.                                                                                                                                                | Calls `JSON.stringify(input[i], replace)` **once per object, with a replacer**, then `'[' + output.join(',') + ']'`.                                                                                                                                                                        | None recorded.                                                                                                                                                                                                                                                                                                                                                                              | The replacer disables the V8 fast path (§1.1). This is the user's rejected design 3 with extra overhead. Do not copy.                                                                                                                                                            |
| **@ungap/structured-clone 1.4.0** (`esm/serialize.js`, `json.js`) | Recursive `pair`. A `Map` keyed by value, **primitives included**, so equal strings and keys are de-duplicated into shared records.                                                                      | Builds `[[TYPE, value], …]` records, then a single `JSON.stringify`.                                                                                                                                                                                                                        | None recorded.                                                                                                                                                                                                                                                                                                                                                                              | The same architecture as this codec: flat records, then one native stringify. It interns individual key strings through Map lookups, where this codec interns whole key _sequences_ (shapes), which takes fewer lookups per record.                                              |
| **seroval 1.6.9** (`dist/dev/index.js`)                           | Two phases: parse the value into a tree of `SerovalNode` objects with reference marking (`markRef`, `getReferenceID`), then serialize the nodes to JS source or JSON.                                    | The serializer concatenates strings and joins arrays.                                                                                                                                                                                                                                       | None found in the package.                                                                                                                                                                                                                                                                                                                                                                  | Also capture, then tree, then emit. No evidence that it beats this codec's single native stringify.                                                                                                                                                                              |
| **superjson 2.2.6** (`dist/plainer.js`)                           | Recursive `walker` with `seenObjects: Map`. Identities are tracked as `Map<object, path[]>`. Allocates `[...path, index]` and `[...objectsInThisPath, object]` **per node**, which is O(depth) per node. | Produces a JSON tree plus path annotations.                                                                                                                                                                                                                                                 | None.                                                                                                                                                                                                                                                                                                                                                                                       | A counterexample: allocations proportional to path length are what to avoid.                                                                                                                                                                                                     |

None of these libraries publishes a mechanism that beats "capture to flat transport tree, then
one native `JSON.stringify`" for graph-shaped data. devalue's measured choices (native escaping,
skipping escapes on clean strings) agree with the user's rejected designs 1 and 2.

---

## 4. Classic and academic work: claim, assumptions, applicability

| Source                                                                                                                                                                                                                 | Claim and mechanism                                                                                                                                                                                                                                                                                                                   | Assumptions                                                                                                                                       | Applicability here                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Wadler, _Deforestation: transforming programs to eliminate trees_, TCS 73(2):231–248, 1990, https://doi.org/10.1016/0304-3975(90)90147-A                                                                               | Composing functions in "treeless form" removes the intermediate trees.                                                                                                                                                                                                                                                                | First-order, pure, total functions transformed by a compiler.                                                                                     | **Analogy.** The consumer here is opaque native C++ (`JSON.stringify`), so no JS transformation can fuse the producer into it. Fusing in JS means writing the consumer in JS, which is rejected designs 1 and 2. Those designs lost because the native consumer's per-byte speed (SIMD escaping, native dtoa, a C++ buffer) outweighs the cost of the intermediate rows. The real lever is to make the intermediate rows **cheaper to produce** while keeping them on the native consumer's fast path.                                                                         |
| Gill, Launchbury & Peyton Jones, _A short cut to deforestation_, FPCA 1993, https://doi.org/10.1145/165180.165214; Coutts, Leshchinskiy & Stewart, _Stream fusion_, ICFP 2007, https://doi.org/10.1145/1291151.1291199 | `foldr`/`build` rewriting, and its stream (unfold) generalization, remove intermediate lists.                                                                                                                                                                                                                                         | Pure code, inlining, and rewrite rules (GHC RULES). The producer and consumer must both be expressible as `build`/`foldr` or `stream`/`unstream`. | **Analogy**, as above. One part transfers: the `entries` array then `[2,len,...entries]` copy _within JS_ is a small producer/consumer pair that can be fused by hand by writing straight into the row (E4).                                                                                                                                                                                                                                                                                                                                                                   |
| Reynolds 1972 (reprinted HOSC 1998, https://doi.org/10.1023/A:1010027404223); Danvy & Nielsen, _Defunctionalization at work_, PPDP 2001, https://doi.org/10.1145/773184.773202                                         | An explicit-stack state machine is the defunctionalized CPS form of the recursive traversal.                                                                                                                                                                                                                                          | Semantic equivalence; nothing about cost.                                                                                                         | The `Frame`/`phase` machine is exactly this, and the Lean `recursive_refines_stack` result states the equivalence. The cost of defunctionalized continuations depends on their _representation_. V8's own new stringifier keeps a `std::vector` of small `ContinuationRecord` **values**. The JS equivalent is a struct-of-arrays stack: parallel arrays of ids, phases and indices instead of one heap object per frame (E6). Generators, the other resumable form, cost about 25% in this repository's own measurement (docs/development.md, "Kept: complexity exceptions"). |
| Filliâtre & Conchon, _Type-safe modular hash-consing_, ML Workshop 2006, https://doi.org/10.1145/1159876.1159880                                                                                                       | Hash each structure once on construction, keep a unique representative, and compare by physical equality from then on.                                                                                                                                                                                                                | Immutable values whose structural equality is the intended identity.                                                                              | **Applies to shapes only.** A shape (a list of key names) is private data, so interning it by content is sound. It does **not** apply to application objects, because AGENTS.md says equal values do not establish shared storage. The paper's point that you hash once and then compare pointers maps onto V8 internalized strings: key names from `getOwnPropertyNames` are internalized and have cached hashes, so a trie of `Map<string, node>` hashes no new string (E1).                                                                                                 |
| Java Object Serialization protocol, https://docs.oracle.com/en/java/javase/21/docs/specs/serialization/protocol.html                                                                                                   | Handles are assigned in sequence from `0x7E0000` (`newHandle`) **before** contents (`TC_OBJECT classDesc newHandle classdata[]`). `TC_REFERENCE` refers back to a handle. A `classDesc` (field names and types) is written once per stream and then referenced by handle.                                                             | One stream, with handles valid until `TC_RESET`.                                                                                                  | Direct analogue: preorder ids with references are this codec's `-(i+6)` tokens, and `classDesc` handles are its `shapes` table. This confirms the design but suggests no new mechanism.                                                                                                                                                                                                                                                                                                                                                                                        |
| Kryo README (https://github.com/EsotericSoftware/kryo, "References")                                                                                                                                                   | Reference tracking is **off by default** because "every object that is read or written needs to be tracked". The default `MapReferenceResolver` uses `IdentityObjectIntMap`, which is "fast and minimizes allocation". A list resolver can be faster for small graphs. Unregistered class names are written once, then as varint ids. | Tracking can be dropped per class where identity does not matter.                                                                                 | In JS every object has observable identity, so this codec cannot drop tracking. A linear-scan resolver for small graphs is only an analogy: JS `Map.get` is already inlined (§1.5).                                                                                                                                                                                                                                                                                                                                                                                            |
| Protocol Buffers (https://protobuf.dev/programming-guides/encoding/)                                                                                                                                                   | Tree-shaped, with no back-references.                                                                                                                                                                                                                                                                                                 | Schema-defined messages.                                                                                                                          | Not applicable to graphs.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| FlatBuffers (`include/flatbuffers/flatbuffer_builder.h`; https://flatbuffers.dev/tutorial/)                                                                                                                            | Children are built before parents, and the buffer is written back to front. **Per buffer, vtables are deduplicated** by a linear scan with `memcmp` over earlier vtables (`dedup_vtables_`). `CreateSharedString` reuses offsets of identical strings.                                                                                | Schema-defined tables; the dedup state lives for one buffer.                                                                                      | Shows that per-call layout interning by plain byte comparison is standard practice, with no stringify and hash step. Supports E1.                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| Cap'n Proto encoding (https://capnproto.org/encoding.html)                                                                                                                                                             | "no more than one pointer can point at each object", so messages are trees. Canonical form is preorder. Readers enforce a _traversal limit_ (64 MiB default) against amplification.                                                                                                                                                   | Schema-defined messages.                                                                                                                          | Not applicable to graphs. The traversal limit is the same defense as §0.6: bound allocation by input size.                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| Boehm, Atkinson & Plass, _Ropes: an alternative to strings_, SP&E 25(12), 1995, https://doi.org/10.1002/spe.4380251203                                                                                                 | Ropes make concatenation and substring O(1) or O(log n) and help when there are many edits and few full traversals.                                                                                                                                                                                                                   | Long strings that are edited often and scanned rarely.                                                                                            | **Assumptions fail here.** The document is built once and then fully scanned by its consumer once. A rope (V8 `ConsString`) only defers one full copy to the consumer (§1.4), and it knocks the new JSON fast path off entirely (§0.2). `Array.join`, which allocates once at exact size, matches this access pattern.                                                                                                                                                                                                                                                         |
| Clifford, Payer, Stanton & Titzer, _Memento Mori_, ISMM 2015, pp. 105–117, https://doi.org/10.1145/2754169.2754181                                                                                                     | Allocation mementos link objects to their allocation sites and drive pretenuring, pretransitioning of elements kinds and presizing (implemented in V8).                                                                                                                                                                               | Behaviour stable per site over time.                                                                                                              | **Explains, but cannot be steered portably.** Long-lived encoder rows from literal sites can be pretenured automatically (§1.7). Pretransitioning is why `[tag, shape]` literal sites learn `PACKED_ELEMENTS`. A testable consequence: allocating rows from array _literals_ (sites with mementos) rather than spread or `new Array` keeps them eligible. Observe with `--trace-pretenuring`; expect gains only on large documents.                                                                                                                                            |
| Chambers, Ungar & Lee, _An efficient implementation of SELF_, OOPSLA 1989, https://doi.org/10.1145/74877.74884; Hölzle, Chambers & Ungar, _Polymorphic inline caches_, ECOOP 1991, https://doi.org/10.1007/BFb0057013  | Maps (hidden classes) and polymorphic inline caches make property access fast when a call site sees few maps.                                                                                                                                                                                                                         | Few maps per site.                                                                                                                                | **Applies directly** to the `Frame` and `kind` objects (§1.6) and to the decoder's `decoders[row[0]]` objects, whose `link` and `fill` properties exist on some decoders and not others, giving several shapes.                                                                                                                                                                                                                                                                                                                                                                |
| Column stores: Abadi, Madden & Ferreira, SIGMOD 2006, https://doi.org/10.1145/1142473.1142548; Melnik et al., _Dremel_, VLDB 2010, https://doi.org/10.14778/1920841.1920886                                            | Homogeneous records stored as columns allow per-column encoding and fewer per-record headers.                                                                                                                                                                                                                                         | Batches of homogeneous records, with ordering free to change.                                                                                     | **Analogy, with a large wire change.** Columns per shape would cut JSON.parse array allocations (one array per column instead of one per record) and give `PACKED_SMI`/`PACKED_DOUBLE` columns. It conflicts with preorder node ids, the single row layout and the existing proofs. Not recommended before E1–E5 and D1.                                                                                                                                                                                                                                                       |

---

## 5. Ranked mechanisms to test

Each mechanism lists its basis, what it is expected to change, the workloads it affects, and its
main risk. Under AGENTS.md, each also needs a frozen source tree, the counted work it removes
written down before the edit, and a Lean statement first wherever it changes a finite algorithm.

### (a) Encoder capture cost

1. **E1: intern shapes without building a signature string.** Replace `JSON.stringify(keys)`
   plus `Map<string,id>` with a per-call trie. Each node is `{ id, next: Map<string, node> }`,
   walked with the internalized key strings from `getOwnPropertyNames`. Optionally check the
   previous record's `keys` array element by element first.
   - _Basis:_ §1.1 (a C++ call and a fresh string hash per record); FlatBuffers per-buffer
     vtable dedup; hash-consing; V8's own per-call `map_cache_`.
   - _Counted work removed:_ one native call, one string allocation and one O(total key
     characters) hash per record.
   - _Workloads:_ record-heavy ones, where this was 7–28% self time.
   - _Test:_ the wire must be **byte-identical**, because shape ids are still assigned in
     first-seen order.
   - _Risk:_ the trie costs _k_ `Map.get` calls per record, which could lose on very wide
     records. The previous-record check could be read as a "shape-specific fast path"; the plain
     trie is a general per-call data structure. Needs a Lean lemma that trie interning matches
     interning by key sequence.
2. **E2: one fixed `Frame` layout.** Create every frame through a single constructor that
   initializes **all** fields (`row`, `child`, `keys`, `entries`, `iterator`, `next`, `state`,
   and the rest) in one fixed order, and add the new names to the mangle list.
   - _Basis:_ §1.6 and the 4-map polymorphism limit; the Self and PIC papers.
   - _Expected effect:_ the driver loop's field accesses become monomorphic and in-object, with
     no `PropertyArray` regrowth, and the 5–7× slowdown from polluted feedback should shrink.
   - _Workloads:_ mixed graphs (records with arrays and collections), DAGs, deep chains.
   - _Test:_ use `--log-ic` or `--trace-deopt` in a clean process and in a deliberately polluted
     one; compare times in both.
   - _Risk:_ larger frames (about 20 fields, all young-generation and short-lived). No change to
     observations.
3. **E3: `value[key]` instead of `Reflect.get(value, key)`** in `record()`.
   - _Basis:_ §1.6. TurboFan lowers `Reflect.get` to the generic `GetProperty` builtin with no
     feedback, and Maglev 13.6 has no reduction for it.
   - _Expected effect:_ a keyed-load IC with inline field loads for monomorphic or polymorphic
     record sets and stub-cache handlers when megamorphic.
   - _Workloads:_ records.
   - _Risk:_ low semantically, since both perform `[[Get]](key, value)` and proxy traps and
     getters see the same arguments; add a differential trace test anyway. The gain may be small
     when the site is megamorphic over many shapes.
4. **E4: write rows in place.**
   - Dense arrays: start with `row = [2, 0]`, `push` child tokens, set `row[1]` at the end, and
     switch to the sparse layout only when the first hole appears. This drops `entries` and the
     `[...entries]` spread copy.
   - Records: either keep `push` (packed rows), or preallocate `new Array(2 + keys.length)`,
     which is exact-sized but holey.
   - _Basis:_ §1.3 (growth from capacity 2 to 19 to 44; two copies for dense arrays);
     ValueSerializer's per-kind element loops.
   - _Workloads:_ large arrays, wide records and collections.
   - _Risk:_ holey rows tie the new fast path to the `NoElements` protector. Measure the push
     and preallocated variants separately. If a getter throws, a partial row is discarded as it
     is today.
5. **E5: return a small integer from `recognize()`** (tag, plus detail packed into spare bits)
   instead of `{tag}` or `{detail, tag}`; do the same for `nativeKind`.
   - _Basis:_ §1.6. The current code allocates on every object visit, has two result shapes,
     and escape analysis needs the call inlined.
   - _Workloads:_ every graph; most visible on small nodes and deep chains.
   - _Risk:_ low. `Frame.detail` stays a number.
6. **E6: struct-of-arrays explicit stack.** Keep frame scalars (`id`, `tag`, `phase`, `index`,
   `length`) in parallel per-call arrays, and keep only the object-valued state (`value`, `row`,
   `keys`, `iterator`) in object arrays. This allocates no heap object per frame.
   - _Basis:_ V8's `ContinuationRecord` value stack; defunctionalization.
   - _Workloads:_ deep chains and DAGs with many small nodes.
   - _Risk:_ highest of the list: the Lean refinement (`indexed_step_exact`) must be restated,
     `IteratorClose` unwinding must still close frames in reverse order, and the gain over E2
     may be small because young-generation allocation is a bump pointer. Do E2 first and do E6
     only if allocation profiles still show `Frame` as hot.

Measurement prerequisites for (a), not optimizations:

- Run every workload on Node 24 both with the default flags and with `--json-stringify-fast-path`
  (or on Node ≥ 25).
- Include fixtures whose strings are ropes or slices (§0.2).
- Run each workload in a fresh process and in a deliberately polluted one (§0.4).
- Consume the output string fully before stopping the clock (§0.5).

### (b) Decoder cost

1. **D1: build records by cloning a per-shape template.** For each shape, the first time it is
   allocated in a call, build `template = {}` with every key set to `undefined` (use
   `defineProperty` for `__proto__`). Allocate each record as `{...template}` and fill it with
   plain assignments to the **existing** own properties.
   - _Basis:_ `CloneObjectIC` has a `kIdenticalMap` fast path for literal-map sources with
     simple data properties (`GetCloneModeForMap`, `N24src/ic/ic.cc#L3289`). Starting from `{}`
     instead costs _k_ transitioning stores and out-of-line regrowth after 4 fields (§1.6).
     ValueSerializer and JSON.parse also avoid repeated transition searches (§1.2, §2).
   - _Workloads:_ record-heavy decodes, especially records with more than 4 keys.
   - _Risk:_ (i) **A semantic difference in polluted environments.** Today `obj[key] = v` runs a
     setter inherited from `Object.prototype` for that key, while a clone defines own data
     properties first, so the setter would not run. This needs an explicit contract decision.
     (ii) Field-representation generalization on the first stores. (iii) Null-proto records
     cannot use this, because null-proto literals and `Object.create(null)` are dictionary
     mode. (iv) It could be read as a "shape-specific path"; it is general, per call and
     bounded.
2. **D2: wire change — emit ordinary records as JSON objects** `{key: token, …}`.
   - _Basis:_ JSON.parse then allocates each object at its exact size, internalizes its keys and
     reuses map feedback from the previous object in the same array (§1.2). devalue takes this
     approach. The decoder would only rewrite reference and special tokens in place.
   - _Workloads:_ record-heavy decodes, where JSON.parse is 30–90%.
   - _Risk:_ the largest of the list: a wire change, larger text (keys repeated in every record),
     an encoder cost to build the objects (it would need E1-style per-shape templates), D1's
     setter semantics plus integer-key ordering, and new Lean statements for the wire
     correspondence. Test only if D1 and D3 leave JSON.parse dominant.
3. **D3: drop redundant decode passes.** Set a per-call flag in the allocate pass when any row
   has a `link` hook (view or `URLSearchParams`) and skip the link loop otherwise. Store fill
   functions in a dense array indexed by tag instead of reading `decoders[tag].fill` from objects
   of differing shapes.
   - _Basis:_ PIC theory (§1.6).
   - _Workloads:_ every decode; the share matters most when JSON.parse is the small part.
   - _Risk:_ very low. The proof obligation is only that the pass order is unchanged when links
     exist.
4. **D4: reorder `read()` checks by frequency.** Test `typeof token === 'number'` first, then
   the reference range `token <= -6 && Number.isInteger(token)`, then non-negative values; leave
   `-0` and specials to the slow tail.
   - _Basis:_ every token passes through `read()`. `Object.is(token, -0)` and two
     `Number.isSafeInteger` calls currently run on every numeric token.
   - _Workloads:_ every decode.
   - _Risk:_ low, but keep the exact accept/reject set and verify it differentially against the
     current `read` on the fuzz corpus.
5. **D5: allocate output arrays deliberately.**
   - For dense rows, consider `[]` followed by `push` during fill: the result stays packed for
     the consumer, at the cost of about log₁.₅ n reallocations, versus `new Array(n)`, which is
     holey forever (§1.3). Measure decode time _and_ a consumer loop.
   - For sparse rows, stop eagerly allocating storage sized by the untrusted length (§0.6).
   - _Workloads:_ array-heavy decodes and sparse arrays.
   - _Risk:_ packing can slow decode slightly. The sparse change is a robustness fix and should
     be justified on that ground.
6. **D6: recognize `PACKED_DOUBLE` rows as a known cost.** Rows whose tokens are all numbers
   with at least one non-integer become `FixedDoubleArray`s, and every read of an element boxes a
   new HeapNumber (§1.2). No portable decoder-side fix exists. Treat it as a _diagnostic_: if
   profiles of float-heavy decodes show HeapNumber allocation in `read`, only a wire change
   (D2-like, or columns) addresses it. _Risk:_ none, because it is measurement only.

### Considered and not recommended

- **`JSON.rawJSON` to embed pre-serialized rows.** V8's `ParseRawJson` accepts only primitive
  JSON text (string, number, `true`, `false`, `null`; `N24src/json/json-parser.cc#L1395`), and
  raw-JSON objects knock the new stringify fast path off.
- **One `Reflect.ownKeys` call instead of `getOwnPropertyNames` plus `getOwnPropertySymbols`.**
  It changes how many times the proxy `ownKeys` trap runs, which the contract forbids.
- **Snapshotting Map and Set contents as structured clone does.** It changes iterator
  observations.
- **Persistent quoted-key caches (devalue).** Forbidden by the "no persistent caches" rule.
- **`WeakMap` as the identity memo.** Ephemeron tables add GC work and offer no lookup
  advantage.
- **`Object.setPrototypeOf(fastObj, null)` for null-proto records.** A runtime call per object.
  This repository already rejected a related prototype-map approach (docs/development.md,
  "returning key-deleted roots to fast properties").
