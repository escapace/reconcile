# Wire-format prior art: separating control from data in a graph-preserving JSON codec

Review date: 2026-10-17. I read the codec at `src/serialization/` (encode.ts, frames.ts, parse.ts,
shapes.ts, leaf.ts, common.ts, facets/*.ts), the earlier report
`research/serialization/encoder-capture-evidence/reports/prior-art.md` (cited below as **PA**), and
`research/serialization/scalar-wire-acceptance/DECISION.md` (cited as **SWA**). Nothing in the
repository was changed. Nothing was executed: no node, builds, tests or benchmarks. This report extends
PA and does not repeat it. PA's V8 findings (stringify fast-path gate, rope restarts, `Reflect.get`,
frame maps and so on) are referred to by section number.

Conventions:

- `N24` = `https://github.com/nodejs/node/blob/v24.22.0/deps/v8/` (V8 13.6.233.17, the measured
  runtime). `V8M` = `https://github.com/v8/v8/blob/main/` (read 2026-10-17). `N25`/`N26` = the
  Node v25.0.0/v26.0.0 V8 copies.
- `SPEC` = ECMA-262 editor's draft, `https://tc39.es/ecma262/` (source `tc39/ecma262` `spec.html`, read
  2026-10-17).
- _(blog)_ marks blog posts and other secondary sources. **Analogy** means the source's assumptions do
  not hold here, so it can suggest a direction but provides no evidence for this codec.
- Line numbers refer to the files as downloaded on the review date.

---

## 0. Findings that matter most for the redesign

1. **Every serious in-band design in the survey has shipped an ambiguity or injection bug, or says
   in its spec that it cannot avoid one.** MongoDB Extended JSON says type wrappers "could be
   indistinguishable from another document" and that it "has no provision for escaping a leading `$`"
   (§1). Telejson decodes any user string `"_NaN_"` as `NaN` (§5). superjson's out-of-band `meta`
   still addressed data by **string property paths**, which allowed `__proto__.x` and led to RCE
   (CVE-2022-23631, §5). devalue's CVE-2025-57820 came from not checking that a slot value was a
   number before using it as an index, so `"push"` resolved to `Array.prototype.push` (§5). The
   LangSec taxonomy names this class "overloaded field in input format". Its canonical example is
   "placing the special value 5 in a field otherwise used as a byte counter" (§2). The current
   `-1…-5` / `-(i+6)` / `[-7,x]` tokens are the same pattern, safely implemented: the ranges are
   disjoint and proved. The owner's goal of removing them is well supported.
2. **The formats that avoid the problem decide interpretation by position or schema, never by
   value.** CBOR uses major type and tag, a channel no data value can occupy (RFC 8949 §3, §3.4).
   Protobuf uses field tags. Avro says "Binary encoded Avro data does not include type information"
   and resolves unions by schema index (§1). Arrow uses validity bitmaps and union type-id buffers,
   and "masked" slots "can have any value" (§3). The candidate's positional layouts are the JSON
   analogue of these designs.
3. **JSON gives exactly one free out-of-band channel: the syntactic type of a slot.** Composite
   values never appear inline in this codec, so a JSON array or object in a slot cannot be data. A
   reference written as a syntactic composite, such as `[i]`, would therefore be unambiguous with no
   layout at all. The cost is that JSON.parse allocates an array per reference. The repository's own
   measurement shows this cost is large: removing the `[-1]` singleton arrays made the undefined-10k
   decode 0.233× (SWA). Integer references plus out-of-band kinds are therefore the right trade-off
   for performance, and the singleton-array design is the safety baseline (§7, D).
4. **A parallel all-integer descriptor array is the cheapest thing JSON.parse can build, but only if
   every integer has at most 9 digits.** `ParseJsonArray` has a dedicated path for arrays of numbers
   that "Avoid[s] allocating HeapNumbers until we really need to" (`N24src/json/json-parser.cc#L1532`).
   It produces `PACKED_SMI_ELEMENTS` only while every number takes the inline Smi path, and that path
   stops at `kMaxSmiLength = 9` digits (`#L2010`). A 10-digit integer goes through the double path
   and turns the **whole** array into `PACKED_DOUBLE_ELEMENTS`. Bitmap words therefore must be ≤ 29
   bits (≤ 536 870 911), not 30 or 32. The same holds in V8M (`#L1368`, `#L1828`).
5. **Zero-copy reuse of JSON.parse arrays and objects is semantically equivalent to
   allocate-plus-CreateDataProperty, but not to allocate-plus-assignment.** JSON.parse defines
   properties with CreateDataProperty (SPEC ParseJSON → PropertyDefinitionEvaluation; V8
   `DefineOwnPropertyIgnoreAttributes`, `#L982`), even for `"__proto__"`. Today's decoder fills
   records with `object[key] = value` (`common.ts` `define`) and arrays with `array[i] = value`, so an
   inherited setter would run. README line 61 puts ambient setters outside the contract, so this is
   not a bug. It does mean that zero-copy reuse moves the decoder **closer** to JSON.parse's safety
   model (§4.3).
6. **On the new stringify fast path, an object with any integer-like key falls back for the whole
   document.** `CanFastSerializeJSObjectFastPath` requires `elements` to be empty
   (`N24src/json/json-stringifier.cc#L2314`, same in V8M), and PA §0.2 shows that every fall-off
   restarts from the root. Emitting records as JSON objects (D2 in PA, and the candidate's object
   option) therefore puts the entire document on the slow path on Node ≥ 25 whenever one record has a
   key such as `"0"` or `"123"`. Value-array records with a shapes table avoid this.
7. **Patching zero-copy arrays costs nothing for Smi arrays but O(n) for double arrays.** Storing an
   object into a `PACKED_SMI` array changes only the map. Storing one into a `PACKED_DOUBLE` array
   allocates a new FixedArray and one HeapNumber per element (`CopyDoubleToObjectElements`,
   `N24src/objects/elements.cc#L280`). Patching reference fields of parsed objects is an **in-place**
   representation change (Smi→Tagged), with no map deprecation (`MightCauseMapDeprecation`,
   `N24src/objects/property-details.h#L141`).
8. **Holes should not be produced by `delete` on reused arrays.** `DeleteCommon` decides whether to
   normalize to dictionary elements using an **isolate-wide** `elements_deletion_counter`
   (`elements.cc#L2154-L2203`). The resulting elements kind, and so later speed, depends on the
   isolate's execution history. Keep holes in a separate sparse/holey node kind.
9. **JSON.parse SIMD string scanning exists only in V8 main.** V8M `ScanJsonString` uses Highway
   SIMD and a heuristic internalization budget (`V8Msrc/json/json-parser.cc` around #L2077, #L1952).
   Neither appears in N24, N25 or N26 (checked by grepping each copy). Plain unescaped strings, with
   no prefix that JS code must inspect, are the representation that benefits.
10. **The jsonic.io guide is a secondary source with unsourced numbers.** Some claims match engine
    source: replacer and space disable the fast path; consistent key order helps. Others do not: "One
    Unicode key" slowing "that object" does not match V8, which chooses between one-byte and two-byte
    parsing **per document** (`template class JsonParser<uint8_t>/<uint16_t>`). See §4.6.

---

## 1. Graph, reference and type-annotation encodings: how each separates control from data

"In-band" means a data value can, by its value alone, be mistaken for control. "Positional" means a
slot's position or schema decides how to read it. "Syntactic" means a channel no data value can occupy.

| Format (source)                                                                                     | Control channel                                                                                                                                                                                                      | Reference / sharing model                                                                                                                                                                                              | In-band?                                                                                                                                                                                                                                                                                                                                                  | Known escaping or ambiguity failures; lesson                                                                                                                                                                                                                                                                                                                                          |
| --------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **CBOR**, RFC 8949 (https://www.rfc-editor.org/rfc/rfc8949)                                         | 3-bit major type per item; tags are major type 6 and enclose exactly one item (§3.4).                                                                                                                                | None in the base format.                                                                                                                                                                                               | **Syntactic.** A tag cannot be confused with an integer or string. §10: "giving the entire range of encodable values a meaning where possible".                                                                                                                                                                                                           | §10 warns about multiple interpretations ("duplicate keys in maps … different precision") and asks protocols to reduce them to one. §5.3.1 says duplicate map keys are invalid, but a "streaming decoder may not even be able to notice".                                                                                                                                             |
| **CBOR tags 28/29 (value sharing)**, http://cbor.schmorp.de/value-sharing                           | Tag 28 marks the first occurrence as shareable; tag 29 wraps an unsigned index.                                                                                                                                      | "index 0 refers to the first value marked as shareable in the CBOR stream". Cycles are supported, and decoders must "record the reference before decoding the value". This is preorder registration, as in this codec. | Syntactic: the index is wrapped in a tag, so a plain integer is never a reference.                                                                                                                                                                                                                                                                        | Notes "cannot be implemented on top of every generic CBOR encoder/decoder" (order must be controlled) and resource-exhaustion risk. **This is the inline-first-occurrence model (alternative B in §7).**                                                                                                                                                                              |
| **CBOR stringref (tags 256/25)**, http://cbor.schmorp.de/stringref                                  | Tag 256 opens a namespace; tag 25 holds an index.                                                                                                                                                                    | **Implicit** table: every definite-length string at or above a minimum length "MUST" get the next index, even if never referenced. The thresholds keep a reference no longer than the string.                          | Syntactic.                                                                                                                                                                                                                                                                                                                                                | Encoder and decoder must apply identical eligibility rules, or every later index shifts. This is the same implicit-table fragility as Smile (below).                                                                                                                                                                                                                                  |
| **Packed CBOR**, draft-ietf-cbor-packed-19 (2026-02-02, expired, WG state "Revised I-D Needed")     | Simple values 0–15 and tag 6 reference a shared-item table; tag 113 sets up the table.                                                                                                                               | Explicit tables (§2.1). **Tag 114 "record"** combines a key array with a value array (§4.2), which is the same idea as this codec's shapes table.                                                                      | Mostly syntactic, **except** that the record function treats a value item equal to `undefined` as "absent" (§4.2). That is an in-band sentinel even inside an IETF draft: a record built this way cannot carry an `undefined` value.                                                                                                                      | §9: "Loops in the Packed CBOR can be used as a denial of service attack". Lesson: interning key lists is standard practice; do not overload a data value as "absent".                                                                                                                                                                                                                 |
| **Amazon Ion**, https://amazon-ion.github.io/ion-docs/docs/symbols.html                             | Type descriptor per value (binary); `annotation::value` syntax (text); local symbol tables.                                                                                                                          | Symbol IDs into tables; no object graph.                                                                                                                                                                               | Annotations are syntactic. Symbol tables are **in-band at top level**: a top-level struct whose first annotation is `$ion_symbol_table` is a "system value". `$ion_1_0` resets the table, and a quoted `'$ion_1_0'` is a no-op that "breaks the data" if unquoted by a converter.                                                                         | Lesson: reserved annotations are safe only if the grammar keeps them out of user data. Ion relies on quoting, so a lossy text conversion can turn data into control.                                                                                                                                                                                                                  |
| **Transit** (cognitect/transit-format README)                                                       | String prefixes `~`, `~#tag`, `^` (cache), `"^ "` map marker as the first array element; backquote reserved.                                                                                                         | Cache codes `^0…` (44² entries) assigned implicitly in stream order; "the writer and the reader encounter cacheable values in the same order". No object graph.                                                        | **In-band with escaping**: "any data string that begins with one of those characters is escaped by prepending a ~".                                                                                                                                                                                                                                       | Every string must be checked on write and read. A maintainer stated that invalid input is undefined behaviour _(Clojurians Slack log, 2023-03-01, secondary)_. Lesson: escaping puts a per-string test on the hottest path.                                                                                                                                                           |
| **Smile** (FasterXML smile-format-specification)                                                    | Reserved token bytes; shared-name and shared-value back-references with 10-bit indices into a buffer of 1024 entries that is cleared when full.                                                                      | Implicit, stream-ordered tables.                                                                                                                                                                                       | Byte-level reserved values (`0xFD`–`0xFF`).                                                                                                                                                                                                                                                                                                               | 2025-05-18 erratum: an "existing (implement by Jackson codec) but previously undocumented requirement to skip Shared String/Key Name references ending with `0xFE` / `0xFF`". The implicit-table rules were incompletely specified for about 15 years. Lesson: prefer explicit tables with explicit indices.                                                                          |
| **MessagePack** ext (msgpack/spec.md)                                                               | Format byte families; ext carries an integer type plus bytes; 0–127 for applications, −128…−1 reserved.                                                                                                              | None.                                                                                                                                                                                                                  | Syntactic (separate format family).                                                                                                                                                                                                                                                                                                                       | Lesson: a disjoint "type" field, not a reserved value.                                                                                                                                                                                                                                                                                                                                |
| **BSON** / **MongoDB Extended JSON v2** (mongodb/specifications `extended-json.md`)                 | BSON: a type byte per element (syntactic). Extended JSON: objects with `$`-prefixed keys.                                                                                                                            | DBRef by convention only.                                                                                                                                                                                              | **Extended JSON is in-band with no escape**: "has no provision for escaping a leading `$`"; a document "could be indistinguishable from another document with a type wrapper"; "SHOULD NOT be used in contexts where `$`-prefixed keys could exist". The canonical regex form changed because of a "conflict … with the `$regex` MongoDB query operator". | Textbook case of key-name control shadowing user keys. Meteor EJSON adds `$escape` (packages/ejson/ejson.js #L181-L209), so every object is tested against every converter on encode and wrapped if it matches.                                                                                                                                                                       |
| **UBJSON** (ubjson.org, Draft 12; not re-read for this review, the spec file URL returned 404)      | A type marker per value, plus "optimized containers" that declare one element type and a count once (`[$][type][#][count]`).                                                                                         | None.                                                                                                                                                                                                                  | Syntactic.                                                                                                                                                                                                                                                                                                                                                | **Per-container type declaration is the closest analogue to a per-node layout.**                                                                                                                                                                                                                                                                                                      |
| **superjson** (README; plainer.ts per PA §3)                                                        | Out-of-band `meta.values` (type annotations by path) and `meta.referentialEqualities` (path → paths).                                                                                                                | References are **string property paths** into the decoded value.                                                                                                                                                       | Out-of-band in location, but control **addresses data by user-controlled names**.                                                                                                                                                                                                                                                                         | CVE-2022-23631 / GHSA-5888-ffcr-r425 (critical, RCE): paths such as `__proto__.x` were applied as assignments; Blitz.js "blocked … `__proto__`, `constructor`, and `prototype`" _(Sonar blog, https://www.sonarsource.com/blog/blitzjs-prototype-pollution/)_. **Lesson: out-of-band is not enough; control must address private tables by validated integers, never data by names.** |
| **Falcor JSON Graph** (netflix.github.io/falcor/documentation/jsongraph.html)                       | Objects `{ $type: "ref" \| "atom" \| "error", value }`.                                                                                                                                                              | Path references "followed from the root".                                                                                                                                                                              | **In-band key** (`$type`); the document does not say whether `$type` is reserved or how to escape it.                                                                                                                                                                                                                                                     | Same class as Extended JSON.                                                                                                                                                                                                                                                                                                                                                          |
| **JSON Reference** (draft-pbryan-zyp-json-ref-03, expired) / **JSON-LD 1.1** (W3C Rec, §3.1)        | `{"$ref": uri}`; JSON-LD keywords `@…`.                                                                                                                                                                              | URI/path references; "can be structured to resolve cyclically".                                                                                                                                                        | In-band: "Any members other than "$ref" … SHALL be ignored"; JSON-LD: strings of the keyword form "must not be used as terms".                                                                                                                                                                                                                            | Reserved-name designs: data cannot use those names.                                                                                                                                                                                                                                                                                                                                   |
| **YAML 1.2.2** (https://yaml.org/spec/1.2.2/, §3.2.2.2, §3.3.2)                                     | Anchors `&a` and aliases `*a`; tags `!…`.                                                                                                                                                                            | An alias "refers to the most recent event … having the specified anchor"; anchors "need not be unique" and are "a serialization detail". Nodes may contain themselves.                                                 | Anchors and aliases are syntactic. **Implicit typing of plain scalars is value-based**: they "may be matched against a set of regular expressions"; 1.2 "removed many of the problematic implicit typing recommendations" of 1.1.                                                                                                                         | The YAML 1.1 implicit-typing problems (e.g. `no` read as boolean) are the value-decides-type failure. Alias expansion is the classic amplification vector (not re-read here).                                                                                                                                                                                                         |
| **Python pickle** (PEP 3154; docs.python.org pickle warning)                                        | Opcodes.                                                                                                                                                                                                             | Memo: PEP 3154 adds `MEMOIZE`, which stores "at the index equal to the current size of the memo" (implicit preorder ids, as here) because "PUT opcodes are emitted for all non-atomic datatypes".                      | Syntactic opcodes.                                                                                                                                                                                                                                                                                                                                        | The opcode language includes callable reconstruction (`GLOBAL`/`REDUCE`), hence "not secure". **Lesson: the language must not include name-to-constructor lookup.**                                                                                                                                                                                                                   |
| **Java Object Serialization** (PA §4)                                                               | `TC_*` type codes; handles from `0x7E0000`.                                                                                                                                                                          | Preorder handles; `classDesc` once per stream.                                                                                                                                                                         | Syntactic.                                                                                                                                                                                                                                                                                                                                                | Its gadget-chain RCE history comes from reconstruction by class name, not from the reference scheme.                                                                                                                                                                                                                                                                                  |
| **V8 ValueSerializer / HTML structured clone** (`N24src/objects/value-serializer.cc#L117ff`; PA §2) | One tag byte per value (`'^'` object reference, `'_'` undefined, `'-'` hole, `'I'` int32, `'N'` double, …).                                                                                                          | Preorder ids; `kObjectReference` + varint.                                                                                                                                                                             | Syntactic; holes are their own tag, not a sentinel.                                                                                                                                                                                                                                                                                                       | A fully tagged binary format; pays one tag byte per value, which JSON cannot match cheaply.                                                                                                                                                                                                                                                                                           |
| **Cap'n Proto / FlatBuffers / Protobuf** (PA §4; protobuf.dev encoding)                             | Pointers with kinds (Cap'n Proto); vtables (FlatBuffers); `(field_number << 3) \| wire_type` per field (Protobuf).                                                                                                   | Trees only (Cap'n Proto: "no more than one pointer can point at each object").                                                                                                                                         | Positional/schema-typed.                                                                                                                                                                                                                                                                                                                                  | FlatBuffers deduplicates vtables per buffer, which is the per-call layout interning the candidate proposes.                                                                                                                                                                                                                                                                           |
| **Avro** (apache/avro Specification)                                                                | Schema.                                                                                                                                                                                                              | None.                                                                                                                                                                                                                  | **Positional**: "Binary encoded Avro data does not include type information or field names". A union is "an `int` … position within the union". The JSON encoding wraps union values as `{"type": value}`, and "the original schema is still required" to read it.                                                                                        | **Strongest precedent for "schema decides, value never does."** The candidate's layout is a per-document, per-node schema.                                                                                                                                                                                                                                                            |
| **devalue 6.0.3** (src/parse.js, constants.js)                                                      | Every container slot is an **index** into a flat table. Negative codes −1…−7 (`UNDEFINED`, `HOLE`, `NAN`, …, `SPARSE`) appear only in index positions. Typed entries are arrays whose first element is a string tag. | All values, primitives included, are table entries.                                                                                                                                                                    | Positional (slot = index), with sentinels in the index space, like this codec's current references.                                                                                                                                                                                                                                                       | CVE-2025-57820: `parse` "does not check that an index is numeric", so `[{"toString":"push"}]` assigned `Array.prototype.push`. See §5 for later advisories.                                                                                                                                                                                                                           |

**Synthesis.** Bugs follow from three properties. Formats where a **data value can denote control**
(Extended JSON, Transit, Falcor, telejson, YAML 1.1 implicit typing) have ambiguity or escaping costs
and failures. Formats where **control addresses data by names** (superjson paths, JSON Reference
paths, ungap's constructor-name lookup, pickle `GLOBAL`) have pollution or code-execution failures.
Formats with **implicit tables** whose indices both sides must derive identically (Transit cache, Smile,
CBOR stringref) have synchronisation fragility. The safe family uses a disjoint syntactic channel (CBOR,
MessagePack, ValueSerializer) or schema/position (Avro, Protobuf, Arrow, UBJSON optimized containers),
with explicit integer indices into private tables.

---

## 2. Theory: what makes an encoding safe by construction

### 2.1 LangSec

- Sassaman, Patterson, Bratus & Shubina, "The Halting Problems of Network Stack Insecurity", _;login:_
  36(6), Dec 2011 (USENIX; PDF hosted by a co-author). Relevant passages:
  - **Principle 1: minimal computational power.** "An input language should only be as
    computationally complex as absolutely needed … if the input language is context-free, then the
    parser should be no more powerful than a deterministic pushdown automaton."
  - **Principle 2: parser computational equivalence.** Composition "necessarily relies for its
    security on the different components of the system performing equivalent computations on the
    input languages". Equivalence is decidable only for regular and deterministic context-free
    grammars (sidebar).
  - **Signalling confused with data.** The PHY-layer example: a recognizer "can be easily tricked into
    'recognizing' signaling as data and vice versa".
- Sassaman, Patterson, Bratus & Locasto, "Security Applications of Formal Language Theory", _IEEE
  Systems Journal_ 7(3), 2013, https://doi.org/10.1109/JSYST.2012.2222000 (DOI checked; text not
  re-read). It is the journal version of the same principles.
- Momot, Bratus, Hallberg & Patterson, "The Seven Turrets of Babel: A Taxonomy of LangSec Errors and
  How to Expunge Them", IEEE SecDev 2016, https://doi.org/10.1109/SecDev.2016.019 (full text read).
  Relevant categories:
  - **Shotgun parsing**: "parsing and input-validating code is mixed with and spread across
    processing code".
  - **Overloaded field in input format.** Its examples are the Windows LFH case ("placing the special
    value 5 in a field otherwise used as a byte counter") and the NTP authentication bypass, where the
    key-id field was "overloaded to indicate 'authentication not required'".
  - **Parser differentials** and **permissive processing**.
  - Remedy: "Input should be fully validated … Only once validation succeeds should any application
    logic proceed".
- "Parse, don't validate" _(blog, Alexis King, 2019)_: decode into a type that makes invalid states
  unrepresentable instead of checking and then passing the raw data on. It is a programming-practice
  restatement of the LangSec recognizer-first rule.

### 2.2 Canonical and unambiguous encodings

- **ASN.1 DER** (ITU-T X.690): a single encoding per value (minimal lengths, ordered `SET OF`, fixed
  boolean). Decoders that check DER rules reject non-canonical input.
- **CBOR deterministic encoding** (RFC 8949 §4.2.1): shortest arguments, shortest floats, no
  indefinite lengths, keys sorted bytewise. Decoders may check this, but it is defined as an encoder
  property.
- **Bencode** (BitTorrent BEP 3): dictionary keys sorted, integers without leading zeros. One
  spelling per value.
- **JSON-specific.** RFC 8259 §4: "The names within an object SHOULD be unique", and behaviour with
  duplicates is "unpredictable". I-JSON (RFC 7493) makes duplicate names a "MUST NOT" and forbids
  surrogate code points. RFC 8785 (JCS) builds canonical JSON on ECMAScript's `JSON.stringify`
  primitive serialization plus recursively sorted properties.
- **ECMA-262 JSON.parse** (SPEC `#sec-ParseJSON`): "It is not permitted for a conforming
  implementation of `JSON.parse` to extend the JSON grammars". With duplicate names, "lexically
  preceding values for the same key shall be overwritten". The Early Error for duplicate `"__proto__"`
  does not apply, and `"__proto__"` becomes an ordinary own property (`isProtoSetter` is false during
  ParseJSON, SPEC `#sec-runtime-semantics-propertydefinitionevaluation`).

### 2.3 Mapping to this codec

| Property                              | What establishes it by construction                                                                                                                                                                                                                                                                                                                                                     | Status today / under the candidate                                                                                                                                                                                                                                                                                                                                                      |
| ------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| One grammar at both ends (LangSec P2) | Use JSON.parse as the only lexer. Its grammar is fixed by spec, and extension is forbidden.                                                                                                                                                                                                                                                                                             | Holds today and under the candidate.                                                                                                                                                                                                                                                                                                                                                    |
| No overloaded fields                  | A slot's meaning is a function of (node descriptor, slot index) only. A literal denotes itself for every JSON scalar value.                                                                                                                                                                                                                                                             | Today numbers are overloaded, with disjoint ranges proved in Lean. **The candidate removes this.**                                                                                                                                                                                                                                                                                      |
| Control addresses only private tables | Every control datum is a validated non-negative safe integer used to index a private array (`output`, layouts, shapes). No wire string is ever used as a property key in `[[Set]]` on an object whose own keys it did not create.                                                                                                                                                       | Holds today (`int()` checks; `define` special-cases `__proto__`). The candidate's "records as JSON objects with ref **keys listed by name** in the layout" would break this unless each listed key is checked with `Object.hasOwn` first, or references are listed by **ordinal**. Otherwise `obj["__proto__"] = node` sets the prototype (the superjson failure).                      |
| Typed references                      | A reference whose target must have a specific kind (view → ArrayBuffer, URLSearchParams → URL owner) checks the target's kind.                                                                                                                                                                                                                                                          | Holds today (`view.link` checks `nodes[…][0] !== 7`). The type-confusion advisories in devalue (CVE-2026-22774) and seroval (GHSA-9355-h2pj-8fqj) show what happens without it. Positional slot typing does **not** cover this; it is a separate per-kind rule.                                                                                                                         |
| No code execution                     | Dispatch by integer into a frozen table of native constructors. No `globalThis[name]`, no eval.                                                                                                                                                                                                                                                                                         | Holds. Compare @ungap/structured-clone, which constructs `new env[name](…)` with a denylist added in 1.3.1 _(socket.dev diff, secondary)_, and telejson, which uses eval for functions.                                                                                                                                                                                                 |
| Allocation bounded by input           | Every allocation size derives from parsed text size, not from a wire integer.                                                                                                                                                                                                                                                                                                           | Sparse-array `new Array(len)` violates this (PA §0.6). The same class appears in devalue GHSA-77vg-94rm-hx3p and seroval GHSA-jp82-f5mq-hwhp. Cap'n Proto's traversal limit and RFC 8949 §10 make the same demand.                                                                                                                                                                      |
| Recognize before processing           | Decode creates only fresh objects, so a mid-decode rejection discards everything and nothing outside is visible.                                                                                                                                                                                                                                                                        | Holds in effect: validation is interleaved with allocation, but the only side effects are fresh native objects plus `URL`/Temporal constructors. Keep this property explicit if zero-copy reuse lets JSON.parse objects escape.                                                                                                                                                         |
| Canonical (one text per value)        | Define canonicity on the **JSON value tree**, not the text. JSON.parse is many-to-one: whitespace, `1e2` versus `100`, `A` versus `A`, duplicate keys. Text-level canonicity follows on the encoder side because `JSON.stringify` is deterministic (RFC 8785's argument). Checking it on the decoder side would need `JSON.stringify(JSON.parse(t)) === t`, a full extra serialization. | Today the decoder accepts some non-canonical trees, such as unused or duplicate shapes. Decide explicitly between **unambiguous** (every accepted text has exactly one meaning; essential and cheap) and **canonical** (every value has exactly one accepted text; costlier, DER-style checks). CBOR treats determinism as an encoder obligation with optional decoder checking (§4.2). |

---

## 3. Representing per-slot kinds: columnar and shredding precedents

| Source                                                                                                                                                                                                                  | Mechanism                                                                                                                                                                                                            | Evidence and assumptions                                                                                                                                               | Relevance                                                                                                                                                                                                                                                                                                                                |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Melnik et al., _Dremel_, PVLDB 3(1), 2010, https://doi.org/10.14778/1920841.1920886                                                                                                                                     | Per-value repetition and definition levels: small integers, kept out of band, that say where nested optional or repeated fields are present.                                                                         | Schema-known nested records; levels compressed by RLE and bit-packing.                                                                                                 | **Analogy.** Presence and absence are recorded out of band, never by a null sentinel in the value column. The three-way distinction hole / own undefined / value maps to definition levels, but this codec's holes are rare enough to keep in a separate node kind (§0.8).                                                               |
| Apache Arrow Columnar Format (https://arrow.apache.org/docs/format/Columnar.html)                                                                                                                                       | Validity bitmap with 1 bit per slot, LSB numbering, omittable when `null_count == 0`. Dense union: int8 **types buffer** plus int32 offsets; sparse union: types buffer only. Run-end encoding; dictionary encoding. | Masked slots "can have any value and need not be zeroed". Unions "do not have their own validity bitmap". The layout targets random access and SIMD, not minimal size. | **Direct precedent** for (a) the kind living outside the value buffer, (b) placeholder values at masked positions being meaningless (so canonicity must fix them), and (c) omitting the kind structure entirely when a node has no references.                                                                                           |
| Apache Parquet, RLE/bit-packing hybrid (https://parquet.apache.org/docs/file-format/data-pages/encodings/)                                                                                                              | Runs are either `rle-run` or a `bit-packed-run` of multiples of 8 values; header `varint(len<<1 \| flag)`.                                                                                                           | Used for repetition and definition levels, dictionary indices and booleans. The spec gives no rule for choosing between the two run types.                             | Precedent for **choosing per segment between runs and dense bits**. That needs two decode paths, at a DRY cost.                                                                                                                                                                                                                          |
| Chambi, Lemire, Kaser & Godin, "Better bitmap performance with Roaring bitmaps", _SPE_ 46(5), 2016, https://doi.org/10.1002/spe.2325; Lemire, Ssi-Yan-Kai & Kaser, _SPE_ 46(11), 2016, https://doi.org/10.1002/spe.2402 | Per 2¹⁶-value chunk: a sorted array of 16-bit values when the chunk is sparse (at most 4096 entries, the break-even with an 8 KiB bitmap), a bitmap when it is dense, and run containers (2016 paper).               | Measured: the hybrid is "several times faster (up to two orders of magnitude)" than RLE-only bitmaps and compresses better (arXiv 1603.06549 abstract).                | The best per-slot kind representation depends on **density and run structure**: index lists for sparse references, bitmaps for dense mixed patterns, runs for homogeneous patterns. For this codec, homogeneous nodes dominate: all-literal number or string arrays, all-reference arrays of records, and records with a stable pattern. |
| Durner, Leis & Neumann, _JSON Tiles_, SIGMOD 2021, https://doi.org/10.1145/3448016.3452809 (PDF read)                                                                                                                   | Detects frequent key paths per tile of documents (frequent itemset mining), materializes them as typed columns and handles outliers separately.                                                                      | Analytical DBMS; tiles of about 2¹⁰ documents; reorders tuples.                                                                                                        | **Analogy only.** It confirms that local structure (per tile, or per document here) is enough to get columnar benefits, which supports per-document interning of layouts. Reordering is incompatible with preorder ids.                                                                                                                  |
| Chambers, Ungar & Lee, OOPSLA 1989, https://doi.org/10.1145/74877.74884 (Self maps; PA §4)                                                                                                                              | Objects share a "map" (layout) describing slot names and kinds; values live in the object.                                                                                                                           | Few maps per program.                                                                                                                                                  | The candidate's interned layout is a Self map for nodes. V8 uses the same structure for JSON.parse objects (`JSDataObjectBuilder` starts from the object-literal map cache, `N24…json-parser.cc#L714`).                                                                                                                                  |
| UBJSON optimized containers (above)                                                                                                                                                                                     | One type and a count per container.                                                                                                                                                                                  | —                                                                                                                                                                      | Run-length with a single open-ended run is the JSON equivalent for homogeneous arrays.                                                                                                                                                                                                                                                   |

### 3.1 Cost model for this codec (derived; needs measurement)

The slot kinds that need representing are only {literal, reference}, provided holes stay in a sparse or
holey node kind (§0.8). For a node with _n_ slots, _r_ references and _k_ runs:

| Representation                                                          | Wire size per **distinct** layout | Decode work per node                                   | Canonical form                                                           | Interns across lengths?                                                                        |
| ----------------------------------------------------------------------- | --------------------------------- | ------------------------------------------------------ | ------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------- |
| Bitmap words (≤ 29 bits each, §0.4)                                     | ⌈n/29⌉ numbers of up to 9 digits  | O(⌈n/29⌉ + r) with `Math.clz32` bit iteration          | No trailing zero words; fixed width                                      | No: length-dependent                                                                           |
| Sorted reference-position list                                          | r numbers                         | O(r)                                                   | Strictly increasing, each < n                                            | No for all-reference arrays (list = 0…n−1)                                                     |
| Alternating run lengths, starting with literal, **last run open-ended** | k numbers                         | O(k), or O(r) after expanding once per layout per call | No zero-length runs except a leading literal run of 0; last run implicit | **Yes for homogeneous nodes**: "all literal" = `[]`, "all reference" = `[0]`, independent of n |

Because layouts are interned, wire size per **node** is one descriptor integer in all three cases. The
representation is paid once per distinct layout, and the decoder can expand it once per call into a
reference-position array, a per-call bounded cache like today's `checkedShapes`. The choice therefore
rests on (a) interning hit rate and (b) validation simplicity, not per-slot decode speed. **Runs with
an open last run** are the only option that makes the two most common array layouts length-independent,
so they should give the best hit rate. This is an inference that needs measurement (U1 in §6).

---

## 4. Native JSON.parse and JSON.stringify: new engine and specification facts

PA §1 covers stringify gates, ropes, elements growth and parse basics. The facts below are new.

### 4.1 Numbers

- **Integers on the inline path.** `ParseJsonNumberAsDoubleOrSmi` scans at most `kMaxSmiLength = 9`
  digits inline (`N24…json-parser.cc#L2008-L2018`). Anything with a fraction, an exponent, `-0` or 10
  or more digits goes through the double path.
- **Number-only arrays.** `ParseJsonArray` collects leading numbers in `smi_elements_` or
  `double_elements_` with no handles or HeapNumbers. A pure-number array becomes `PACKED_SMI` or
  `PACKED_DOUBLE` in one allocation (`#L1530-L1584`). The first non-number moves everything to the
  generic path, which boxes the doubles collected so far (`#L1590-L1600`).
- **Consequences.**
  - Keep descriptors, layout ids, node ids and run lengths below 10⁹, so the descriptor array is one
    `PACKED_SMI` allocation.
  - A reference slot holding a node id is a Smi, so arrays of references parse as `PACKED_SMI`.
  - Today's negative references and specials are Smis too, so the change is not about number-parse
    cost. The `[-7,x]` and `[-6,"…"]` escapes do cost one JSArray plus one FixedArray each (PA §1.2).
- **Smi range.** It is 31 bits with pointer compression (Chrome) and 32 bits without (default Node
  builds). The 9-digit limit (< 10⁹ < 2³⁰) is below both, so "≤ 29 bits per bitmap word" is
  portable.
- **Number printing.** Node 24 uses Grisu-based `DoubleToAscii`; Node ≥ 25 uses Dragonbox (PA §1.1).
  Primary algorithm sources: Adams, "Ryū", PLDI 2018, https://doi.org/10.1145/3192366.3192369;
  Giulietti, "The Schubfach way to render doubles" (technical report, 2020; the basis of JDK 19
  `Double.toString`); Jeon, "Dragonbox" (technical report, 2020, github.com/jk-jeon/dragonbox). Small
  integers avoid all of these, which is another reason to keep control as small integers.
- **Parsing literature.** Lemire, "Number parsing at a gigabyte per second", _SPE_ 51(8), 2021,
  https://doi.org/10.1002/spe.2984: "parsing decimal numbers from strings becomes a bottleneck". The
  wire should not add numbers it does not need, such as length fields that JSON array length already
  implies. The candidate drops `len` from dense array rows.

### 4.2 Objects, strings and the reviver path

- **Reviver path.** Without a reviver, V8 13.6 parses with `ParseJsonValueRecursive` and falls back to
  the iterative parser at the stack limit. With a callable reviver, it uses the iterative
  `ParseJsonValue<true>` with source tracking and no mutable HeapNumbers (`#L531-L545`, `#L1339-L1346`).
  Reviver-based designs (flatted's `Primitives` reviver; using `context.source` from the source-text
  access feature, now in SPEC `JSON.parse`, to read big integers as number literals) therefore move
  JSON.parse to its slow mode **and** call JS for every value. They are not candidates.
- **Object construction.** `JSDataObjectBuilder` (`#L704-L1000`) builds objects from the object-literal
  map cache, follows `ExpectedTransition` on raw key bytes, creates fields as
  `PropertyConstness::kConst` (`#L867`), and falls back to `DefineOwnPropertyIgnoreAttributes(…, NONE)`
  (`#L982`). The previous **sibling in the same JSON array** supplies the expected final map
  (`#L1606-L1616`).
  - In a flat preorder node table, a record's payload neighbours are usually its own children, not
    same-shape siblings. Expected-map feedback therefore mostly misses.
  - In a nested (tree-inlined) layout, arrays of records are literal siblings, and feedback hits.
    This matters for alternative B in §7.
- **Integer-like keys.** Keys that are array indices go to elements, or to a dictionary when sparse
  (`BuildJsonObject`, `#L1300-L1336`). Enumeration order is still OrdinaryOwnPropertyKeys order
  (integers ascending, then strings in insertion order), which matches the encoder's
  `getOwnPropertyNames` order.
- **String scanning.** V8M scans strings with Highway SIMD and internalizes short one-byte strings
  under a budget, otherwise only looking up existing internalized strings (`V8M…json-parser.cc` around
  #L1952, #L2077-L2140). Neither feature is in N24, N25 or N26. Avoid any string representation that
  makes JS inspect every string (Transit `~`, telejson `_…_`). Positional typing needs no per-string JS
  work for literal slots.
- **Simdjson.** Langdale & Lemire, "Parsing gigabytes of JSON per second", _VLDB J._ 28(6), 2019,
  https://doi.org/10.1007/s00778-019-00578-5, and Keiser & Lemire, "On-demand JSON: a better way to
  parse documents?", _SPE_ 54(6), 2024, https://doi.org/10.1002/spe.3313. Their abstract lists
  Node.js as a user of On-Demand, but V8's `JSON.parse` is V8's own parser (source read), so simdjson
  is not reachable from portable JS. **Analogy:** the general lessons transfer as wire properties that
  any parser rewards: fewer structural characters and numbers, unescaped strings, ASCII or Latin-1
  text. On-Demand's lazy materialization does not apply, because the decoder materializes everything.

### 4.3 Is reusing a JSON.parse result equivalent to building it?

| Aspect                          | JSON.parse result (SPEC ParseJSON → ArrayLiteral / ObjectLiteral evaluation)                                 | `new Array(n)` + `a[i] = v` / `{}` + `o[k] = v` (today's decoder)                                         | Equivalent?                                                                                                                                                                                                                                                                                                                                                              |
| ------------------------------- | ------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Prototype                       | %Array.prototype% / %Object.prototype% of the current realm                                                  | Same                                                                                                      | Yes                                                                                                                                                                                                                                                                                                                                                                      |
| Extensibility                   | Extensible ordinary objects (SPEC asserts "ordinary, extensible object with no non-configurable properties") | Same                                                                                                      | Yes                                                                                                                                                                                                                                                                                                                                                                      |
| Property attributes             | CreateDataProperty: `{writable, enumerable, configurable: true}`; array `length` as ArrayCreate defines it   | Same when no inherited setter exists                                                                      | Yes in an unmodified environment                                                                                                                                                                                                                                                                                                                                         |
| Inherited setters / `__proto__` | **Never invoked**; `"__proto__"` becomes an own property                                                     | `[[Set]]` invokes inherited setters (out of contract, README line 61); `__proto__` is handled by `define` | JSON.parse is **stricter**, so reuse removes the dependence on ambient setters                                                                                                                                                                                                                                                                                           |
| Holes                           | Impossible: JSON arrays are always packed                                                                    | Possible                                                                                                  | Holey arrays need a non-reuse path                                                                                                                                                                                                                                                                                                                                       |
| Duplicate keys                  | Last value wins at the first key's position; undetectable after parse                                        | Not applicable                                                                                            | Detect by comparing the key count with the layout's arity (a length-carrying layout makes duplicates detectable)                                                                                                                                                                                                                                                         |
| Engine state (not observable)   | Packed elements kinds; const fields; maps shared with object literals                                        | `new Array(n)` is HOLEY forever (PA §1.3)                                                                 | Not observable. Reuse gives consumers **packed** arrays (a likely consumer speedup, U5). Patching: Smi→object is a map change; Double→object copies and boxes (§0.7); field Smi→Tagged is in place (§0.7); writing const fields generalizes constness, which can deoptimize code depending on literal maps (inferred from `kConst` plus map sharing; needs measurement). |

**Conclusion.** Reusing the arrays and plain objects that `JSON.parse` returns is semantically safe.
JSON.parse produces fresh, private, ordinary objects equal to what `ArrayCreate` / `OrdinaryObjectCreate`
plus CreateDataProperty would produce. Patching reference slots with `[[Set]]` is also safe: the
property is an own writable data property, so OrdinarySet never consults the prototype. This holds as
long as the key or index comes from the object itself (ordinal) or is checked with `Object.hasOwn`.

### 4.4 Stringify facts beyond PA

- **Objects with elements.** Integer-like keys disqualify an object from the fast path (§0.6). In V8M
  the fast path also caches a per-DescriptorArray `fast_iterable` state across calls
  (`V8M…json-stringifier.cc` around #L2829-L2994). This is an engine-internal cache, not a codec cache.
- **`toJSON`.** SerializeJSONProperty calls `GetV(value, "toJSON")` on every Object or BigInt (SPEC
  `#sec-serializejsonproperty`). The fast path bails out when any prototype map
  `may_have_interesting_properties` (`V8M…json-stringifier.cc#L2374-L2395`, `#L3243-L3250`; N24
  `#L2301-L2330`), and the slow path then calls the
  inherited `toJSON`. Both today's transport and the candidate's are exposed to an ambient
  `Object.prototype.toJSON` or `Array.prototype.toJSON`. README line 61 puts this out of contract. A
  per-call check that these are absent would be cheap if the contract is ever widened.
- **Non-JSON values.** `-0` prints as `0`, non-finite numbers as `null`, and BigInt throws (SPEC
  SerializeJSONProperty). Native stringify can therefore never carry these values in band. Moving them
  to nodes is what the candidate needs, and it removes the `[-6,…]` and `[-7,…]` arrays.

### 4.5 Allocation in the decoder and `delete`

`DeleteCommon` (`N24src/objects/elements.cc#L2136-L2204`) normalizes a fast array to dictionary
elements only when a heuristic based on an **isolate-wide counter** fires. Representing holes in a
reused JSON.parse array by `delete` would make elements kinds depend on unrelated earlier work in the
process. This is a measurement-reproducibility hazard of the kind PA §0.4 already describes, so avoid
it.

### 4.6 The jsonic.io guide (owner-supplied)

"JSON Parse Performance JavaScript: V8 Fast-Path, simdjson & Streaming", Jsonic editorial team,
updated 2026-05-20. This is a **secondary source with no named author**. Most figures cite no
benchmark, hardware or engine version. The "typical output" timings are labelled typical, not
measured.

| Claim                                                                                                        | Verdict against primary sources                                                                                                                                                                                                                                                                              |
| ------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Parse fast path needs ASCII keys and simple values; "one Unicode key" slows that object 2–3×                 | **Not supported as stated.** V8 instantiates `JsonParser<uint8_t>` or `<uint16_t>` from the representation of the **whole source string** (`#L2313-L2314`). There is no per-object ASCII path. Per-key costs (internalization, `ExpectedTransition` byte comparison) do exist. The 2–3× figure is unsourced. |
| The slow path is "V8's general-purpose recursive descent parser"                                             | Partly true. The **default** no-reviver path is recursive (`ParseJsonValueRecursive`) with an iterative fallback; the reviver path is iterative (§4.2). The guide's fast/slow split does not match the source.                                                                                               |
| Consistent key order keeps objects monomorphic                                                               | Supported: sibling map feedback in `ParseJsonArray` (`#L1606-L1616`) and inline-cache theory (PA §4).                                                                                                                                                                                                        |
| A replacer is called for every value; `space` slows stringify                                                | Supported by SPEC and by the fast-path gate (replacer and gap must be undefined; PA §1.1). The percentages are unsourced.                                                                                                                                                                                    |
| Stringify is 20–40% slower than parse; MessagePack decodes 60–80% faster; fast-json-stringify is 3–7× faster | Unsourced; disregard. The Node 24 versus Node ≥ 25 stringify flag difference (PA §0.1) alone invalidates version-free comparisons.                                                                                                                                                                           |
| simdjson reaches 2–4 GB/s, about 8× JSON.parse                                                               | The order of magnitude matches Langdale & Lemire, but simdjson is not reachable from portable JS (§4.2), so the claim is irrelevant here.                                                                                                                                                                    |

Nothing in the guide changes the design analysis. Its accurate advice (no replacer, reviver or space;
stable key order) is already reflected here and in PA.

---

## 5. JS libraries: design choices, recorded rationale and advisories

| Library (version / source)                                 | Control/data separation                                                                                                                                                                                                                                                                                                                   | Recorded rationale or incidents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| ---------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **devalue** (main, 6.0.3)                                  | Flat table; container slots are indices; negative codes appear only in index positions; typed entries are `["Tag", …]`, told apart from plain arrays by `typeof value[0] === 'string'` (plain arrays hold integers). Records are JSON objects whose values are indices, and the decoder rebuilds them (`ops.createObject()` + `ops.set`). | GitHub advisories, read 2026-10-17 (16 listed):<br>• Prototype pollution: GHSA-vj54-72f3-p5jv, CVE-2025-57820; GHSA-cfw5-2vxh-hr84, CVE-2026-30226.<br>• Own `__proto__` properties: GHSA-mwv9-gp5h-frr4; GHSA-4q55-j62x-fr9h, a bypass "via property-key coercion".<br>• Type confusion leading to DoS: CVE-2026-22774 ("typed array hydration expecting an `ArrayBuffer` … not checking"); CVE-2026-22775 (base64 not checked).<br>• Sparse-array memory/CPU: GHSA-77vg-94rm-hx3p, GHSA-33hq-fvwr-56pm.<br>Devalue now **rejects** own `__proto__` keys, which diverges from JSON.parse; this codec preserves them. Changelog perf entries are in PA §3. |
| **flatted** (main)                                         | Every string is moved into the table and replaced by its index **as a string**, so a string in a container means "reference" and literal strings exist only at the top level. Parsing uses a reviver that boxes strings.                                                                                                                  | No recorded rationale. The reviver puts JSON.parse on the slow iterative path (§4.2), and the per-object stringify replacer leaves the fast path (PA §3).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| **@ungap/structured-clone** (main)                         | `[TYPE, value]` pairs with integer types −1…8 plus string types for newer kinds; records as `[[keyIndex, valueIndex], …]`; own `__proto__` via `defineProperty`.                                                                                                                                                                          | Error and other kinds were reconstructed with `new env[name](…)` (globalThis lookup by wire name). 1.3.1 added a denylist guard (`Function`, `eval`, `Worker`, `setTimeout`, …) _(socket.dev package diff, secondary; no advisory found)_. A denylist is the opposite of LangSec allowlisting.                                                                                                                                                                                                                                                                                                                                                             |
| **seroval** (main, `packages/seroval/src/core/types.ts`)   | **Fully tagged**: every value, including numbers and strings, is a node object `{t, i, s, …}` with 37 node types. The primary output mode is JavaScript source to evaluate.                                                                                                                                                               | Advisories (page 1, read 2026-10-17):<br>• "TypedArray/DataView buffer type-confusion" (GHSA-9355-h2pj-8fqj).<br>• "unchecked TypedArray length" (GHSA-jp82-f5mq-hwhp).<br>• Promise/thenable type confusion that invokes attacker-influenced methods (GHSA-mv8w-475r-vwqw, GHSA-p6vx-979v-rg4c, critical).<br>• Deep-nesting DoS (GHSA-3j22-8qj3-26mx, GHSA-v7hr-4gv3-67h6).<br>Lesson: full tagging prevents ambiguity but **not** target-kind confusion or resource abuse.                                                                                                                                                                              |
| **superjson** (2.2.6, README)                              | Tree as `json` plus `meta` keyed by **path strings**.                                                                                                                                                                                                                                                                                     | CVE-2022-23631 (§1). PA §3 notes O(depth) path allocations per node.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| **telejson** (storybookjs/telejson master, `src/index.ts`) | **In-band string sentinels with no escaping**: `'_undefined_'`, `'_NaN_'`, `'_Infinity_'`, `` `_bigint_${…}` ``, `` `_date_${…}` ``, `'_regexp_…'`, `'_symbol_…'`, `'_duplicate_…'` paths, `'_constructor-name_'` key. Functions are revived by `eval` (README: "The eval happens via `eval()`").                                         | No advisory found. By construction, any user string equal to `"_NaN_"` round-trips as `NaN`. This is the clearest counterexample to in-band signalling.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |

**Lessons for this codec:**

1. Validate that every control integer is an integer in range **before** using it as an index (devalue
   CVE-2025-57820).
2. Check the kind of every typed reference's target (devalue CVE-2026-22774, seroval GHSA-9355).
3. Never allocate from wire integers (devalue and seroval sparse-array and TypedArray-length advisories).
4. Never look up constructors by name (ungap, pickle, Java).
5. Never interpret data strings (telejson, Transit, Extended JSON).

The candidate addresses item 5 completely. Today's codec already satisfies items 1, 2 and 4. Item 3
remains open (PA §0.6).

---

## 6. Critique of the candidate direction

**Candidate.** Positional typing: per-node interned layouts give each slot's kind (literal or
reference), and specials, bigint and `-0` become nodes. Descriptors go in a parallel integer array.
Payload arrays are reused zero-copy, with reference slots patched in place. Records are either value
arrays with interned keys or JSON objects.

### 6.1 Strengths, with sources

1. **No overloaded fields.**
   - Every JSON scalar denotes itself in every literal slot. Negative numbers become literals, which
     removes `[-7,x]` and its JSArray plus FixedArray pair per value (PA §1.2).
   - References become non-negative integers, one character shorter than `-(i+6)`.
   - This is the LangSec "overloaded field" remedy (§2.1) and the Avro/Arrow/Protobuf principle (§1,
     §3).
   - It also removes the Lean obligation that special and reference ranges stay disjoint. Range
     arithmetic is replaced by a typing judgement: layout × slot index → kind.
2. **The control plane is cheap to parse.**
   - Descriptors as an all-Smi array take V8's number-array path: one allocation, no handles, no
     HeapNumbers (§4.1).
   - Dense array payloads drop the `[2,len,` header (length is implied), so a 1-element array row goes
     from `[2,1,x]` to `[x]` plus one descriptor integer.
3. **Zero-copy arrays are sound** (§4.3), give consumers packed arrays instead of HOLEY
   `new Array(n)`, and avoid the inherited-setter dependence of `a[i] = v`.
4. **Interned layouts match established practice**: FlatBuffers vtable dedup, packed-CBOR record tag,
   Self maps, JSON Tiles. The decoder expands each layout once per call, as it already does for
   shapes, so per-node decode cost is O(references) after validation.

### 6.2 Risks

1. **Two sources of truth.**
   - A slot's JSON type already distinguishes composite from scalar, and the layout adds literal versus
     reference. The decoder must reject every disagreement: a literal slot holding an array or object,
     a reference slot holding a string, `-0` or a fraction.
   - To be canonical (§2.3) it must also reject literal `-0`, which JSON.parse produces from `-0`,
     because `-0` is supposed to be a node.
   - So the decoder still pays an **O(n) type scan per payload**, not O(references), unless the owner
     accepts "unambiguous" without "canonical" for literal slots.
   - Fewer invalid states would be better. Alternative D (§7) has exactly one source of truth.
2. **Encode cost of layouts.** Every node needs its kind pattern accumulated (cheap integer operations
   per slot) and then interned: a trie or Map probe per node, keyed by (kind, shape, runs). PA §5 E1
   removed a per-record signature string for the same reason. **Do not build a layout signature
   string.** Intern by integer trie. The previous scalar-wire attempt was rejected for 8–12%
   regressions on single workloads (SWA). The candidate touches every node on both sides, so the
   "no performance cost" requirement is at real risk for deep chains of tiny nodes, where
   per-node constant cost dominates.
3. **Layout explosion.**
   - Records whose field is sometimes a reference and sometimes a literal (`parent: null` versus
     `parent: {...}`) split into 2^(variable fields) layouts.
   - Mixed arrays without open-ended runs get one layout per (length, pattern).
   - In the worst case there is one layout per node, which costs more than today's in-band tokens.
     Measure distinct layouts per node (U1).
4. **Records as JSON objects.**
   - (a) Integer-like keys knock the **whole** stringify off the Node ≥ 25 fast path (§0.6).
   - (b) Repeated key text in every record; gzip helps the wire, not parse time.
   - (c) The encoder must build a transport object with k keyed stores. Each `o[k] = v` is a
     transitioning store, megamorphic across shapes. `__proto__` needs `defineProperty`.
   - (d) Null-prototype records cannot reuse JSON.parse objects (PA, not recommended), so two record
     representations would exist, which is not DRY.
   - (e) Listing reference keys by **name** reopens the superjson class unless checked with
     `Object.hasOwn`. Use ordinals.
   - (f) Sibling-feedback misses in a flat node table (§4.2).
   - Recommendation: value-array records first; measure objects separately.
5. **Elements-kind traps when patching.** A double array containing a reference copies and boxes all
   elements once (§0.7). Rare, but must be in the fixtures.
6. **Holes.** They cannot be zero-copy without `delete`, which has history-dependent normalization
   (§4.5). Keep the dense/sparse split as node kinds; only hole-free arrays are reused.
7. **Specials as nodes.** One node per distinct special value per document (primitives have no
   identity, so sharing is sound), plus a decoder kind per special. Map keys normalize `-0` by
   SameValueZero anyway. Root handling needs one rule, for example "root is always slot 0 of a
   1-slot root layout", so scalar roots stay MECE.
8. **Proof obligations.** The current Lean results (`Inline.lean direct_rows_exact`, scalar
   disjointness, ShapeRadix) state the row layout. A positional wire needs new statements before
   implementation:
   - layout typing soundness: every accepted document decodes uniquely;
   - encode ∘ decode identity on the value model;
   - interning matches first-use order (radix-style).
     It also needs a native correspondence obligation that JSON.parse returns CreateDataProperty-built
     ordinary objects (§4.3).
9. **Nothing here addresses the open DoS item.** Sparse `new Array(len)` (PA §0.6) is independent of
   the wire redesign and should be fixed in any variant.

### 6.3 Unknowns that need measurement

All of these are under AGENTS.md rules: frozen source, counted work written first, never overlapped,
≤ 300 s per round, on Node 24 with and without `--json-stringify-fast-path` (or Node ≥ 25).

| Id  | Question                                                                               | Metric                                                                                            |
| --- | -------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------- |
| U1  | Interning effectiveness                                                                | Distinct layouts / nodes per fixture, for runs-with-open-tail versus bitmap versus position lists |
| U2  | Per-node encode overhead of layout accumulation plus interning                         | Encode time on deep-chain, DAG and records fixtures                                               |
| U3  | Decode benefit of zero-copy arrays net of the validation scan and elements transitions | Decode time on number-, string-, ref- and mixed-array fixtures, including a float+ref array       |
| U4  | Records as value arrays versus JSON objects                                            | Encode, decode and size; one fixture with integer-like keys on Node ≥ 25                          |
| U5  | Consumer speed of packed versus holey decoded arrays                                   | A fixed consumer loop after decode                                                                |
| U6  | Text size and gzip size versus the current wire                                        | Bytes                                                                                             |
| U7  | Cost of canonical checks (literal-slot scan, `-0` rejection, table first-use order)    | Decode time with and without the checks, to inform the canonical-versus-unambiguous decision      |
| U8  | Execution-history sensitivity (PA §0.4)                                                | Fresh versus polluted process                                                                     |

---

## 7. Alternative designs worth measuring (ranked)

All four remove in-band sentinels, keep integer control in private tables, and use one native
`JSON.stringify` and one `JSON.parse`.

### A (rank 1): flat positional wire, the candidate's conservative variant

- **Document.** `[root, shapes, layouts, descriptors, payloads]`.
  - `descriptors`: all-Smi, values < 10⁹, one per node.
  - `layouts`: interned; each is (node kind, shape id when a record, alternating literal/reference
    run lengths with an open last run).
  - `payloads`: the dense array itself; a record's value array; a Map's `[k, v, …]`; a Set's
    `[…]`; a Date's time; a buffer's base64; a sparse array's `[len, idx, tok, …]`.
- **Special scalars and bigint.** Shared nodes, one kind each.
- **Zero-copy.** Only hole-free dense arrays. Records stay value arrays plus shapes, so one record
  path covers ordinary and null-prototype records (DRY).
- **Why first.** It keeps preorder ids, the explicit frame stack and the flat rows that the proofs
  describe, and changes only token typing. It isolates the questions in U1–U3.

### B (rank 2): tree-inlined payloads with implicit preorder ids and references only for repeats

- **Model.** This is the CBOR tag 28/29 model, pickle `MEMOIZE` and YAML anchors.
  - A composite's **first** occurrence is written inline as a JSON array (or a JSON object for
    records), in the parent slot.
  - Later occurrences are integer references to the preorder id.
  - Preorder ids need not be written: they equal the position in the descriptors array, which lists
    one layout per composite in preorder.
  - In a slot, a JSON composite always means "inline node" and a number in a reference position means
    "repeat". The layout only has to mark which numbers are references.
- **Expected benefit.**
  - Tree-shaped data, the common case, needs **no references at all**. Each tree edge is free instead
    of costing one integer.
  - JSON.parse builds the nested structure natively, and arrays of records become JSON siblings, so
    `ParseJsonArray`'s map feedback hits (§4.2).
- **Risks.**
  - Deep graphs become deep JSON. Node 24's default stringifier is recursive with a stack check (PA
    §1.1), so very deep chains could throw where today's flat wire cannot.
  - The decoder needs an explicit-stack walk.
  - The proofs change more, because the row structure changes.
  - Possible mitigations: (i) measure the depth limit on Node 24/25/26; (ii) a fixed, deterministic
    depth cut-off that falls back to references, which keeps the output canonical but adds a rule.
- **Measure** against A on records-1k, the depth-200 chain and a 10⁵-deep chain.

### C (rank 3): CSR reference positions instead of interned layouts

- **Model.** No layout table. Each node's descriptor is (kind, shape) plus a reference count, and one
  flat all-Smi `refSlots` array lists reference slot indices for all nodes in order, as in Arrow
  dense-union offsets or compressed sparse rows.
- **Benefit.** Encode cost per reference is one `push`, with no interning probe. Decode is O(references)
  with no per-call layout cache.
- **Cost.** About one small integer per reference in addition to the reference id.
- **Purpose.** If U2 shows interning cost dominating encode, C is the fallback with the same safety
  properties.

### D (rank 4, safety baseline / control): syntactic-channel references

- **Model.** A reference is the singleton array `[i]`. Composites never appear inline, so a JSON array
  in a slot cannot be data. Specials and bigint are nodes as in A.
- **Properties.**
  - No layouts.
  - Kind is decided by JSON type alone, giving exactly **one source of truth**: the literal-slot scan
    and the reference check are the same test.
  - The encoder can reuse one `[i]` object per referenced node, a per-call bounded cache, so encode
    allocates once per node rather than once per reference.
- **Expected outcome.** JSON.parse still allocates one array per reference occurrence. In-repo evidence
  (SWA: removing `[-1]` arrays gave 0.233× decode) predicts a large decode loss on reference-heavy
  graphs.
- **Purpose.** Measure it as the control that quantifies what A's layouts buy.

### Considered and not recommended

- **devalue-style "every slot is an index", with primitives in the table.** Every scalar costs an
  extra integer and an indirection, payloads cannot be reused zero-copy, and literal strings move
  away from their slots.
- **Reviver-based decoding**, such as flatted's, or `context.source` for bigints. It forces the
  iterative source-tracking parser and a JS call per value (§4.2).
- **String-prefix escaping** (Transit, EJSON `$escape`, telejson). It adds a JS check per string and
  has an escaping-bug history.
- **Columnar shredding per shape** (Dremel or Arrow style). This is still an analogy, for the reasons
  in PA §4: it conflicts with preorder ids and needs a large proof restatement.

---

## 8. Design principles the sources support

1. **A value never decides its own interpretation; position or schema does.** Sources: Avro
   ("does not include type information"; unions by schema index); Arrow (out-of-band validity and
   union type ids; masked slots may hold any value); Protobuf field tags; LangSec "overloaded field"
   (Momot et al. 2016); failures in Extended JSON, Transit, telejson and YAML 1.1.
2. **Control addresses private tables by validated integers, never data by names.** Sources:
   superjson CVE-2022-23631; devalue CVE-2025-57820; ungap's name lookup; pickle and Java
   name-based reconstruction.
3. **Use the one grammar both ends already share, and add no second lexer.** JSON.parse is fixed and
   non-extensible (SPEC ParseJSON). LangSec Principle 2 (parser equivalence) and Principle 1 (minimal
   power): a deterministic context-free grammar, no escapes, no regex-typed scalars.
4. **Explicit tables with explicit indices beat implicit stream-order tables.** Smile's 2025 erratum,
   Transit's cache and CBOR stringref's mandatory indexing show the fragility. CBOR tag 29 and packed
   CBOR use explicit indices. Preorder implicit ids, as in pickle `MEMOIZE` and this codec, are safe
   when the order is a proved invariant.
5. **Typed references: check the target's kind, not only the range.** Sources: devalue CVE-2026-22774
   and seroval GHSA-9355; RFC 8949 §5.3.2 ("Inadmissible type for tag content").
6. **Allocation proportional to input text.** Sources: RFC 8949 §10; Cap'n Proto traversal limit;
   devalue and seroval sparse-array and length advisories; PA §0.6.
7. **Recognize fully before effects; parse into the final type.** Sources: Momot et al. ("shotgun
   parsing"); "Parse, don't validate" _(blog)_. For this codec, only fresh objects are created before
   acceptance.
8. **Unambiguous is mandatory; canonical is a separate, costed decision defined on the JSON value
   tree.** Sources: RFC 8949 §4.2 and §10; RFC 8785; RFC 7493; RFC 8259 §4; SPEC duplicate-key rule.
9. **Keep control as small integers (< 10⁹), all-integer arrays where possible, and no per-value
   wrapper arrays.** Sources: V8 `kMaxSmiLength = 9` and the number-array fast path (§4.1); PA §1.2
   (array per token); SWA measurements.
10. **Stay on native fast paths: no replacer, reviver or space; no objects with integer keys in
    stringified output; no ropes** (PA §0.2). Sources: V8 stringifier and parser source (§4.2, §4.4).
11. **Reuse JSON.parse results only where reuse is semantically identical: hole-free arrays and plain
    objects, patched through own properties only.** Sources: SPEC PropertyDefinitionEvaluation in
    ParseJSON; V8 `DefineOwnPropertyIgnoreAttributes`; elements and representation transitions (§4.3).
12. **Choose kind representations by density; interning amortizes them.** Sources: Roaring (array,
    bitmap and run containers); Parquet hybrid; UBJSON per-container type; FlatBuffers vtable dedup.

---

## Sources fetched or read for this review (beyond PA)

- V8 source: N24 `src/json/json-parser.cc`, `json-parser.h`, `json-stringifier.cc`,
  `objects/value-serializer.cc`, `objects/elements.cc`, `objects/property-details.h`,
  `flags/flag-definitions.h`; V8M `src/json/json-parser.cc`, `json-parser.h`, `json-stringifier.cc`;
  N25/N26 `json-parser.cc` (grep only).
- ECMA-262 `spec.html` (tc39/ecma262 main): `#sec-json.parse`, `#sec-ParseJSON`,
  `#sec-runtime-semantics-propertydefinitionevaluation`, `#sec-json.rawjson`,
  `#sec-serializejsonproperty`.
- RFC 8949, RFC 8259, RFC 7493, RFC 8785 (rfc-editor.org text); draft-ietf-cbor-packed-19;
  cbor.schmorp.de value-sharing and stringref.
- Transit format README; Smile specification; MessagePack spec; MongoDB Extended JSON spec; Meteor
  `packages/ejson/ejson.js`; Amazon Ion symbols spec; Falcor JSON Graph; draft-pbryan-zyp-json-ref-03;
  JSON-LD 1.1 §3.1; YAML 1.2.2 §3.2–3.3; PEP 3154; Avro specification (`Specification/_index.md`);
  Arrow Columnar Format; Parquet encodings.
- Papers (DOIs checked against OpenAlex): Sassaman et al. 2011 (_;login:_, PDF read); Sassaman et al.
  2013 (10.1109/JSYST.2012.2222000); Momot et al. 2016 (10.1109/SecDev.2016.019, PDF read); Melnik et
  al. 2010 (10.14778/1920841.1920886); Durner et al. 2021 (10.1145/3448016.3452809, PDF read);
  Langdale & Lemire 2019 (10.1007/s00778-019-00578-5); Lemire 2021 (10.1002/spe.2984); Keiser &
  Lemire 2024 (10.1002/spe.3313); Adams 2018 (10.1145/3192366.3192369); Chambi et al. 2016
  (10.1002/spe.2325); Lemire et al. 2016 (10.1002/spe.2402); Chambers et al. 1989
  (10.1145/74877.74884).
- Libraries: devalue `src/parse.js`, `src/constants.js`, `CHANGELOG.md` and GitHub security
  advisories; flatted `esm/index.js`; @ungap/structured-clone `esm/types.js` and `esm/deserialize.js`;
  seroval `core/types.ts`, `core/constants.ts` and advisories; superjson README and
  GHSA-5888-ffcr-r425; telejson README and `src/index.ts`.
- Secondary: jsonic.io guide (§4.6); Sonar blog on Blitz.js; v8.dev blogs (react-cliff 2019,
  elements-kinds, json-stringify 2025); socket.dev diff of @ungap/structured-clone; Clojurians Slack
  log.
