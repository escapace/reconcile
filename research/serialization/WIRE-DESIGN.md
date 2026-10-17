# Positional wire: design and adoption record (2026-10-17)

Status: approved and adopted on this branch. The proposal below is kept as written; the
[adoption record](#adoption-record) at the end lists what changed during implementation, the
decision rounds and the accepted and rejected hypotheses. The exploratory measurements are the
original prototypes, not decision evidence.

## Problem

The current wire overloads values. Negative integers mean references (−(i+6)) and special
values (−1…−5), so every genuine negative number needs the escape `[-7, x]`, and bigint needs
`[-6, "digits"]`. That costs an array allocation per negative value and a check on every token,
and it makes the grammar depend on value ranges. The owner asked for a wire that shadows no
data type and uses no special strings or numbers, is safe by construction at least to the level
of `JSON.parse`/`JSON.stringify`, costs nothing in performance, is compact, DRY and MECE, and
uses the native JSON fast paths.

## Principles (sources in the research reports)

1. A value never decides its own interpretation; its position does. Every surveyed in-band
   design has a documented ambiguity or incident: MongoDB Extended JSON cannot escape a leading
   `$`; telejson reads the string `"_NaN_"` as NaN; superjson CVE-2022-23631 and devalue
   CVE-2025-57820 came from data reaching control. Avro, Arrow and Protobuf type by position or
   schema; CBOR uses a channel data cannot occupy. The LangSec taxonomy calls the defect an
   "overloaded field".
2. Control addresses private tables by validated integers, never data by names, and a reference
   is checked against the kind of its target, not only its range.
3. One grammar: `JSON.parse` and `JSON.stringify` only, with no replacer, reviver, `toJSON`,
   space argument, second lexer or escapes.
4. Control values are small integers below 10⁹, so V8 parses them inline (`kMaxSmiLength` 9),
   and integer-only control arrays stay on the number-array path. No per-value wrapper arrays.
5. Reuse a `JSON.parse` result only where reuse is semantically identical: hole-free arrays,
   patched through own elements.
6. Choose kind representations by density and intern them.

## Design

The document is `[root, shapes, layouts, descriptors, payloads]`.

- **Slots.** Every value position is a slot. A slot is either a literal, any JSON scalar that
  denotes itself (all finite numbers including negative ones, strings, booleans, `null`), or a
  reference, a node id. Which one is decided by the slot's layout, never by its value.
- **Nodes.** Every composite and every non-JSON scalar is a node. Undefined, NaN, ±Infinity,
  −0 and each distinct bigint are shared nodes, created on first use, so references are the
  only control channel and no number or string is reserved. Holes are absence, not a value.
- **Descriptors.** One integer per node, the id of its interned layout. The array holds only
  small integers.
- **Layouts.** A layout is the node kind plus, for containers, the slot kinds, and for records
  a shape id. Slot kinds are alternating run lengths starting with literals, with an open last
  run, so all-literal and all-reference containers share one layout regardless of length. The
  encoder interns layouts with integer tries; it builds no signature strings.
- **Payloads.** One per node, in node order: the dense array itself (no header; length is
  implied); a record's value array (keys come from its shape); a Map's alternating keys and
  values; a Set's members; a sparse array's length, present-index runs and present values; a
  Date's time; a buffer's base64 text; a view's buffer reference, offset and length; and so on.
  Each node kind has one fixed payload schema.
- **Root.** The root is one slot whose kind uses the same run encoding.

Decoding allocates nodes, links dependent natives, then fills references, as today. A hole-free
array payload is reused as the decoded array, so only its reference slots are written. Records,
Maps, Sets and sparse arrays are constructed. Records stay value arrays: one path serves
ordinary and null-prototype records.

## Safety by construction

- **Unambiguous.** Each slot has exactly one interpretation, fixed by its layout. There is no
  escaping, so there are no escaping bugs, and every JSON scalar round-trips unchanged.
- **Typed control.** References are integers checked for range and for the kind of their
  target (a view's buffer must be a buffer node, a URL parameter owner a URL node).
- **No effects before acceptance.** The decoder creates only fresh objects; `__proto__` stays an
  own data property; no getter, setter or user code runs; iteration is explicit, with no
  recursion.
- **Canonical, if chosen.** Rejecting composites and `-0` in literal slots and requiring
  first-use table order makes every graph have exactly one accepted encoding. That costs one
  type scan per payload element (about 4 ns per element in a prototype); see the decision
  points.
- **Zero-copy equivalence.** `JSON.parse` defines each element with CreateDataProperty, so a
  reused array is an ordinary extensible array with writable, enumerable, configurable own
  elements and `Array.prototype` — the same observable result as allocating and filling.

## Exploratory measurements

| Question                                              | Result                                                                                                                                                                                                                                           |
| ----------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Zero-copy dense arrays                                | `numeric-10k` decode 254 µs vs `JSON.parse` 253 µs (production today about 361)                                                                                                                                                                  |
| Negative numbers as literals                          | `scalar-boundaries` decode 362 µs vs 874 today; text 65,822 vs 83,498 characters                                                                                                                                                                 |
| Records as JSON objects instead of value rows         | decode faster on uniform records (490 vs 769 µs), slower with varied shapes (874 vs 594) and floats; encode up to 2.2× slower; text up to 2.3× larger. Rejected                                                                                  |
| Tree-inlined first occurrences (CBOR tag 28/29 model) | 10–45% smaller text, but decode slower on every fixture, and Node 24's default `JSON.stringify` throws `RangeError` at nesting depth 10,000 while the flat wire handles 100,000. Rejected                                                        |
| Replacer, `toJSON` or reviver as the traversal        | stringify replacer 4–8×, a single metadata `toJSON` restarts the document on the slow path (up to 3.6× with the fast path), reviver 15–25×; over source objects they also read `toJSON`, skip non-enumerable keys and cannot see holes. Rejected |
| Layout interning                                      | 1–5 distinct layouts on most fixtures; 65 on `records-varied`; one per record only where every record has unique keys                                                                                                                            |

## Risks to measure

- Per-node encode cost of run tracking and interning on deep chains of tiny nodes.
- Layout growth for fields that alternate between literal and reference.
- Writing a reference into an array that `JSON.parse` made a double array copies and boxes it
  once.
- The canonical type scan on many short arrays.
- Sparse `new Array(length)` allocation is unchanged and remains a separately accepted risk.

## Plan after approval

1. Lean first: the slot typing judgement, run partitioning, layout interning in first-use order,
   decode ∘ encode identity on the finite graph model, canonical injectivity, and typed
   references; the existing models stay as retained research.
2. Runtime in a scratch arm: encoder emission (capture and observations unchanged), decoder,
   updated structural bridge and wire tests.
3. Semantic checks: trace and fault differential on encoding, graph-fidelity and malformed-input
   corpora on decoding.
4. Full measurement rounds against the current codec and devalue, isolated, history and
   fast-path modes, with identical-copy controls; then gates, documentation and a commit.

## Decision points

1. Canonical (reject non-canonical literal slots, about 4 ns per element) or unambiguous only
   (accept any JSON scalar or composite a literal slot holds, with `JSON.parse`-equal safety).
2. Confirm records as value rows and the flat table; the measurements above reject the
   alternatives.
3. Sparse-array allocation stays as accepted, or is revisited separately.

## Adoption record

### Changes from the proposal

- **Document.** `[literal]` for a JSON-literal root, otherwise `[control, payloads]` with the
  root as node 0. One control table replaces the four tables: each node's layout id, the shape
  count, each shape framed by its length, then each layout framed by its length. The decoder
  reads shapes and layouts in place by offset (`Positional.lean` `decode_encode_control`,
  `encode_decode_control`).
- **Decision point 1: neither extreme.** Literal slots stay checked (no composite, `-0` or
  non-finite number), as do the run grammar, control integers, reference range and kind, URL
  ownership and the depth-first node numbering (`Preorder.lean` `preorder_iff`), which makes
  every node reachable. Table distinctness and first-use order are not checked: tables are used
  as given, so reordered, repeated or unused entries, a name repeated within a shape (first
  position, last value) and repeated shared scalars are accepted with one meaning each
  (`decode_encode_relaxed`, `decodeNodes_sound`). The encoder still writes first-use tables, so
  equal graphs still give equal text. The canonical theorems are retained as research.
- **Decision point 2.** Records stay value rows over interned shapes; the flat table is the
  control table above.
- **Decision point 3.** A sparse array whose present values are fewer than half its length
  grows from an empty array, filled in ascending order, and then takes its declared length;
  a denser one is still allocated at its length. Holes and the accepted memory cost are kept.
- **Encoder.** Layouts without runs are interned by tag and key in a per-call table; layouts
  with runs go through a scratch key and an integer radix lookup before interning. Constant
  nodes share one frozen empty payload. Output is segmented only around base64 of at least
  256 characters, which skips the serializer's escape scan.

### Decision rounds

Pre-registered rule and harness as in
[ENCODER-CAPTURE.md](ENCODER-CAPTURE.md#method): a cell is a regression when it is above
1.03 and outside the identical copy's range in every round. Evidence:
[wire-design-evidence](wire-design-evidence/README.md).

| Rounds                                        | enc   | encc  | dec   | rt    |
| --------------------------------------------- | ----- | ----- | ----- | ----- |
| W3+W4 isolated, vs previous wire (geomean)    | 0.991 | 0.980 | 0.898 | 0.952 |
| H5 history mode, vs previous wire             | 1.063 | 1.037 | 0.872 | 0.956 |
| FP2 `--json-stringify-fast-path`, vs previous | 1.042 | 1.051 | 0.907 | 0.972 |
| DV4+DV5 vs devalue (30 fixtures)              | 0.508 | 0.490 | 0.760 | 0.569 |

Against the previous wire, decoding is faster almost everywhere, and the wire is 12.5% smaller
by geometric mean (half the size on arrays with one hole). Encoding regressed in every round on
`mixed-10k` (1.6–2.3×), `dict-records` (1.5–1.6×), `records-small` (1.1–1.5×), `rich`
(1.3–2.0×) and `undefined-10k` (1.1–1.3×), and on `views-shared` encode in the isolated rounds
(1.15–1.2×). These documents are dominated by values the previous wire wrote in-band (negative
sentinels for undefined and special numbers, `[-6, digits]` for bigint) or by per-call setup;
here each is a shared node with a layout id, and distinct bigints are interned by value
(about 90 ns each). Profiles show no single hotspot. The minified bundle grew from 13.5 kB to
17.3 kB (5.2 to 6.6 kB gzip).

Against devalue, 97 of 120 cells were more than 5% faster in both rounds. Cells more than 5%
slower in both rounds: `scalar-boundaries` decode (1.5–1.9×, accepted), `records-small` decode
(1.14–1.30×, previously 1.45×; a longer text for native parsing), `rich` (1.05–1.37×) and
`views-shared` decode and encode (1.06–1.18×). `binary-1m` read 1.07–1.25× in these rounds
but 0.98–1.06× against the previous wire with the copy control, so it is attributed to arm
interleaving, not the codec.

### Hypotheses

Accepted: positional slots with shared scalar nodes; one flat control table read by offset;
relaxed table checks with the numbering check kept; density-based sparse allocation; tag-keyed
interning of run-free layouts; a shared empty payload for constants; an explicit stack index
for run boundaries instead of shrinking the array; array children for integer radix keys
instead of a `Map`; segmenting output only at long base64.

Rejected or not pursued:

- First flat-control prototype that sliced layouts out of the control table: not clearly better.
  Adopted later with in-place offsets.
- Literal deduplication: not pursued by decision.
- A `Map` for integer radix children: slower than array children.
- Building the control text from separately serialized parts: about 0.2 µs slower per tiny
  document, within noise on large ones.
- A presized control array and lazily created radix roots: within noise.
- Dropping bigint interning: would remove about 90 ns per distinct bigint but changes the
  output for repeated bigints. Not pursued.
