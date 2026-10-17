# Positional wire: design proposal (2026-10-17)

Status: proposal for approval. No runtime or proof change has been made. Measurements below
are exploratory single-process prototypes on Node 24.22.0, not decision evidence.

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
