# Positional wire

The active codec writes `[literal]` for a JSON-literal root and `[control, payloads]` otherwise,
with the root as node 0. Every value position is a slot whose kind, literal or reference, comes
from its node's layout, never from its value, so no number or string is reserved. The control
table holds each node's layout id, the number of shapes, each shape framed by its length, then
each layout framed by its length. A layout is a tag, a key for records, views and Temporal
values, and alternating slot-kind run lengths that start with literals and leave the last run
open. These models were checked before the corresponding runtime edits.

## Checked finite claims

`Positional.lean` works over an abstract wire value type `W` whose literal and natural-number
readings each round-trip and need not be disjoint.

- `kinds_runs`, `runs_kinds`: run encoding is a bijection between slot-kind lists and
  canonical run lists.
- `decode_encode_slots`, `encode_decode_slots`: slot decoding inverts slot encoding when every
  reference is in range, and accepts nothing else.
- `decode_encode_relaxed`: the runtime's decoder, which uses the tables as given, inverts the
  encoder. `decodeNodes_sound` states what every accepted document means: each payload is the
  slot encoding of its decoded node, each layout id names that node's layout and every
  reference is in range.
- `decode_encode_control`, `encode_decode_control`: the control table splits into exactly the
  layout ids, shapes and layouts it was built from, and every accepted control table is the
  framing of what it splits into. `frame_unframe` and `unframeN_frame` are the framing laws.
- `renumber_first_use`: renumbering the encoder's provisional layout ids (numbered as
  containers complete) in node order yields the first-use table.
- `sparse_roundtrip`: a sparse array's presence runs expand to exactly its present indices.
- `typedRef_sound`: a view's buffer and an owned parameter list's URL reference a node of the
  required kind.

`Preorder.lean` proves that the decoder's reverse scan, with one subtree end per node, accepts
exactly the documents whose depth-first traversal from node 0 enters `0, 1, …, n - 1`
(`preorder_iff`, lifted to the runtime table fill by `check_iff`), so every node is reachable.
`encoder_canonical` shows the encoder's entry-order numbering passes.

## Canonical theorems retained as research

`decode_encode_document`, `encode_decode_document`, `intern_canonical`, `canonical_intern` and
`sparse_canonical` prove that a decoder which also requires duplicate-free tables in first-use
order accepts exactly one encoding per graph. The runtime does not perform those checks: tables
may be reordered, repeated or unused, a shape may repeat a name (the first position and last
value are kept, as for an object literal) and a shared scalar may appear as several nodes. The
canonical theorems remain true of the encoder's output, which still uses first-use tables, but
they do not describe what the decoder accepts.

## Executable bridge

`Oracle.lean` splits each runtime document with the proved `decodeControl`, decodes it with
`decodeRelaxed`, `kindsOf`, `presentFrom` and the `Preorder` check, and re-emits it with
`encodeDocument`, `encodeControl` and `presenceRuns`. `scripts/check-serialization-lean.ts`
requires the re-emitted text to equal every `stringify` output in its corpus, requires Lean and
the runtime to reject every malformed document in its invalid list, and requires both to decode
every document in its non-canonical list to the same graph. Its bridge domain is records,
null-prototype records, dense and sparse arrays, JSON literals and shared scalar nodes.

## Runtime obligations

`JSON.parse` is trusted to produce the parsed tree; the proofs do not model its grammar or
number rounding, and the bridge's hand-written importer uses Lean JSON numbers. Literal
validity (no composite, `-0` or non-finite number in a literal slot), control integers, bigint
decimal text, Date and Duration values, native view bounds, URL ownership, Temporal payloads
and collection folding are checked by runtime code and tests; collection folding has its own
[proof and bridge](COLLECTION.md). The encoder's traversal, observation order and shape trie are
covered by [the encoder proofs](ENCODER.md); emission into slots and layouts is a runtime
obligation checked by the bridge's exact re-emission. Dense arrays reuse the `JSON.parse` array;
sparse arrays are allocated by native `Array` with their declared length, which is an accepted
memory cost outside the finite model. No whole-JavaScript correctness, memory or speed claim
follows.
