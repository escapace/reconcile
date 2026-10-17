# Encoder traversal, direct rows and shape trie

The encoder tokenizes container children in place, builds array rows directly and interns
record shapes in a per-call path-compressed trie. The wire is byte-identical to the previous
encoder. These modules were checked before the corresponding runtime edits; existing theorem
statements are unchanged.

## Checked finite claims

`Inline.lean` models the in-place traversal over a static graph `g : Nat → List Nat` of
object children, with a `leaf` predicate for native kinds captured without a frame
(`leaf n → g n = []`).

- `scan_refines`, `inline_step_refines`: one in-place step (tokenize seen and leaf children,
  stop after entering a non-leaf child or at the end) is a composition of existing
  `SerializationDFS.step`s on the lowered configuration.
- `inline_run_refines`, `start_refines`: any fuelled in-place run refines the stack machine.
- `steps_terminal_unique`: the stack machine is deterministic, so runs ending with an empty
  stack have one trace and one memo.
- `inline_matches_recursive`: a terminating in-place run from a fresh root has exactly the
  `enter`/`edge` trace and memo of the recursive specification `Recursive`. This is partial
  correctness under the `done` premise; termination is not proved, and the `decide`
  examples only exercise small graphs.
- `append_row_exact`, `append_all_exact`, `finish_direct_exact`, `direct_rows_exact`: the
  runtime row layout (`[2, 0, ...values]` while dense, `sparseRow` to `[3, 0, i, v, ...]`,
  slot 1 patched at the end) equals the previous entries-buffer construction for every
  sequence of present elements and captured length.

`ShapeRadix.lean` models the active path-compressed trie over any key type with decidable
equality, so UTF-16 code-unit sequences, including lone surrogates, are covered. An edge is a
first key, the rest of its label and a subtree; `setR` creates one leaf for an unmatched
suffix and splits an edge where a shape diverges or ends inside it, as `shapes.ts` does.

- `strip_some_iff`, `strip_append`: label matching is prefix stripping.
- `getR_single`, `getR_split`: splitting an edge into a prefix and a middle node preserves
  the denotation of every query.
- `getR_setR`: storing an id changes the denotation only at the stored key sequence.
- `radix_matches_memo`, `radix_matches_signature`: the path-compressed trie assigns the same
  first-occurrence ids as the signature memo for every sequence of shapes.

`ShapeTrie.lean` proves the same result for a per-key trie with one node and one `Map` per
key. That variant was screened first and is inactive: a record used as a dictionary with
10,000 unique keys allocated one `Map` per key and encoded about 37% slower than the
signature memo in a single-process check. The proof is retained as research.

The audit covers these modules through the Lake roots. The structural bridge compares the
actual encoder's wire with the Lean oracle on 99 graphs, which exercises shape ids and row
layout end to end.

## Runtime correspondence obligations

The static graph omits most application observations: `length` reads, `in` checks, getters
on primitive slots, iterator `next`/`return`, Map entry destructuring, the trailing
`getOwnPropertySymbols`, native leaf captures and IteratorClose. The theorem constrains the
order of entering and referencing objects, not those reads. The runtime argument for them is
a local simulation:

1. **Local simulation.** Previously the only work between an advance returning `false` and
   its re-entry was the driver's `token(frame.child)` and private stores. The new advance
   calls `token` at that same point. No application-visible operation moves, and
   `frame.active` is unchanged across a yield, so the frames closed on a throw are the same at
   every throw point.
2. **`pushed()` is exact.** Every frame is a fresh object literal; `ids` lets an object push
   at most once per call; `token` pushes at most one frame and never pops; `recognize` and leaf
   captures never touch the stack; an advance runs only on the stack top. So `pushed()` holds
   exactly when the child was a fresh, non-leaf object whose `recognize` returned.
3. **Leafness is fixed per call.** `recognize` runs once per object, which justifies a static
   `leaf` predicate; every leaf kind has no child edges.
4. **Reads before edges.** Primitive slots are not in `g`. A Map entry is destructured before
   the key's subtree runs, and URL parameters and view buffers are read inside
   `readURL`/`readView` before their child is tokenized, as before.
5. **Shape trie premises.** `JSON.stringify` is injective on string arrays and observes
   nothing on fresh key arrays (for the previous memo). Trie nodes are fresh per call and
   reachable by one path, so the runtime's in-place `Map.set` and edge split agree with the
   functional `setR`; label slices of a shared keys array are never mutated; the next id is
   `shapes.length`. The runtime walk is a single pass that changes nothing when the shape is
   found and otherwise performs exactly `setR`'s leaf creation or split, so it equals
   `internR`.

Obligations 1–5 are checked empirically, not proved. A seeded fuzz compared 20,000 random
sequences of record shapes (prefixes, extensions, permutations, lone surrogates, `__proto__`)
byte for byte against the previous encoder. A differential checker compares the
previous and new bundles on every observation (proxy traps, getter receivers, iterator
`next`/`return`, destructuring) and injects a throw at each observation index; an
independent reviewer's seeded differential suite compared 4,044 cases, including mutation by
getters, custom and native-revisiting iterators, throwing `return`, cycles, aliases and
native kinds. The public serialization tests cover representative traces.

With patched built-ins, which the contract excludes, observations differ: the previous array
spread called `%ArrayIteratorPrototype%.next`, and the previous shape signature called an
inherited `toJSON` once per record. `recognize` traps now run one JavaScript frame deeper, so
the depth at which a stack-overflow `RangeError` occurs can move.
