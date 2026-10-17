# Serialization proofs

The active codec uses the [positional wire](POSITIONAL.md): slot kinds come from interned layouts, so no number or string is reserved, and the decoder uses the control table as given. The compact scalar tokens below and in [COMPACT.md](COMPACT.md), and the three-component document further down, are retained research for the previous wire; no runtime path uses them.

The [collection reconstruction proof and native bridge](COLLECTION.md) cover repeated
Map keys and Set members, native insertion order and every attempted token read.

The [encoder traversal, direct-row and shape-trie proofs](ENCODER.md) cover in-place child
tokenization, the array row layout and per-call shape interning, with their runtime
correspondence obligations.

# Three-component document and inline reconstruction checks

`Reconstruction.lean` was checked before the corresponding runtime parser changes. It imports existing finite graph definitions without altering retained proofs. The document model is exactly `(root, shapes, nodes)` with no format identifier. The proof adds no arbitrary quotas, timers, counters or separate validation pass.

## Established finite obligations

- `token_valid_iff_decode`: the finite reference-bound predicate agrees with actual existing token-decoder success. Atoms pass unchanged; reference r requires r < actual table length.
- `resolve_allocated`: a valid finite node ID resolves to the corresponding already-allocated handle. `resolve_identity` preserves aliases and nonmerging when the supplied handle table is injective. Native allocation freshness is an explicit premise, not a proved JavaScript fact.
- `cached_shape_check_exact`: checking a selected shape through a per-call memo is equivalent to checking that selected shape directly, provided previously remembered IDs were valid. `remember_shape_sound` preserves that invariant when remembering a successful check. Nothing scans or constrains unreferenced shape entries.
- `record_exact`: existing ordered shape expansion recovers exact ordered entries when the selected shape has those keys. The underlying expansion rejects nonexistent shape IDs and unequal key/value arity. Duplicate-key validation is separate and performed on the selected shape's first use.
- `view_link_requires_buffer`: a successful view dependency lookup implies an in-bounds ID, a buffer-kind target and exactly that target's allocated handle. It does not accept an arbitrary allocated object merely because its ID exists.
- `view_extent_bound`: offset ≤ buffer length and count ≤ floor((length − offset) / unit) imply offset + count × unit ≤ length. Runtime also checks positive native unit size and alignment; the theorem does not construct a native view.
- `empty_resize_exact`: resizing an empty sparse shell to L has the same finite length and absent slots as allocating a length-L sparse shell.
- `write_length`, `write_presence`, `write_other`: an in-bounds write preserves length, installs the requested present value and leaves other slots unchanged. Presence is `Option value`, so a present undefined-like value remains distinct from absence.
- `fill_length`, `sparse_fill_same`: successful ordered sparse filling preserves declared length; replacing initial length-L allocation with empty allocation followed by length assignment yields exactly the same result.

The sparse model is a finite declared length plus an index-to-optional-value function. It does not allocate L entries. Its checked example distinguishes an absent slot from a present `none` payload. The model does not claim actual JavaScript arrays use this representation internally.

## Inline checks and phases

The intended runtime keeps allocation, dependency linking and structural filling phases. These phases are construction dependencies, not a separate document-validation framework. Node tags, arity and payloads are checked before their immediate use. Shape keys and duplicate keys are inspected only when the shape is first referenced by a record. Tokens are checked when read. Sparse indices are checked immediately before writes. Views check the referenced node's kind and native bounds/alignment before construction.

The per-call shape memo has a fixed document as its semantic input; the proof's soundness premise requires that entries cannot change after being marked valid. JSON.parse produces the private input tree used by the parser. If implementation callbacks or later mutations could change that tree, this lifetime assumption would need to be re-established. The proof does not authorize retaining shape-validation caches across documents.

Removing arbitrary policy quotas does not require inventing a new finite semantic limit. The native JavaScript array-length bound 2^32 − 1 and valid native view constructor ranges remain necessary representation conditions. The theorem uses natural-number lengths; the bridge and runtime enforce the actual array bound before assignment.

## Trust boundaries and remaining native correspondence

JSON.parse is trusted to produce the parsed JSON tree. The proof does not mechanize its grammar, numeric rounding, negative-zero handling or property construction. The envelope's three-array layout and positional extraction are executable bridge/runtime details, not a proved JSON-parser transformation.

Scalar-reference token decoding continues to rely on the retained v5 collision proof and its native Number correspondence obligations. This file's reference theorems operate after token normalization into `Token Nat`; they do not redefine which JSON numbers represent references.

The allocation table's freshness, native object/array property writes, own `__proto__` handling, actual `Array.length` semantics, collection construction, buffer bytes, native view constructors, URL ownership and Temporal payloads remain runtime obligations. The view theorem proves buffer-kind selection and abstract handle identity, not byte reconstruction or constructor execution. Sparse length/presence proofs do not prove every ECMAScript descriptor or prototype interaction.

No whole-JavaScript correctness, memory use, termination under resource exhaustion or speed claim follows. Existing source-observation guarantees and prior proof limitations remain unchanged.

## Executable bridge for the actual document

`Oracle.lean` accepts requests of the form `{"wire":[root,shapes,nodes]}`. It is adapted from the existing structural bridge and uses the actual three-component document and scalar references. Records, null-prototype records, dense arrays, sparse arrays, primitive atoms, cycles and aliases are supported; native/internal-slot nodes remain outside this bridge.

It interprets shapes on first referenced use, executing the proved `shapeCheck`, then existing `dictionaryExpand`, `decodeToken`, `decodeNode`, `encodeToken` and `encodeNode`. Sparse reconstruction additionally executes `fill(allocatedSparse(L),pairs)` and checks the resulting declared length and all present entries. It emits normalized ordered graphs and a reconstructed three-component wire document for the actual JavaScript parser. Reemission may use one shape per record and sparse encoding for arrays, so semantic equality rather than byte equality is expected.

The bridge retains no arbitrary node/edge/byte budgets or internal timer. It checks necessary structural and native-array bounds. The shared repository oracle runs it in the existing bounded check workflow. The coordinator may wrap an entire research validation round with a timeout; that is a task-execution bound, not a codec feature.

The handwritten importer/emitter remains unproved. It uses Lean JSON number semantics, so lexical negative zero, rounding and overflow can differ from JavaScript. Bigint canonicalization is narrower than the runtime's historical accepted grammar. These are known oracle-domain limits, not a claim of parser-language equivalence. Unused malformed shapes are intentionally not interpreted.

## Repository integration and reproduction

Run `pnpm check:lean` from the repository root. The existing 295-second complete-round wrapper builds all registered Lean modules, audits all declarations, and executes the shared native oracle against the typed runtime. No external experiment directory is needed.

`Serialization` is a shared oracle family: its input is a JSON array of `{ "wire": [root, shapes, nodes] }` requests, and its output is a JSON array of results. `scripts/check-serialization-lean.ts` sends 99 actual typed `stringify` documents, compares normalized ordered graph models with independent source traversal, and parses the Lean-emitted documents with the actual typed `parse`. The corpus includes deterministic cyclic/shared graphs, null records, sparse arrays, dangerous property names and special scalar values. It also checks malformed documents and an unused malformed shape.

The retained `Codec` and `Roots` modules prove finite table/token round trips, ordered dictionary expansion, and primitive-only roots. `Scalar` proves collision-free scalar reference encoding in an exact rational model. `DFS` proves recursive static observation traces refine the explicit stack, with unique memo entries; `Refinement` proves indexed continuation lowering, synchronous leaf contraction and dense-first accumulation. These statements are unchanged from the checked prototypes. `Inline` and `ShapeRadix` add the in-place traversal, direct rows and active path-compressed shape trie; the per-key `ShapeTrie` is retained inactive. See [ENCODER.md](ENCODER.md). One flexible `simp` invocation was spelled `simp only` to satisfy the repository warning gate.

The structural oracle executes the actual retained token/node decode and encode definitions, shape checks and sparse reconstruction definitions. It does not execute the whole `Graph.encode` table constructor or the DFS refinement model; those proofs are separately checked. The finite graph differential test connects imported/exported models to actual runtime values, but the handwritten JSON importer and emitter are not mechanically proved correct. Getter/iterator side effects, abrupt completion cleanup, native identity allocation and internal slots remain runtime test obligations. No whole-library verification claim follows.

## Retained sparse-shell experiments (inactive)

The active codec allocates both dense and sparse arrays with validated `new Array(length)`. Its finite starting state is `allocatedSparse length`; only present sparse entries are filled. The accepted native memory cost is outside the finite model. No descriptor seeding, MAX-index priming, length-proportional prevalidation or application quota is part of this allocation path.

`SparseShell.lean` retains checked historical statements; no active runtime branch depends on its alternative constructors. It models two candidate private fresh-array constructions. The first defines index zero with a configurable, nonwritable, nonenumerable temporary data descriptor, assigns the requested length, then deletes index zero. The second defines the final index with an ordinary writable/enumerable/configurable data descriptor, then deletes it; length zero uses the empty shell directly.

For integer lengths from zero through 2^32−1, both constructions yield exactly the empty shell with the requested length, all numeric slots absent, default length-property attributes and the original handle. Filling either result with the same ordered present entries yields the same descriptors and values as filling an ordinary fresh shell. A present undefined-like value remains distinct from a hole. Deletion is modeled as fallible for a nonconfigurable present property; the proved candidates use configurable properties. Shrinking the first candidate to zero removes its temporary index before the final harmless deletion.

These experiments required the helper to complete before the target was published to the caller's identity map or receives captured entries. The proof is valid for arbitrary subsequent entries, so selection need not inspect occupancy in advance. It does not justify scanning a source twice or delaying an observable identity-map callback. Native `Object.defineProperty`, array length assignment, deletion, fresh allocation, inherited setter avoidance, prototypes and property attributes must match the model. The caller must preserve native constructor behavior outside valid numeric lengths through its original fallback; the model's invalid-length rejection is not a proof of that fallback. No JavaScript heap representation, allocation size or performance result follows from these theorems.

`selected_shell_exact` also proves that a Boolean choice between ordinary empty-shell allocation and the last-index construction yields that same shell. This supported the experimental selection of ordinary allocation for known dense occupancy and a shared constructor for unknown occupancy; the active codec no longer makes that selection. It does not prove that a runtime density predicate is accurate; shell equality itself holds for either choice.

The inactive `prepareMax` experiment models another private sequence: define an ordinary data descriptor at index 4294967294, delete that descriptor, then assign the requested final length. `prepareMax_exact` proves the resulting shell equals ordinary empty allocation for every valid array length, including zero and 4294967295. `max_matches_last` compares it directly with the requested-final-index strategy; `max_fill_exact` preserves arbitrary subsequent ordered fills. The retained handle and default attributes follow from exact shell equality. This proof distinguishes the operation order: maximum-index deletion occurs before final resizing. It makes no claim about allocation at that temporary length or the engine's backing store. The active codec and core allocation do not use this strategy.
