# Pre-registered hypotheses (frozen before decision rounds; 2026-10-17)

Control: b6299905 (consumer bundle sha256 09ffefd2…5940, 12,870 B min / 4,972 B gzip).
Harness: scratchpad/harness (worker sha recorded per round), manifest-v1 (fixed call counts, sha fdb25a5e…).
Exploratory decomposition (single process, not decision evidence): native JSON.stringify is 9–28% of
encode on graph-shaped fixtures and 50–90% on primitive/string arrays; JSON.parse is 30–90% of decode.

| Id  | Mechanism                                                                                                                                            | Counted work removed                                                                 | Expected effect                                  | Affected                         | Falsifier                                                            | Differs from rejected work                                                                                                               |
| --- | ---------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------ | ------------------------------------------------ | -------------------------------- | -------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------- |
| M2  | Per-call trie over interned own-key strings replaces JSON.stringify(keys)+string Map                                                                 | one JSON.stringify(keys) string build+hash+compare per record                        | records/DAG/collection encode −15…−30%           | every record-bearing workload    | ratio vs control within copy variation, or any non-record regression | no emission change; wire byte-identical. A prior "shape-trie" experiment is referenced in HANDOFF but its artifacts are missing          |
| M1  | Containers tokenize children in place; yield only when a child pushed a frame; arrays build rows directly (no entries buffer + spread); local cursor | one outer-loop dispatch + frame.input round trip per child; one array copy per array | primitive-array encode −15…−30%; records −5…−15% | arrays, records, collections     | sparse/hole scans regress; any observation-trace difference          | not an emission change; native whole-document stringify retained. A "synchronous-child"/"array-row" experiment is referenced but missing |
| M3  | recognize returns packed int (no {tag,detail} object)                                                                                                | one small allocation per object                                                      | ≤5%                                              | graph-heavy                      | no gain beyond copy variation                                        | —                                                                                                                                        |
| M5  | Frames created with full fixed field layout                                                                                                          | polymorphic frame maps in main loop                                                  | mixed graphs/history mode                        | graph-heavy, history             | no gain in isolated or history mode                                  | frame-reuse (rejected/mixed) pooled frames; this keeps per-node frames                                                                   |
| D2  | Dense array decode: shell = row.slice(2) then replace non-literal tokens in place                                                                    | per-element read() call and holey store for literal elements                         | primitive-array decode −10…−20% of JS part       | numeric/strings/nested decode    | decode regression on reference-heavy arrays                          | —                                                                                                                                        |
| W1  | Negative non-integers emitted literally (only negative integers escaped)                                                                             | [-7,x] array per negative fraction                                                   | negative-fraction-heavy encode/decode large      | scalar-boundaries, geo-like data | —                                                                    | WIRE CHANGE: requires explicit user approval before adoption                                                                             |

Acceptance (codec): on the final sources, two independent complete rounds; a fixture/op whose
candidate/control median ratio exceeds 1.03 in both rounds AND exceeds the identical-copy
variation in both rounds is a regression that blocks adoption unless explained by a
documented, reproduced control effect. Targets must improve in both rounds beyond copy variation.
Core snapshot/reconcile/produce: ab-time.py two 8-pair rounds, 3% guard (the codec changes do not
touch core sources; bundles must be byte-identical for snapshot/reconcile/produce exports).

## Addendum after registration (recorded as it happened)

- The independent review found that the per-key trie allocates one `Map` per key on new
  shapes. Two dictionary diagnostics (`dict-10k`, `dict-records`) were added with frozen
  baseline counts (`manifest-v2.json`), and the path-compressed trie replaced M2 before the
  decision rounds F3/F4. Its proof (`ShapeRadix.lean`) was checked before the runtime edit.
- Decode ratios for unchanged decode code moved in mixed-operation processes. A decode-only
  manifest (same counts) was added to separate decode cost from GC work induced by encoding.
- Core `ab-time.py` rounds at 20 batches could not resolve the 3% guard (A/A up to +5.0%).
  The batch count was raised to 60 after that observation; all rounds are retained.
- D2, D7, M3, M6 and W1 were screened and not adopted; see ENCODER-CAPTURE.md.
