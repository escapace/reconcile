# Wire design evidence

Supporting material for [WIRE-DESIGN.md](../WIRE-DESIGN.md), now adopted.

- `wire-prior-art.md`: primary-source review of graph and type-annotation encodings, LangSec,
  per-slot kind representations, native `JSON.parse`/`JSON.stringify` internals in V8 13.6 and
  V8 main, and JavaScript serializer advisories. Produced by a research agent; it cites its
  sources, but not every engine claim was independently re-verified.
- `wire-microbenchmarks.tar.gz`: the exploratory single-process scripts behind the proposal's
  measurement table (`micro.mjs` records as rows vs objects and zero-copy arrays, `tree.mjs`
  flat vs tree-inlined, `oneloop.mjs` and `meta-tojson.mjs` replacer, `toJSON` and reviver
  costs, `replacer-trace.mjs` native observation trace, `runs.mjs` layout counts). They import
  the harness corpus from `../encoder-capture-evidence/harness.tar.gz` (extract both side by
  side). Results are not decision evidence.
- `harness.tar.gz`: the decision-round harness, archived unchanged (extract it to get
  `harness/`); method as in [the encoder capture evidence](../encoder-capture-evidence/README.md#method).
  Absolute scratch paths in receipts refer to that environment and no longer exist.
- `rounds/`: each decision round's design, receipts (`bounded-receipt.json` is the 295-second
  wrapper), median-ratio table and gzip summary, with per-batch samples in `<round>.csv.gz`.
  Arms: `baseline` and `copy` are the previous wire (identical bytes at two paths),
  `positional` the adopted codec, `devalue` devalue 6.0.3 with its portable base64 backend.
  W3 and W4 are isolated rounds, H5 history mode, FP2 isolated under
  `--json-stringify-fast-path`, and DV4 and DV5 isolated rounds on 30 fixtures against devalue.
- `sizes/`: minified and gzip sizes of each bundle.
