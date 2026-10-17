# Wire design evidence

Supporting material for [WIRE-DESIGN.md](../WIRE-DESIGN.md), a proposal not yet approved for
implementation.

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
