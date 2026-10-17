# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 13.51 |                  15.03 |               +5.85% |                     5/8 |
| reconcile              |                107.77 |                 103.68 |               -2.05% |                     1/8 |
| reconcile-plain-object |                 34.59 |                  37.79 |               +4.90% |                     4/8 |
| produce                |                 93.82 |                  91.36 |               -1.23% |                     2/8 |
