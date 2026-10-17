# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 14.73 |                  14.61 |               +9.30% |                     5/8 |
| reconcile              |                101.62 |                 102.18 |               -1.12% |                     3/8 |
| reconcile-plain-object |                 39.86 |                  35.56 |              -10.66% |                     1/8 |
| produce                |                 93.72 |                  98.29 |               +6.49% |                     5/8 |
