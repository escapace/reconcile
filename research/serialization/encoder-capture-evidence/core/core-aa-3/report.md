# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 12.83 |                  13.12 |               -1.16% |                     3/8 |
| reconcile              |                 98.45 |                  99.55 |               +2.83% |                     4/8 |
| reconcile-plain-object |                 32.21 |                  32.06 |               -2.24% |                     2/8 |
| produce                |                 84.02 |                  86.13 |               +1.79% |                     3/8 |
