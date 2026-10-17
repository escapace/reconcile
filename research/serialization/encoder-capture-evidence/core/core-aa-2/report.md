# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 14.58 |                  13.98 |               -2.91% |                     3/8 |
| reconcile              |                103.35 |                 103.29 |               -0.03% |                     3/8 |
| reconcile-plain-object |                 36.14 |                  36.21 |               +3.55% |                     4/8 |
| produce                |                 95.20 |                  97.36 |               -0.54% |                     3/8 |
