# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 13.68 |                  14.16 |               -1.01% |                     3/8 |
| reconcile              |                101.70 |                 102.86 |               +0.29% |                     0/8 |
| reconcile-plain-object |                 36.81 |                  37.99 |               +3.27% |                     4/8 |
| produce                |                 90.47 |                  88.95 |               -0.04% |                     2/8 |
