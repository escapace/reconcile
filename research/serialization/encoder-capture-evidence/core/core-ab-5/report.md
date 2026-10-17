# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 13.61 |                  13.82 |               -4.15% |                     3/8 |
| reconcile              |                102.75 |                 102.90 |               +0.51% |                     2/8 |
| reconcile-plain-object |                 33.88 |                  33.64 |               +1.68% |                     4/8 |
| produce                |                 90.37 |                  89.76 |               +4.12% |                     4/8 |
