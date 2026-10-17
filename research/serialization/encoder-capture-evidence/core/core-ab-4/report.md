# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 13.12 |                  12.91 |               -1.95% |                     2/8 |
| reconcile              |                 95.73 |                  95.59 |               +3.28% |                     4/8 |
| reconcile-plain-object |                 32.95 |                  32.37 |               +0.94% |                     3/8 |
| produce                |                 81.60 |                  85.98 |               +2.24% |                     3/8 |
