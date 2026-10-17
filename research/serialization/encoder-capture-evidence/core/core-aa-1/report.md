# Alternating A/B timing round

Negative changes mean the candidate is faster. Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.

| Workload               | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |
| ---------------------- | --------------------: | ---------------------: | -------------------: | ----------------------: |
| snapshot               |                 13.92 |                  13.91 |               -0.06% |                     3/8 |
| reconcile              |                105.35 |                 101.44 |               -2.49% |                     3/8 |
| reconcile-plain-object |                 33.56 |                  35.92 |               +5.01% |                     6/8 |
| produce                |                 92.75 |                  90.77 |               -2.32% |                     1/8 |
