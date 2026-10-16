# Final outlined-helper gate: acceptance remains unresolved

The outlined helper preserves A's large undefined-array improvement but does not demonstrate an additional benefit over original A. Full-suite performance nonregression remains unresolved relative to both identical-code controls. Under the user's strict requirement, this is **not an acceptance pass**. Retain the restored5,021B-gzip baseline; preserve A and the outlined candidate as isolated experiments.

All330 observations passed fidelity checks. The complete final round finished in255.03seconds under295seconds. No timeout, split round, profiler, tuning or further measurement occurred. This completes the authorized final gate.

## Key results

Outlined undefined10k decode is0.257× restored baseline (range0.233–0.261) and roundtrip0.350× (0.348–0.406). Against original A, decode is0.993× (0.898–1.107), so the helper itself has no demonstrated incremental target gain.

Rest-performance findings remain uncertain:

- Deep200 roundtrip: outlined/base1.082 [0.973,1.115]; its byte-identical outlined-copy/outlined0.864 [0.813,1.008].
- Records10k roundtrip: outlined/base1.102 [0.930,1.273].
- Dates2k roundtrip: outlined/base1.047 [0.973,1.091]; outlined/A1.121 [1.012,1.139].
- Binary1m decode includes a broad outlined/base0.798–1.401 range.

There are also faster observations, and exact-copy controls contain substantial variation/outliers. These do not establish a specific algorithmic regression or a JIT cause, but they cannot prove the required absence of regressions either. Inconclusive results are not passes. No acceptance threshold was relaxed after seeing the data.

## Frozen implementation and correctness

The only intended runtime change from A is placement of failed-reference/special-scalar decoding in a helper. The integer-sentinel wire and encoder remain unchanged. The validated outlined full build SHA-256 is `0b96165db9d5cce0cdab709ed960ce49d7ef585cbab7a5f51eaa2d11ca9f6fcb`.

The harness verified:

- Original A and outlined encode-only bundles are byte-identical.
- Outlined and its separately named control combined bundles are byte-identical.
- Restored baseline and its separately named control combined bundles are byte-identical.
- A and outlined emitted identical SHA-256 wire hashes for every fixture/repetition, including their control.
- The outlined source and all frozen measured artifacts remained unchanged after execution.
- Every graph-fidelity check passed: all22 fixtures across five arms and three repetitions, including sparse holes, explicit undefined, special scalars, aliases/cycles, native types and shared binary views.

manifest.json records hashes/equalities. Original A and restored baseline are copied from preserved artifacts; no production core code was changed by this harness.

## Measurement design

Full existing21 fixtures plus deterministic negative/special/numeric-looking-string coverage. Five arms: original A, outlined, restored baseline, exact outlined control and exact baseline control. Three fresh-process repetitions rotate order. Each process has five warmups and three at-least70ms batches per encode/decode/roundtrip, capped at100,000 calls. The middle batch is its result. Seventy milliseconds was selected before execution to leave headroom for the complete330-process matrix.

Host is Node v24.19.0 with native Temporal and detected fallback base64. This does not measure native-base64 performance. Each operation is independently timed; roundtrip is not a sum of encode and decode medians. Paired ranges below are observed min/max, not confidence intervals or causal tests.

## Bundle sizes

| Arm | Export | Minified B | gzip B |
|---|---|---:|---:|
| baseline | encode | 7,686 | 3,043 |
| baseline | decode | 6,927 | 2,862 |
| baseline | both | 13,012 | 5,021 |
| a | encode | 7,680 | 3,042 |
| a | decode | 6,860 | 2,843 |
| a | both | 12,939 | 4,998 |
| outlined | encode | 7,680 | 3,042 |
| outlined | decode | 6,878 | 2,849 |
| outlined | both | 12,957 | 5,004 |

Outlined both is5,004B gzip:6B larger than original A (4,998B),17B smaller than restored baseline (5,021B). Size savings do not resolve performance acceptance.

## Payloads

Original A and outlined payloads are exactly equal. Both control payloads match their corresponding implementation.

| Fixture | Restored bytes/gzip | A and outlined bytes/gzip |
|---|---:|---:|
| numeric-10k | 65,579 / 22,884 | 65,579 / 22,884 |
| undefined-10k | 50,019 / 126 | 30,019 / 82 |
| mixed-10k | 60,760 / 10,063 | 49,648 / 9,910 |
| records-small | 108 / 106 | 108 / 108 |
| records-1k | 54,904 / 14,863 | 54,919 / 14,872 |
| records-10k | 618,410 / 137,854 | 618,430 / 137,790 |
| dag-2k | 39,876 / 10,154 | 40,188 / 10,107 |
| dense-dag | 47,009 / 5,572 | 47,659 / 5,521 |
| cycle-300 | 5,707 / 1,833 | 5,727 / 1,912 |
| deep-200 | 2,130 / 469 | 2,140 / 462 |
| deep-2000 | 22,932 / 4,671 | 22,947 / 4,664 |
| collections | 19,638 / 6,344 | 19,671 / 6,476 |
| dates-2k | 27,804 / 9,563 | 27,819 / 9,566 |
| rich | 372 / 224 | 371 / 224 |
| views-shared | 1,457 / 112 | 1,457 / 112 |
| binary-1m | 1,398,193 / 1,053,150 | 1,398,193 / 1,053,150 |
| url-linked | 8,453 / 1,566 | 8,467 / 1,582 |
| temporal-exact | 7,586 / 577 | 7,596 / 581 |
| hole-first | 97,795 / 12,421 | 97,795 / 12,421 |
| hole-last | 97,789 / 12,414 | 97,789 / 12,414 |
| strings-10k | 228,909 / 25,909 | 228,909 / 25,909 |
| scalar-boundaries | 86,208 / 593 | 83,498 / 574 |

## Absolute latency

Median microseconds per operation across three process results. Raw batches and call counts remain in samples.json.

| Fixture | Operation | Restored µs | A µs | Outlined µs | Outlined-copy µs | Restored-copy µs |
|---|---|---:|---:|---:|---:|---:|
| numeric-10k | encode | 752.09 | 734.57 | 709.96 | 754.39 | 745.61 |
| numeric-10k | decode | 278.01 | 290.60 | 280.80 | 283.01 | 280.91 |
| numeric-10k | roundtrip | 1020.31 | 1044.42 | 1013.04 | 1098.80 | 1040.66 |
| undefined-10k | encode | 585.17 | 279.37 | 272.22 | 288.27 | 584.75 |
| undefined-10k | decode | 721.72 | 179.34 | 178.74 | 171.48 | 676.41 |
| undefined-10k | roundtrip | 1325.23 | 458.20 | 502.32 | 481.07 | 1256.34 |
| mixed-10k | encode | 680.17 | 494.92 | 510.57 | 517.96 | 707.79 |
| mixed-10k | decode | 766.55 | 489.51 | 487.91 | 481.12 | 754.10 |
| mixed-10k | roundtrip | 1434.08 | 1025.53 | 1131.06 | 1096.96 | 1387.28 |
| records-small | encode | 1.72 | 1.83 | 1.93 | 1.83 | 1.77 |
| records-small | decode | 1.66 | 1.65 | 1.62 | 1.66 | 1.59 |
| records-small | roundtrip | 3.60 | 3.59 | 3.56 | 3.71 | 3.52 |
| records-1k | encode | 1012.47 | 1062.74 | 996.62 | 1002.11 | 980.20 |
| records-1k | decode | 485.03 | 454.86 | 463.46 | 507.31 | 501.20 |
| records-1k | roundtrip | 1479.11 | 1466.03 | 1462.49 | 1491.41 | 1479.55 |
| records-10k | encode | 16388.52 | 17793.62 | 18072.43 | 17095.02 | 15946.48 |
| records-10k | decode | 5198.44 | 5589.20 | 5170.25 | 5291.22 | 5102.23 |
| records-10k | roundtrip | 20694.04 | 20452.20 | 22811.47 | 22082.25 | 20467.94 |
| dag-2k | encode | 1114.48 | 1110.29 | 1090.39 | 1149.33 | 1096.40 |
| dag-2k | decode | 380.81 | 369.18 | 369.04 | 372.49 | 364.89 |
| dag-2k | roundtrip | 1476.79 | 1343.50 | 1397.52 | 1430.87 | 1338.17 |
| dense-dag | encode | 773.34 | 763.47 | 780.62 | 815.02 | 825.23 |
| dense-dag | decode | 294.44 | 289.16 | 289.90 | 284.80 | 323.13 |
| dense-dag | roundtrip | 1034.15 | 1034.37 | 1007.00 | 1084.49 | 1098.29 |
| cycle-300 | encode | 156.27 | 137.08 | 133.71 | 143.11 | 139.54 |
| cycle-300 | decode | 80.57 | 72.91 | 75.05 | 76.73 | 78.15 |
| cycle-300 | roundtrip | 216.52 | 201.58 | 205.90 | 221.26 | 209.34 |
| deep-200 | encode | 67.35 | 62.60 | 66.77 | 62.28 | 66.21 |
| deep-200 | decode | 46.17 | 42.92 | 45.55 | 41.71 | 46.24 |
| deep-200 | roundtrip | 112.67 | 108.38 | 121.89 | 105.34 | 114.14 |
| deep-2000 | encode | 816.84 | 766.68 | 755.96 | 796.32 | 755.50 |
| deep-2000 | decode | 424.10 | 427.51 | 423.49 | 411.60 | 414.41 |
| deep-2000 | roundtrip | 1097.23 | 1176.93 | 1121.19 | 1090.83 | 1135.21 |
| collections | encode | 535.45 | 485.81 | 553.54 | 478.88 | 477.24 |
| collections | decode | 218.92 | 209.83 | 214.22 | 221.08 | 211.22 |
| collections | roundtrip | 739.80 | 672.40 | 661.62 | 727.76 | 701.64 |
| dates-2k | encode | 280.72 | 286.67 | 338.42 | 301.15 | 287.39 |
| dates-2k | decode | 288.72 | 297.03 | 296.14 | 300.07 | 285.15 |
| dates-2k | roundtrip | 569.76 | 546.02 | 621.82 | 577.71 | 556.22 |
| rich | encode | 7.58 | 7.87 | 7.85 | 8.56 | 7.29 |
| rich | decode | 5.44 | 5.31 | 5.03 | 5.61 | 5.33 |
| rich | roundtrip | 13.68 | 12.81 | 12.68 | 12.95 | 13.56 |
| views-shared | encode | 6.50 | 6.56 | 6.69 | 6.32 | 6.75 |
| views-shared | decode | 5.15 | 5.28 | 5.31 | 5.61 | 4.91 |
| views-shared | roundtrip | 11.70 | 12.27 | 12.41 | 11.65 | 11.21 |
| binary-1m | encode | 7902.99 | 7871.39 | 8553.75 | 8194.54 | 8704.56 |
| binary-1m | decode | 2966.17 | 3087.11 | 2958.53 | 3001.81 | 3015.03 |
| binary-1m | roundtrip | 11642.21 | 11420.58 | 11781.34 | 11530.59 | 11639.84 |
| url-linked | encode | 166.48 | 154.27 | 152.65 | 153.02 | 161.10 |
| url-linked | decode | 114.16 | 107.23 | 101.58 | 106.92 | 109.81 |
| url-linked | roundtrip | 272.55 | 269.94 | 262.30 | 259.06 | 273.81 |
| temporal-exact | encode | 376.92 | 361.53 | 380.71 | 341.04 | 360.42 |
| temporal-exact | decode | 493.53 | 484.00 | 493.96 | 459.61 | 507.89 |
| temporal-exact | roundtrip | 865.14 | 878.67 | 867.47 | 925.18 | 828.20 |
| hole-first | encode | 979.89 | 798.38 | 735.31 | 751.96 | 928.57 |
| hole-first | decode | 373.45 | 356.48 | 357.60 | 362.12 | 364.84 |
| hole-first | roundtrip | 1273.42 | 1135.21 | 1176.70 | 1239.25 | 1278.22 |
| hole-last | encode | 784.40 | 859.65 | 790.88 | 710.06 | 738.52 |
| hole-last | decode | 345.79 | 352.48 | 354.22 | 354.11 | 344.71 |
| hole-last | roundtrip | 1152.27 | 1213.56 | 1168.46 | 1238.00 | 1142.24 |
| strings-10k | encode | 717.56 | 697.94 | 757.87 | 764.13 | 744.13 |
| strings-10k | decode | 350.65 | 356.56 | 351.53 | 357.20 | 348.95 |
| strings-10k | roundtrip | 1136.38 | 1039.94 | 1098.84 | 1133.55 | 1052.33 |
| scalar-boundaries | encode | 922.50 | 772.52 | 819.42 | 780.50 | 835.83 |
| scalar-boundaries | decode | 751.28 | 640.47 | 658.43 | 624.86 | 696.45 |
| scalar-boundaries | roundtrip | 1534.03 | 1480.67 | 1412.78 | 1412.56 | 1514.90 |

## outlined/base paired ratios

Median [minimum, maximum] across three corresponding process pairs. Less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 0.934 [0.878, 0.994] | 1.012 [0.979, 1.020] | 0.973 [0.901, 1.017] |
| undefined-10k | 0.454 [0.453, 0.491] | 0.257 [0.233, 0.261] | 0.350 [0.348, 0.406] |
| mixed-10k | 0.732 [0.715, 0.758] | 0.628 [0.541, 0.742] | 0.789 [0.677, 0.800] |
| records-small | 1.141 [0.986, 1.186] | 0.966 [0.941, 1.139] | 0.991 [0.931, 1.004] |
| records-1k | 1.003 [0.824, 1.114] | 0.931 [0.909, 1.146] | 1.041 [0.989, 1.556] |
| records-10k | 0.990 [0.893, 1.115] | 1.031 [0.954, 1.070] | 1.102 [0.930, 1.273] |
| dag-2k | 1.019 [0.928, 1.029] | 0.968 [0.958, 0.980] | 1.009 [0.946, 1.038] |
| dense-dag | 0.984 [0.913, 1.009] | 0.997 [0.948, 1.033] | 0.974 [0.968, 0.981] |
| cycle-300 | 0.845 [0.713, 0.910] | 0.973 [0.891, 0.988] | 0.953 [0.951, 1.022] |
| deep-200 | 0.991 [0.972, 1.416] | 0.978 [0.934, 1.068] | 1.082 [0.973, 1.115] |
| deep-2000 | 0.925 [0.862, 1.110] | 0.984 [0.981, 1.061] | 1.041 [0.947, 1.046] |
| collections | 1.026 [0.845, 1.190] | 0.983 [0.960, 1.018] | 0.953 [0.876, 0.953] |
| dates-2k | 1.118 [0.981, 1.254] | 0.972 [0.925, 1.026] | 1.047 [0.973, 1.091] |
| rich | 1.035 [0.993, 1.043] | 0.964 [0.794, 1.107] | 0.889 [0.881, 1.063] |
| views-shared | 1.077 [0.974, 1.120] | 0.956 [0.799, 1.158] | 1.000 [0.860, 1.069] |
| binary-1m | 1.091 [0.973, 1.108] | 1.052 [0.798, 1.401] | 1.012 [0.915, 1.046] |
| url-linked | 0.921 [0.917, 0.945] | 0.944 [0.890, 0.949] | 0.941 [0.940, 0.994] |
| temporal-exact | 1.010 [1.003, 1.024] | 0.965 [0.908, 1.060] | 1.019 [0.964, 1.071] |
| hole-first | 0.840 [0.750, 0.865] | 0.911 [0.905, 1.003] | 0.882 [0.859, 0.940] |
| hole-last | 1.026 [1.008, 1.066] | 1.024 [1.010, 1.039] | 0.995 [0.984, 1.089] |
| strings-10k | 1.049 [0.992, 1.056] | 1.007 [1.003, 1.011] | 0.956 [0.842, 1.391] |
| scalar-boundaries | 0.970 [0.888, 1.007] | 0.940 [0.845, 0.990] | 0.947 [0.905, 1.043] |

## A/base paired ratios

Median [minimum, maximum] across three corresponding process pairs. Less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.007 [0.909, 1.027] | 1.045 [1.004, 1.053] | 1.006 [0.978, 1.025] |
| undefined-10k | 0.479 [0.435, 0.504] | 0.234 [0.232, 0.291] | 0.353 [0.346, 0.477] |
| mixed-10k | 0.695 [0.678, 0.755] | 0.639 [0.536, 0.679] | 0.687 [0.672, 0.729] |
| records-small | 1.061 [1.028, 1.117] | 0.964 [0.929, 1.093] | 0.947 [0.932, 1.043] |
| records-1k | 1.067 [0.965, 1.188] | 0.915 [0.913, 1.095] | 0.991 [0.942, 1.136] |
| records-10k | 1.045 [0.944, 1.096] | 1.075 [0.990, 1.169] | 1.020 [0.914, 1.204] |
| dag-2k | 1.018 [0.900, 1.037] | 0.960 [0.946, 1.053] | 0.943 [0.904, 1.016] |
| dense-dag | 0.987 [0.833, 1.058] | 0.995 [0.922, 1.037] | 0.997 [0.974, 1.013] |
| cycle-300 | 0.868 [0.833, 0.920] | 0.945 [0.866, 1.026] | 0.950 [0.922, 1.003] |
| deep-200 | 0.963 [0.929, 1.012] | 0.994 [0.903, 1.206] | 1.000 [0.962, 1.380] |
| deep-2000 | 0.967 [0.905, 1.061] | 1.041 [0.957, 1.149] | 1.073 [0.982, 1.137] |
| collections | 0.907 [0.824, 1.083] | 0.958 [0.902, 1.007] | 0.931 [0.896, 0.995] |
| dates-2k | 1.026 [0.947, 1.112] | 1.029 [0.893, 1.048] | 0.958 [0.934, 0.961] |
| rich | 1.110 [0.962, 1.215] | 0.921 [0.907, 0.976] | 0.937 [0.832, 1.018] |
| views-shared | 1.008 [0.943, 1.062] | 0.945 [0.900, 1.026] | 1.021 [0.768, 1.093] |
| binary-1m | 1.004 [0.916, 1.121] | 1.041 [0.875, 1.045] | 1.007 [0.970, 1.017] |
| url-linked | 0.974 [0.909, 1.035] | 0.938 [0.877, 1.032] | 0.946 [0.922, 1.023] |
| temporal-exact | 0.945 [0.774, 1.048] | 1.025 [0.981, 1.026] | 1.000 [0.980, 1.016] |
| hole-first | 0.943 [0.771, 1.081] | 0.953 [0.908, 1.077] | 0.897 [0.891, 1.038] |
| hole-last | 1.197 [1.018, 1.241] | 1.040 [0.996, 1.058] | 1.050 [0.949, 1.093] |
| strings-10k | 0.973 [0.949, 1.033] | 1.017 [0.974, 1.023] | 0.915 [0.888, 1.042] |
| scalar-boundaries | 0.832 [0.808, 0.940] | 0.853 [0.820, 0.982] | 0.925 [0.911, 1.000] |

## outlined/A paired ratios

Median [minimum, maximum] across three corresponding process pairs. Less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 0.967 [0.909, 0.987] | 0.969 [0.930, 1.016] | 0.992 [0.896, 0.995] |
| undefined-10k | 0.974 [0.947, 1.042] | 0.993 [0.898, 1.107] | 0.990 [0.729, 1.174] |
| mixed-10k | 1.030 [1.003, 1.080] | 1.010 [0.984, 1.094] | 1.082 [0.985, 1.189] |
| records-small | 1.021 [0.959, 1.118] | 1.039 [0.977, 1.043] | 0.999 [0.963, 1.047] |
| records-1k | 0.938 [0.854, 0.940] | 1.019 [0.994, 1.047] | 0.998 [0.917, 1.652] |
| records-10k | 0.948 [0.946, 1.018] | 0.959 [0.916, 0.964] | 1.206 [0.772, 1.248] |
| dag-2k | 1.011 [0.982, 1.031] | 1.013 [0.919, 1.020] | 1.021 [1.003, 1.115] |
| dense-dag | 1.022 [0.929, 1.096] | 1.003 [0.995, 1.028] | 0.976 [0.956, 1.007] |
| cycle-300 | 0.989 [0.821, 1.015] | 1.028 [0.963, 1.029] | 1.019 [1.003, 1.031] |
| deep-200 | 1.067 [1.010, 1.398] | 1.074 [0.774, 1.083] | 0.973 [0.808, 1.125] |
| deep-2000 | 0.957 [0.953, 1.046] | 1.019 [0.854, 1.028] | 0.964 [0.920, 0.970] |
| collections | 1.099 [0.931, 1.245] | 1.001 [0.976, 1.129] | 0.958 [0.941, 1.064] |
| dates-2k | 1.128 [0.957, 1.181] | 0.997 [0.928, 1.036] | 1.121 [1.012, 1.139] |
| rich | 0.940 [0.852, 1.033] | 1.047 [0.876, 1.135] | 1.045 [0.949, 1.059] |
| views-shared | 1.014 [0.966, 1.188] | 0.932 [0.887, 1.225] | 1.048 [0.915, 1.120] |
| binary-1m | 1.063 [0.988, 1.087] | 1.007 [0.912, 1.346] | 1.039 [0.900, 1.043] |
| url-linked | 0.970 [0.889, 1.009] | 1.013 [0.914, 1.015] | 0.994 [0.972, 1.020] |
| temporal-exact | 1.084 [0.964, 1.296] | 0.940 [0.926, 1.034] | 1.040 [0.949, 1.071] |
| hole-first | 0.891 [0.800, 0.973] | 0.949 [0.932, 1.003] | 0.957 [0.849, 1.054] |
| hole-last | 0.859 [0.857, 0.991] | 0.999 [0.955, 1.028] | 0.938 [0.910, 1.147] |
| strings-10k | 1.046 [1.016, 1.086] | 0.988 [0.986, 1.034] | 1.045 [0.948, 1.336] |
| scalar-boundaries | 1.068 [1.032, 1.246] | 1.030 [0.957, 1.162] | 0.994 [0.948, 1.128] |

## outlined-copy/outlined paired ratios

Median [minimum, maximum] across three corresponding process pairs. Less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.063 [1.003, 1.098] | 1.008 [0.976, 1.072] | 1.075 [1.018, 1.085] |
| undefined-10k | 0.997 [0.993, 1.098] | 0.956 [0.910, 1.000] | 0.958 [0.947, 0.958] |
| mixed-10k | 0.995 [0.982, 1.065] | 0.986 [0.967, 1.061] | 0.987 [0.847, 1.086] |
| records-small | 1.046 [0.882, 1.169] | 1.035 [0.858, 1.036] | 1.034 [0.962, 1.206] |
| records-1k | 0.987 [0.976, 1.241] | 1.146 [0.861, 1.151] | 1.027 [0.633, 1.119] |
| records-10k | 0.997 [0.944, 1.114] | 1.009 [0.987, 1.108] | 0.968 [0.847, 1.117] |
| dag-2k | 1.003 [0.967, 1.136] | 0.996 [0.990, 1.085] | 1.004 [0.982, 1.024] |
| dense-dag | 0.977 [0.935, 1.130] | 0.995 [0.969, 0.997] | 1.048 [1.014, 1.077] |
| cycle-300 | 1.056 [1.028, 1.103] | 1.040 [1.022, 1.059] | 1.036 [1.001, 1.094] |
| deep-200 | 0.933 [0.540, 0.999] | 0.916 [0.909, 0.961] | 0.864 [0.813, 1.008] |
| deep-2000 | 1.022 [0.921, 1.102] | 0.987 [0.966, 1.006] | 1.016 [0.962, 1.069] |
| collections | 0.922 [0.853, 1.059] | 1.032 [0.920, 1.073] | 1.108 [1.032, 1.207] |
| dates-2k | 0.890 [0.869, 1.049] | 1.025 [0.943, 1.084] | 0.976 [0.917, 1.048] |
| rich | 1.153 [1.089, 1.199] | 1.058 [1.024, 1.116] | 1.019 [0.940, 1.041] |
| views-shared | 0.999 [0.813, 1.092] | 0.990 [0.967, 1.140] | 0.939 [0.866, 0.994] |
| binary-1m | 0.962 [0.920, 0.991] | 0.970 [0.755, 1.063] | 0.972 [0.957, 1.077] |
| url-linked | 1.022 [0.913, 1.037] | 1.055 [0.814, 1.090] | 0.988 [0.909, 1.052] |
| temporal-exact | 0.890 [0.880, 0.896] | 1.004 [0.930, 1.060] | 1.110 [0.993, 1.146] |
| hole-first | 1.027 [0.880, 1.127] | 1.015 [0.981, 1.150] | 1.053 [1.014, 1.056] |
| hole-last | 0.940 [0.898, 0.961] | 1.015 [0.975, 1.099] | 1.027 [0.987, 1.155] |
| strings-10k | 0.932 [0.929, 1.008] | 0.959 [0.947, 1.016] | 1.043 [0.716, 1.080] |
| scalar-boundaries | 0.924 [0.827, 0.953] | 0.949 [0.841, 0.950] | 1.017 [0.827, 1.078] |

## base-copy/base paired ratios

Median [minimum, maximum] across three corresponding process pairs. Less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.043 [0.892, 1.150] | 0.997 [0.979, 1.121] | 0.984 [0.926, 1.050] |
| undefined-10k | 0.977 [0.956, 1.055] | 0.965 [0.937, 0.974] | 0.964 [0.870, 1.052] |
| mixed-10k | 1.024 [1.021, 1.041] | 0.984 [0.890, 0.999] | 0.958 [0.949, 0.967] |
| records-small | 1.029 [1.018, 1.032] | 0.932 [0.930, 1.027] | 0.974 [0.913, 0.978] |
| records-1k | 0.971 [0.903, 1.069] | 1.066 [0.971, 1.119] | 1.000 [0.932, 1.624] |
| records-10k | 0.973 [0.960, 0.983] | 1.019 [0.981, 1.030] | 0.989 [0.934, 1.062] |
| dag-2k | 0.997 [0.984, 1.041] | 0.969 [0.898, 0.998] | 0.985 [0.904, 1.010] |
| dense-dag | 1.067 [0.836, 1.170] | 1.097 [1.031, 1.130] | 1.055 [1.032, 1.062] |
| cycle-300 | 0.877 [0.744, 0.945] | 1.013 [0.888, 1.058] | 0.971 [0.967, 0.977] |
| deep-200 | 0.964 [0.814, 1.045] | 0.973 [0.948, 1.080] | 0.987 [0.983, 1.140] |
| deep-2000 | 0.925 [0.881, 1.105] | 0.999 [0.960, 1.018] | 1.059 [1.029, 1.072] |
| collections | 0.956 [0.844, 1.052] | 0.965 [0.907, 1.009] | 0.969 [0.948, 1.038] |
| dates-2k | 1.017 [0.999, 1.024] | 1.001 [0.850, 1.059] | 0.982 [0.971, 1.037] |
| rich | 1.028 [0.920, 1.096] | 0.936 [0.847, 1.066] | 0.985 [0.942, 1.091] |
| views-shared | 1.087 [0.882, 1.146] | 0.925 [0.738, 1.035] | 0.939 [0.701, 0.989] |
| binary-1m | 1.024 [0.956, 1.113] | 0.988 [0.852, 1.091] | 0.978 [0.952, 1.008] |
| url-linked | 0.919 [0.889, 1.039] | 0.963 [0.819, 1.057] | 1.014 [0.919, 1.030] |
| temporal-exact | 0.956 [0.758, 1.057] | 0.968 [0.953, 1.090] | 0.973 [0.947, 0.989] |
| hole-first | 0.981 [0.892, 1.097] | 0.939 [0.930, 1.038] | 0.988 [0.980, 1.004] |
| hole-last | 1.005 [0.905, 1.066] | 1.024 [0.986, 1.069] | 1.029 [0.986, 1.451] |
| strings-10k | 1.018 [0.940, 1.111] | 0.952 [0.938, 1.010] | 0.971 [0.926, 0.998] |
| scalar-boundaries | 0.967 [0.850, 1.014] | 0.935 [0.881, 1.024] | 0.988 [0.926, 1.021] |

## Disposition and limits

The data supports the substantial integer-sentinel undefined workload gain, not strict no-other-regression acceptance or a benefit from this helper placement. Exact-copy variation makes attribution uncertain. No engine profiler, optimization/deoptimization trace or assembly inspection was performed; no causal JIT conclusion is warranted. The helper changes code placement, but timing alone cannot identify the mechanism behind differences.

Do not adopt this experiment as satisfying the user's requirement. Retain the restored baseline and all previous reports. This final gate does not authorize another tuning cycle; no additional runs are scheduled.

samples.json contains all330 raw observations and per-batch counts, summary.json all absolute distributions/ratios, sizes.json bundle sizes, manifest.json frozen identities, and receipt.json completed bounded execution. Incidental occupancy measurements remain from the reused worker but this was not a separate memory investigation.

Reproduction requires renewed exclusive coordination and overwrites these artifacts:

```sh
source /workspace/shared/escapace-dev/activate.sh
python3 /workspace/reconcile-upstream/scripts/bounded-check.py --seconds 295 --receipt /workspace/serialization-lab/outlined-final-acceptance/receipt.json -- python3 /workspace/serialization-lab/outlined-final-acceptance/round.py
```
