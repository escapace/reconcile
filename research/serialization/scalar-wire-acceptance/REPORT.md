# Compact scalar formats: gains demonstrated, acceptance not established

Both wire candidates substantially improve undefined-array decoding, especially A. Neither satisfies the strict requirement that other performance must not suffer in this full comparison. Retain the restored5,021B-gzip baseline unless that acceptance requirement is explicitly changed or subsequently established. No automatic selection, tuning or additional measurement followed this round.

A encodes special scalars as reserved negative integers and shifts reference integers. B uses reserved negative half-integers while retaining existing references. Both preserve ordinary negative numbers through their escaped representation. The baseline keeps special scalars in singleton arrays. This is a whole-format comparison rather than a microbenchmark of just scalar decoding.

All264 observations pass graph fidelity. The single full22-fixture comparison completed in224.03seconds, including builds, under295seconds. It was not a screening round followed by a winner-only rerun. A/B, baseline and exact baseline control ran on the same corpus with the same settings.

## Findings relevant to acceptance

A undefined10k decode is0.233× baseline (range0.232–0.242), and roundtrip0.340× (0.325–0.372). B decode is0.464× (0.440–0.480), and roundtrip0.815× (0.638–0.846). Control decode is0.973× (0.949–0.976). These target decoding gains clearly exceed observed unchanged-code variation.

A does not meet rest-performance acceptance: deep200 roundtrip is1.111× (1.055–1.258), versus control0.980× (0.925–1.076); Dates decode is1.117× (1.030–1.185); cycle300 encode is1.126× (1.014–1.224). Other results overlap control variation. These findings are not silently traded away for the undefined gain.

B likewise does not meet acceptance: records1k roundtrip is1.085× (1.064–1.093), versus control0.984× (0.966–1.030); first-hole decode is1.090× (1.047–1.119), versus control0.963× (0.889–1.001). Its undefined encoding result is uncertain, despite the clear decode improvement.

Observed ranges are not confidence intervals or a formal significance test. Some changes are unresolved relative to the noisy identical control. Under the user's requirement, unresolved nonregression is not a pass. A is the stronger target improvement, not an accepted winner.

## Scope, freezes and fidelity

The frozen restored baseline is copied unchanged from the earlier accepted candidate. A and B were copied from validated built outputs only after proof/review/runtime gates completed. Both sources remained unchanged after timing; baseline/control combined bytes are exactly equal. The frozen source SHA-256 values are:

- A: `b72cfba23feabde7f634763f2d7143d17ef39df105f282e7e5909846b1f2e0c3`
- B: `a49c61f667bd373c4109c42bf59a3a8e9f6296bba6ce567751e78999187ffc62`
- Restored baseline: `37cdfa0494779526e6a4c1f62cf3197796dfcc337460fd3c66e5aa84e6a54514`

The full existing21 fixtures plus a deterministic dense scalar-boundary fixture cover negatives, fractions/half-integers, numeric extrema,−0,nonfinite values,undefined and numeric-looking strings. All checks preserve graph aliases/cycles, sparse holes versus own undefined, buffer/view sharing and spans, collection identity/order, and exact URL/Temporal state. No fixture was excluded. Native constructors and representations differ only as required by the encoded values; no core API implementation was changed by this harness.

Three fresh-process repetitions rotate four-arm order. Every process warms five calls and records three at-least80ms batches per encode/decode/roundtrip, capped at100,000 calls; its middle batch is used. Node v24.19.0 uses native Temporal and the detected fallback base64 backend. This round does not measure native-base64 timing. Encode, decode and complete roundtrip are measured independently.

## Actual JSON examples

The common input is `{values:[undefined,NaN,Infinity,-Infinity,-0,-1,-0.5,1,"-1","-0.5","~0"],a:shared,b:shared}`, where `shared={n:-1}`. Exact measured encodings:

Restored baseline:

```json
[-1,[["values","a","b"],["n"]],[[0,0,-2,-3,-3],[2,11,[-1],[-2],[-3],[-4],[-5],[-7,-1],[-7,-0.5],1,"-1","-0.5","~0"],[0,1,[-7,-1]]]]
```

A: reserved integers, shifted references:

```json
[-6,[["values","a","b"],["n"]],[[0,0,-7,-8,-8],[2,11,-1,-2,-3,-4,-5,[-7,-1],[-7,-0.5],1,"-1","-0.5","~0"],[0,1,[-7,-1]]]]
```

B: reserved half-integers, unchanged references:

```json
[-1,[["values","a","b"],["n"]],[[0,0,-2,-3,-3],[2,11,-0.5,-1.5,-2.5,-3.5,-4.5,[-7,-1],[-7,-0.5],1,"-1","-0.5","~0"],[0,1,[-7,-1]]]]
```


Ordinary JSON.parse returns these encoded arrays and tables. Each matching codec parse reconstructs exact special numbers and undefined, ordinary negative values and literal strings, plus `a===b`. Examples were graph-checked in the worker. Matching-version requirements remain; these formats are not interchangeable.

## Bundle sizes

| Arm | Export | Minified B | gzip B |
|---|---|---:|---:|
| baseline | encode | 7,686 | 3,043 |
| baseline | decode | 6,927 | 2,862 |
| baseline | both | 13,012 | 5,021 |
| a | encode | 7,680 | 3,042 |
| a | decode | 6,860 | 2,843 |
| a | both | 12,939 | 4,998 |
| b | encode | 7,689 | 3,049 |
| b | decode | 6,861 | 2,844 |
| b | both | 12,949 | 5,004 |

Combined gzip: baseline5,021B, A4,998B, B5,004B. Small size savings do not waive the performance requirement.

## Payload sizes

UTF-8 bytes / gzip level9 bytes. The unchanged control payload matches baseline.

| Fixture | Baseline | A | B |
|---|---:|---:|---:|
| numeric-10k | 65,579 / 22,884 | 65,579 / 22,884 | 65,579 / 22,884 |
| undefined-10k | 50,019 / 126 | 30,019 / 82 | 50,019 / 128 |
| mixed-10k | 60,760 / 10,063 | 49,648 / 9,910 | 60,760 / 10,066 |
| records-small | 108 / 106 | 108 / 108 | 108 / 106 |
| records-1k | 54,904 / 14,863 | 54,919 / 14,872 | 54,904 / 14,863 |
| records-10k | 618,410 / 137,854 | 618,430 / 137,790 | 618,410 / 137,854 |
| dag-2k | 39,876 / 10,154 | 40,188 / 10,107 | 39,876 / 10,154 |
| dense-dag | 47,009 / 5,572 | 47,659 / 5,521 | 47,009 / 5,572 |
| cycle-300 | 5,707 / 1,833 | 5,727 / 1,912 | 5,707 / 1,833 |
| deep-200 | 2,130 / 469 | 2,140 / 462 | 2,130 / 469 |
| deep-2000 | 22,932 / 4,671 | 22,947 / 4,664 | 22,932 / 4,671 |
| collections | 19,638 / 6,344 | 19,671 / 6,476 | 19,638 / 6,344 |
| dates-2k | 27,804 / 9,563 | 27,819 / 9,566 | 27,804 / 9,563 |
| rich | 372 / 224 | 371 / 224 | 372 / 226 |
| views-shared | 1,457 / 112 | 1,457 / 112 | 1,457 / 112 |
| binary-1m | 1,398,193 / 1,053,150 | 1,398,193 / 1,053,150 | 1,398,193 / 1,053,150 |
| url-linked | 8,453 / 1,566 | 8,467 / 1,582 | 8,453 / 1,566 |
| temporal-exact | 7,586 / 577 | 7,596 / 581 | 7,586 / 577 |
| hole-first | 97,795 / 12,421 | 97,795 / 12,421 | 97,795 / 12,421 |
| hole-last | 97,789 / 12,414 | 97,789 / 12,414 | 97,789 / 12,414 |
| strings-10k | 228,909 / 25,909 | 228,909 / 25,909 | 228,909 / 25,909 |
| scalar-boundaries | 86,208 / 593 | 83,498 / 574 | 86,208 / 587 |

## Absolute latency

Median microseconds per operation across the three process results. Raw per-batch values and counts remain in samples.json.

| Fixture | Operation | Baseline µs | A µs | B µs | Control µs |
|---|---|---:|---:|---:|---:|
| numeric-10k | encode | 708.40 | 738.89 | 722.44 | 741.77 |
| numeric-10k | decode | 273.93 | 282.43 | 292.42 | 282.99 |
| numeric-10k | roundtrip | 1009.43 | 1031.55 | 1040.11 | 1010.09 |
| undefined-10k | encode | 699.13 | 278.81 | 724.31 | 572.99 |
| undefined-10k | decode | 726.89 | 168.62 | 326.28 | 689.84 |
| undefined-10k | roundtrip | 1270.42 | 461.81 | 1034.82 | 1347.17 |
| mixed-10k | encode | 684.37 | 536.98 | 731.81 | 686.34 |
| mixed-10k | decode | 726.17 | 465.70 | 603.87 | 772.20 |
| mixed-10k | roundtrip | 1346.26 | 1003.18 | 1359.14 | 1419.13 |
| records-small | encode | 1.95 | 1.76 | 1.79 | 1.71 |
| records-small | decode | 1.66 | 1.58 | 1.59 | 1.51 |
| records-small | roundtrip | 3.81 | 3.53 | 3.45 | 3.42 |
| records-1k | encode | 982.15 | 963.56 | 1032.92 | 916.26 |
| records-1k | decode | 426.06 | 446.18 | 457.58 | 448.81 |
| records-1k | roundtrip | 1400.15 | 1372.11 | 1490.08 | 1412.01 |
| records-10k | encode | 16031.01 | 17759.94 | 17843.02 | 16797.20 |
| records-10k | decode | 4784.04 | 4954.97 | 4898.46 | 4951.17 |
| records-10k | roundtrip | 18737.14 | 21785.34 | 21100.45 | 20777.98 |
| dag-2k | encode | 1119.87 | 1070.54 | 1184.16 | 1055.85 |
| dag-2k | decode | 354.55 | 365.69 | 361.17 | 381.28 |
| dag-2k | roundtrip | 1307.53 | 1348.83 | 1446.66 | 1382.68 |
| dense-dag | encode | 831.23 | 786.61 | 748.09 | 717.98 |
| dense-dag | decode | 307.38 | 293.35 | 300.42 | 286.56 |
| dense-dag | roundtrip | 1081.91 | 1007.85 | 1073.24 | 1031.74 |
| cycle-300 | encode | 131.23 | 160.58 | 129.14 | 132.39 |
| cycle-300 | decode | 74.17 | 82.19 | 72.76 | 76.95 |
| cycle-300 | roundtrip | 222.11 | 201.81 | 211.13 | 216.43 |
| deep-200 | encode | 64.60 | 66.06 | 65.85 | 62.31 |
| deep-200 | decode | 41.83 | 43.79 | 42.62 | 41.62 |
| deep-200 | roundtrip | 106.04 | 123.70 | 100.90 | 103.90 |
| deep-2000 | encode | 730.29 | 730.44 | 806.77 | 771.63 |
| deep-2000 | decode | 411.71 | 410.75 | 430.63 | 410.81 |
| deep-2000 | roundtrip | 1148.42 | 1137.68 | 1112.59 | 1173.31 |
| collections | encode | 448.57 | 485.23 | 497.75 | 494.89 |
| collections | decode | 206.42 | 229.84 | 223.35 | 212.95 |
| collections | roundtrip | 668.99 | 688.81 | 710.48 | 690.18 |
| dates-2k | encode | 306.90 | 297.86 | 279.14 | 274.09 |
| dates-2k | decode | 273.15 | 301.85 | 277.79 | 278.43 |
| dates-2k | roundtrip | 552.27 | 590.06 | 559.53 | 583.32 |
| rich | encode | 7.90 | 8.08 | 8.05 | 9.00 |
| rich | decode | 6.31 | 5.17 | 5.38 | 5.52 |
| rich | roundtrip | 14.09 | 12.68 | 13.65 | 13.06 |
| views-shared | encode | 6.80 | 6.92 | 6.98 | 6.39 |
| views-shared | decode | 5.03 | 5.21 | 4.72 | 4.79 |
| views-shared | roundtrip | 11.66 | 11.87 | 12.65 | 11.12 |
| binary-1m | encode | 8233.45 | 7762.72 | 8602.77 | 8356.15 |
| binary-1m | decode | 2975.65 | 2910.12 | 3129.98 | 2870.60 |
| binary-1m | roundtrip | 11985.08 | 11527.98 | 11504.69 | 12063.81 |
| url-linked | encode | 151.96 | 148.71 | 149.01 | 153.84 |
| url-linked | decode | 116.30 | 97.50 | 100.26 | 99.45 |
| url-linked | roundtrip | 264.71 | 263.11 | 255.77 | 259.09 |
| temporal-exact | encode | 352.76 | 337.88 | 357.46 | 332.67 |
| temporal-exact | decode | 480.68 | 481.22 | 479.10 | 455.82 |
| temporal-exact | roundtrip | 847.06 | 849.01 | 842.18 | 797.17 |
| hole-first | encode | 915.02 | 761.46 | 828.35 | 860.82 |
| hole-first | decode | 389.91 | 364.27 | 436.35 | 372.99 |
| hole-first | roundtrip | 1282.93 | 1154.82 | 1263.00 | 1266.88 |
| hole-last | encode | 770.75 | 736.65 | 757.73 | 744.77 |
| hole-last | decode | 383.88 | 351.65 | 353.85 | 387.19 |
| hole-last | roundtrip | 1161.33 | 1164.43 | 1276.08 | 1214.31 |
| strings-10k | encode | 745.06 | 734.45 | 719.61 | 809.37 |
| strings-10k | decode | 325.97 | 346.64 | 328.86 | 368.97 |
| strings-10k | roundtrip | 1049.83 | 1052.83 | 1019.03 | 1048.93 |
| scalar-boundaries | encode | 902.99 | 818.71 | 887.14 | 866.78 |
| scalar-boundaries | decode | 718.33 | 629.34 | 663.73 | 708.41 |
| scalar-boundaries | roundtrip | 1592.64 | 1424.75 | 1517.87 | 1512.49 |

## A/base paired ratios

Median [minimum, maximum] of three corresponding process ratios; less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.043 [1.043, 1.103] | 1.047 [0.972, 1.054] | 1.031 [0.994, 1.036] |
| undefined-10k | 0.399 [0.351, 0.457] | 0.233 [0.232, 0.242] | 0.340 [0.325, 0.372] |
| mixed-10k | 0.785 [0.752, 0.796] | 0.642 [0.551, 0.653] | 0.733 [0.677, 0.755] |
| records-small | 0.901 [0.416, 1.039] | 0.953 [0.880, 1.126] | 0.918 [0.830, 1.046] |
| records-1k | 0.982 [0.972, 1.107] | 1.033 [0.991, 1.053] | 1.001 [0.974, 1.242] |
| records-10k | 1.112 [0.951, 1.164] | 1.011 [0.996, 1.092] | 1.079 [1.045, 1.163] |
| dag-2k | 0.948 [0.904, 1.033] | 1.027 [1.001, 1.077] | 1.032 [0.977, 1.150] |
| dense-dag | 0.946 [0.881, 1.049] | 0.973 [0.954, 0.980] | 0.932 [0.922, 0.944] |
| cycle-300 | 1.126 [1.014, 1.224] | 1.077 [1.037, 1.108] | 0.963 [0.714, 0.966] |
| deep-200 | 1.023 [0.964, 1.047] | 1.051 [0.965, 1.071] | 1.111 [1.055, 1.258] |
| deep-2000 | 1.018 [0.910, 1.035] | 1.005 [0.998, 1.018] | 1.030 [0.977, 1.053] |
| collections | 1.107 [1.028, 1.141] | 1.098 [1.055, 1.192] | 1.030 [1.003, 1.562] |
| dates-2k | 0.928 [0.925, 1.060] | 1.117 [1.030, 1.185] | 1.051 [0.997, 1.068] |
| rich | 1.023 [0.977, 1.039] | 0.809 [0.803, 0.920] | 0.905 [0.859, 1.037] |
| views-shared | 1.045 [0.914, 1.098] | 0.923 [0.869, 1.087] | 0.955 [0.949, 1.038] |
| binary-1m | 0.976 [0.915, 1.035] | 0.974 [0.972, 0.997] | 0.987 [0.957, 1.004] |
| url-linked | 0.983 [0.942, 1.051] | 0.837 [0.817, 1.053] | 0.994 [0.930, 1.061] |
| temporal-exact | 0.958 [0.925, 1.046] | 1.001 [0.991, 1.231] | 0.978 [0.967, 1.002] |
| hole-first | 0.799 [0.782, 0.856] | 0.950 [0.868, 0.982] | 0.869 [0.846, 0.900] |
| hole-last | 0.990 [0.817, 1.117] | 0.916 [0.878, 0.940] | 0.991 [0.975, 1.018] |
| strings-10k | 0.988 [0.986, 0.994] | 1.063 [0.944, 1.083] | 0.978 [0.956, 1.093] |
| scalar-boundaries | 0.911 [0.899, 0.969] | 0.879 [0.876, 0.931] | 0.895 [0.831, 1.025] |

## B/base paired ratios

Median [minimum, maximum] of three corresponding process ratios; less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.020 [0.973, 1.044] | 1.084 [1.018, 1.093] | 1.048 [0.961, 1.212] |
| undefined-10k | 1.036 [0.892, 1.203] | 0.464 [0.440, 0.480] | 0.815 [0.638, 0.846] |
| mixed-10k | 1.070 [1.060, 1.170] | 0.841 [0.721, 1.025] | 0.967 [0.917, 1.048] |
| records-small | 0.930 [0.417, 1.050] | 0.964 [0.960, 1.032] | 0.904 [0.794, 1.013] |
| records-1k | 1.096 [1.041, 1.138] | 1.074 [1.057, 1.176] | 1.085 [1.064, 1.093] |
| records-10k | 1.169 [1.077, 1.294] | 1.018 [1.015, 1.027] | 1.126 [0.881, 1.283] |
| dag-2k | 1.049 [1.007, 1.062] | 1.030 [1.014, 1.068] | 1.106 [1.042, 1.122] |
| dense-dag | 0.888 [0.801, 0.967] | 0.921 [0.911, 1.054] | 0.983 [0.921, 1.008] |
| cycle-300 | 0.984 [0.880, 1.042] | 0.982 [0.906, 1.033] | 0.916 [0.769, 1.011] |
| deep-200 | 0.987 [0.941, 1.067] | 1.006 [0.986, 1.049] | 0.973 [0.904, 1.024] |
| deep-2000 | 1.072 [1.067, 1.105] | 1.042 [1.024, 1.081] | 1.018 [0.956, 1.057] |
| collections | 1.108 [1.096, 1.809] | 1.067 [1.051, 1.471] | 1.062 [0.989, 1.124] |
| dates-2k | 0.938 [0.870, 0.974] | 1.008 [0.979, 1.032] | 1.013 [0.984, 1.022] |
| rich | 1.002 [0.998, 1.029] | 0.903 [0.852, 0.919] | 0.969 [0.920, 1.033] |
| views-shared | 1.027 [0.866, 1.107] | 0.946 [0.906, 0.994] | 0.970 [0.925, 1.143] |
| binary-1m | 1.045 [0.937, 1.157] | 1.045 [1.007, 1.114] | 0.960 [0.950, 1.075] |
| url-linked | 0.978 [0.955, 0.985] | 0.899 [0.808, 1.008] | 0.966 [0.941, 1.010] |
| temporal-exact | 0.996 [0.968, 1.090] | 1.000 [0.997, 1.009] | 0.960 [0.938, 0.994] |
| hole-first | 0.859 [0.836, 0.932] | 1.090 [1.047, 1.119] | 0.990 [0.957, 0.997] |
| hole-last | 0.971 [0.860, 1.044] | 0.917 [0.893, 0.949] | 1.099 [0.987, 1.169] |
| strings-10k | 0.966 [0.905, 0.987] | 1.009 [0.981, 1.017] | 0.973 [0.915, 0.995] |
| scalar-boundaries | 0.974 [0.966, 1.093] | 0.912 [0.891, 0.943] | 0.941 [0.930, 1.012] |

## control/base paired ratios

Median [minimum, maximum] of three corresponding process ratios; less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.072 [0.947, 1.147] | 1.013 [0.985, 1.071] | 1.018 [0.971, 1.040] |
| undefined-10k | 0.820 [0.741, 0.962] | 0.973 [0.949, 0.976] | 0.994 [0.837, 1.068] |
| mixed-10k | 1.003 [0.934, 1.154] | 0.995 [0.923, 1.101] | 1.045 [0.958, 1.103] |
| records-small | 0.869 [0.499, 1.042] | 0.987 [0.859, 1.001] | 0.896 [0.826, 0.998] |
| records-1k | 0.972 [0.927, 0.990] | 1.053 [0.989, 1.106] | 0.984 [0.966, 1.030] |
| records-10k | 1.066 [1.042, 1.071] | 1.034 [1.025, 1.035] | 1.019 [1.014, 1.159] |
| dag-2k | 0.978 [0.930, 1.041] | 1.075 [1.005, 1.132] | 1.022 [1.016, 1.093] |
| dense-dag | 0.864 [0.837, 0.918] | 0.959 [0.923, 1.006] | 0.969 [0.920, 1.051] |
| cycle-300 | 0.968 [0.909, 1.105] | 1.002 [0.962, 1.102] | 1.036 [0.926, 1.189] |
| deep-200 | 0.967 [0.965, 1.045] | 0.995 [0.958, 1.018] | 0.980 [0.925, 1.076] |
| deep-2000 | 1.007 [0.969, 1.103] | 0.970 [0.933, 1.087] | 1.046 [0.954, 1.088] |
| collections | 1.103 [1.037, 1.428] | 1.063 [0.980, 1.089] | 1.059 [0.928, 1.090] |
| dates-2k | 0.921 [0.893, 0.968] | 1.019 [0.947, 1.067] | 1.061 [0.952, 1.081] |
| rich | 1.139 [0.970, 1.171] | 0.983 [0.825, 1.111] | 0.941 [0.885, 0.945] |
| views-shared | 0.901 [0.874, 1.081] | 0.952 [0.793, 1.305] | 0.899 [0.853, 1.048] |
| binary-1m | 1.083 [0.934, 1.115] | 0.981 [0.953, 0.994] | 1.041 [0.962, 1.054] |
| url-linked | 1.012 [0.934, 1.228] | 0.855 [0.854, 0.988] | 0.979 [0.945, 1.002] |
| temporal-exact | 0.943 [0.905, 1.113] | 0.954 [0.923, 0.982] | 0.941 [0.923, 0.973] |
| hole-first | 0.942 [0.941, 0.965] | 0.963 [0.889, 1.001] | 0.958 [0.935, 0.987] |
| hole-last | 1.001 [0.831, 1.067] | 0.950 [0.929, 1.038] | 1.062 [0.906, 1.234] |
| strings-10k | 1.109 [0.953, 1.122] | 1.142 [0.931, 1.279] | 0.985 [0.952, 1.119] |
| scalar-boundaries | 0.960 [0.906, 1.056] | 0.986 [0.920, 1.009] | 0.983 [0.884, 1.009] |

## A/control paired ratios

Median [minimum, maximum] of three corresponding process ratios; less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 0.973 [0.910, 1.164] | 0.987 [0.984, 1.034] | 1.012 [0.996, 1.024] |
| undefined-10k | 0.475 [0.474, 0.487] | 0.245 [0.237, 0.248] | 0.375 [0.318, 0.389] |
| mixed-10k | 0.782 [0.651, 0.852] | 0.597 [0.593, 0.645] | 0.707 [0.665, 0.723] |
| records-small | 0.997 [0.832, 1.037] | 1.024 [0.952, 1.141] | 1.024 [1.005, 1.048] |
| records-1k | 1.010 [0.982, 1.194] | 0.999 [0.934, 1.003] | 1.009 [0.972, 1.262] |
| records-10k | 1.067 [0.887, 1.092] | 0.977 [0.972, 1.056] | 1.026 [0.931, 1.146] |
| dag-2k | 1.020 [0.868, 1.056] | 0.931 [0.907, 1.071] | 0.957 [0.944, 1.132] |
| dense-dag | 1.096 [0.960, 1.254] | 1.022 [0.968, 1.034] | 0.974 [0.877, 1.013] |
| cycle-300 | 1.107 [1.048, 1.239] | 1.035 [1.006, 1.120] | 0.932 [0.601, 1.040] |
| deep-200 | 1.060 [0.923, 1.083] | 1.032 [1.007, 1.076] | 1.168 [1.077, 1.202] |
| deep-2000 | 0.939 [0.938, 1.011] | 1.029 [0.924, 1.091] | 0.967 [0.934, 1.079] |
| collections | 0.932 [0.799, 1.067] | 1.120 [0.969, 1.120] | 1.109 [0.920, 1.476] |
| dates-2k | 1.035 [1.008, 1.094] | 1.088 [1.047, 1.163] | 0.989 [0.940, 1.103] |
| rich | 0.898 [0.887, 1.007] | 0.936 [0.723, 0.980] | 0.971 [0.958, 1.102] |
| views-shared | 1.016 [1.015, 1.196] | 0.970 [0.833, 1.096] | 1.056 [0.990, 1.120] |
| binary-1m | 0.929 [0.901, 0.980] | 1.003 [0.993, 1.020] | 0.964 [0.936, 0.995] |
| url-linked | 0.930 [0.801, 1.125] | 0.979 [0.957, 1.067] | 1.015 [0.984, 1.059] |
| temporal-exact | 1.016 [0.939, 1.023] | 1.050 [1.009, 1.334] | 1.048 [1.005, 1.065] |
| hole-first | 0.830 [0.827, 0.910] | 0.981 [0.977, 0.986] | 0.912 [0.883, 0.929] |
| hole-last | 0.989 [0.983, 1.046] | 0.924 [0.905, 0.986] | 0.959 [0.790, 1.094] |
| strings-10k | 0.897 [0.879, 1.037] | 0.949 [0.831, 1.015] | 0.993 [0.977, 1.004] |
| scalar-boundaries | 0.949 [0.918, 0.992] | 0.888 [0.871, 1.012] | 0.940 [0.910, 1.016] |

## B/control paired ratios

Median [minimum, maximum] of three corresponding process ratios; less than1 favors the numerator.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 0.974 [0.890, 1.027] | 1.033 [1.012, 1.079] | 1.030 [0.990, 1.165] |
| undefined-10k | 1.250 [1.204, 1.264] | 0.475 [0.463, 0.493] | 0.763 [0.762, 0.851] |
| mixed-10k | 1.067 [1.013, 1.135] | 0.782 [0.764, 1.031] | 0.950 [0.925, 0.958] |
| records-small | 1.008 [0.836, 1.071] | 1.046 [0.959, 1.122] | 1.009 [0.962, 1.015] |
| records-1k | 1.127 [1.051, 1.228] | 1.020 [0.956, 1.190] | 1.102 [1.053, 1.111] |
| records-10k | 1.097 [1.005, 1.242] | 0.993 [0.981, 0.994] | 1.107 [0.864, 1.110] |
| dag-2k | 1.029 [1.020, 1.128] | 0.993 [0.896, 1.025] | 1.026 [1.012, 1.098] |
| dense-dag | 1.028 [0.957, 1.054] | 0.987 [0.960, 1.048] | 1.001 [0.935, 1.040] |
| cycle-300 | 0.968 [0.891, 1.076] | 0.942 [0.891, 1.030] | 0.976 [0.646, 0.989] |
| deep-200 | 1.023 [0.900, 1.104] | 1.030 [0.991, 1.050] | 0.978 [0.904, 1.045] |
| deep-2000 | 1.060 [1.002, 1.106] | 1.056 [0.994, 1.116] | 0.936 [0.914, 1.108] |
| collections | 1.069 [0.768, 1.640] | 1.089 [0.966, 1.383] | 1.062 [0.908, 1.144] |
| dates-2k | 1.005 [0.945, 1.051] | 0.988 [0.968, 1.034] | 0.963 [0.937, 1.033] |
| rich | 0.904 [0.855, 1.029] | 0.919 [0.767, 1.114] | 1.030 [0.974, 1.167] |
| views-shared | 1.024 [0.962, 1.175] | 0.952 [0.725, 1.254] | 1.090 [1.030, 1.138] |
| binary-1m | 1.039 [0.865, 1.119] | 1.097 [1.013, 1.136] | 0.987 [0.922, 1.019] |
| url-linked | 0.944 [0.802, 1.047] | 1.021 [0.946, 1.052] | 0.997 [0.987, 1.008] |
| temporal-exact | 1.101 [0.869, 1.155] | 1.045 [1.018, 1.093] | 1.016 [0.987, 1.056] |
| hole-first | 0.912 [0.888, 0.965] | 1.162 [1.089, 1.177] | 1.033 [0.969, 1.066] |
| hole-last | 0.978 [0.970, 1.035] | 0.940 [0.914, 0.987] | 1.089 [0.890, 1.102] |
| strings-10k | 0.861 [0.816, 1.036] | 0.891 [0.789, 1.054] | 0.960 [0.870, 1.010] |
| scalar-boundaries | 1.035 [1.007, 1.075] | 0.934 [0.924, 0.969] | 1.004 [0.957, 1.052] |

## Evidence and boundaries

manifest.json records frozen source/bundle hashes, settings, control equality and unchanged-source checks. sizes.json records bundle bytes. samples.json retains all264 observations, payloads, examples and per-batch timings; summary.json preserves every paired ratio. receipt.json records completed execution within the bound. Incidental memory occupancy fields are retained by the reused worker, but no memory profiler or true peak-heap investigation was performed.

No further benchmark or optimization is scheduled. This comparison does not establish universal runtime performance, browser performance, or any core API speed claim. The rejected singleton-switch and dense-only experiments remain separate.

Reproduction requires renewed exclusive coordination and overwrites this evidence:

```sh
source /workspace/shared/escapace-dev/activate.sh
python3 /workspace/reconcile-upstream/scripts/bounded-check.py --seconds 295 --receipt /workspace/serialization-lab/scalar-wire-acceptance/receipt.json -- python3 /workspace/serialization-lab/scalar-wire-acceptance/round.py
```
