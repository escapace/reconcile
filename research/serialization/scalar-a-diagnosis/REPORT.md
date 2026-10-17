# A-format bounded diagnosis

The earlier deep200 roundtrip, Dates decode and cycle encode slowdowns are not reliably reproduced in this controlled subset. Exact-copy variation is substantial, and separate-export results differ from combined-export results. This leaves the cause unresolved; it does not prove nonregression or justify attributing costs to shifted references. A's large undefined-array improvement remains robust in both modes.

All200 observations pass fidelity checks. The single authorized round completed in168.86seconds under295seconds. No codec implementation changed, no profiler ran, and no additional measurement followed. This focused diagnosis does not replace the prior full-suite acceptance requirement.

## Findings first

| Target, combined mode | A/base median [range] | Relevant identical-control evidence |
|---|---|---|
| deep200 roundtrip | 0.975 [0.743,1.077] | Baseline-copy/base0.925 [0.737,1.271] |
| Dates2k decode | 1.045 [0.947,1.070] | Baseline-copy/base1.044 [0.877,1.113] |
| cycle300 encode | 1.069 [0.956,1.128] | Baseline-copy/base1.150 [1.064,1.155] |

Separate-export Dates decode is0.992 [0.917,1.137] and cycle encode0.995 [0.892,1.068]. Their direction and ranges do not support a stable shifted-reference penalty. Combined undefined decode remains0.239 [0.191,0.251]; separate undefined decode0.241 [0.239,0.248]. Numeric results overlap unchanged-code variation.

Ratios below1 favor A. Ranges are observed min/max across five process pairs, not confidence intervals or formal significance tests. The prior full-suite uncertainty remains; this result must not be relabeled an acceptance pass.

## Design and frozen evidence

Five fixtures (deep200,Dates2k,cycle300,undefined10k,numeric10k), four arms (A,exact A copy,restored baseline,exact baseline copy), two export modes and five rotated repetitions produce200 fresh processes. Combined mode measures encode/decode/roundtrip. Separate mode imports the encode-only and decode-only bundles and measures encode/decode only. Both modes perform the same roundtrip fidelity check before timing.

Each operation uses five warmups and three at-least100ms batches capped at100,000 calls; process timing is the median batch. Arm and mode order rotate. Node v24.19.0 uses native Temporal and detected fallback base64. No native-base64 result is claimed.

All encode/decode/combined bundles were copied from the frozen artifacts already measured in `scalar-wire-acceptance`. Each duplicate is asserted byte-identical to its corresponding original for every export mode. Hashes are frozen before execution and checked unchanged afterward in `manifest.json`. `source-differences.patch` records the source comparison before execution; actual executed artifacts are identified independently by their bundle hashes. No bundling or implementation mutation occurred during timing.

## Payload size

Both modes and both exact copies emit identical payloads within each format. Byte changes are modest for the three suspected regressions; they do not measure number-conversion cost or establish a cause.

| Fixture | Baseline UTF-8 B | A UTF-8 B | Difference B | Difference % |
|---|---:|---:|---:|---:|
| deep-200 | 2,130 | 2,140 | +10 | +0.469% |
| dates-2k | 27,804 | 27,819 | +15 | +0.054% |
| cycle-300 | 5,707 | 5,727 | +20 | +0.350% |
| undefined-10k | 50,019 | 30,019 | -20,000 | -39.985% |
| numeric-10k | 65,579 | 65,579 | +0 | +0.000% |

Deep adds10bytes, Dates15bytes and cycle20bytes, while undefined payload falls by20,000bytes. Larger or smaller payloads are plausible contributors to work, but this experiment does not isolate their cost. It cannot infer that a tiny byte increase explains a much larger timing ratio, or that shifted-reference arithmetic is responsible.

## Absolute latency

Median microseconds per operation over five processes. Separate mode has no timed roundtrip.

| Mode | Fixture | Operation | A µs | Baseline µs | A-copy µs | Baseline-copy µs |
|---|---|---|---:|---:|---:|---:|
| combined | deep-200 | encode | 65.32 | 68.16 | 65.74 | 66.07 |
| combined | deep-200 | decode | 43.70 | 43.50 | 43.26 | 43.08 |
| combined | deep-200 | roundtrip | 112.71 | 116.26 | 106.92 | 108.11 |
| combined | dates-2k | encode | 290.07 | 297.45 | 294.28 | 283.49 |
| combined | dates-2k | decode | 291.27 | 285.58 | 290.52 | 280.75 |
| combined | dates-2k | roundtrip | 611.34 | 561.36 | 586.96 | 597.54 |
| combined | cycle-300 | encode | 134.73 | 130.94 | 141.15 | 145.25 |
| combined | cycle-300 | decode | 76.51 | 73.22 | 74.71 | 76.41 |
| combined | cycle-300 | roundtrip | 210.00 | 211.68 | 205.47 | 211.17 |
| combined | undefined-10k | encode | 277.89 | 630.26 | 260.34 | 603.81 |
| combined | undefined-10k | decode | 170.45 | 697.81 | 167.07 | 697.91 |
| combined | undefined-10k | roundtrip | 450.71 | 1247.41 | 459.51 | 1284.29 |
| combined | numeric-10k | encode | 760.68 | 766.66 | 746.12 | 749.68 |
| combined | numeric-10k | decode | 289.32 | 290.07 | 294.48 | 285.89 |
| combined | numeric-10k | roundtrip | 1047.23 | 1053.02 | 1066.66 | 1021.59 |
| separate | deep-200 | encode | 65.74 | 63.04 | 65.13 | 63.51 |
| separate | deep-200 | decode | 42.09 | 42.68 | 43.31 | 41.70 |
| separate | dates-2k | encode | 289.70 | 289.46 | 286.23 | 278.91 |
| separate | dates-2k | decode | 292.88 | 297.86 | 288.22 | 275.56 |
| separate | cycle-300 | encode | 135.67 | 133.61 | 146.11 | 136.12 |
| separate | cycle-300 | decode | 80.87 | 77.44 | 81.62 | 77.63 |
| separate | undefined-10k | encode | 284.26 | 604.81 | 306.06 | 582.88 |
| separate | undefined-10k | decode | 170.57 | 692.23 | 173.02 | 727.26 |
| separate | numeric-10k | encode | 767.50 | 775.51 | 739.73 | 784.65 |
| separate | numeric-10k | decode | 303.77 | 292.18 | 295.90 | 292.74 |

## A/base paired ratios

Median [minimum, maximum] across five paired processes. Exact-copy comparisons quantify variation without an implementation difference.

| Mode | Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|---|
| combined | deep-200 | 1.045 [0.920, 1.237] | 1.015 [0.965, 1.046] | 0.975 [0.743, 1.077] |
| combined | dates-2k | 1.046 [0.919, 1.141] | 1.045 [0.947, 1.070] | 0.996 [0.988, 1.130] |
| combined | cycle-300 | 1.069 [0.956, 1.128] | 1.018 [0.989, 1.046] | 1.018 [0.901, 1.086] |
| combined | undefined-10k | 0.447 [0.367, 0.617] | 0.239 [0.191, 0.251] | 0.366 [0.321, 0.440] |
| combined | numeric-10k | 0.998 [0.736, 1.059] | 1.013 [0.893, 1.039] | 1.009 [0.913, 1.041] |
| separate | deep-200 | 1.000 [0.901, 1.143] | 0.972 [0.958, 1.026] | not timed |
| separate | dates-2k | 1.009 [0.927, 1.177] | 0.992 [0.917, 1.137] | not timed |
| separate | cycle-300 | 0.995 [0.892, 1.068] | 0.980 [0.884, 1.066] | not timed |
| separate | undefined-10k | 0.458 [0.362, 0.528] | 0.241 [0.239, 0.248] | not timed |
| separate | numeric-10k | 0.983 [0.951, 1.055] | 1.006 [0.976, 1.068] | not timed |

## Acopy/A paired ratios

Median [minimum, maximum] across five paired processes. Exact-copy comparisons quantify variation without an implementation difference.

| Mode | Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|---|
| combined | deep-200 | 0.967 [0.864, 1.043] | 1.013 [0.964, 1.057] | 1.018 [0.949, 1.105] |
| combined | dates-2k | 0.969 [0.903, 1.093] | 0.978 [0.953, 1.020] | 1.011 [0.960, 1.057] |
| combined | cycle-300 | 1.048 [0.869, 1.179] | 0.957 [0.906, 1.036] | 1.010 [0.907, 1.024] |
| combined | undefined-10k | 0.909 [0.774, 1.220] | 0.980 [0.956, 1.036] | 1.004 [0.925, 1.054] |
| combined | numeric-10k | 0.974 [0.916, 1.037] | 1.038 [0.941, 1.063] | 1.025 [0.948, 1.073] |
| separate | deep-200 | 1.016 [0.906, 1.038] | 1.025 [1.022, 1.034] | not timed |
| separate | dates-2k | 0.948 [0.942, 1.038] | 0.982 [0.917, 1.055] | not timed |
| separate | cycle-300 | 0.979 [0.932, 1.262] | 1.034 [0.925, 1.235] | not timed |
| separate | undefined-10k | 1.056 [0.886, 1.191] | 1.036 [0.906, 1.039] | not timed |
| separate | numeric-10k | 0.989 [0.920, 1.161] | 1.005 [0.936, 1.079] | not timed |

## basecopy/base paired ratios

Median [minimum, maximum] across five paired processes. Exact-copy comparisons quantify variation without an implementation difference.

| Mode | Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|---|
| combined | deep-200 | 1.001 [0.887, 1.058] | 0.977 [0.924, 1.070] | 0.925 [0.737, 1.271] |
| combined | dates-2k | 1.099 [0.920, 1.313] | 1.044 [0.877, 1.113] | 1.016 [0.973, 1.105] |
| combined | cycle-300 | 1.150 [1.064, 1.155] | 1.018 [0.941, 1.050] | 1.000 [0.929, 1.050] |
| combined | undefined-10k | 0.959 [0.797, 1.051] | 0.983 [0.780, 1.036] | 1.030 [0.928, 1.076] |
| combined | numeric-10k | 1.009 [0.740, 1.044] | 0.975 [0.908, 1.044] | 0.970 [0.920, 1.011] |
| separate | deep-200 | 1.007 [0.870, 1.043] | 0.970 [0.933, 1.021] | not timed |
| separate | dates-2k | 0.954 [0.863, 1.017] | 0.945 [0.868, 1.044] | not timed |
| separate | cycle-300 | 1.004 [0.838, 1.078] | 0.992 [0.836, 1.026] | not timed |
| separate | undefined-10k | 0.885 [0.804, 1.068] | 1.011 [0.906, 1.079] | not timed |
| separate | numeric-10k | 1.019 [0.953, 1.188] | 1.009 [0.918, 1.083] | not timed |

## Acopy/basecopy paired ratios

Median [minimum, maximum] across five paired processes. Exact-copy comparisons quantify variation without an implementation difference.

| Mode | Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|---|
| combined | deep-200 | 1.069 [0.916, 1.085] | 1.045 [0.961, 1.077] | 0.991 [0.804, 1.188] |
| combined | dates-2k | 0.968 [0.785, 1.084] | 0.964 [0.914, 1.102] | 0.994 [0.946, 1.126] |
| combined | cycle-300 | 0.926 [0.876, 1.112] | 0.995 [0.952, 1.036] | 0.993 [0.893, 1.030] |
| combined | undefined-10k | 0.457 [0.419, 0.507] | 0.239 [0.234, 0.245] | 0.362 [0.332, 0.398] |
| combined | numeric-10k | 0.988 [0.897, 1.025] | 1.014 [0.917, 1.153] | 1.044 [0.940, 1.150] |
| separate | deep-200 | 1.052 [0.897, 1.070] | 1.025 [1.013, 1.083] | not timed |
| separate | dates-2k | 1.026 [0.971, 1.126] | 1.015 [0.963, 1.117] | not timed |
| separate | cycle-300 | 1.069 [0.923, 1.292] | 1.051 [0.952, 1.248] | not timed |
| separate | undefined-10k | 0.522 [0.449, 0.572] | 0.238 [0.228, 0.273] | not timed |
| separate | numeric-10k | 0.946 [0.880, 1.144] | 0.994 [0.942, 1.088] | not timed |

## Causal limits and disposition

Separate export bundles change compilation/module context and generated code layout while retaining the same algorithms. The result is consistent with context-sensitive execution and measurement variation; it does not identify a particular JIT optimization, deoptimization, cache effect or process-order mechanism. No engine internals or CPU profiles were collected. The combined baseline cycle encoder being slower in every exact-copy comparison is a direct warning against treating repeated direction alone as causal evidence.

This diagnosis weakens the claim that the three earlier slower ratios are stable intrinsic costs of A. It does not establish that they are absent under other workloads or that A satisfies strict full-suite no-other-regression. The large undefined gain is well supported here; the rest-performance acceptance question remains unresolved. Preserve the existing baseline and artifacts; no automatic adoption or follow-up experiment is authorized by this report.

`summary.json` preserves every paired ratio and absolute distribution, `samples.json` all200 rows and timing batches, and `receipt.json` the completed bound. Payload and incidental occupancy fields remain in the reused worker output; no separate memory diagnosis was performed. Prior full-matrix artifacts remain untouched.

Reproduction requires renewed exclusive coordination and overwrites these results:

```sh
source /workspace/shared/escapace-dev/activate.sh
python3 /workspace/reconcile-upstream/scripts/bounded-check.py --seconds 295 --receipt /workspace/serialization-lab/scalar-a-diagnosis/receipt.json -- python3 /workspace/serialization-lab/scalar-a-diagnosis/round.py
```
