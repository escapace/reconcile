# Final native-array codec comparison

The final candidate passes all20 measured fidelity fixtures, including sparse arrays with exact holes and explicit undefined. Its codec-only bundle is smaller than the preserved typed prior. Sparse decode is faster than that prior in this corpus; other timings vary by workload. No blanket performance-parity or general speedup claim is made.

All240 observations completed in48.26seconds under the295second bound. No follow-up experiment ran. The parent independently verified all285 frozen validation inputs unchanged afterward. Measured built candidate SHA-256: `37cdfa0494779526e6a4c1f62cf3197796dfcc337460fd3c66e5aa84e6a54514`.

## Scope and references

Candidate is the final `/workspace/reconcile-serialization/lib/neutral/index.js` codec, restored to native sparse-array allocation for trusted application state. Core implementation changes and allocator research are outside this comparison. The accepted memory cost is not presented as a solved problem.

References are the preserved closer typed-prior codec; accepted aligned v8 with its selected explicit-frame/synchronous-leaf/direct-dense settings; and raw pinned devalue6.0.3 without adapters. v8 retains its format identifier and experimental fixed caps, while candidate and typed prior use identifier-free wire. These differences prevent attributing all v8 comparisons to the decoder change alone.

All four arms were rebundled with identical browser/ES2020 esbuild options for encode, decode, both, core-only and codec+core exports. The candidate and typed-prior encoders are unchanged; their observed encode latency differences are measurement variation, not demonstrated algorithmic improvements. Core-only output is exactly the same size between these two arms. It is not byte-size-identical to the older frozen upstream core reference because the integrated API/error surface differs.

## Fidelity

Candidate, v8 and typed prior pass every fixture in all three repetitions. Independent graph-bijection checks cover aliases/cycles/distinct identity, prototypes, special numbers, sparse holes versus explicit undefined, shared backing buffers and view spans, collection order, URL-owned parameters, and exact Temporal state. The Temporal fixture uses intrinsic equality, exact Duration components and intrinsic MonthDay/YearMonth strings including hidden ISO reference dates.

Raw devalue produces these same failures in all three repetitions:

| Fixture | Observed failure | Timing treatment |
|---|---|---|
| deep-2000 | Encoding stack overflow | Rejection recorded; not comparable successful encoding |
| url-linked | URLSearchParams shared identity split | No comparable codec timings |
| temporal-exact | Native Temporal equality mismatch | No comparable codec timings |

All other devalue fixtures pass, including shared views and sparse arrays. Exclusions are fixture-specific, not a claim that every URL or Temporal value fails.

## Actual sparse JSON

For the JavaScript value `[1, /* hole */, undefined, 4]`, candidate and typed prior emit:

```json
[-1,[],[[3,4,0,1,2,[-1],3,4]]]
```

v8 emits the same body with its leading format identifier:

```json
[4,-1,[],[[3,4,0,1,2,[-1],3,4]]]
```

Raw devalue emits:

```json
[[1,-2,-1,2],1,4]
```

Ordinary JSON.parse returns these encoded arrays. The corresponding codec parse reconstructs an array of length4 with index1 absent, index2 present with undefined, and values1 and4 at the ends. All example round trips were verified in the measured worker.

## Bundle sizes

| Codec | Export | Minified B | gzip B |
|---|---|---:|---:|
| typed | encode | 7,686 | 3,043 |
| typed | decode | 7,153 | 2,930 |
| typed | both | 13,238 | 5,091 |
| typed | core | 47,778 | 17,264 |
| typed | combined | 60,030 | 21,530 |
| v8 | encode | 7,400 | 2,872 |
| v8 | decode | 6,731 | 2,786 |
| v8 | both | 12,814 | 4,847 |
| v8 | core | 47,773 | 17,278 |
| v8 | combined | 60,708 | 21,712 |
| devalue | encode | 6,692 | 2,776 |
| devalue | decode | 4,521 | 1,768 |
| devalue | both | 10,823 | 4,011 |
| devalue | core | 47,773 | 17,278 |
| devalue | combined | 58,649 | 20,934 |
| candidate | encode | 7,686 | 3,043 |
| candidate | decode | 6,927 | 2,862 |
| candidate | both | 13,012 | 5,021 |
| candidate | core | 47,778 | 17,264 |
| candidate | combined | 59,804 | 21,473 |

Candidate both is5,021B gzip versus typed prior5,091B, v8 4,847B and devalue4,011B. Candidate core-only is47,778B minified/17,264B gzip, exactly matching typed prior; the older frozen-core entry used with v8/devalue is47,773B/17,278B. Matching integrated core sizes alone do not prove absence of retained initialization; byte equality was not asserted by this size harness.

## Candidate latency and payload

Times are process medians in microseconds. Each of three rotated fresh processes uses five warmups and three timed batches of at least8ms, capped at100,000 operations. Large single operations can exceed8ms. Encode, decode and full roundtrip are independently measured; roundtrip is not their arithmetic sum. Wire size is UTF-8 and gzip level9.

| Fixture | Encode µs | Decode µs | Roundtrip µs | Wire B | gzip B |
|---|---:|---:|---:|---:|---:|
| numeric-10k | 816.21 | 264.85 | 1121.06 | 65,579 | 22,884 |
| undefined-10k | 703.51 | 695.23 | 1238.67 | 50,019 | 126 |
| mixed-10k | 881.05 | 787.24 | 1377.57 | 60,760 | 10,063 |
| records-small | 2.95 | 2.39 | 3.89 | 108 | 106 |
| records-1k | 958.23 | 502.87 | 1341.42 | 54,904 | 14,863 |
| records-10k | 17927.24 | 4594.56 | 19468.07 | 618,410 | 137,854 |
| dag-2k | 1344.87 | 507.92 | 1516.86 | 39,876 | 10,154 |
| dense-dag | 1240.56 | 308.74 | 1221.43 | 47,009 | 5,572 |
| cycle-300 | 160.54 | 85.58 | 208.16 | 5,707 | 1,833 |
| deep-200 | 71.95 | 44.58 | 110.87 | 2,130 | 469 |
| deep-2000 | 1015.03 | 544.12 | 1037.94 | 22,932 | 4,671 |
| collections | 525.04 | 219.28 | 662.70 | 19,638 | 6,344 |
| dates-2k | 342.02 | 340.87 | 571.95 | 27,804 | 9,563 |
| rich | 11.84 | 6.56 | 14.99 | 372 | 224 |
| views-shared | 9.46 | 5.85 | 15.43 | 1,457 | 112 |
| binary-1m | 7529.19 | 3078.62 | 11919.30 | 1,398,193 | 1,053,150 |
| url-linked | 279.55 | 164.19 | 335.31 | 8,453 | 1,566 |
| temporal-exact | 448.47 | 534.06 | 839.99 | 7,586 | 577 |
| hole-first | 836.93 | 346.11 | 1254.17 | 97,795 | 12,421 |
| hole-last | 761.56 | 328.04 | 1005.08 | 97,789 | 12,414 |

## Candidate/typed paired ratios

Median [minimum, maximum] across paired process repetitions; less than1 favors candidate. Ranges describe observed variation, not confidence intervals. Mismatching fixtures have no comparable ratio.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.00 [0.75, 1.09] | 1.02 [0.94, 1.04] | 1.08 [0.97, 1.20] |
| undefined-10k | 0.94 [0.67, 1.05] | 1.02 [0.97, 1.07] | 0.96 [0.93, 1.06] |
| mixed-10k | 1.25 [0.84, 1.35] | 0.99 [0.84, 1.43] | 0.98 [0.90, 1.11] |
| records-small | 1.10 [0.88, 1.19] | 1.13 [0.75, 1.25] | 0.96 [0.94, 0.97] |
| records-1k | 0.88 [0.76, 0.99] | 0.91 [0.81, 0.98] | 0.94 [0.89, 1.02] |
| records-10k | 1.00 [0.92, 1.04] | 1.00 [0.93, 1.05] | 1.08 [0.83, 1.12] |
| dag-2k | 1.06 [1.03, 1.24] | 1.18 [0.86, 1.29] | 1.14 [1.06, 1.15] |
| dense-dag | 1.48 [0.95, 1.53] | 0.97 [0.93, 1.12] | 0.94 [0.93, 1.02] |
| cycle-300 | 0.86 [0.82, 1.01] | 1.11 [1.00, 1.42] | 0.95 [0.93, 0.99] |
| deep-200 | 1.07 [0.99, 1.07] | 0.97 [0.85, 1.07] | 0.98 [0.87, 1.04] |
| deep-2000 | 1.06 [0.89, 1.10] | 1.07 [0.95, 1.15] | 0.89 [0.87, 0.97] |
| collections | 0.84 [0.58, 0.92] | 1.03 [1.00, 1.04] | 0.95 [0.86, 1.02] |
| dates-2k | 1.09 [1.07, 1.11] | 1.06 [0.96, 1.24] | 1.03 [0.90, 1.05] |
| rich | 0.96 [0.87, 1.06] | 0.76 [0.69, 0.96] | 0.98 [0.91, 1.01] |
| views-shared | 0.91 [0.90, 1.10] | 1.05 [1.05, 1.34] | 1.01 [0.98, 1.54] |
| binary-1m | 0.94 [0.92, 1.05] | 0.99 [0.88, 1.04] | 1.09 [1.04, 1.28] |
| url-linked | 1.11 [1.09, 1.25] | 1.13 [1.00, 1.24] | 1.08 [1.02, 1.15] |
| temporal-exact | 1.15 [1.06, 1.22] | 1.09 [1.01, 1.12] | 1.06 [0.97, 1.13] |
| hole-first | 0.98 [0.93, 1.00] | 0.54 [0.51, 0.58] | 0.76 [0.72, 0.79] |
| hole-last | 1.03 [0.95, 1.04] | 0.54 [0.49, 0.55] | 0.76 [0.72, 0.79] |

## Candidate/v8 paired ratios

Median [minimum, maximum] across paired process repetitions; less than1 favors candidate. Ranges describe observed variation, not confidence intervals. Mismatching fixtures have no comparable ratio.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 1.04 [0.85, 1.07] | 0.96 [0.87, 1.02] | 0.97 [0.94, 1.18] |
| undefined-10k | 1.05 [0.88, 1.09] | 0.84 [0.68, 0.95] | 0.98 [0.84, 1.05] |
| mixed-10k | 1.23 [0.95, 1.33] | 1.06 [1.00, 1.41] | 1.02 [1.01, 1.17] |
| records-small | 0.92 [0.87, 1.20] | 0.98 [0.67, 1.31] | 1.04 [0.91, 1.07] |
| records-1k | 0.91 [0.87, 0.95] | 0.93 [0.89, 0.97] | 0.96 [0.93, 0.99] |
| records-10k | 1.01 [1.00, 1.20] | 0.97 [0.95, 0.98] | 0.84 [0.78, 1.10] |
| dag-2k | 1.05 [1.04, 1.38] | 1.19 [0.87, 1.20] | 1.02 [0.98, 1.08] |
| dense-dag | 1.20 [1.01, 1.54] | 0.94 [0.71, 1.05] | 0.94 [0.84, 0.98] |
| cycle-300 | 1.00 [0.98, 1.05] | 1.00 [0.97, 1.37] | 0.97 [0.93, 1.02] |
| deep-200 | 0.87 [0.84, 1.10] | 0.97 [0.73, 1.05] | 0.98 [0.95, 1.15] |
| deep-2000 | 1.25 [0.99, 1.38] | 1.17 [1.01, 1.32] | 0.94 [0.92, 0.95] |
| collections | 0.71 [0.64, 0.95] | 0.98 [0.64, 1.02] | 0.93 [0.91, 0.98] |
| dates-2k | 1.01 [0.72, 1.19] | 1.12 [0.83, 1.17] | 0.94 [0.87, 0.95] |
| rich | 0.99 [0.74, 1.23] | 0.90 [0.73, 0.93] | 0.95 [0.82, 0.99] |
| views-shared | 1.00 [0.97, 1.18] | 0.97 [0.95, 1.37] | 1.04 [0.94, 1.58] |
| binary-1m | 0.97 [0.96, 0.99] | 0.93 [0.60, 1.03] | 1.10 [0.94, 1.26] |
| url-linked | 1.55 [1.10, 1.57] | 1.08 [1.07, 1.62] | 0.94 [0.81, 1.11] |
| temporal-exact | 1.03 [0.99, 1.26] | 0.92 [0.85, 1.09] | 0.92 [0.91, 0.97] |
| hole-first | 0.97 [0.88, 1.01] | 1.02 [0.83, 1.04] | 0.99 [0.88, 1.09] |
| hole-last | 1.04 [0.91, 1.10] | 0.98 [0.85, 1.05] | 0.88 [0.84, 0.97] |

## Candidate/devalue paired ratios

Median [minimum, maximum] across paired process repetitions; less than1 favors candidate. Ranges describe observed variation, not confidence intervals. Mismatching fixtures have no comparable ratio.

| Fixture | Encode | Decode | Roundtrip |
|---|---|---|---|
| numeric-10k | 0.32 [0.28, 0.32] | 0.45 [0.42, 0.45] | 0.33 [0.28, 0.36] |
| undefined-10k | 1.35 [1.30, 1.35] | 4.16 [3.82, 4.24] | 1.90 [1.77, 1.95] |
| mixed-10k | 0.80 [0.53, 0.83] | 1.35 [1.15, 2.03] | 0.98 [0.91, 1.16] |
| records-small | 0.96 [0.73, 1.01] | 1.34 [1.18, 1.56] | 1.00 [0.99, 1.12] |
| records-1k | 0.66 [0.62, 0.70] | 0.84 [0.79, 0.87] | 0.81 [0.73, 0.82] |
| records-10k | 0.95 [0.91, 1.06] | 0.59 [0.57, 0.69] | 0.64 [0.56, 0.85] |
| dag-2k | 0.89 [0.83, 1.63] | 0.91 [0.84, 0.95] | 0.99 [0.97, 1.03] |
| dense-dag | 0.94 [0.53, 1.25] | 0.61 [0.60, 0.82] | 0.96 [0.89, 0.99] |
| cycle-300 | 0.68 [0.58, 0.81] | 0.75 [0.71, 1.06] | 0.83 [0.74, 0.85] |
| deep-200 | 1.20 [1.07, 1.35] | 0.98 [0.87, 1.25] | 1.19 [1.12, 1.34] |
| collections | 0.76 [0.73, 0.94] | 0.88 [0.80, 0.88] | 0.94 [0.91, 0.95] |
| dates-2k | 0.26 [0.23, 0.27] | 0.47 [0.40, 0.47] | 0.27 [0.26, 0.33] |
| rich | 1.01 [0.88, 1.19] | 0.90 [0.70, 0.92] | 1.06 [0.99, 1.10] |
| views-shared | 1.13 [1.12, 1.55] | 1.13 [1.01, 1.22] | 1.27 [1.04, 1.54] |
| binary-1m | 1.00 [0.91, 1.08] | 0.96 [0.95, 1.01] | 1.09 [1.09, 1.34] |
| hole-first | 0.55 [0.51, 0.58] | 0.94 [0.90, 0.96] | 0.65 [0.61, 0.67] |
| hole-last | 0.47 [0.44, 0.50] | 0.85 [0.84, 0.85] | 0.51 [0.50, 0.58] |

Relative to the closer typed prior, both sparse decode medians are approximately0.54×; their roundtrip medians are approximately0.76×. Other decoder outcomes are mixed, including slower DAG and native fixture medians. Candidate versus v8 or devalue varies further by workload and supported fidelity. The unchanged-encoder ratios illustrate the noise of this short screen; do not interpret isolated encode ratios as improvements/regressions caused by the decoder edit.

Across all three pairs versus typed prior, DAG roundtrip was slower by6.2–14.7% (median13.9%), binary1m roundtrip by3.7–28.3% (median9.5%), URL decode by0.4–24.4% (median13.4%), and Temporal decode by1.3–11.5% (median8.5%). These are notable repeated observations in this short screen, not established causal effects of the sparse allocation change or a formal significance test.

## Memory and sparse allocation cost

Values below are retained heap bytes after two explicit GCs, median [minimum, maximum]. Inputs remain live; encoded text also remains live during decode. Small negative values are runtime cleanup/noise. Raw rows additionally retain immediate post-call heap, external memory and process maxRSS growth.

| Fixture | Candidate encode heap B | Candidate decode heap B | Typed prior decode heap B |
|---|---:|---:|---:|
| numeric-10k | 96,312 [96,312, 187,920] | 171,352 [167,640, 171,568] | 169,480 [72,072, 173,232] |
| undefined-10k | 491,200 [485,712, 492,024] | 741,984 [734,240, 742,048] | 742,016 [319,848, 745,328] |
| mixed-10k | 538,400 [538,400, 547,328] | 639,224 [191,512, 641,392] | 650,496 [645,680, 651,160] |
| records-small | 10,712 [10,712, 10,712] | 6,824 [6,824, 6,824] | 6,856 [6,856, 6,856] |
| records-1k | 635,672 [635,624, 637,800] | 431,008 [188,000, 431,008] | 419,880 [199,792, 434,488] |
| records-10k | 680,648 [680,600, 680,648] | 3,957,184 [3,953,432, 3,959,792] | 3,960,016 [3,960,016, 3,962,304] |
| dag-2k | 612,936 [84,928, 614,288] | 371,312 [155,944, 373,560] | 155,976 [155,976, 384,824] |
| dense-dag | 422,224 [421,768, 423,976] | 167,744 [154,928, 167,976] | 155,192 [155,152, 168,200] |
| cycle-300 | 133,696 [133,696, 133,880] | 77,552 [76,920, 80,952] | 80,984 [77,008, 80,984] |
| deep-200 | 29,616 [29,616, 29,616] | 28,704 [27,328, 28,704] | 28,704 [27,328, 28,704] |
| deep-2000 | 54,264 [51,872, 553,144] | 131,752 [130,856, 131,752] | 134,888 [131,752, 314,952] |
| collections | 69,592 [69,288, 69,592] | 110,616 [110,496, 114,480] | 110,616 [110,616, 222,192] |
| dates-2k | 76,304 [76,040, 76,304] | 224,952 [224,952, 404,504] | 226,584 [226,576, 406,128] |
| rich | 27,456 [27,456, 27,456] | 26,600 [26,600, 26,600] | 26,632 [26,632, 26,632] |
| views-shared | 12,712 [12,712, 12,712] | 9,616 [9,616, 9,616] | 9,616 [9,616, 9,616] |
| binary-1m | 1,409,824 [1,409,824, 1,409,824] | 12,640 [12,640, 12,640] | 12,640 [12,640, 12,640] |
| url-linked | 88,944 [81,952, 139,224] | 84,904 [26,032, 84,904] | 84,936 [84,936, 84,992] |
| temporal-exact | 62,312 [62,312, 62,512] | 39,872 [39,872, 39,872] | 38,584 [38,528, 39,904] |
| hole-first | 324,888 [324,888, 324,888] | 53,056 [46,272, 246,760] | 45,112 [-110,224, 258,808] |
| hole-last | 328,288 [137,536, 335,984] | 250,200 [52,704, 252,296] | 250,992 [250,992, 251,040] |

The sparse benchmark fixtures are length10,000 with one missing index, not million-length mostly-empty arrays. Their final candidate decode heap deltas are reported above but are noisy and include more than array element storage. This round does not remeasure the earlier approximately8MB million-length native-hole allocation; it must not be cited as a new confirmation of that exact figure. Native length-based sparse allocation remains the explicitly accepted tradeoff.

These are occupancy deltas, not cumulative allocation or true peak heap. `maxRSSGrowthKiB` is process-lifetime RSS highwater growth during each phase, not isolated phase peak: previous phases may have already established the highwater mark, and RSS includes nonheap memory. All four arms' memory distributions remain in `summary.json` and raw snapshots in `samples.json`.

## Reproduction and limits

The stopped MAX-index experiment and preserved dense-only benchmark were not rerun or overwritten. The Node invocation uses `--harmony-temporal --expose-gc` without `--js-base-64`, exercising the default fallback base64 path. This final comparison does not measure core API performance, browser performance, native base64 latency or true heap peaks.

```sh
source /workspace/shared/escapace-dev/activate.sh
python3 /workspace/reconcile-upstream/scripts/bounded-check.py --seconds 295 --receipt /workspace/serialization-lab/release-codec-bench/receipt.json -- python3 /workspace/serialization-lab/release-codec-bench/round.py /workspace/reconcile-serialization/lib/neutral/index.js
```

`corpus.mjs` and `worker.mjs` define assertions and measurements; `build.mjs` defines export-specific bundles; `sizes.json`, `samples.json`, `summary.json` and `receipt.json` retain evidence. Reexecution requires an exclusive slot and overwrites results. No further runs are scheduled, and this report does not authorize publication.
