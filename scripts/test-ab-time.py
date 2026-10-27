"""Checks the decision logic of ab-time.py without running a measurement."""

import importlib.util
import pathlib
import sys

sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location(
    "ab_time", pathlib.Path(__file__).resolve().parent / "ab-time.py",
)
ab = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ab)

# Too few pairs give no interval, so identical code cannot read as a significant change.
assert ab.interval([-14.0, -13.0]) is None
assert ab.reading(-14.0, None, 2.0, 3.0) == "too few pairs"

changes = [-4.0, -3.5, -3.0, -2.5, -3.2, -2.8, -3.1, -2.9, -3.3, -2.7]
low, high = ab.interval(changes)
assert low <= -3.0 <= high < 0, (low, high)
assert ab.reading(-3.0, [low, high], 2.0, 3.0) == "faster"
assert ab.reading(-1.0, [-1.5, -0.5], 2.0, 3.0) == "slightly faster"  # below the minimum gain
assert ab.reading(0.5, [-1.5, 2.0], 2.0, 3.0) == "unresolved"
assert ab.reading(4.0, [3.5, 4.5], 2.0, 3.0) == "slower"
assert ab.reading(2.0, [1.0, 3.0], 2.0, 3.0) == "slightly slower"  # resolved, within the guard
assert ab.interval([0.0] * 10) == [0.0, 0.0]

# Automatic batches target the measured seconds at the faster tree's batch time.
preflight = [
    {"scenario": "reconcile", "elapsedMs": 75.0, "wallSeconds": 0.65},
    {"scenario": "reconcile", "elapsedMs": 100.0, "wallSeconds": 0.7},
    {"scenario": "snapshot", "elapsedMs": 5.0, "wallSeconds": 0.41},
    {"scenario": "snapshot", "elapsedMs": 5.0, "wallSeconds": 0.41},
]
counts = ab.batch_counts(preflight, "auto", "auto", 1.0)
assert counts["reconcile"] == {"batches": 67, "warmup": 33}, counts  # 15 ms per batch
assert counts["snapshot"] == {"batches": 1000, "warmup": 500}, counts
assert ab.batch_counts(preflight, 20, 10, 1.0)["snapshot"] == {"batches": 20, "warmup": 10}
assert ab.batch_counts([{"scenario": "x", "elapsedMs": 3000.0, "wallSeconds": 3.5}], "auto", "auto", 1.0)[
    "x"
]["batches"] == 20  # never fewer than 20

# The estimate is per-process startup plus the loop time of every batch, times the pairs.
# A preflight runs 5 warmup and 5 measured batches: 50 ms measured, 0.6 s wall, 0.5 s startup.
one = [{"scenario": "x", "elapsedMs": 50.0, "wallSeconds": 0.6}]
assert abs(ab.estimate_seconds(one, 2, {"x": {"batches": 10, "warmup": 5}}) - 2 * (0.5 + 0.15)) < 1e-9

# The frozen scenarios share one bundle per tree, every other scenario the overlay's.
assert [ab.harness(name) for name in ("produce", "serialize", "reconcile-1", "diag-views")] == [
    "frozen", "overlay", "overlay", "overlay",
]

print("ab-time decision logic verified")
