"""Alternating whole-process A/B timing round over frozen harness bundles (``pnpm bench ab``).

Bundles each source tree once per scenario through ``scripts/profile.ts --bundle-only``, runs
every bundle for a few batches, sizes each scenario's batches (about ``--seconds`` of measured
work per process by default) and stops if the round would not fit the budget. It then registers
the design (scenarios, pairs, batches, size, bundle hashes, Node version, tree commits, frozen
workload hashes) before any sample is taken, and alternates candidate/baseline order per pair in
fresh Node processes. Every completed sample is persisted immediately. ``pnpm bench`` runs the
round, including bundling and descendant shutdown, under one 295-second budget; a timeout is
incomplete evidence, not a pass.

Each scenario reports the median paired change (negative is faster), a bootstrap 90% interval
from 10 pairs on, the count of faster pairs and a reading. The default round (ten pairs of all
six scenarios at half a second each) checks for regressions; a deciding round selects one
scenario, or two frozen ones, and runs ``--pairs 32 --seconds 1``.

Usage:
  pnpm bench ab --baseline <tree> [--candidate <tree>] [--scenario name]... [--pairs 10]
    [--batches auto] [--seconds 0.5] [--warmup auto] [--size 256] [--gain 2] [--guard 3] --out <dir>
"""

import argparse
import hashlib
import json
import pathlib
import random
import statistics
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent


def parse_arguments(argv):
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0], formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--baseline", required=True, help="frozen control source tree")
    parser.add_argument("--candidate", default=str(ROOT), help="candidate source tree")
    parser.add_argument("--scenario", action="append", required=True, dest="scenarios",
                        help="a scenario or diag-* diagnostic; repeat for more")
    parser.add_argument("--pairs", type=int, default=10, help="an even count, so each order runs equally")
    parser.add_argument("--batches", default="auto",
                        help="batches per process, or auto for about --seconds of measured work")
    parser.add_argument("--seconds", type=float, default=0.5,
                        help="measured seconds per process when --batches is auto")
    parser.add_argument("--warmup", default="auto", help="warmup batches, or auto for half the batches")
    parser.add_argument("--size", type=int, default=256, help="diagnostic size")
    parser.add_argument("--guard", type=float, default=3.0, help="regression guard in percent")
    parser.add_argument("--gain", type=float, default=2.0, help="minimum gain in percent")
    parser.add_argument("--out", required=True, help="new output directory")
    arguments = parser.parse_args(argv)
    if arguments.pairs < 2 or arguments.pairs % 2 != 0:
        parser.error("--pairs must be an even integer >= 2")
    for name, minimum in (("batches", 1), ("warmup", 0)):
        value = getattr(arguments, name)
        if value != "auto":
            if not value.isdigit() or int(value) < minimum:
                parser.error(f"--{name} must be auto or an integer >= {minimum}")
            setattr(arguments, name, int(value))
    if arguments.size < 1 or arguments.seconds <= 0:
        parser.error("--size and --seconds must be positive")
    return arguments


def bundle(root, scenario, size, destination):
    destination.mkdir(parents=True, exist_ok=True)
    command = [
        "pnpm", "exec", "tsx", "scripts/profile.ts", scenario, "--candidate", str(root),
        "--mode", "time", "--size", str(size), "--bundle-only", "--out", str(destination),
    ]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode != 0:
        raise RuntimeError(f"Bundling {scenario} from {root} failed:\n{result.stdout}{result.stderr}")
    for line in result.stdout.splitlines():
        if line.startswith("RECONCILE_BUNDLE "):
            return line.removeprefix("RECONCILE_BUNDLE ").strip()
    raise RuntimeError(f"No bundle path reported for {scenario} from {root}")


def measure(bundle_path, scenario, batches, warmup, log_path):
    started = time.monotonic()
    result = subprocess.run(
        ["node", bundle_path, scenario, str(batches), str(warmup)], text=True, capture_output=True,
    )
    log_path.write_text(result.stdout + result.stderr)
    if result.returncode != 0:
        raise RuntimeError(f"{scenario} failed, see {log_path}")
    for line in result.stdout.splitlines():
        if line.startswith("RECONCILE_TIME "):
            report = json.loads(line.removeprefix("RECONCILE_TIME "))
            return {"wallSeconds": time.monotonic() - started, **report}
    raise RuntimeError(f"No timing record for {scenario}, see {log_path}")


BUDGET_SECONDS = 280  # within the dispatcher's 295-second budget, leaving room for shutdown
ESTIMATE_MARGIN = 1.15  # the estimate has run up to 7% short
MIN_INTERVAL_PAIRS = 10


def interval(changes, draws=2000):
    """Bootstrap 90% interval of the median paired change, with a fixed seed.

    Fewer than ``MIN_INTERVAL_PAIRS`` pairs give no interval: a percentile bootstrap of so few
    pairs can exclude zero for identical code.
    """
    if len(changes) < MIN_INTERVAL_PAIRS:
        return None
    generator = random.Random(0x9E3779B9)
    medians = sorted(
        statistics.median(generator.choices(changes, k=len(changes))) for _ in range(draws)
    )
    return [medians[int(draws * 0.05)], medians[int(draws * 0.95) - 1]]


def reading(median, bounds, gain, guard):
    """Classifies one round. A resolved change (interval excluding zero) reads faster or slower
    beyond the gain or guard and slightly faster or slower within them."""
    if bounds is None:
        return "too few pairs"
    if bounds[1] < 0:
        return "faster" if median <= -gain else "slightly faster"
    if bounds[0] > 0:
        return "slower" if median >= guard else "slightly slower"
    return "unresolved"


PREFLIGHT_BATCHES = 5
PREFLIGHT_WARMUP = 5


def batch_counts(preflight, batches, warmup, seconds):
    """Batches and warmup per scenario: explicit counts, or enough for ``seconds`` of measured work
    at the faster tree's preflight batch time (at least 20), with half as many warmup batches.
    A preflight still runs partly cold, so its batch time is an upper bound."""
    counts = {}
    for scenario in {sample["scenario"] for sample in preflight}:
        batch = min(
            sample["elapsedMs"] / 1000 / PREFLIGHT_BATCHES
            for sample in preflight
            if sample["scenario"] == scenario
        )
        measured = batches if batches != "auto" else max(20, round(seconds / batch))
        counts[scenario] = {
            "batches": measured,
            "warmup": warmup if warmup != "auto" else measured // 2,
        }
    return counts


def estimate_seconds(preflight, pairs, counts):
    """Predicts the sampling time of the round from the preflight runs."""
    total = 0.0
    for sample in preflight:
        loop = sample["elapsedMs"] / 1000
        count = counts[sample["scenario"]]
        startup = sample["wallSeconds"] - loop * (PREFLIGHT_BATCHES + PREFLIGHT_WARMUP) / PREFLIGHT_BATCHES
        total += max(startup, 0) + loop / PREFLIGHT_BATCHES * (
            count["batches"] + count["warmup"]
        )
    return total * pairs


def git_state(root):
    """The commit and whether the tree has uncommitted changes, or None outside git."""
    head = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], text=True, capture_output=True)
    if head.returncode != 0:
        return None
    status = subprocess.run(["git", "-C", str(root), "status", "--porcelain"], text=True, capture_output=True)
    return {"commit": head.stdout.strip(), "dirty": bool(status.stdout.strip())}


def frozen_hash(root):
    """Hash of the frozen workload files, which both trees must share."""
    digest = hashlib.sha256()
    for name in ("perf/scenarios.ts", "perf/config.ts", "perf/profile-harness.ts"):
        path = root / name
        digest.update(path.read_bytes() if path.exists() else b"missing")
    return digest.hexdigest()


def run_round(arguments):
    started = time.monotonic()
    out = pathlib.Path(arguments.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    scenarios = list(dict.fromkeys(arguments.scenarios))
    roots = {
        "candidate": pathlib.Path(arguments.candidate).resolve(),
        "baseline": pathlib.Path(arguments.baseline).resolve(),
    }
    bundles = {label: {} for label in roots}
    for label, root in roots.items():
        for scenario in scenarios:
            bundles[label][scenario] = bundle(
                root, scenario, arguments.size, out / "bundles" / label / scenario,
            )
    # One short run of every bundle, so a tree that lacks a scenario fails before any sample.
    preflight = [
        {"scenario": scenario, **measure(
            path, scenario, PREFLIGHT_BATCHES, PREFLIGHT_WARMUP,
            out / f"preflight-{scenario}-{label}.log",
        )}
        for label, paths in bundles.items()
        for scenario, path in paths.items()
    ]
    counts = batch_counts(preflight, arguments.batches, arguments.warmup, arguments.seconds)
    estimate = estimate_seconds(preflight, arguments.pairs, counts)
    remaining = BUDGET_SECONDS - (time.monotonic() - started)
    if estimate * ESTIMATE_MARGIN > remaining:
        raise SystemExit(
            f"The round needs about {estimate:.0f} s of sampling but {remaining:.0f} s remain in the "
            "budget; select fewer scenarios, pairs or batches.",
        )
    frozen = {label: frozen_hash(root) for label, root in roots.items()}
    if frozen["candidate"] != frozen["baseline"]:
        print("Warning: the trees' perf/ workloads differ, so the scenarios are not the same.")
    plan = {
        "batches": counts,
        "bundles": bundles,
        "estimatedSamplingSeconds": estimate,
        "frozenWorkloadSha256": frozen,
        "gainPercent": arguments.gain,
        "git": {label: git_state(root) for label, root in roots.items()},
        "node": subprocess.run(["node", "--version"], text=True, capture_output=True).stdout.strip(),
        "guardPercent": arguments.guard,
        "pairs": arguments.pairs,
        "roots": {label: str(root) for label, root in roots.items()},
        "scenarios": scenarios,
        "size": arguments.size,
        "sha256": {
            label: {
                scenario: hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
                for scenario, path in paths.items()
            }
            for label, paths in bundles.items()
        },
        "measuredSecondsPerProcess": arguments.seconds,
    }
    (out / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    rows = []
    for pair in range(arguments.pairs):
        order = ["candidate", "baseline"] if pair % 2 == 0 else ["baseline", "candidate"]
        for scenario in scenarios:
            for label in order:
                sample = measure(
                    bundles[label][scenario], scenario, counts[scenario]["batches"],
                    counts[scenario]["warmup"], out / f"{pair}-{scenario}-{label}.log",
                )
                rows.append({"label": label, "pair": pair, "scenario": scenario, **sample})
                (out / "samples.json").write_text(json.dumps(rows, indent=2) + "\n")
        print(f"Completed pair {pair + 1}/{arguments.pairs}", flush=True)
    summary = {}
    lines = [
        "| Workload | Baseline median µs/op | Candidate median µs/op | Median paired change "
        "| 90% interval | Faster pairs | Pairs slower than guard | Reading |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |",
    ]
    for scenario in scenarios:
        samples = [row for row in rows if row["scenario"] == scenario]
        candidate = [row["elapsedMs"] for row in samples if row["label"] == "candidate"]
        baseline = [row["elapsedMs"] for row in samples if row["label"] == "baseline"]
        operations = samples[0]["operations"]
        changes = [100 * (left / right - 1) for left, right in zip(candidate, baseline)]
        summary[scenario] = {
            "baselineMedianUsPerOperation": statistics.median(baseline) * 1000 / operations,
            "candidateMedianUsPerOperation": statistics.median(candidate) * 1000 / operations,
            "medianPairedPercentChange": statistics.median(changes),
            "medianPairedPercentInterval": interval(changes),
            "pairedPercentChanges": changes,
            "fasterPairs": sum(change < 0 for change in changes),
            "slowerPairsAboveGuard": sum(change > arguments.guard for change in changes),
        }
        entry = summary[scenario]
        bounds = entry["medianPairedPercentInterval"]
        entry["reading"] = reading(
            entry["medianPairedPercentChange"], bounds, arguments.gain, arguments.guard,
        )
        shown = "n/a" if bounds is None else f"[{bounds[0]:+.2f}%, {bounds[1]:+.2f}%]"
        lines.append(
            f"| {scenario} | {entry['baselineMedianUsPerOperation']:.2f} | "
            f"{entry['candidateMedianUsPerOperation']:.2f} | "
            f"{entry['medianPairedPercentChange']:+.2f}% | "
            f"{shown} | {entry['fasterPairs']}/{len(changes)} | "
            f"{entry['slowerPairsAboveGuard']}/{len(changes)} | {entry['reading']} |"
        )
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    report = "\n".join(lines)
    (out / "report.md").write_text(
        "# Alternating A/B timing round\n\nNegative changes mean the candidate is faster. "
        "Medians of paired whole-process loop latency; no cumulative or general speedup is inferred. "
        f"A reading is faster when the interval is below zero and the median gains at least "
        f"{arguments.gain:g}%, slower when the interval is above zero and the median exceeds the "
        f"{arguments.guard:g}% guard, and slightly faster or slower when the interval excludes "
        "zero within those limits. Keeping a change needs two independent faster rounds.\n\n"
        + report + "\n",
    )
    print(report)
    print("Negative is faster. Keeping a change needs two independent rounds that read faster.")


def main(argv):
    run_round(parse_arguments(argv))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
