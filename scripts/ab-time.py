"""Alternating whole-process A/B timing round over frozen harness bundles.

Bundles each source tree once per scenario through ``scripts/profile.ts --bundle-only``,
registers the design (scenarios, pairs, batches, warmup, bundle hashes, guard) before any
sample is taken, then alternates candidate/baseline order per pair in fresh Node processes.
Every completed sample is persisted immediately. The whole round, including bundling and
descendant shutdown, runs under one 295-second ``bounded-check.py`` budget; a timeout is
incomplete evidence, not a pass.

Usage:
  python3 scripts/ab-time.py --baseline /path/to/frozen-control [--candidate .]
    [--scenarios reconcile,produce,...] [--pairs 5] [--batches 20] [--warmup 10]
    [--guard 3] --out /tmp/ab-round
"""

import argparse
import hashlib
import json
import pathlib
import statistics
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCENARIOS = ["snapshot", "reconcile", "reconcile-plain-object", "produce"]


def parse_arguments(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--baseline", required=True, help="frozen control source tree")
    parser.add_argument("--candidate", default=str(ROOT), help="candidate source tree")
    parser.add_argument("--scenarios", default=",".join(SCENARIOS))
    parser.add_argument("--pairs", type=int, default=5)
    parser.add_argument("--batches", type=int, default=20)
    parser.add_argument("--warmup", type=int, default=10)
    parser.add_argument("--guard", type=float, default=3.0, help="regression guard in percent")
    parser.add_argument("--out", required=True, help="new output directory")
    parser.add_argument("--unbounded", action="store_true", help=argparse.SUPPRESS)
    return parser.parse_args(argv)


def bundle(root, scenario, destination):
    destination.mkdir(parents=True, exist_ok=True)
    command = [
        "pnpm", "exec", "tsx", "scripts/profile.ts", scenario, "--source", str(root),
        "--mode", "time", "--bundle-only", "--out", str(destination),
    ]
    output = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=True).stdout
    for line in output.splitlines():
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


def run_round(arguments):
    out = pathlib.Path(arguments.out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    scenarios = [name for name in arguments.scenarios.split(",") if name]
    roots = {
        "candidate": pathlib.Path(arguments.candidate).resolve(),
        "baseline": pathlib.Path(arguments.baseline).resolve(),
    }
    bundles = {label: {} for label in roots}
    for label, root in roots.items():
        for scenario in scenarios:
            bundles[label][scenario] = bundle(root, scenario, out / "bundles" / label / scenario)
    plan = {
        "batches": arguments.batches,
        "bundles": bundles,
        "guardPercent": arguments.guard,
        "pairs": arguments.pairs,
        "roots": {label: str(root) for label, root in roots.items()},
        "scenarios": scenarios,
        "sha256": {
            label: {
                scenario: hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
                for scenario, path in paths.items()
            }
            for label, paths in bundles.items()
        },
        "warmup": arguments.warmup,
    }
    (out / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    rows = []
    for pair in range(arguments.pairs):
        order = ["candidate", "baseline"] if pair % 2 == 0 else ["baseline", "candidate"]
        for scenario in scenarios:
            for label in order:
                sample = measure(
                    bundles[label][scenario], scenario, arguments.batches, arguments.warmup,
                    out / f"{pair}-{scenario}-{label}.log",
                )
                rows.append({"label": label, "pair": pair, "scenario": scenario, **sample})
                (out / "samples.json").write_text(json.dumps(rows, indent=2) + "\n")
        print(f"Completed pair {pair + 1}/{arguments.pairs}", flush=True)
    summary = {}
    lines = [
        "| Workload | Baseline median µs/op | Candidate median µs/op | Median paired change | Pairs slower than guard |",
        "| --- | ---: | ---: | ---: | ---: |",
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
            "pairedPercentChanges": changes,
            "slowerPairsAboveGuard": sum(change > arguments.guard for change in changes),
        }
        entry = summary[scenario]
        lines.append(
            f"| {scenario} | {entry['baselineMedianUsPerOperation']:.2f} | "
            f"{entry['candidateMedianUsPerOperation']:.2f} | "
            f"{entry['medianPairedPercentChange']:+.2f}% | "
            f"{entry['slowerPairsAboveGuard']}/{len(changes)} |"
        )
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    report = "\n".join(lines)
    (out / "report.md").write_text(
        "# Alternating A/B timing round\n\nNegative changes mean the candidate is faster. "
        "Medians of paired whole-process loop latency; no cumulative or general speedup is inferred.\n\n"
        + report + "\n",
    )
    print(report)


def main(argv):
    arguments = parse_arguments(argv)
    if arguments.unbounded:
        run_round(arguments)
        return 0
    receipt = pathlib.Path(arguments.out).resolve().parent / (
        pathlib.Path(arguments.out).name + "-receipt.json"
    )
    print(f"A/B timing receipt: {receipt}", flush=True)
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts/bounded-check.py"), "--seconds", "295",
         "--receipt", str(receipt), "--", sys.executable, __file__, "--unbounded", *argv],
        cwd=ROOT,
    )
    return result.returncode


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
