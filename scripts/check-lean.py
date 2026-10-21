"""Run the complete Lean gate under one process-tree budget, with a fresh receipt."""

import os
import pathlib
import subprocess
import sys
import tempfile

root = pathlib.Path(__file__).resolve().parent.parent
receipt = pathlib.Path(tempfile.mkdtemp(prefix="reconcile-lean-receipt-")) / "receipt.json"
print(f"Lean gate receipt: {receipt}", flush=True)
env = dict(os.environ)
env["LEAN_CC"] = str(root / "scripts/lean-cc.py")
# The check compiler intentionally differs from release-optimized build caches.
env["LAKE_ARTIFACT_CACHE"] = "false"
result = subprocess.run(
    [sys.executable, str(root / "scripts/bounded-check.py"), "--seconds", "295",
     "--receipt", str(receipt), "--", "bash", "-c",
     "LEAN_SYSROOT=$(lean --print-prefix) && export LEAN_SYSROOT && "
     "lake build --wfail && PYTHONDONTWRITEBYTECODE=1 python3 scripts/test-axioms.py && "
     'pnpm exec tsx "$@" scripts/check-lean.ts',
     "check-lean", *sys.argv[1:]],
    cwd=root, env=env,
)
sys.exit(result.returncode)
