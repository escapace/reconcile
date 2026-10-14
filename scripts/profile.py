"""Bound the entire profiling command, including every alternating comparison pair."""

import pathlib
import subprocess
import sys
import tempfile

root = pathlib.Path(__file__).resolve().parent.parent
receipt = pathlib.Path(tempfile.mkdtemp(prefix="reconcile-profile-receipt-")) / "receipt.json"
print(f"Profiling receipt: {receipt}", flush=True)
result = subprocess.run(
    [sys.executable, str(root / "scripts/bounded-check.py"), "--seconds", "295",
     "--receipt", str(receipt), "--", "pnpm", "exec", "tsx", "scripts/profile.ts", *sys.argv[1:]],
    cwd=root,
)
sys.exit(result.returncode)
