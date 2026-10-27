#!/usr/bin/env python3
"""Run one complete validation/measurement round with a <=300s process-tree budget.

Usage: python3 scripts/bounded-check.py --receipt /archive/check.json -- command args...
The budget includes child shutdown.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--receipt', required=True, type=Path)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not 3 <= args.seconds <= 300:
        parser.error('--seconds must be between 3 and 300')
    if not command:
        parser.error('a command is required after --')
    if args.receipt.exists():
        parser.error(f'refusing to overwrite receipt: {args.receipt}')
    if os.name != 'posix':
        parser.error('POSIX process groups are required for descendant cancellation')
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    process = None
    status, result = 'failed', 1
    diagnostic = None

    def interrupted(_signal, _frame):
        raise KeyboardInterrupt

    previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        process = subprocess.Popen(command, start_new_session=True)
        # Reserve two seconds for termination and receipt publication.
        result = process.wait(timeout=max(0, args.seconds - 2 - (time.monotonic() - started)))
        status = 'passed' if result == 0 else 'failed'
    except subprocess.TimeoutExpired:
        status, result = 'timed_out', 124
    except KeyboardInterrupt:
        status, result = 'cancelled', 130
    except OSError as error:
        diagnostic = str(error)
    finally:
        signal.signal(signal.SIGTERM, previous)
        if process is not None:
            # Also terminate leftover descendants when the leader has already exited.
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=0.5)
            except subprocess.TimeoutExpired:
                pass
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=1)
        receipt = {
            'command': command,
            'budgetSeconds': args.seconds,
            'elapsedSeconds': time.monotonic() - started,
            'status': status,
            'exitCode': result,
            'diagnostic': diagnostic,
        }
        with args.receipt.open('x') as output:
            output.write(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(receipt), file=sys.stderr)
    return result if result >= 0 else 128 - result


if __name__ == '__main__':
    sys.exit(main())
