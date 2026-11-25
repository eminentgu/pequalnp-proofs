"""Replay the residuals with the relaxed-domain live-wire search, with explicit wall-clock cutoffs."""
import argparse
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("binary", type=Path)
parser.add_argument("graphs", type=Path)
parser.add_argument("--seconds", type=float, default=10)
parser.add_argument("--continue-from", type=int, default=0)
args = parser.parse_args()
timeouts = []
for row in args.graphs.read_text().splitlines():
    idx = int(row.split()[0])
    if idx < args.continue_from:
        continue
    try:
        result = subprocess.run([str(args.binary.resolve()), str(idx), str(idx), "0", "--direct", "16"],
                                input=row+'\n', text=True, capture_output=True, timeout=args.seconds)
    except subprocess.TimeoutExpired:
        timeouts.append(idx)
        print(f"kernel {idx} TIMEOUT at {args.seconds:g}s", flush=True)
        continue
    if result.returncode or " NONE states " not in result.stdout:
        print(result.stdout, result.stderr, file=sys.stderr)
        raise SystemExit(f"case {idx} did not return a negative verdict")
    print(result.stdout.rstrip(), flush=True)

if timeouts:
    raise SystemExit(f"Incomplete cases: {timeouts}")
