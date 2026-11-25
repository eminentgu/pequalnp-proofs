"""Independently check the complete unlabelled case list against the pinned external generator."""
import argparse
from pathlib import Path
import sys

from enumerate_four import candidates, canonical, minimum_covers


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("pinned_source", type=Path, help="L-meta-612 directory in pequalnp-research-notes")
args = parser.parse_args()
sys.path.insert(0, str(args.pinned_source.resolve()))
from cover_kernels import kernels

reference = set()
for n, m, edges in kernels(4):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    if any(adj[a] & adj[b] for a, b in edges):
        continue
    size, covers = minimum_covers(adj)
    assert size == 4
    reference.add(canonical(adj, covers))
local = {key for _, key in candidates()}
assert local == reference, (len(local - reference), len(reference - local))
print(f"Both generators yielded the same {len(local)} unlabelled triangle-free classes.")
