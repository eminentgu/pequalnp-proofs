"""Greedily remove whole symmetry orbits while retaining every input sensitivity."""
from itertools import permutations
from random import Random
import sys

from rows import rows, solve, theta


def perm(row, p):
    return sum((row >> i & 1) << p[i] for i in range(7))


def main(seed):
    basepos, baseneg = rows('three')
    autos = [p for p in permutations(range(7)) if all(perm(e, p) in theta.MASKS for e in theta.MASKS)]
    trials = []
    for sign, bank in ((True,basepos), (False,baseneg)):
        groups = {tuple(sorted({perm(row, p) for p in autos})) for row in bank}
        trials.extend((sign, g) for g in sorted(groups))
    Random(seed).shuffle(trials)
    trials.sort(key=lambda item: -len(item[1]))
    pr, nr = set(basepos), set(baseneg)
    for sign, orbit in trials:
        p = pr.difference(orbit) if sign else pr
        n = nr if sign else nr.difference(orbit)
        if any(not any(row ^ 1 << i in n for row in p) for i in range(7)):
            continue
        outcome = solve(sorted(p), sorted(n), cap=25000, quiet=True)
        if outcome is not None and not outcome['possible']:
            pr, nr = p, n
            print(len(p)+len(n), outcome['normal'], outcome['calls'], sorted(p), sorted(n), flush=True)
    print("final", solve(sorted(pr),sorted(nr)), flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv)>1 else 0)
