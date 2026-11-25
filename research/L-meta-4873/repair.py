"""Allow an arbitrary second gate rewrite after bypassing one prefix gate."""
from itertools import combinations
from star_prefix import EDGES, N, star_prefix, check


def boundary():
    positives = [(1 << p) | (1 << l) for p, l in EDGES]
    negatives = {m for m in range(1 << N) if all(m & e != e for e in positives)}
    maximal = sorted(m for m in negatives if all((m | (1 << i)) not in negatives
                     for i in range(N) if not m & (1 << i)))
    assert len(maximal) == 37
    return positives + maximal + [1, 128]


rows = boundary()
mask = (1 << len(rows)) - 1
target = (1 << len(EDGES)) - 1
marked = 3 << (len(rows) - 2)
inputs = [sum(((m >> i) & 1) << j for j, m in enumerate(rows)) for i in range(N)]


def replay(gates, h, g, forced=-1, value=0):
    wires = inputs.copy()
    for i, (op, a, b) in enumerate(gates, N):
        wires.append(value if i == forced else
                     (wires[a] & wires[b] if op == 'and' else wires[a] | wires[b]))
    a, b = wires[h] | inputs[2], wires[h] | wires[g]
    error = ((a & b) ^ target) | ((a | b) & marked)
    return error, wires


def repairs():
    base, h0, g0 = star_prefix()
    for skip in range(N, N + len(base)):
        for sub in range(skip):
            def rename(w):
                return sub if w == skip else w - int(w > skip)

            h, g = rename(h0), rename(g0)
            if h in (2, g):
                continue
            gates = [(op, rename(a), rename(b)) for i, (op, a, b)
                     in enumerate(base, N) if i != skip]
            repeats = {j for j, (_, a, b) in enumerate(gates, N) if a == b}
            for j in range(N, N + len(gates)):
                if repeats - {j}:
                    continue
                bad0, wires = replay(gates, h, g, j, 0)
                bad1, _ = replay(gates, h, g, j, mask)
                if bad0 & bad1:
                    continue
                for a, b in combinations(range(j), 2):
                    for op, value in [('and', wires[a] & wires[b]), ('or', wires[a] | wires[b])]:
                        if (bad0 & ~value) or (bad1 & value):
                            continue
                        candidate = gates.copy()
                        candidate[j-N] = op, a, b
                        if check(candidate, h, g):
                            yield candidate, h, g


if __name__ == '__main__':
    solutions = list(repairs())
    print(f'{len(solutions)} repairs pass all assignments.')
    for solution in solutions:
        print(solution)
