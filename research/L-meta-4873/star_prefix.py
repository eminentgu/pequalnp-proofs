"""Check the marked Fano circuit and all one-gate bypasses in its fixed prefix."""
from itertools import product

N = 14
ROWS = 1 << N
ALL = (1 << ROWS) - 1
RAW = [((1 << (1 << i)) - 1) * (ALL // ((1 << (2 << i)) - 1)) << (1 << i)
       for i in range(N)]
EDGES = [(p, 7 + l) for p, l in product(range(7), repeat=2) if (p-l) % 7 in {0, 1, 3}]
TARGET = 0
for p, l in EDGES:
    TARGET |= RAW[p] & RAW[l]


def star_prefix():
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return N + len(gates) - 1

    def neighborhood(p):
        a, b, c = [l for q, l in EDGES if q == p]
        return gate('or', gate('or', a, b), c)

    stars = [gate('and', p, neighborhood(p)) for p in range(7) if p != 2]
    h = stars[0]
    for s in stars[1:]:
        h = gate('or', h, s)
    return gates, h, neighborhood(2)


def check(gates, h, g, bypass=None):
    wires = RAW.copy()
    skipped, substitute = bypass or (-1, -1)

    def wire(i):
        return substitute if i == skipped else i

    for i, (op, left, right) in enumerate(gates, N):
        if i == skipped:
            wires.append(0)
            continue
        a, b = wire(left), wire(right)
        if a == b:
            return False
        assert max(a, b) < i
        wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
    h, g = wire(h), wire(g)
    if h in (2, g):
        return False
    a = wires[h] | RAW[2]
    b = wires[h] | wires[g]
    singletons = (1 << (1 << 0)) | (1 << (1 << 7))
    return a & b == TARGET and (a | b) & singletons == 0


if __name__ == '__main__':
    gates, h, g = star_prefix()
    assert len(gates) == 25 and check(gates, h, g)
    candidates = [(i, j) for i in range(N, N+len(gates)) for j in range(i)]
    solutions = [(i, j) for i, j in candidates if check(gates, h, g, (i, j))]
    print(f'{len(gates)} prefix gates + 3 final gates pass all {ROWS} assignments.')
    print(f'{len(solutions)} of {len(candidates)} single-gate bypasses pass: {solutions}')
