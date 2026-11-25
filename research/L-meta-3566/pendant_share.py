"""Test cofactor merging and dead-gate pruning on a leaf adjoining a cubic vertex."""

from itertools import combinations

N = 10
ALL = (1 << (1 << N)) - 1
LEAF, JOINT = 9, 8
EDGES = [(i, (i + 1) % 8) for i in range(8)] + [(8, 0), (8, 4), (8, 9)]


def gates_for_graph():
    gates = []

    def gate(op, x, y):
        gates.append((op, x, y))
        return N + len(gates) - 1

    # CNF for the disjunction of two disjoint cycle edges, 0--1 and 4--3.
    shared = gate("or", 0, 4)
    first = gate("and", shared, gate("or", 0, 3))
    second = gate("and", gate("or", 1, 4), gate("or", 1, 3))
    tail = gate("and", first, second)
    for i, j in EDGES[:8]:
        if (i, j) not in [(0, 1), (3, 4)]:
            tail = gate("or", tail, gate("and", i, j))
    output = gate("or", tail, gate("and", JOINT, gate("or", LEAF, shared)))
    return gates, output


def value(w):
    return sum(1 << x for x in range(1 << N) if x >> w & 1)


def costs(gates, output, substitution):
    roots = list(map(value, range(N)))
    for x, y in substitution.items():
        roots[x] = y

    def combine(op, x, y):
        return (x & y) if op == "and" else (x | y)

    values = list(roots)
    representatives = {v: i for i, v in enumerate(roots)}
    parents = {}
    for i, (op, x, y) in enumerate(gates, start=N):
        z = combine(op, values[x], values[y])
        values.append(z)
        if z not in representatives and z not in (0, ALL):
            parents[i] = representatives[values[x]], representatives[values[y]]
            representatives[z] = i
    expected = 0
    for x, y in EDGES:
        expected |= roots[x] & roots[y]
    assert values[output] == expected
    stack = [representatives[values[output]]]
    used = set()
    while stack:
        top = stack.pop()
        if top in parents and top not in used:
            used.add(top)
            stack.extend(parents[top])
    return len(parents), len(used)


def cover_size(edges):
    return min(len(c) for k in range(N + 1) for c in combinations(range(N), k)
               if all(i in c or j in c for i, j in edges))


def main():
    E = {frozenset((i, j)) for i, j in EDGES}
    neighbors = [{next(iter(e - {i})) for e in E if i in e} for i in range(N)]
    left = {0, 2, 4, 6, LEAF}
    assert all((i in left) != (j in left) for i, j in EDGES)
    assert len(neighbors[LEAF]) == 1 and len(neighbors[JOINT]) == 3
    assert all(len(neighbors[i] & neighbors[j]) <= 1 for i, j in combinations(range(N), 2))
    assert cover_size(EDGES) == 5
    for w in [JOINT, LEAF]:
        assert cover_size([(i, j) for i, j in EDGES if w not in (i, j)]) == 4
    gates, output = gates_for_graph()
    for name, sub, expect in [
        ("unrestricted", {}, (22, 22)),
        ("leaf=0", {LEAF: 0}, (21, 21)),
        ("joint=0, leaf=0", {JOINT: 0, LEAF: 0}, (19, 19)),
        ("joint=0, leaf=1", {JOINT: 0, LEAF: ALL}, (19, 19)),
    ]:
        result = costs(gates, output, sub)
        print(name, result)
        assert result == expect


if __name__ == "__main__":
    main()
