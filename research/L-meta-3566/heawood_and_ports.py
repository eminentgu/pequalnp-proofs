"""Emit a CNF refuting six physical AND gates for the Heawood edge function."""

import sys
from itertools import combinations


class Cnf:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def new(self):
        self.variables += 1
        return self.variables

    def add(self, *literals):
        self.clauses.append(literals)

    def conjunction(self, left, right):
        out = self.new()
        self.add(-out, left)
        self.add(-out, right)
        self.add(-left, -right, out)
        return out

    def disjunction(self, inputs):
        out = self.new()
        self.add(-out, *inputs)
        for value in inputs:
            self.add(out, -value)
        return out

    def write(self):
        print("p cnf", self.variables, len(self.clauses))
        for clause in self.clauses:
            print(*clause, 0)


def heawood():
    points = range(7)
    vertices = range(14)
    edges = {(i, 7 + j) for j in points for i in (j, (j + 1) % 7, (j + 3) % 7)}
    neighbors = [set() for _ in vertices]
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)

    maximal = []
    for mask in range(128):
        left = {i for i in points if (mask >> i) & 1}
        right = {v for v in range(7, 14) if neighbors[v].isdisjoint(left)}
        group = left | right
        if all(neighbors[v] & group for v in set(vertices) - group):
            maximal.append(group)

    assert len(edges) == 21 and len(maximal) == 37
    assert all(sum(v in group for group in maximal) == 12 for v in vertices)
    assert all(neighbors[x] - neighbors[y] for x in vertices for y in vertices if x != y)
    # Check the seven-star construction on the full 14-variable truth table.
    for mask in range(1 << 14):
        selected = {v for v in vertices if (mask >> v) & 1}
        graph_value = any(a in selected and b in selected for a, b in edges)
        star_value = any(i in selected and neighbors[i] & selected for i in points)
        assert graph_value == star_value
    return edges, maximal


def main():
    edges, maximal = heawood()
    vertices = range(14)
    gates = range(6)
    rows = [{v} for v in vertices] + maximal
    f = Cnf()

    # Values of both operand wires of each gate on each test input.
    ports = [[(f.new(), f.new()) for _ in gates] for _ in rows]
    oriented = [
        [(f.conjunction(l, -r), f.conjunction(-l, r)) for l, r in row]
        for row in ports
    ]

    # Twelve maximal extensions require at least four ANDs quiet on this
    # singleton. Thus at most two of six ANDs can have an active operand.
    for x in vertices:
        lit = [f.disjunction((l, r)) for l, r in ports[x]]
        for triple in combinations(lit, 3):
            f.add(*(-v for v in triple))

    for i, group in enumerate(maximal, start=14):
        for x in group:
            for (l, r), (a, b) in zip(ports[x], ports[i]):
                f.add(-l, a)
                f.add(-r, b)

    # Union of the two negative tests contains an edge in either case.
    for x, y in list(edges) + list(combinations(range(14, len(rows)), 2)):
        witnesses = []
        for (lx, rx), (ly, ry) in zip(oriented[x], oriented[y]):
            witnesses.append(f.conjunction(lx, ry))
            witnesses.append(f.conjunction(rx, ly))
        f.add(*witnesses)

    # Every ordered pair of different vertices has a private neighbor for x.
    for x in vertices:
        for y in vertices:
            if x == y:
                continue
            witnesses = []
            for (lx, rx), (l, r) in zip(oriented[x], ports[y]):
                witnesses.append(f.conjunction(lx, -l))
                witnesses.append(f.conjunction(rx, -r))
            f.add(*witnesses)

    # Swap ports so the first singleton with unequal values has a true left
    # port. A gate with identical ports on all singletons satisfies this too.
    for j in gates:
        for x in vertices:
            f.add(-oriented[x][j][1], *(oriented[y][j][0] for y in range(x)))

    # Permute the six abstract gate labels into descending lexicographic
    # order of their full singleton records. Equal records may occur.
    for j in range(5):
        previous_greater = []
        for row in ports[:14]:
            for a, b in zip(row[j], row[j + 1]):
                f.add(-b, a, *previous_greater)
                previous_greater.append(f.conjunction(a, -b))

    print(f"{f.variables} variables, {len(f.clauses)} clauses", file=sys.stderr)
    f.write()


if __name__ == "__main__":
    main()
