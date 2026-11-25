"""Exact truth-table check of zero-folding on the 14-vertex Fano incidence graph."""

from itertools import permutations

ORDER = 7
ARITY = 2 * ORDER
ASSIGNMENTS = 1 << ARITY
ALL = (1 << ASSIGNMENTS) - 1
POINTS = range(ORDER)
LINES = range(ORDER, ARITY)
INCIDENCE = tuple(
    (point, ORDER + line)
    for line in range(ORDER)
    for point in ((line + delta) % ORDER for delta in (0, 1, 3))
)


def star_circuit():
    gates = []
    stars = []

    def emit(op, left, right):
        index = ARITY + len(gates)
        gates.append((op, left, right))
        return index

    for point in POINTS:
        first, second, third = sorted(line for p, line in INCIDENCE if p == point)
        neighborhood = emit('or', emit('or', first, second), third)
        stars.append(emit('and', point, neighborhood))
    output = stars[0]
    for following in stars[1:]:
        output = emit('or', output, following)
    return gates, output


def variable_truth_table(bit):
    block_length = 1 << bit
    block = ((1 << block_length) - 1) << block_length
    repeats = ALL // ((1 << (2 * block_length)) - 1)
    return block * repeats


def evaluate(gates, output, fixed_zero=None):
    wires = [variable_truth_table(bit) if bit != fixed_zero else 0 for bit in range(ARITY)]
    representative = {value: wire for wire, value in enumerate(wires) if value}
    emitted, arguments = set(), {}
    for index, (op, left, right) in enumerate(gates, start=ARITY):
        result = wires[left] & wires[right] if op == 'and' else wires[left] | wires[right]
        wires.append(result)
        if result and result not in representative:
            emitted.add(index)
            arguments[index] = (representative[wires[left]], representative[wires[right]])
            representative[result] = index
    reachable, stack = set(), [representative[wires[output]]]
    while stack:
        index = stack.pop()
        if index in emitted and index not in reachable:
            reachable.add(index)
            stack.extend(arguments[index])
    expected = 0
    for point, line in INCIDENCE:
        expected |= wires[point] & wires[line]
    assert wires[output] == expected
    return len(emitted), len(reachable)


def main():
    edges = set(INCIDENCE)
    assert len(edges) == 21
    for p in POINTS:
        for q in POINTS:
            if p != q:
                assert sum((p, line) in edges and (q, line) in edges for line in LINES) == 1
    # A perfect matching forces cover number seven; removing either end of
    # one matching edge leaves six disjoint edges, covered by that side's
    # six surviving vertices.
    assert any(all((p, line) in edges for p, line in zip(POINTS, matching))
               for matching in permutations(LINES))
    gates, output = star_circuit()
    assert len(gates) == 27
    assert evaluate(gates, output) == (27, 27)
    for side, vertices, expected in [('point', POINTS, (25, 23)), ('line', LINES, (24, 24))]:
        for vertex in vertices:
            assert evaluate(gates, output, vertex) == expected
        emitted, live = expected
        print(f'{side}: all {len(vertices)} restrictions; '
              f'{emitted} merging gates ({27 - emitted} saved), '
              f'{live} gates after pruning ({27 - live} saved)')


if __name__ == '__main__':
    main()
