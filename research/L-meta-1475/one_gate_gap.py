"""Construct the 125-gate reference circuit with the fixed 14-gate Fano prefix."""
from itertools import product

RAW = 42
DIFFERENCES = (0, 5, 7, 17, 20)


def line(point, offset):
    return 21 + (point + offset) % 21


def build():
    gates = []

    def gate(op, left, right):
        result = RAW + len(gates)
        assert 0 <= left < result and 0 <= right < result
        gates.append((op, left, right))
        return result

    pairs = [gate("or", line(p, 5), line(p, 17)) for p in range(0, 21, 3)]
    triples = [gate("or", pairs[p // 3], line(p, 20)) for p in range(0, 21, 3)]
    assert len(gates) == 14
    stars = []
    for point in range(21):
        if point % 3 == 0:
            neighbors = [triples[point // 3], line(point, 0), line(point, 7)]
        else:
            neighbors = [line(point, d) for d in DIFFERENCES]
        signal = neighbors[0]
        for neighbor in neighbors[1:]:
            signal = gate("or", signal, neighbor)
        stars.append(gate("and", point, signal))

    output = stars[0]
    for term in stars[1:]:
        output = gate("or", output, term)
    return gates, output


def minimal(terms):
    """Absorption removes every term strictly containing another term."""
    kept = []
    for term in sorted(terms, key=lambda t: (t.bit_count(), t)):
        if all((earlier & term) != earlier for earlier in kept):
            kept.append(term)
    return frozenset(kept)


def minterms(gates, output):
    # A term is a bit mask of raw inputs whose conjunction suffices.
    wires = [frozenset({1 << i}) for i in range(RAW)]
    for op, left, right in gates:
        a, b = wires[left], wires[right]
        if op == "or":
            terms = a | b
        else:
            assert op == "and"
            terms = {x | y for x, y in product(a, b)}
        wires.append(minimal(terms))
    return wires[output]


if __name__ == "__main__":
    gates, output = build()
    expected = {(1 << p) | (1 << line(p, d)) for p in range(21) for d in DIFFERENCES}
    assert len(expected) == 105
    assert minterms(gates, output) == expected
    assert len(gates) == 125
    print("14 prefix gates + 111 residual gates = 125 gates")
    print("All 105 positive minterms agree with the plane incidence function.")
