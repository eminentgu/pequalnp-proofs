"""Check the nine-input example by evaluating the entire Boolean cube."""

from itertools import combinations

EDGES = [(0, 1), (1, 2), (1, 3), (2, 4), (2, 8), (3, 5), (5, 8), (6, 8), (7, 8)]
GATES = [
    ("or", 0, 3), ("and", 1, 9), ("or", 10, 2), ("or", 1, 8),
    ("or", 3, 8), ("or", 12, 4), ("and", 11, 14), ("or", 6, 7),
    ("and", 12, 16), ("or", 17, 5), ("and", 13, 18), ("or", 15, 19),
]


def evaluate(mask):
    wires = [bool(mask & (1 << i)) for i in range(9)]
    for op, a, b in GATES:
        wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
    return wires


def check():
    assert all(evaluate(mask)[20] == any(mask & (1 << u) and mask & (1 << v)
                                         for u, v in EDGES) for mask in range(512))
    covers = [set(s) for k in range(10) for s in combinations(range(9), k)
              if all(a in s or b in s for a, b in EDGES)]
    assert min(map(len, covers)) == 4
    assert {0, 2, 3, 8} in covers
    predecessors = [set() for _ in range(9)]
    owned = {}
    false_pairs = []
    for j, (op, a, b) in enumerate(GATES):
        ancestors = predecessors[a] | predecessors[b] | {u - 9 for u in (a, b) if u >= 9}
        predecessors.append(ancestors)
        if op != "and":
            continue
        owned[j] = []
        for u in range(9):
            for v in range(u, 9):
                wires = evaluate((1 << u) | (1 << v))
                if not wires[9 + j]:
                    continue
                if (u, v) not in EDGES:
                    false_pairs.append((j, u, v))
                elif not any(GATES[k][0] == "and" and wires[9 + k] for k in ancestors):
                    owned[j].append((u, v))
    assert owned == {1: [(0, 1), (1, 3)], 6: [(1, 2), (2, 4), (2, 8)],
                     8: [(6, 8), (7, 8)], 10: [(3, 5), (5, 8)]}
    assert false_pairs == [(8, 1, 6), (8, 1, 7)]
    print("Verified 512 outputs, a minimum cover of four vertices, and all four AND ownership sets.")
    print("AND gate 8 accepts two nonedge pairs:", false_pairs)


if __name__ == "__main__":
    check()
