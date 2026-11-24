"""Verify the first-gate orbits for the 14-input Fano incidence function."""
from itertools import combinations, combinations_with_replacement, permutations

VERTICES = range(14)
COORDINATES = range(7)
EDGES = frozenset(
    (p, 7 + line)
    for p in COORDINATES
    for line in COORDINATES
    if (p + line) % 7 in (0, 1, 3)
)
REPRESENTATIVES = {
    "repeated": (0, 0),
    "same side": (0, 1),
    "incident": (0, 7),
    "nonincident": (0, 9),
}


def image(permutation, pair):
    a, b = pair
    return tuple(sorted((permutation[a], permutation[b])))


def automorphisms():
    neighborhoods = [
        frozenset(p for p in COORDINATES if (p, 7 + line) in EDGES)
        for line in COORDINATES
    ]
    line_number = {points: line for line, points in enumerate(neighborhoods)}
    assert len(line_number) == 7
    preserving = []
    for points in permutations(COORDINATES):
        images = [frozenset(points[p] for p in surface) for surface in neighborhoods]
        if all(surface in line_number for surface in images):
            lines = tuple(7 + line_number[surface] for surface in images)
            preserving.append(points + lines)

    # Each pair of points shares a line, and each line contains a point.
    # Connected bipartiteness permits just the two global choices of bank.
    assert all(any({p, q} <= surface for surface in neighborhoods)
               for p, q in combinations(COORDINATES, 2))
    assert all(neighborhoods)
    duality = tuple((v + 7) % 14 for v in VERTICES)
    assert {image(duality, e) for e in EDGES} == EDGES
    reversing = [tuple(duality[v] for v in g) for g in preserving]
    group = preserving + reversing
    assert len(preserving) == 168 and len(set(group)) == len(group) == 336
    for g in group:
        assert set(g) == set(VERTICES)
        assert {image(g, edge) for edge in EDGES} == EDGES
    return group


def pair_kind(pair):
    a, b = pair
    if a == b:
        return "repeated"
    if (a < 7) == (b < 7):
        return "same side"
    return "incident" if pair in EDGES else "nonincident"


def main():
    group = automorphisms()
    all_pairs = list(combinations_with_replacement(VERTICES, 2))
    print(f"{len(group)} automorphisms; 168 preserve the two sides, 168 exchange them")
    for kind, representative in REPRESENTATIVES.items():
        orbit = {image(g, representative) for g in group}
        expected = {pair for pair in all_pairs if pair_kind(pair) == kind}
        assert orbit == expected
        stabilizers = sum(image(g, representative) == representative for g in group)
        assert len(orbit) * stabilizers == len(group)
        print(f"{kind:12} representative {representative}, {len(orbit):2} pairs, "
              f"stabilizer order {stabilizers}")
    assert len(all_pairs) == 105


if __name__ == "__main__":
    main()
