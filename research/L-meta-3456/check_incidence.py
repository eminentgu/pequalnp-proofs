"""Enumerate square bipartite C4-free graphs and compute their exact monotone sizes."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
import json

from exact_monotone import bounded_search, graph_data


def orbit_census(n):
    width_mask = (1 << n) - 1
    relabel = [
        [sum(1 << perm[j] for j in range(n) if row >> j & 1) for row in range(1 << n)]
        for perm in permutations(range(n))
    ]

    @lru_cache(maxsize=None)
    def canonical(rows):
        columns = tuple(sum(1 << i for i, row in enumerate(rows) if row >> j & 1)
                        for j in range(n))
        # The least significant group of n bits holds row zero. To minimize
        # the integer after a column permutation, put the largest row first.
        def encoding(side, mapping):
            sorted_rows = sorted((mapping[r] for r in side), reverse=True)
            return sum(row << (n * i) for i, row in enumerate(sorted_rows))
        return min(encoding(side, mapping) for side in (rows, columns) for mapping in relabel)

    groups = Counter()
    for key in range(1 << (n * n)):
        rows = tuple(sorted(((key >> (i * n)) & width_mask for i in range(n)), reverse=True))
        if all((a & b).bit_count() <= 1 for a, b in combinations(rows, 2)):
            groups[canonical(rows)] += 1
    return groups


def verify_upper(edges, n, expected):
    # Truth tables over the entire Boolean cube, including every singleton.
    vertices = 2 * n
    assignments = range(1 << vertices)
    wires = [sum(1 << x for x in assignments if x >> i & 1) for i in range(vertices)]
    singleton_rows = sum(1 << (1 << i) for i in range(vertices))
    target = sum(1 << x for x in assignments if any(x & edge == edge for edge in edges))
    if not edges:
        assert expected == 0 and target == 0
        return
    cover = min((x for x in assignments if all(x & edge for edge in edges)), key=int.bit_count)
    stars = {i: [] for i in range(vertices) if cover >> i & 1}
    for edge in edges:
        i, j = [v for v in range(vertices) if edge >> v & 1]
        center, leaf = (i, j) if i in stars else (j, i)
        stars[center].append(leaf)

    def gate(left, right, is_and):
        assert left < len(wires) and right < len(wires)
        value = wires[left] & wires[right] if is_and else wires[left] | wires[right]
        if is_and:
            assert not (value & singleton_rows)
        wires.append(value)
        return len(wires) - 1

    def disjoin(indices):
        result, *others = indices
        for other in others:
            result = gate(result, other, False)
        return result

    outputs = [gate(c, disjoin(leaves), True) for c, leaves in stars.items()]
    output = disjoin(outputs)
    assert wires[output] == target
    assert len(wires) - vertices == expected


def forward_minimum(key, n, limit):
    # Independent control: unrestricted forward generation on FULL truth tables.
    # Only used with four raw inputs. The set records every available signal,
    # so repeated reads and sharing need no special case.
    edges, _, _, _ = graph_data(key, n)
    if not edges:
        return 0
    rows = range(1 << (2 * n))
    target = sum(1 << x for x in rows if any(x & e == e for e in edges))
    inputs = frozenset(sum(1 << x for x in rows if x >> i & 1) for i in range(2 * n))
    frontier = {inputs}
    for depth in range(limit + 1):
        if any(target in pool for pool in frontier):
            return depth
        if depth < limit:
            frontier = {pool | {new} for pool in frontier for a, b in combinations(pool, 2)
                        for new in (a & b, a | b) if new not in pool}
    return None


def run_controls():
    # Include every 2x2 graph, including the 4-cycle where the star bound
    # is strictly improvable. This tests both positive and negative answers.
    for key in range(16):
        edges, maximal, active, _ = graph_data(key, 2)
        minimum = forward_minimum(key, 2, 3)
        for budget in range(4):
            found, _ = bounded_search(edges, maximal, active, budget)
            assert found == (minimum is not None and minimum <= budget), (key, budget)
    assert forward_minimum(15, 2, 3) == 3
    assert graph_data(15, 2)[-1] == 5


def main():
    run_controls()
    output = {'controls': 'All 16 labelled 2x2 graphs at budgets 0..3; C4 optimum 3.', 'sides': {}}
    for n in range(1, 5):
        counts = orbit_census(n)
        cases = []
        for key, multiplicity in sorted(counts.items()):
            edges, maximal, active, upper = graph_data(key, n)
            verify_upper(edges, n, upper)
            lower_budget = upper - 1
            found, states = bounded_search(edges, maximal, active, lower_budget)
            assert not found, (n, key, lower_budget)
            cases.append(dict(key=key, labelled_matrices=multiplicity, exact_monotone_size=upper,
                              searched_states=states))
        output['sides'][str(n)] = dict(labelled=sum(counts.values()), classes=len(counts), cases=cases)
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
