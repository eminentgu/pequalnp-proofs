"""Exact bounded monotone circuit search for the six remaining 4-by-4 incidence graphs."""
import argparse
import json
from functools import lru_cache
from itertools import combinations
from time import monotonic

CASES = (862, 4958, 4973, 5804, 5805, 13726)


def graph_data(key, side):
    vertices = 2 * side
    full = (1 << vertices) - 1
    edges = [(1 << i) | (1 << (side + j)) for i in range(side)
             for j in range(side) if key >> (side * i + j) & 1]
    independent = {row for row in range(full + 1) if all((row & e) != e for e in edges)}
    maximal = sorted(row for row in independent if all(
        (row | (1 << i)) not in independent for i in range(vertices) if not row >> i & 1))
    cover = vertices - max(row.bit_count() for row in independent)
    active = [i for i in range(vertices) if any(edge >> i & 1 for edge in edges)]
    return edges, maximal, active, len(edges) + cover - 1 if edges else 0


def bounded_search(edges, maximal, active, budget):
    # A monotone function matches the target iff it accepts every edge and
    # rejects every maximal independent set. Store its values on these rows.
    if not edges:
        return budget >= 0, 0
    if budget < 0:
        return False, 0
    rows = edges + maximal
    target = (1 << len(edges)) - 1
    all_ones = (1 << len(rows)) - 1
    all_pairs = (1 << (len(edges) * len(maximal))) - 1
    inputs = [sum(1 << t for t, row in enumerate(rows) if row >> i & 1) for i in active]
    negative_bits = (1 << len(maximal)) - 1

    @lru_cache(maxsize=200_000)
    def covers(wire):
        negative_zeros = negative_bits ^ (wire >> len(edges))
        separated = 0
        for i in range(len(edges)):
            if wire >> i & 1:
                separated |= negative_zeros << (i * len(maximal))
        return separated

    @lru_cache(maxsize=350_000)
    def possible(pool, gates_left):
        if pool == (target,):
            return True
        if not gates_left or len(pool) > gates_left + 1:
            return False
        combined = 0
        for wire in pool:
            combined |= covers(wire)
        if combined != all_pairs:
            return False

        # A useful binary gate consumes two live predecessors, creating one
        # result. Either input may remain live for other uses (arbitrary fanout).
        for i, j in combinations(range(len(pool)), 2):
            a, b = pool[i], pool[j]
            rest = pool[:i] + pool[i + 1:j] + pool[j + 1:]
            for value in (a & b, a | b):
                if value == 0 or value == all_ones or value in pool:
                    continue
                next_pool = (*rest, value)
                if possible(tuple(sorted(next_pool)), gates_left - 1):
                    return True
                if len(pool) <= gates_left:
                    if possible(tuple(sorted((*next_pool, a))), gates_left - 1):
                        return True
                    if possible(tuple(sorted((*next_pool, b))), gates_left - 1):
                        return True
                if len(pool) < gates_left:
                    if possible(tuple(sorted((*next_pool, a, b))), gates_left - 1):
                        return True
        return False

    found = possible(tuple(sorted(inputs)), budget)
    states = possible.cache_info().misses
    possible.cache_clear()
    covers.cache_clear()
    return found, states


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--side', type=int, default=4)
    parser.add_argument('keys', nargs='*', type=int)
    args = parser.parse_args()
    for key in args.keys or CASES:
        edges, maximal, active, upper = graph_data(key, args.side)
        start = monotonic()
        found, states = bounded_search(edges, maximal, active, upper - 1)
        result = dict(key=key, side=args.side, edges=len(edges), active=len(active),
                      maximal_independent_sets=len(maximal), star_upper_bound=upper,
                      tested_gate_budget=upper - 1, smaller_circuit=found,
                      explored_states=states, seconds=round(monotonic() - start, 3))
        print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
