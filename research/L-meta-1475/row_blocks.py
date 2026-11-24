"""Reproduce the PG(2,4) outside-row census and the finite checks in row_blocks.md."""
from collections import Counter
from functools import cache
from itertools import combinations, permutations
from math import comb

DIFFERENCES = (0, 5, 7, 17, 20)
ROWS = [{(r + d) % 21 for d in DIFFERENCES} for r in range(21)]
OUTSIDE = [r for r in range(21) if r % 3]
# Each core column is the bit mask of its selected incident rows.
TEMPLATES = {
    (1, ()): (),
    (2, ()): (3,),
    (3, (3,)): (7,),
    (3, ()): (3, 5, 6),
    (4, (4,)): (15,),
    (4, (3,)): (7, 9, 10, 12),
    (4, ()): (3, 5, 6, 9, 10, 12),
}
EXPECTED = {
    1: {(): 14},
    2: {(): 91},
    3: {(): 308, (3,): 56},
    4: {(): 427, (3,): 560, (4,): 14},
    5: {(): 98, (3,): 1008, (3, 3): 756, (4,): 140},
}


def column_masks(rows):
    return [sum(1 << i for i, r in enumerate(rows) if c in ROWS[r]) for c in range(21)]


@cache
def canonical(k, core):
    """Forget the labels of the k rows and of the shared columns."""
    def relabel(order):
        return tuple(sorted(sum(1 << order[i] for i in range(k) if m >> i & 1) for m in core))
    return min(relabel(order) for order in permutations(range(k)))


def census():
    assert all(len(a & b) == 1 for a, b in combinations(ROWS, 2))
    fano = {c for c in range(21) if c % 3 == 2}
    subplane_rows = [ROWS[r] & fano for r in range(0, 21, 3)]
    assert all(len(row) == 3 for row in subplane_rows)
    assert all(len(a & b) == 1 for a, b in combinations(subplane_rows, 2))
    assert all(sum(c in row for row in subplane_rows) == 3 for c in fano)
    for k, expected in EXPECTED.items():
        counts = Counter()
        for rows in combinations(OUTSIDE, k):
            masks = column_masks(rows)
            assert sum(m.bit_count() for m in masks) == 5 * k
            shape = tuple(sorted(m.bit_count() for m in masks if m.bit_count() >= 3))
            counts[shape] += 1
            if k <= 4:
                core = tuple(sorted(m for m in masks if m.bit_count() >= 2))
                assert canonical(k, core) == canonical(k, TEMPLATES[k, shape])
                assert all((1 << i) in masks for i in range(k))
        assert counts == expected and sum(counts.values()) == comb(14, k)
        print(f"{k} {'row' if k == 1 else 'rows'}: " + ", ".join(f"{shape} = {counts[shape]}" for shape in sorted(counts)))


def extremal_rows(k, cols):
    positives = [(1 << i) | (1 << (k + j)) for j, col in enumerate(cols)
                 for i in range(k) if col >> i & 1]
    negatives = []
    for left in range(1 << k):
        right = [j for j, col in enumerate(cols) if col & left == 0]
        if all(left >> i & 1 or any(cols[j] >> i & 1 for j in right) for i in range(k)):
            negatives.append(left | sum(1 << (k + j) for j in right))
    return positives, negatives


def has_smaller_circuit(k, core):
    """Exhaust circuits below the star bound after retaining one private column per row."""
    cols = tuple(1 << i for i in range(k)) + core
    positives, negatives = extremal_rows(k, cols)
    rows = positives + negatives
    target = (1 << len(positives)) - 1
    all_bits = (1 << len(rows)) - 1
    neg_bits = (1 << len(negatives)) - 1
    all_pairs = (1 << (len(positives) * len(negatives))) - 1
    inputs = tuple(sorted(sum(((row >> v) & 1) << i for i, row in enumerate(rows))
                          for v in range(k + len(cols))))

    @cache
    def covers(wire):
        neg_zeros = neg_bits ^ (wire >> len(positives))
        return sum(neg_zeros << (p * len(negatives))
                   for p in range(len(positives)) if wire >> p & 1)

    @cache
    def possible(pool, budget):
        if pool == (target,):
            return True
        if not budget or len(pool) > budget + 1:
            return False
        separated = 0
        for wire in pool:
            separated |= covers(wire)
        if separated != all_pairs:
            return False
        for i, j in combinations(range(len(pool)), 2):
            a, b = pool[i], pool[j]
            others = tuple(w for h, w in enumerate(pool) if h != i and h != j)
            for new in (a & b, a | b):
                if new in pool or new in (0, all_bits):
                    continue
                # A last read releases an operand. Otherwise it remains available.
                for retained in ((), (a,), (b,), (a, b)):
                    if len(others) + len(retained) + 1 <= budget:
                        child = tuple(sorted((*others, new, *retained)))
                        if possible(child, budget - 1):
                            return True
        return False

    upper = len(positives) + k - 1
    found = possible(inputs, upper - 1)
    possible.cache_clear()
    covers.cache_clear()
    return upper, found


def check_four_path_candidate():
    # Bit positions 0,1 are the hubs; the pairs at 2..9 are the four path interiors.
    failures = []
    for mask in range(1024):
        bits = [bool(mask >> i & 1) for i in range(10)]
        a, b = bits[:2]
        paths = list(zip(bits[2::2], bits[3::2]))
        wanted = any((a and u) or (u and v) or (v and b) for u, v in paths)
        result = any((u or b) and (v or a) for u, v in paths)
        if result != wanted:
            failures.append(mask)
    assert failures == [3]
    print("Four-path candidate: 1 discrepancy in 1,024 assignments (only the hubs are active).")


if __name__ == "__main__":
    census()
    for (k, shape), core in TEMPLATES.items():
        if k <= 3:
            upper, found = has_smaller_circuit(k, core)
            assert not found
            print(f"Compressed {k}-row block {shape}: exact minimum {upper}.")
    check_four_path_candidate()
