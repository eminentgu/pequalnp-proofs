"""Reproduce the unrestricted-NOT and monotone subcase checks with Python 3."""
from itertools import permutations

import monotone_search as mono
import theta_search as signed


def check_witnesses():
    edges = {frozenset(edge) for edge in mono.EDGES}
    vertex = range(9)
    choices = (1, 2, 3, 5, 6, 7, 8)

    def edge(row):
        return any(row & e == e for e in mono.POS)

    for j in choices:
        def aux(row):
            return bool(row & (1 | 16 | (1 << j)))

        k = 5 if j in (2, 6) else 1
        low = (1 << j) | (1 << k)
        ordered = ((1, 17, 4), (low, low | 1, 0))
        for lo, hi, bit in ordered:
            assert lo ^ hi == 1 << bit
            assert not edge(lo) and edge(hi) and aux(lo) == aux(hi)
        assert not (low & 16)
        for x in range(512):
            if not x & 17:
                assert aux(x) == bool(x >> j & 1)
                assert edge(x) == any(x >> a & x >> b & 1 for a, b in signed.EDGES)

        # After removing any one of the first nine signatures, the remaining
        # signatures order at least one positive below one negative.
        roots = mono.RAW + (mono.RAW[0] | mono.RAW[4] | mono.RAW[j],)
        for i in vertex:
            covering = 0
            for t, wire in enumerate(roots):
                if t != i:
                    covering |= mono.separates(wire)
            assert covering != mono.ALL

    aut = [p for p in permutations(vertex)
           if all(frozenset((p[a], p[b])) in edges for a, b in mono.EDGES)]
    assert len(aut) == 12
    triples = {j: {0, 4, j} for j in choices}
    for j, expected in ((1, {1,5}), (2,{2,8}), (3,{3}), (6,{6,7})):
        orbit = [{p[v] for v in triples[j]} for p in aut]
        assert {k for k in choices if triples[k] in orbit} == expected
    assert len(mono.POS) == len(mono.NEG) == 12
    assert len(signed.POS) == 101 and len(signed.NEG) == 27

    # Four stars give an 11-gate upper bound matching the signed lower bound.
    for row in range(128):
        x1, x2, x3, x5, x6, x7, x8 = [(row >> i) & 1 for i in range(7)]
        computed = ((x1 & (x2 | x6)) | (x2 & (x3 | x7)) |
                    (x5 & x7) | (x8 & (x3 | x6 | x5)))
        assert bool(computed) == any(row & e == e for e in signed.MASKS)
    print("Sensitivity, 128-row cofactor, 11-gate upper bound, and automorphisms agree.", flush=True)


if __name__ == "__main__":
    check_witnesses()
    if signed.solve(10):
        raise RuntimeError("Found a signed theta circuit with at most ten gates")
    for case in (None, 1, 2, 3, 5, 6, 7, 8):
        if mono.solve(case, 13):
            raise RuntimeError(f"Found a monotone circuit in the {case} case")
