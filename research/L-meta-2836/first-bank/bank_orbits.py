"""Exact coordinate-permutation invariants of the three two-OR banks in L-meta-2836."""
from itertools import permutations, product

EDGES = {(0,1), (1,2), (2,3), (3,4), (0,4), (0,5),
         (1,6), (2,7), (3,8), (5,7), (6,8), (5,8)}
BANKS = {"A": (0, ((0,4), (0,3))),
         "B": (4, ((0,4), (1,4))),
         "C": (4, ((0,4), (4,5)))}

def edge(i, j):
    return tuple(sorted((i,j)))

def image(rows, perm):
    return {edge(perm[i],perm[j]) for i,j in rows}

def orbit_table():
    auts = [p for p in permutations(range(9)) if image(EDGES,p) == EDGES]
    assert len(auts) == 12
    for b,(hidden,rails) in BANKS.items():
        compatible = sorted(c for c,(j,target) in BANKS.items() if
                            any(p[hidden] == j and image(rails,p) == set(target)
                                for p in auts))
        positives = set()
        negatives = set()
        for mask in range(1<<9):
            raw = [mask>>i & 1 for i in range(9)]
            row = tuple(raw[i] for i in range(9) if i != hidden)
            row += tuple(raw[i] | raw[j] for i,j in rails)
            label = any(raw[i] and raw[j] for i,j in EDGES)
            (positives if label else negatives).add(row)
        assert positives.isdisjoint(negatives)
        spectrum = sorted(map(sum,zip(*positives)))
        print(b, "raw-equivalent", compatible, "positive", len(positives),
              "negative",len(negatives), "positive-column-counts", spectrum)
        yield spectrum

if __name__ == "__main__":
    def label(mask):
        return any((mask >> i) & (mask >> j) & 1 for i, j in EDGES)

    def bank_a(mask):
        hidden = mask & 1
        rail_c = hidden | ((mask >> 4) & 1)
        rail_d = hidden | ((mask >> 3) & 1)
        return (mask & ~1) | (rail_c << 9) | (rail_d << 10)

    for a,b,c,d in product((0,1), repeat=4):
        face = (a << 1) | (b << 5) | (c << 9) | (d << 10)
        if (a or b) and c and d:
            raw = 3 if a else 33
            assert label(raw) and (bank_a(raw) & face) == bank_a(raw)
        else:
            raw = 42 if not c else 50 if not d else 1
            assert not label(raw) and (bank_a(raw) & face) == face
    a,b,c = orbit_table()
    assert a != b and b == c
    # Complementing one signed column exchanges its zeros and ones.
    signed = lambda row: sorted(min(n, 390-n) for n in row)
    assert signed(a) != signed(b)
