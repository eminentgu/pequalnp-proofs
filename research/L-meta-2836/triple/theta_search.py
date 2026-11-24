"""Exact signed AND search for the seven vertices left after x4=x0=0."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import combinations
from time import monotonic

VERTICES = (1, 2, 3, 5, 6, 7, 8)
EDGES = ((1, 2), (2, 3), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5))
MASKS = tuple((1 << VERTICES.index(a)) | (1 << VERTICES.index(b)) for a, b in EDGES)
POS = [x for x in range(128) if any(x & e == e for e in MASKS)]
NEG = [x for x in range(128) if x not in POS]
P = len(POS)
N = len(NEG)
NEG_MASK = (1 << N) - 1
D = POS + NEG
GOAL = (1 << P) - 1
TOP = (1 << len(D)) - 1
ALL_PAIRS = (1 << (P * N)) - 1
RAW = tuple(sum(((x >> j) & 1) << i for i, x in enumerate(D)) for j in range(7))


def canon(x):
    return x ^ TOP if x & 1 else x


@lru_cache(maxsize=32768)
def separation(x):
    high = x >> P
    positive_to_negative = 0
    negative_to_positive = 0
    for i in range(P):
        if x >> i & 1:
            positive_to_negative |= (NEG_MASK ^ high) << (N * i)
        else:
            negative_to_positive |= high << (N * i)
    return positive_to_negative | negative_to_positive, positive_to_negative


def solve(budget):
    calls = Counter()
    goal = canon(GOAL)

    @lru_cache(maxsize=120000)
    def works(state, remaining):
        calls[remaining] += 1
        if remaining == 0 or len(state) == 1:
            return state == (goal,)
        slack = remaining + 1 - len(state)
        if slack < 0:
            return False
        seps = [separation(x) for x in state]
        once = 0
        multiple = 0
        for separating, _ in seps:
            multiple |= separating & once
            once |= separating
        if once != ALL_PAIRS:
            return False
        if not slack:
            exclusive = ALL_PAIRS ^ multiple
            for separating, forward in seps:
                private = separating & exclusive
                if private & forward and private & ~forward:
                    return False
        for i, j in combinations(range(len(state)), 2):
            a, b = state[i], state[j]
            rest = state[:i] + state[i + 1:j] + state[j + 1:]
            other = 0
            for c in rest:
                other |= separation(c)[0]
            missing = ALL_PAIRS ^ other
            for lit_a in (a, a ^ TOP):
                for lit_b in (b, b ^ TOP):
                    out = canon(lit_a & lit_b)
                    if not out or out in state:
                        continue
                    left = missing & ~separation(out)[0]
                    child = (*rest, out)
                    if not left and works(tuple(sorted(child)), remaining - 1):
                        return True
                    if slack:
                        if not left & ~seps[i][0] and works(tuple(sorted((*child, a))), remaining - 1):
                            return True
                        if not left & ~seps[j][0] and works(tuple(sorted((*child, b))), remaining - 1):
                            return True
                    if slack > 1 and works(tuple(sorted((*child, a, b))), remaining - 1):
                        return True
        return False

    start = monotonic()
    answer = works(tuple(sorted(map(canon, RAW))), budget)
    print(f"binary gates {budget}, possible {answer}, states {sum(calls.values())}, "
          f"by remaining budget {sorted(calls.items())}, seconds {monotonic()-start:.2f}", flush=True)
    return answer


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("budgets", type=int, nargs="+")
    for gates in parser.parse_args().budgets:
        solve(gates)
