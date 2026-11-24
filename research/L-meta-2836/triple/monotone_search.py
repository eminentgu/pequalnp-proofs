"""Check the remaining monotone cases of L-meta-2836 on its boundary inputs."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
from time import monotonic

EDGES = ((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5))
POS = [(1 << a) | (1 << b) for a,b in EDGES]
IND = {x for x in range(512) if not any(x & e == e for e in POS)}
NEG = sorted(x for x in IND if all(x | 1 << i not in IND for i in range(9) if not x >> i & 1))
N = len(NEG)
LOW = (1 << N) - 1
D = POS + NEG
GOAL = (1 << len(POS)) - 1
TOP = (1 << len(D)) - 1
ALL = (1 << (len(POS) * N)) - 1
RAW = tuple(sum(((x >> j) & 1) << i for i, x in enumerate(D)) for j in range(9))


@lru_cache(maxsize=100000)
def separates(x):
    col = LOW ^ (x >> len(POS))
    return sum(col << (i*N) for i in range(len(POS)) if x >> i & 1)


@lru_cache(maxsize=50000)
def hull(cells):
    rows, cols = 0,0
    for i in range(len(POS)):
        row = cells >> (i*N) & LOW
        if row:
            rows |= 1 << i
            cols |= row
    return sum(cols << (i*N) for i in range(len(POS)) if rows >> i & 1)


def intersects_forced_rectangles(seps, singles):
    used = 0
    for sep in seps:
        rectangle = hull(sep & singles)
        if rectangle & used:
            return True
        used |= rectangle
    return False


def solve(j,budget):
    roots = RAW + (() if j is None else (RAW[0] | RAW[4] | RAW[j],))
    nodes = Counter()
    start = monotonic()

    @lru_cache(maxsize=180000)
    def works(state, rem):
        nodes[rem] += 1
        if len(state) == 1:
            return state[0] == GOAL
        slack = rem + 1 - len(state)
        if slack < 0:
            return False
        seps = [separates(w) for w in state]
        union, one, two = 0,0,0
        for z in seps:
            two ^= z & (two ^ one)
            one = (z ^ union) & (z | one)
            union |= z
        if union != ALL or (not slack and intersects_forced_rectangles(seps,one)):
            return False
        for i,j in combinations(range(len(state)),2):
            a,b = state[i],state[j]
            sa,sb = seps[i],seps[j]
            missing = (one & (sa|sb)) | (two & sa & sb)
            rest = state[:i] + state[i+1:j] + state[j+1:]
            for out in (a&b,a|b):
                if out == 0 or out == TOP or out in state:
                    continue
                todo = missing & ~separates(out)
                child = (*rest,out)
                if not todo and works(tuple(sorted(child)),rem-1):
                    return True
                if slack:
                    if not todo & ~sa and works(tuple(sorted((*child,a))),rem-1):
                        return True
                    if not todo & ~sb and works(tuple(sorted((*child,b))),rem-1):
                        return True
                if slack >= 2 and works(tuple(sorted((*child,a,b))),rem-1):
                    return True
        return False

    answer = works(tuple(sorted(roots)),budget)
    print(f"aux {j}, budget {budget}, possible {answer}, states {sum(nodes.values())}, "
          f"by budget {sorted(nodes.items())}, seconds {monotonic()-start:.2f}",flush=True)
    return answer


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cases',nargs='+')
    parser.add_argument('--budget',type=int,default=13)
    args = parser.parse_args()
    for case in args.cases:
        solve(None if case == 'bare' else int(case),args.budget)
