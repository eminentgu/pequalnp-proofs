"""Exact search for a bounded signed AND circuit on selected truth table rows."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations

import graph as theta


def rows(bank):
    if bank == "full":
        return theta.POS, theta.NEG
    if bank == "three":
        return [row for row in theta.POS if row.bit_count() <= 3], theta.NEG
    if bank == "tiny":
        positive = [6,14,21,22,25,41,44,49,56,67,68,69,74,82,98,100]
        negative = [5,9,10,12,18,20,24,33,36,48,65,66,96]
        return positive, negative
    raise ValueError(bank)


def permute(row, permutation):
    return sum(((row >> i) & 1) << j for i,j in enumerate(permutation))


def row_permutations(positive, negative):
    domain = positive + negative
    indices = {row: i for i,row in enumerate(domain)}
    for permutation in permutations(range(7)):
        if not all(permute(edge,permutation) in theta.MASKS for edge in theta.MASKS):
            continue
        image = [permute(row,permutation) for row in domain]
        if all(row in indices for row in image):
            yield [indices[row] for row in image]


def swap(value, distance, mask):
    differences = (value ^ (value >> distance)) & mask
    return value ^ differences ^ (differences << distance)


def solve(positive, negative, budget=10, rectangles=True, symmetry=True, cap=0, quiet=False,
          swap_masks=None):
    assert set(positive) <= set(theta.POS) and set(negative) <= set(theta.NEG)
    assert all(any((row ^ (1 << i)) in negative for row in positive) for i in range(7))
    domain = positive + negative
    width = len(negative)
    column_mask = (1 << width) - 1
    full_grid = (1 << (len(positive)*width)) - 1
    positive_mask = (1 << len(positive)) - 1
    top = (1 << len(domain)) - 1

    def canon(wire):
        return wire ^ top if wire & 1 else wire

    raw = [canon(sum(((row >> i) & 1) << j for j,row in enumerate(domain))) for i in range(7)]

    def byte_table(perm):
        blocks = []
        for start in range(0,len(perm),8):
            values = [0]
            for destination in perm[start:start+8]:
                values.extend(value | (1 << destination) for value in tuple(values))
            blocks.append(values)
        return blocks

    tables = []
    if symmetry and swap_masks is None:
        tables = [byte_table(perm) for perm in row_permutations(positive,negative)]

    @lru_cache(maxsize=32768)
    def images(wire):
        if swap_masks is not None:
            return [canon(swap(swap(wire,1,mask1),2,mask2)) for mask1,mask2 in swap_masks]
        result = []
        for table in tables:
            rest, image = wire, 0
            for block in table:
                image |= block[rest & 255]
                rest >>= 8
            result.append(canon(image))
        return result

    def key(state):
        if not symmetry:
            return tuple(sorted(state))
        return min(tuple(sorted(image)) for image in zip(*(images(wire) for wire in state)))

    @lru_cache(maxsize=32768)
    def separating(wire):
        neg = wire >> len(positive)
        forward = sum((column_mask ^ neg) << (i*width) for i in range(len(positive))
                      if (wire >> i) & 1)
        backward = sum(neg << (i*width) for i in range(len(positive)) if not (wire >> i) & 1)
        return forward | backward, forward, backward

    @lru_cache(maxsize=16000)
    def hull(cells):
        rows_present, columns = 0, 0
        while cells:
            row_id = ((cells & -cells).bit_length()-1) // width
            row = (cells >> (row_id*width)) & column_mask
            columns |= row
            rows_present |= 1 << row_id
            cells ^= row << (row_id*width)
        rectangle = 0
        while rows_present:
            bit = rows_present & -rows_present
            rectangle |= columns << ((bit.bit_length()-1)*width)
            rows_present ^= bit
        return rectangle

    def tight_conflict(coverage, private):
        used = 0
        for cells,forward,backward in coverage:
            forced = cells & private
            if forced & forward and forced & backward:
                return True
            if rectangles:
                rectangle = hull(forced)
                if rectangle & used:
                    return True
                used |= rectangle
        return False

    class TrialLimit(Exception):
        pass

    calls, tight = 0, 0
    expanded = Counter()

    @lru_cache(maxsize=160000)
    def possible(state, remaining):
        nonlocal calls, tight
        calls += 1
        if cap and calls > cap:
            raise TrialLimit
        if len(state) == 1:
            return state == (canon(positive_mask),)
        slack = remaining + 1 - len(state)
        if slack < 0:
            return False
        coverage = [separating(wire) for wire in state]
        union, one, two = 0, 0, 0
        # Count exact multiplicities one and two so removing two wires is cheap.
        for cells,_,_ in coverage:
            two ^= cells & (two ^ one)
            one = (cells ^ union) & (cells | one)
            union |= cells
        if union != full_grid:
            return False
        if not slack and tight_conflict(coverage,one):
            tight += 1
            return False
        expanded[remaining] += 1
        for i,j in combinations(range(len(state)),2):
            a,b = state[i],state[j]
            left,right = coverage[i][0],coverage[j][0]
            missing = (one & (left|right)) | (two & left & right)
            rest = state[:i] + state[i+1:j] + state[j+1:]
            for literal_a in (a,a^top):
                for literal_b in (b,b^top):
                    new = canon(literal_a & literal_b)
                    if not new or new in state:
                        continue
                    undone = missing & ~separating(new)[0]
                    child = (*rest,new)
                    if not undone and possible(key(child),remaining-1):
                        return True
                    if slack:
                        if not undone & ~left and possible(key((*child,a)),remaining-1):
                            return True
                        if not undone & ~right and possible(key((*child,b)),remaining-1):
                            return True
                    if slack >= 2 and possible(key((*child,a,b)),remaining-1):
                        return True
        return False

    try:
        answer = possible(key(raw),budget)
    except TrialLimit:
        return None
    result = dict(possible=answer, positive=len(positive), negative=len(negative),
                  normal=sum(expanded.values()), calls=calls, tight=tight,
                  by_budget=dict(sorted(expanded.items())))
    if not quiet:
        print(result,flush=True)
    return result


if __name__ == "__main__":
    cli = argparse.ArgumentParser()
    cli.add_argument("banks",nargs="+",choices=["tiny","three","full"])
    cli.add_argument("--budget",type=int,default=10)
    cli.add_argument("--no-crossings",action="store_true")
    cli.add_argument("--no-symmetry",action="store_true")
    args = cli.parse_args()
    for name in args.banks:
        solve(*rows(name),args.budget,not args.no_crossings,not args.no_symmetry)
