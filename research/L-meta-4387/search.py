"""Exact 58-column monotone circuit synthesis for the L-meta-4387 bank."""
import argparse
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Glucose4

RAW = [
    95229015649943559, 63038587666488, 256462815680, 4292497062759936,
    8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
    155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
    270286071508633728, 288160007407550752,
]
BASE = RAW + [95274182876594239]
TARGET = (1 << 21) - 1


def star_trace():
    gates, roots = [], []

    def append(is_and, a, b):
        gates.append((is_and, min(a, b), max(a, b)))
        return len(BASE) + len(gates) - 1

    for l in range(7):
        a, b, c = (p for p in range(7) if (p + l) % 7 in (0, 1, 3))
        pair = 14 if l == 0 else append(False, a, b)
        roots.append(append(True, append(False, pair, c), 7 + l))
    out, *rest = roots
    for root in rest:
        out = append(False, out, root)
    return gates


def check(gates):
    pool = BASE.copy()
    for is_and, a, b in gates:
        assert 0 <= a <= b < len(pool)
        pool.append(pool[a] & pool[b] if is_and else pool[a] | pool[b])
    return pool[-1] == TARGET


def solve(size, budget, final_gate, control):
    ids, prior, parameters = IDPool(), [], []
    witness = star_trace()
    assert BASE[-1] == RAW[0] | RAW[1] and len(witness) == 26 and check(witness)
    with Glucose4() as solver:
        add = solver.add_clause
        for i in range(size):
            width = len(BASE) + i
            op = ids.id()
            left, right = ([ids.id() for _ in range(width)] for _ in range(2))
            for slots in (left, right):
                add(slots)
                for a, b in combinations(slots, 2):
                    add([-a, -b])
            for a in range(width):
                for b in range(a):
                    add([-left[a], -right[b]])
            if control:
                is_and, a, b = witness[i]
                add([op if is_and else -op])
                add([left[a]])
                add([right[b]])
            if i == size - 1 and final_gate:
                add([op if final_gate == "and" else -op])
            values = []
            for row in range(58):
                a, b, out = (ids.id() for _ in range(3))
                for selectors, arg in ((left, a), (right, b)):
                    for j, sel in enumerate(selectors):
                        if j < len(BASE):
                            add([-sel, arg if BASE[j] & (1 << row) else -arg])
                        else:
                            v = prior[j - len(BASE)][row]
                            add([-sel, -arg, v])
                            add([-sel, arg, -v])
                for clause in ([-op, -out, a], [-op, -out, b], [-op, out, -a, -b],
                               [op, out, -a], [op, out, -b], [op, -out, a, b]):
                    add(clause)
                if i == size - 1:
                    add([out if TARGET & (1 << row) else -out])
                values.append(out)
            prior.append(values)
            parameters.append((op, left, right))
        solver.conf_budget(budget)
        sat = solver.solve_limited()
        if sat is None:
            print("UNKNOWN", size, final_gate, solver.accum_stats()["conflicts"])
        elif sat:
            model = set(solver.get_model())
            gates = [(op in model, next(i for i, s in enumerate(left) if s in model),
                      next(i for i, s in enumerate(right) if s in model))
                     for op, left, right in parameters]
            assert check(gates)
            print("SAT", size, gates)
        else:
            print("UNSAT (solver)", size, final_gate)
        return sat


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("size", type=int, choices=range(1, 27), metavar="1..26")
    p.add_argument("--conflicts", type=int, default=100000)
    p.add_argument("--last", choices=("and", "or"))
    p.add_argument("--check-stars", action="store_true")
    args = p.parse_args()
    if args.conflicts <= 0 or (args.check_stars and (args.size != 26 or args.last)):
        p.error("use a positive budget and size 26 with no final gate restriction for --check-stars")
    if solve(args.size, args.conflicts, args.last, args.check_stars) is not True and args.check_stars:
        raise SystemExit("positive control failed")
