"""Search the explicit Fano plane for small binary monotone circuits using PySAT."""
import argparse
from itertools import combinations

from pysat.formula import IDPool
from pysat.solvers import Glucose4

FLAGS = [(p, l) for p in range(7) for l in range(7) if (p + l) % 7 in (0, 1, 3)]
PAIRS = [(1 << p) | (1 << (7 + l)) for p, l in FLAGS]
ASSIGNMENTS = range(1 << 14)


def target(row):
    return any(row & pair == pair for pair in PAIRS)


def boundary():
    """Keep the minimal true rows and the maximal false rows under bit inclusion."""
    truth = [target(row) for row in ASSIGNMENTS]
    zeros = [row for row in ASSIGNMENTS if not truth[row] and
             all(truth[row | (1 << i)] for i in range(14) if not row & (1 << i))]
    assert len(PAIRS) == 21 and len(zeros) == 37
    for row in ASSIGNMENTS:
        assert any(row & z == row for z in zeros) == (not truth[row])
    return [(r, True) for r in PAIRS] + [(r, False) for r in zeros]


def star_circuit():
    gates = []
    roots = []
    for p in range(7):
        a, b, c = [7 + l for i, l in FLAGS if i == p]
        w = 14 + len(gates)
        gates.extend([("or", a, b), ("or", w, c), ("and", p, w + 1)])
        roots.append(w + 2)
    out = roots[0]
    for root in roots[1:]:
        gates.append(("or", out, root))
        out = 13 + len(gates)
    return gates


def check_model(gates):
    for row in ASSIGNMENTS:
        wires = [bool(row & (1 << i)) for i in range(14)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
        if wires[-1] != target(row):
            raise ValueError(f"candidate disagrees with the incidence function at {row}")


def search(size, conflicts, known, first):
    rows = boundary()
    pool = IDPool()
    with Glucose4() as solver:
        add = solver.add_clause
        variables = []
        outputs = []
        witness = star_circuit() if known else []
        for i in range(size):
            n = 14 + i
            is_and = pool.id()
            left, right = ([pool.id() for _ in range(n)] for _ in range(2))
            for bank in (left, right):
                add(bank)
                for a, b in combinations(bank, 2):
                    add([-a, -b])
            for a in range(n):
                for b in range(a):
                    add([-left[a], -right[b]])
            if first and i == 0:
                op, kind = first.split("-")
                pair = {"same": (0, 1), "flag": (0, 7), "nonflag": (0, 9)}[kind]
                add([is_and if op == "and" else -is_and])
                add([left[pair[0]]])
                add([right[pair[1]]])
            if known:
                op, a, b = witness[i]
                add([is_and if op == "and" else -is_and])
                add([left[min(a, b)]])
                add([right[max(a, b)]])
            result = []
            for r, (row, expected) in enumerate(rows):
                a, b, y = (pool.id() for _ in range(3))
                for bank, arg in ((left, a), (right, b)):
                    for j, selector in enumerate(bank):
                        if j < 14:
                            add([-selector, arg if row & (1 << j) else -arg])
                        else:
                            value = outputs[j - 14][r]
                            add([-selector, -arg, value])
                            add([-selector, arg, -value])
                for clause in ([-is_and, -y, a], [-is_and, -y, b], [-is_and, y, -a, -b],
                               [is_and, y, -a], [is_and, y, -b], [is_and, -y, a, b]):
                    add(clause)
                if i == size - 1:
                    add([y if expected else -y])
                result.append(y)
            variables.append((is_and, left, right))
            outputs.append(result)
        solver.conf_budget(conflicts)
        status = solver.solve_limited()
        if status is None:
            print(f"UNKNOWN after {solver.accum_stats()['conflicts']} conflicts at {size} gates")
        elif not status:
            print(f"UNSAT at {size} gates (solver result)")
        else:
            model = set(solver.get_model())
            gates = [("and" if op in model else "or",
                      next(i for i, bit in enumerate(lhs) if bit in model),
                      next(i for i, bit in enumerate(rhs) if bit in model))
                     for op, lhs, rhs in variables]
            check_model(gates)
            print(f"SAT at {size} gates, verified on all 16384 assignments: {gates}")
        return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("size", type=int, choices=range(1, 28), metavar="1..27")
    parser.add_argument("--conflicts", type=int, default=25000)
    parser.add_argument("--check-stars", action="store_true", help="fix all gates to the known 27-gate realization")
    parser.add_argument("--first", choices=[f"{op}-{kind}" for op in ("and", "or")
                                          for kind in ("same", "flag", "nonflag")],
                        help="restrict the first gate to one symmetry class")
    args = parser.parse_args()
    if args.conflicts <= 0 or (args.check_stars and (args.size != 27 or args.first)):
        parser.error("use a positive budget and exactly 27 gates for --check-stars")
    result = search(args.size, args.conflicts, args.check_stars, args.first)
    if args.check_stars and result is not True:
        raise SystemExit("positive control failed")
