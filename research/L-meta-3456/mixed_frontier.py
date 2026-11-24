"""Check the sharp one-nonedge example for a mixed dirty AND in a C4-free graph."""

from itertools import combinations

LEFT = ("p", "x1", "x2", "u")
RIGHT = ("l", "y1", "y2", "v")
VERTICES = LEFT + RIGHT
EDGES = {("x1", "l"), ("x2", "l"), ("p", "y1"), ("p", "y2"), ("u", "v")}


def graph(z):
    return any(p in z and l in z for p, l in EDGES)


def signals(z):
    core = any(a in z for a in ("x1", "x2", "y1", "y2"))
    a, b = core or "u" in z, core or "v" in z
    h = "p" in z and ("l" in z or "y1" in z)
    rest = (
        ("l" in z and ("x1" in z or "x2" in z))
        or ("p" in z and "y2" in z)
        or ("u" in z and "v" in z)
    )
    return a, b, h, rest


def circuit(z, replace=None):
    a, b, h, rest = signals(z)
    g = {None: a and b, "a": a, "b": b, "false": False, "true": True}[replace]
    return (g and h) or rest


def clean_circuit(z):
    return (
        ("l" in z and ("x1" in z or "x2" in z))
        or ("p" in z and ("y1" in z or "y2" in z))
        or ("u" in z and "v" in z)
    )


def main():
    assert all(
        sum((p, l) in EDGES and (q, l) in EDGES for l in RIGHT) <= 1
        for p, q in combinations(LEFT, 2)
    )
    assignments = [set(s) for k in range(len(VERTICES) + 1) for s in combinations(VERTICES, k)]
    assert all(circuit(z) == graph(z) == clean_circuit(z) for z in assignments)
    assert {(signals(z)[0], signals(z)[1]) for z in assignments} == {
        (False, False), (False, True), (True, False), (True, True)
    }
    singleton_support = {w for w in VERTICES if all(signals({w})[:2])}
    sibling_false_pairs = [(p, l) for p in LEFT for l in RIGHT if signals({p, l})[2] and (p, l) not in EDGES]
    assert sibling_false_pairs == [("p", "l")]
    print("Assignments checked:", len(assignments))
    print("Dirty singleton support:", sorted(singleton_support))
    print("Nonedge accepted by the sibling:", sibling_false_pairs)
    for name, example in [("a", {"p", "l", "u"}), ("b", {"p", "l", "v"}),
                          ("false", {"p", "y1"}), ("true", {"p", "l"})]:
        assert circuit(example, name) != graph(example)
        print("Replacement", name, "fails on", sorted(example))


if __name__ == "__main__":
    main()
