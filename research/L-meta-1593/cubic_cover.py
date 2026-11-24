"""Check the standard vertex-cover construction on a concrete cubic graph."""

from collections import Counter, deque
from functools import cache


def neighbors(n, edges):
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    return adjacency


def girth(n, edges):
    adjacency = neighbors(n, edges)
    best = n + 1
    for a, b in edges:
        queue = deque([(a, 0)])
        seen = {a}
        while queue:
            v, d = queue.popleft()
            if v == b:
                best = min(best, d + 1)
                break
            for w in adjacency[v]:
                if (v, w) != (a, b) and w not in seen:
                    queue.append((w, d + 1))
                    seen.add(w)
    return best


def minimum_cover(n, edges):
    adjacency = neighbors(n, edges)
    masks = [sum(1 << v for v in row) for row in adjacency]

    @cache
    def solve(active):
        # A cover either contains v, or contains all active neighbors of v.
        degrees = [(m & active).bit_count() if active & (1 << i) else 0
                   for i, m in enumerate(masks)]
        if max(degrees) == 0:
            return 0
        v = degrees.index(max(degrees))
        others = active & ~(1 << v)
        neighborhood = masks[v] & others
        take_v = (1 << v) | solve(others)
        skip_v = neighborhood | solve(others & ~neighborhood)
        return min((take_v, skip_v), key=int.bit_count)

    mask = solve((1 << n) - 1)
    result = {v for v in range(n) if mask & (1 << v)}
    assert all(u in result or v in result for u, v in edges)
    return result


def checked_star_circuit(n, edges, cover):
    # Wire i<n is input i. Assign each edge to one of its cover endpoints.
    stars = {c: [] for c in cover}
    for u, v in sorted(edges):
        c, w = (u, v) if u in cover else (v, u)
        stars[c].append(w)

    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return n + len(gates) - 1

    def disjunction(inputs):
        out, *tail = inputs
        for i in tail:
            out = gate("OR", out, i)
        return out

    output = disjunction([gate("AND", c, disjunction(stars[c])) for c in sorted(cover)])
    # Expand the resulting circuit into a positive DNF. Equality of monomials
    # with the original edge set certifies equality on every Boolean input.
    terms = [{frozenset({v})} for v in range(n)]
    for op, a, b in gates:
        if op == "AND":
            terms.append({s | t for s in terms[a] for t in terms[b]})
        else:
            terms.append(terms[a] | terms[b])
    assert terms[output] == {frozenset(e) for e in edges}
    assert len(gates) == len(edges) + len(cover) - 1
    return len(gates)


def main():
    n = 24
    jumps = (12, 7, -7)
    edges = {tuple(sorted((v, (v + step) % n)))
             for v in range(n) for step in (1, jumps[v % 3])}
    assert all(len(row) == 3 for row in neighbors(n, edges))
    print(f"Vertices {n}, edges {len(edges)}, girth {girth(n, edges)}")
    cover = minimum_cover(n, edges)
    print(f"Minimum vertex cover ({len(cover)} vertices): {sorted(cover)}")
    full_size = checked_star_circuit(n, edges, cover)
    print(f"Full cover-construction upper bound: {full_size} gates")
    bounds = {}
    for v in range(n):
        remaining = {e for e in edges if v not in e}
        residual = minimum_cover(n, remaining)
        bounds[v] = checked_star_circuit(n, remaining, residual)
    print(f"Bounds after deleting an incidence set: {dict(Counter(bounds.values()))}")
    assert all(bounds[v] <= full_size - 4 for v in cover)
    print("All 25 fan-in-two circuits were verified by symbolic DNF expansion.")
    print("These are constructive upper bounds. Circuit minima are unknown.")


if __name__ == "__main__":
    main()
