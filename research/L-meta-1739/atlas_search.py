"""Search dense C4-free graph functions in the NetworkX atlas through seven vertices."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
import networkx as nx


def stars(n, edges, covers):
    for cover in covers:
        choices = [[v for v in e if v in cover] for e in edges]
        for owners in product(*choices):
            groups = {v: [] for v in sorted(cover)}
            for (a, b), v in zip(edges, owners):
                groups[v].append(b if a == v else a)
            for reverse in (False, True):
                gates = []

                def add(op, a, b):
                    gates.append((op, min(a, b), max(a, b)))
                    return n + len(gates) - 1

                def union(wires):
                    first, *tail = wires
                    for w in tail:
                        first = add('or', first, w)
                    return first

                terms = [add('and', v, union(sorted(ws, reverse=reverse)))
                         for v, ws in sorted(groups.items(), reverse=reverse)]
                out = union(terms)
                yield out, gates


def evaluate(raw, gates, out, fixed=-1, value=0):
    wires = raw.copy()
    for i, (op, a, b) in enumerate(gates, len(raw)):
        wires.append(value if i == fixed else
                     (wires[a] & wires[b] if op == 'and' else wires[a] | wires[b]))
    return wires[out], wires


def try_repair(raw, target, full, gates, out):
    n = len(raw)
    for skip in range(n, n + len(gates)):
        for sub in range(skip):
            def redirect(i):
                return sub if i == skip else i - int(i > skip)

            reduced = [(op, redirect(a), redirect(b)) for i, (op, a, b)
                       in enumerate(gates, n) if i != skip]
            output = redirect(out)
            if evaluate(raw, reduced, output)[0] == target:
                return reduced, output
            for j in range(n, n + len(reduced)):
                f0, bank = evaluate(raw, reduced, output, j, 0)
                f1, _ = evaluate(raw, reduced, output, j, full)
                bad0, bad1 = f0 ^ target, f1 ^ target
                if bad0 & bad1:
                    continue
                for a, b in combinations_with_replacement(range(j), 2):
                    for op, val in [('and', bank[a] & bank[b]), ('or', bank[a] | bank[b])]:
                        if not (bad0 & ~val or bad1 & val):
                            candidate = reduced.copy()
                            candidate[j-n] = (op, a, b)
                            assert evaluate(raw, candidate, output)[0] == target
                            return candidate, output
    return None


def main():
    counts = Counter()
    for index, graph in enumerate(nx.graph_atlas_g()):
        n = len(graph)
        if n < 3 or not nx.is_connected(graph) or graph.number_of_edges() <= n:
            continue
        if any(len(set(graph[u]) & set(graph[v])) > 1 for u, v in combinations(graph, 2)):
            continue
        edges = sorted(graph.edges())
        covers = []
        for t in range(n+1):
            covers = [set(S) for S in combinations(range(n), t)
                      if all(a in S or b in S for a, b in edges)]
            if covers:
                break
        rows = 1 << n
        raw = [sum(1 << m for m in range(rows) if m & 1 << i) for i in range(n)]
        target = 0
        for u, v in edges:
            target |= raw[u] & raw[v]
        seen = set()
        for out, gates in stars(n, edges, covers):
            key = tuple(gates), out
            if key in seen:
                continue
            seen.add(key)
            assert len(gates) == len(edges)+t-1 and evaluate(raw, gates, out)[0] == target
            witness = try_repair(raw, target, (1 << rows)-1, gates, out)
            if witness:
                print(f'Counterexample: atlas {index}, edges {edges}, gates/output {witness}', flush=True)
                return
        counts[n, 'graphs'] += 1
        counts[n, 'circuits'] += len(seen)
    for n in (5, 6, 7):
        print(f'n={n}: {counts[n,"graphs"]} graphs; {counts[n,"circuits"]} distinct starting circuits.')
    print('No counterexample in the searched neighborhoods.')


if __name__ == '__main__':
    main()
