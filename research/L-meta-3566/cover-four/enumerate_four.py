"""Enumerate all reduced girth-at-least-five graphs of minimum vertex cover size four."""
import argparse
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path


PAIRS = tuple(combinations(range(4), 2))
REORDERINGS = tuple(permutations(range(4)))


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def graph(inside, columns):
    adj = [0] * (4 + len(columns))
    for mask, (a, b) in enumerate(PAIRS):
        if inside & (1 << mask):
            adj[a] |= 1 << b
            adj[b] |= 1 << a
    for v, column in enumerate(columns, 4):
        adj[v] = column
        for u in vertices(column):
            adj[u] |= 1 << v
    return tuple(adj)


def represent(adj, cover):
    """Lexicographically least tagged encoding across the 24 orders of a specified cover."""
    outside = [i for i in range(len(adj)) if not cover >> i & 1]
    labels = tuple(vertices(cover))
    if len(labels) != 4:
        raise ValueError("expected a cover of size four")
    keys = []
    for order in REORDERINGS:
        ordered = [labels[i] for i in order]
        inside = sum(1 << k for k, (i, j) in enumerate(PAIRS) if adj[ordered[i]] >> ordered[j] & 1)
        columns = tuple(sorted(sum(1 << i for i, u in enumerate(ordered) if adj[v] >> u & 1)
                               for v in outside))
        keys.append((inside, columns))
    return min(keys)


def minimum_covers(adj):
    """For a fixed choice inside the first four vertices, all needed outside vertices are forced."""
    choices = []
    for selected in range(16):
        omitted = 15 ^ selected
        if any(adj[v] & omitted for v in vertices(omitted)):
            continue
        forced = sum(1 << v for v in range(4, len(adj)) if adj[v] & omitted)
        choices.append(selected | forced)
    least = min(c.bit_count() for c in choices)
    return least, [c for c in choices if c.bit_count() == least]


def canonical(adj, covers):
    return min(represent(adj, cover) for cover in covers)


def induced_without(adj, v):
    return tuple(other & ~(1 << v) if i != v else 0 for i, other in enumerate(adj))


def structure(adj):
    unseen = set(range(len(adj)))
    bipartite = True
    components = 0
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        color = {start: 0}
        queue = [start]
        for u in queue:
            for v in vertices(adj[u]):
                if v in unseen:
                    unseen.remove(v)
                    queue.append(v)
                    color[v] = 1 - color[u]
                elif color[v] == color[u]:
                    bipartite = False
        components += 1
    return components, bipartite


def candidates():
    """Enumerate normalized distinguished-cover presentations; validate restrictions locally."""
    for inside in range(64):
        base = graph(inside, ())
        if any(base[a] & base[b] and base[a] >> b & 1 for a, b in PAIRS):
            continue
        if any((base[a] & base[b]).bit_count() >= 2 for a, b in PAIRS):
            continue
        if inside != represent(base, 15)[0]:
            continue
        legal = [column for column in range(1, 16)
                 if all(not (base[a] >> b & 1 or base[a] & base[b])
                        for a, b in combinations(vertices(column), 2))]
        used_pairs = {column: sum(1 << k for k, (a, b) in enumerate(PAIRS)
                                  if column >> a & column >> b & 1) for column in legal}
        def extend(i, taken, columns):
            if i == len(legal):
                yield tuple(columns)
                return
            yield from extend(i + 1, taken, columns)
            column = legal[i]
            if not taken & used_pairs[column]:
                yield from extend(i + 1, taken | used_pairs[column], [*columns, column])
        for columns in extend(0, 0, []):
            adj = graph(inside, columns)
            if any(row == 0 for row in adj):
                continue
            leaves = [row for row in adj if row.bit_count() == 1]
            if len(leaves) != len(set(leaves)):
                continue
            least, covers = minimum_covers(adj)
            if least != 4 or (inside, columns) != represent(adj, 15):
                continue
            yield adj, canonical(adj, covers)


def edges(adj):
    return [(i, j) for i, row in enumerate(adj) for j in vertices(row) if i < j]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--published", type=Path, help="optional L-meta-612 cover_four.py table on stdin format")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    keys = set()
    presentations = 0
    for _, key in candidates():
        keys.add(key)
        presentations += 1
    published = {}
    if args.published:
        for line in args.published.read_text().splitlines():
            i, n, m, _, *coords = map(int, line.split())
            adj = [0] * n
            for a, b in zip(coords[::2], coords[1::2]):
                adj[a] |= 1 << b
                adj[b] |= 1 << a
            if any(adj[a] & adj[b] for a, b in edges(adj)):
                continue
            least, covers = minimum_covers(adj)
            assert least == 4 and len(edges(adj)) == m
            published[canonical(adj, covers)] = i
    stages = Counter()
    residual = []
    detailed = []
    for inside, columns in sorted(keys, key=lambda key: (len(key[1]), key)):
        adj = graph(inside, columns)
        n = len(adj)
        es = edges(adj)
        components, bipartite = structure(adj)
        cyclic = len(es) > n - components
        # Independent exact minimum test, including all isolates and without privileging the tagged cover.
        edgemasks = [(1 << a) | (1 << b) for a, b in es]
        covers3 = [sum(1 << v for v in chosen) for chosen in combinations(range(n), 3)]
        assert not any(all(s & e for e in edgemasks) for s in covers3)
        stable = []
        trivial = []
        for v, row in enumerate(adj):
            if row.bit_count() != 1:
                continue
            core = induced_without(adj, v)
            k, _ = minimum_covers(core)
            brute_drop = any(all(s & e or e >> v & 1 for e in edgemasks) for s in covers3)
            assert k in (3, 4) and brute_drop == (k == 3)
            if k == 4:
                stable.append(v)
            u = next(vertices(row))
            if adj[u].bit_count() <= 2:
                trivial.append(v)
        stages['duplicate-free', n] += 1
        if not cyclic:
            stages['forest', n] += 1
        elif stable:
            stages['cyclic/some-stable-leaf', n] += 1
        else:
            stages['cyclic/all-leaves-critical', n] += 1
            index = len(residual)
            pid = published.get((inside, columns))
            if trivial:
                stage = 'isolated-edge' if any(adj[next(vertices(adj[v]))].bit_count() == 1 for v in trivial) else 'pendant-path'
            else:
                stage = 'no-leaf-rule'
            stages[stage, n] += 1
            fields = [index, n, len(es), 4, *(v for edge in es for v in edge)]
            residual.append(' '.join(map(str, fields)))
            detailed.append((index, n, len(es), components, int(bipartite), stage,
                             '' if pid is None else pid, inside, ','.join(map(str, columns))))
            if args.published:
                assert (pid is not None) == (stage == 'no-leaf-rule')
    if args.published:
        assert len(published) == sum(1 for record in detailed if record[6] != '')
    (args.output / 'critical.txt').write_text(''.join(row + '\n' for row in residual))
    (args.output / 'critical.tsv').write_text('id\tn\tedges\tcomponents\tbipartite\tstage\tpublished_id\tinside_mask\toutside_masks\n'
        + ''.join('\t'.join(map(str, row)) + '\n' for row in detailed))
    print('normalized distinguished-cover presentations:', presentations)
    names = ['duplicate-free', 'forest', 'cyclic/some-stable-leaf', 'cyclic/all-leaves-critical',
             'isolated-edge', 'pendant-path', 'no-leaf-rule']
    print('stage'.ljust(31), *(str(n).rjust(5) for n in range(6, 15)), 'total')
    for name in names:
        values = [stages[name, n] for n in range(6, 15)]
        print(name.ljust(31), *(str(count).rjust(5) for count in values), sum(values))
    print('bipartite stable-critical graphs:', sum(row[4] for row in detailed))
    print('bipartite no-leaf-rule graphs:', sum(row[4] for row in detailed if row[5]=='no-leaf-rule'))
    if args.published:
        print('published residual IDs:', *sorted(published.values()))
    print('unlabeled graphs with four vertices in a minimum cover:', len(keys))


if __name__ == '__main__':
    main()
