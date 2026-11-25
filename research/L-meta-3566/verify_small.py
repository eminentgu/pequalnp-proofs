"""Check the 5-by-5 and 5-by-6 matching-saturated square-free cases.

Usage: python3 verify_small.py path/to/helloitswill/L-meta-612/kernel_search.cpp
Requires a C++17 compiler and the original pinned source at commit
894ed421c9bccac0310ab9a270902798c2aec00c of helloitswill/pequalnp-research-notes.
The starting cofactor assumption is the published four-cover result in that source.
"""
import argparse
from hashlib import sha256
from itertools import permutations
from pathlib import Path
import subprocess
import tempfile

N = 5
PINNED_SOURCE = "ba51eae17193196fd3f1f60da98c45db5299a292bcfa6a6422825439ad22f677"


def classes(row_count):
    column_perms = [
        [sum(1 << pi[i] for i in range(N) if v >> i & 1) for v in range(1 << N)]
        for pi in permutations(range(N))
    ]
    pair_masks = [
        sum(1 << (i * N + j) for i in range(N) for j in range(i) if v >> i & v >> j & 1)
        for v in range(1 << N)
    ]
    seen = set()
    result = []

    def gen(rows, lower, used_pairs):
        if len(rows) == row_count:
            if rows in seen:
                return
            matrices = [rows]
            if row_count == N:
                matrices.append(tuple(sum(1 << j for j, row in enumerate(rows) if row >> i & 1)
                                      for i in range(N)))
            for matrix in matrices:
                for perm in column_perms:
                    seen.add(tuple(sorted(perm[r] for r in matrix)))
            matched = {0}
            for row in rows:
                matched |= {mask | (1 << i) for mask in tuple(matched) for i in range(N)
                            if row >> i & 1 and not mask >> i & 1}
            if (1 << N) - 1 in matched:
                result.append(rows)
            return
        for row in range(lower, 1 << N):
            if not used_pairs & pair_masks[row]:
                gen((*rows, row), row, used_pairs | pair_masks[row])

    gen((), 1, 0)
    return sorted(result, key=lambda rows: (sum(r.bit_count() for r in rows), rows))


def graph_input(row_count, rows, index):
    n = row_count + N
    edges = [(u, N + j) for j, row in enumerate(rows) for u in range(N) if row >> u & 1]
    # The column vertices form a minimum cover. Evaluate the resulting star circuit on every input.
    nrows = 1 << n
    patterns = range(nrows)
    wires = [sum(1 << x for x in patterns if x >> i & 1) for i in range(n)]
    tails = []
    gates = 0
    for u in range(N):
        nb = [v for w, v in edges if w == u]
        arm = wires[nb[0]]
        for v in nb[1:]:
            arm |= wires[v]
            gates += 1
        tails.append(wires[u] & arm)
        gates += 1
    output = tails[0]
    for sig in tails[1:]:
        output |= sig
        gates += 1
    assert gates == len(edges) + N - 1
    expected = sum(1 << x for x in patterns if any((x >> u) & (x >> v) & 1 for u, v in edges))
    assert output == expected
    return ' '.join(map(str, (index, n, len(edges), N, *(v for edge in edges for v in edge))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--compiler', default='c++')
    args = parser.parse_args()
    raw = args.source.read_bytes()
    if sha256(raw).hexdigest() != PINNED_SOURCE:
        raise SystemExit('Unexpected kernel_search.cpp SHA-256')
    text = raw.decode()
    # Increase fixed storage bounds for the additional boundary pairs and sampled input rows.
    text = text.replace('std::bitset<256>', 'std::bitset<320>')
    text = text.replace('m * k > 256 || examples.size() > 32', 'm * k > 320 || examples.size() + n >= 64')
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        src = root / 'kernel.cpp'
        src.write_text(text)
        exe = root / 'search'
        subprocess.run([args.compiler, '-std=c++17', '-O3', str(src), '-o', str(exe)], check=True)
        for rows, count in [(5,64), (6,307)]:
            graphs = classes(rows)
            assert len(graphs) == count
            items = [graph_input(rows, g, i) for i, g in enumerate(graphs)]
            run = subprocess.run([str(exe), '0', str(count - 1), '0', '--smaller-optimal', '17'],
                                 input='\n'.join(items) + '\n', capture_output=True, text=True, check=True)
            lines = [s.split() for s in run.stdout.splitlines()]
            assert len(lines) == count and all(f[8] == 'NONE' and int(f[1]) == i for i,f in enumerate(lines))
            print(f'{N+rows} vertices: {count} exclusions, {count} positive controls, '
                  f'{sum(int(s[-1]) for s in lines):,} expanded states', flush=True)


if __name__ == '__main__':
    main()
