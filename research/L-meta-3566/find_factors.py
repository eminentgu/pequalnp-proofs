"""Construct and count physically shared two-branch AO2 circuits for square-free graph functions."""
import argparse
import itertools as it
import random
from collections import Counter
from functools import lru_cache


def members(mask):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


class Search:
    def __init__(self, n, m, edges):
        self.n, self.m = n, m
        self.E = sum(1 << (r * m + c) for r, c in set(edges))
        self.row = tuple((self.E >> (r * m)) & ((1 << m) - 1) for r in range(n))
        self.col = tuple(sum(1 << r for r in range(n) if self.row[r] >> c & 1) for c in range(m))
        assert all((R & S).bit_count() <= 1 for R, S in it.combinations(self.row, 2))
        bad = []
        for r in range(n):
            for c in range(m):
                bad.append(sum(1 << (u*m+v) for u in range(n) for v in range(m)
                               if not (self.row[u] >> c & 1 or self.row[r] >> v & 1)))
        self.bad = bad
        self.cover = lru_cache(maxsize=5000)(self.cover)
        self.blocks = self.blocks_for_graph()
        self.compat = [[j for j, y in enumerate(self.blocks) if not (x[3] & y[2])]
                       for x in self.blocks]
        self.target = self.E.bit_count() + len(self.cover(self.E)) - 1

    def blocks_for_graph(self):
        found = {}
        for trans in [False, True]:
            ns = self.col if trans else self.row
            for i, j in it.combinations(range(len(ns)), 2):
                allowed = tuple(members(ns[i] | ns[j]))
                for k in range(2, min(5, len(allowed)) + 1):
                    for items in it.combinations(allowed, k):
                        a, b = (1 << i) | (1 << j), sum(1 << l for l in items)
                        if trans:
                            a, b = b, a
                        shape = sum(b << (r*self.m) for r in members(a))
                        extras = shape & ~self.E
                        if not extras or extras.bit_count() > 5:
                            continue
                        if (shape & self.E).bit_count() < k+1:
                            continue
                        forbidden = 0
                        for loc in members(extras):
                            forbidden |= self.bad[loc]
                        found[a, b] = (a, b, extras, forbidden, shape)
        return list(found.values())

    def cover(self, edges):
        if not edges:
            return ()
        rows = [(edges >> (r*self.m)) & ((1 << self.m)-1) for r in range(self.n)]
        active = [r for r, cols in enumerate(rows) if cols]
        # Process row covers and derive all compulsory column centers.
        opts = [sum(1 << r for r in active)]
        best = len(active)
        for size in range(len(active)):
            if size >= best:
                break
            for chosen in it.combinations(active, size):
                mask = sum(1 << r for r in chosen)
                cols = 0
                for r in active:
                    if not (mask >> r & 1):
                        cols |= rows[r]
                cost = size + cols.bit_count()
                if cost < best:
                    best, opts = cost, [mask]
                elif cost == best:
                    opts.append(mask)
        # Among minimum covers get the one with largest stars (more potential common ORs).
        options = []
        for roots in opts[:12]:
            rects = [(1 << r, rows[r]) for r in members(roots)]
            for col in range(self.m):
                rs = sum(1 << r for r in active if not (roots >> r & 1) and rows[r] >> col & 1)
                if rs:
                    rects.append((rs, 1 << col))
            options.append(tuple(rects))
        return max(options, key=lambda ss: sum((a.bit_count()*b.bit_count())**2 for a, b in ss))

    def cost(self, left, right):
        blocks = self.blocks
        def union(ids):
            mask = 0
            for i in ids:
                mask |= blocks[i][4]
            return mask
        x, y = union(left), union(right)
        # Distribute out all graph edges absent from both dirty regions.
        common = self.cover(self.E & ~(x|y))
        L = tuple((blocks[i][0], blocks[i][1]) for i in left) + self.cover(self.E & y & ~x)
        R = tuple((blocks[i][0], blocks[i][1]) for i in right) + self.cover(self.E & x & ~y)
        groups = [common, L, R]
        allterms = list(dict.fromkeys(common + L + R))
        # Compile all OR-of-raw operands simultaneously. Duplicate subgates are actual wire aliases.
        operands = [frozenset(members(q)) for a, b in allterms for q in [a, b << self.n]]
        shapes = list(dict.fromkeys(operands))
        todo = {k: set(k) for k in shapes}
        gates, memo = [], {}
        def emit(op, u, v):
            if u == v:
                return u
            key = op, min(u, v), max(u, v)
            if key not in memo:
                memo[key] = self.n+self.m+len(gates)
                gates.append(key)
            return memo[key]
        while any(len(q) > 1 for q in todo.values()):
            pairs = Counter(pair for q in todo.values() for pair in it.combinations(sorted(q), 2))
            pair = max(pairs, key=pairs.get)
            w = emit('or', *pair)
            for q in todo.values():
                if pair[0] in q and pair[1] in q:
                    q.difference_update(pair)
                    q.add(w)
        refs = {q: next(iter(v)) for q, v in todo.items()}
        termw = {t: emit('and', refs[operands[2*i]], refs[operands[2*i+1]])
                 for i, t in enumerate(allterms)}
        def disj(ss):
            ws = sorted({termw[t] for t in ss})
            if not ws:
                return None
            w = ws[0]
            for v in ws[1:]:
                w = emit('or', w, v)
            return w
        c, h, k = map(disj, groups)
        output = emit('and', h, k)
        if c is not None:
            output = emit('or', c, output)
        return len(gates), (gates, output)

    def verify(self, program):
        # Positive tests on each original edge. For every chosen row subset
        # use the largest independent column subset. By monotonicity these
        # negative tests dominate all graph-independent assignments.
        gates, output = program
        tests = []
        for loc in members(self.E):
            r, c = divmod(loc, self.m)
            tests.append(((1 << r) | (1 << (self.n+c)), True))
        for chosen in range(1 << self.n):
            cols = (1 << self.m)-1
            for r in members(chosen):
                cols &= ~self.row[r]
            tests.append((chosen | (cols << self.n), False))
        wires = [sum(1 << i for i, (x, _) in enumerate(tests) if x >> v & 1)
                 for v in range(self.n+self.m)]
        for op, u, v in gates:
            wires.append((wires[u] & wires[v]) if op == 'and' else (wires[u] | wires[v]))
        assert wires[output] == sum(1 << i for i, (_, y) in enumerate(tests) if y)
        return len(tests)

    def run(self, rng, maxcount):
        stats, best, proof = Counter(), None, None
        seen = set()
        picks = [(i, j) for i in range(len(self.blocks)) for j in self.compat[i] if i<j]
        rng.shuffle(picks)
        for i, j in picks[:maxcount]:
            L, R = (i,), (j,)
            variants = [(L, R)]
            for _ in range(8):
                l = rng.choice(self.compat[j])
                vals = [k for k in self.compat[i] if k in self.compat[l] and k!=j]
                if l != i and vals:
                    # Require both rectangles in each factor to add distinct new true/false coverage.
                    k = rng.choice(vals)
                    if self.blocks[l][2] & ~self.blocks[i][2] and self.blocks[i][2] & ~self.blocks[l][2]:
                        if self.blocks[k][2] & ~self.blocks[j][2] and self.blocks[j][2] & ~self.blocks[k][2]:
                            variants.append((tuple(sorted((i,l))), tuple(sorted((j,k)))))
            for l, r in variants:
                key = tuple(sorted((l, r)))
                if key in seen:
                    continue
                seen.add(key)
                stats[len(l),len(r)] += 1
                cost, dag = self.cost(l,r)
                if best is None or cost < best:
                    best, proof = cost, (l,r,dag)
                    if cost < self.target:
                        return stats, best, proof
        return stats, best, proof


def cases(seed):
    rng=random.Random(seed)
    yield 'heawood',7,7,[(p,l) for l in range(7) for p in ((l+k)%7 for k in (0,1,3))]
    yield 'affine3',9,9,[(3*x+y,3*m+c) for x,y,m,c in it.product(range(3),repeat=4) if y==(m*x+c)%3]
    for n in [6,7,8,9,10]:
        for k in range(10):
            pairs=list(it.product(range(n),range(n)));rng.shuffle(pairs)
            rows=[set() for _ in range(n)]
            for r,c in pairs:
                if not any(c in row and rows[r]&row for row in rows):
                    rows[r].add(c)
            yield f'random-{n+n}-{k}',n,n,[(r,c) for r,S in enumerate(rows) for c in S]


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--limit',type=int,default=35)
    p.add_argument('--offset',type=int,default=0)
    p.add_argument('--end',type=int,default=200)
    opts=p.parse_args()
    for idx,(name,n,m,E) in enumerate(cases(3566)):
        if idx<opts.offset or idx>=opts.end:
            continue
        s=Search(n,m,E)
        counts,best,proof=s.run(random.Random(8108+idx),opts.limit)
        tested = s.verify(proof[2]) if proof else 0
        print(name,n+m,len(E),s.target,len(s.blocks),sum(counts.values()),counts[(2,2)],best,tested,flush=True)
        if best is not None and best<s.target:
            print('counterexample',name,E,proof,flush=True)
            break


if __name__=='__main__':
    main()
