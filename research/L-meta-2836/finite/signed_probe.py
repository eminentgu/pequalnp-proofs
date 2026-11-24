"""Exhaustive reference search on the 133 rows, following the project's Live semantics.

Usage: python3 signed_probe.py t1 all 4,3,2,1
       python3 signed_probe.py t1 no-seed 5,4,3,2,1

A state contains the signals still needed by the output. A binary gate consumes
its two operands and may retain either or both for later use. A NOT gate may
retain its input. With k gates and exactly t NOTs left, at most k - t + 1
different signals can still be needed. The initial set must be tried with and
without the free triple-OR signal; the Lean private-pair tests force the rest.
"""
from collections import Counter
from functools import cache, lru_cache
from itertools import combinations
from time import monotonic
import argparse
from sample_rows import P1, I, inputs

def search(branch, seed, budgets):
    keys = [key for key, _ in inputs(0, branch) if seed or key != 10]
    positives, negatives = P1, I
    n, m = len(positives), len(negatives)
    low = (1 << m) - 1
    full = (1 << (n * m)) - 1
    signals = []
    indices = {}
    def intern(sig):
        if sig not in indices:
            indices[sig] = len(signals)
            signals.append(sig)
        return indices[sig]
    neg_repeated = full // low
    for key in keys:
        pos = sum(low << (m * r) for r, x in enumerate(positives) if dict(inputs(x, branch))[key])
        neg = sum(dict(inputs(x, branch))[key] << r for r, x in enumerate(negatives))
        intern((pos, neg * neg_repeated))
    root = tuple(range(len(keys)))
    @cache
    def gate(i, j, is_or):
        p, a = signals[i]; q, b = signals[j]
        sig = (p | q, a | b) if is_or else (p & q, a & b)
        return -1 if sig in ((0, 0), (full, full)) else intern(sig)
    @cache
    def negate(i):
        p, n = signals[i]
        return intern((full ^ p, full ^ n))
    @cache
    def coverage(w, signed):
        p, n = signals[w]
        return p ^ n if signed else p & ~n
    @cache
    def column(w, side):
        word = signals[w][side]
        return tuple((word >> (k if side else m*k)) & 1 for k in range(m if side else n))
    @lru_cache(35000)
    def distinct_rows(w, side):
        rows = [0] * (m if side else n)
        for j, a in enumerate(w):
            for k, v in enumerate(column(a, side)):
                rows[k] |= v << j
        return set(rows)
    def obstruct(k, t, w):
        ps = distinct_rows(w, 0)
        ns = distinct_rows(w, 1)
        if ps & ns: return "equal"
        if len(w)+t != k+1: return None
        # A one-coordinate difference forces that coordinate's signed label.
        # A read-once output's labels occupy disjoint rectangles.
        pos_flags, neg_flags, signs = {}, {}, {}
        for p in ps:
            for i in range(len(w)):
                bit = 1 << i
                q = p ^ bit
                if q not in ns: continue
                s = bool(p & bit)
                if i in signs and signs[i] != s: return "sign"
                signs[i] = s
                pos_flags[p] = pos_flags.get(p, 0) | bit
                neg_flags[q] = neg_flags.get(q, 0) | bit
        if any((a & b).bit_count() >= 2 for a in pos_flags.values() for b in neg_flags.values()):
            return "cross"
        return None
    def children(k, t, wires):
        size = len(wires)
        if size+t>k+1 or t>k: return
        for unary in ([False, True] if t else [False]):
            rem = t-unary
            labels = [coverage(w, bool(rem)) for w in wires]
            union = once = twice = 0
            for cov in labels:
                twice ^= cov & (twice ^ once)
                once = (cov ^ union) & (cov | once)
                union |= cov
            if unary:
                for i, a in enumerate(wires):
                    g = negate(a)
                    if g in wires: continue
                    base = (union ^ (once & labels[i])) | coverage(g, bool(rem))
                    rest = wires[:i] + wires[i+1:] + (g,)
                    if base == full: yield rem, tuple(sorted(rest))
                    if size+1<=k-rem and base | labels[i] == full:
                        yield rem, tuple(sorted(wires+(g,)))
                continue
            for i, j in combinations(range(size), 2):
                a,b = wires[i],wires[j]
                ca,cb = labels[i],labels[j]
                other = union ^ ((once & (ca|cb)) | (twice & ca & cb))
                rest = wires[:i]+wires[i+1:j]+wires[j+1:]
                for is_or in (False, True):
                    g = gate(a,b,is_or)
                    if g < 0 or g in wires: continue
                    base = other | coverage(g,bool(rem))
                    after = rest+(g,)
                    if base == full: yield rem, tuple(sorted(after))
                    if size<=k-rem:
                        if base|ca == full: yield rem, tuple(sorted(after+(a,)))
                        if base|cb == full: yield rem, tuple(sorted(after+(b,)))
                    if size+1<=k-rem and base|ca|cb == full:
                        yield rem, tuple(sorted(wires+(g,)))
    for t in budgets:
        frontier = {(t, root)}
        statistics = Counter()
        peak = 0
        started = monotonic()
        for depth in range(14):
            next_frontier = set()
            peak = max(peak,len(frontier))
            for nt, w in frontier:
                if any(signals[g]==(full,0) for g in w):
                    raise RuntimeError(f"Target reached at depth {depth}, initial NOT count {t}")
                if depth == 13:
                    statistics["budget"] += 1
                    continue
                reason = obstruct(13-depth,nt,w)
                statistics[reason or "ordinary"] += 1
                if reason is None:
                    next_frontier.update(children(13-depth,nt,w))
            if not next_frontier: break
            frontier = next_frontier
        print(branch, "all" if seed else "no-seed", "t", t, dict(statistics),
              "peak",peak,"seconds", round(monotonic()-started,2), flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('branch',choices=['d043','d401','d405']+['t'+str(x) for x in (1,2,3,5,6,7,8)])
    p.add_argument('kind',choices=['all','no-seed'])
    p.add_argument('budgets',help="comma-separated exact NOT counts")
    args=p.parse_args()
    if args.kind=='no-seed' and args.branch[0]!='t': p.error("only the triple-OR seed is optional")
    search(args.branch,args.kind=='all',map(int,args.budgets.split(',')))
