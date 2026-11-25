"""Enumerate reachable live signal sets on the extremal positive and negative rows."""
from functools import cache
from itertools import combinations
from pathlib import Path
import json

edges = [(0,1),(1,2),(1,3),(2,4),(2,8),(3,5),(5,8),(6,8),(7,8)]
n = 9
positive = [(1 << a) | (1 << b) for a, b in edges]
def independent(v):
    return all(v & e != e for e in positive)
negative = [v for v in range(1 << n) if independent(v)
            and not any(independent(v | (1 << t)) for t in range(n) if not v & (1 << t))]
examples = positive + negative
target = (1 << len(positive)) - 1
ones = (1 << len(examples)) - 1
negmask = (1 << len(negative)) - 1
required = (1 << (len(positive)*len(negative))) - 1
inputs = [sum(1 << r for r, sample in enumerate(examples) if sample & (1 << t)) for t in range(n)]

@cache
def separates(w):
    neg = (~(w >> len(positive))) & negmask
    return sum(neg << (i*len(negative)) for i in range(len(positive)) if w & (1 << i))

def closure(states, remaining):
    result = set()
    limit = remaining + 1
    for state in states:
        if target in state:
            raise ValueError("A successful state was reached.")
        for i,j in combinations(range(len(state)), 2):
            a,b = state[i],state[j]
            others = state[:i] + state[i+1:j] + state[j+1:]
            osep = 0
            for w in others:
                osep |= separates(w)
            for c in (a & b, a | b):
                if c == 0 or c == ones or c in state:
                    continue
                sc = osep | separates(c)
                for keep in range(4):
                    ka = bool(keep & 1)
                    kb = bool(keep & 2)
                    if len(others) + 1 + ka + kb > limit:
                        continue
                    enough = sc | (separates(a) if ka else 0) | (separates(b) if kb else 0)
                    if enough != required:
                        continue
                    result.add(tuple(sorted(others + (c,) + ((a,) if ka else ()) + ((b,) if kb else ()))))
    return result

def generate(budget):
    states = {tuple(sorted(inputs))}
    layers = {str(budget): sorted(states)}
    for k in reversed(range(budget)):
        states = closure(states, k)
        if any(target in s for s in states):
            raise ValueError(f'Target reachable with {k} gates left')
        layers[str(k)] = sorted(states)
        print(k,len(states),flush=True)
    return layers

if __name__ == '__main__':
    layers = generate(11)
    result = dict(n_inputs=n,n_rows=len(examples),n_positive=len(positive),target=target,
        edges=edges,positives=positive,negatives=negative,rows=examples,inputs=inputs,
        budget=11,layer_key='remaining gates',layers=layers)
    dest=Path(__file__).resolve().with_name('states94.json')
    dest.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('unique states',sum(map(len,layers.values())),'bytes',dest.stat().st_size,flush=True)
