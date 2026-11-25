"""Index feasible successors of the published reachable-state table for checked replay."""
from itertools import combinations
from pathlib import Path
import json
from certify94 import ones, required, separates, target

def actions(state,child_budget):
    for i,j in combinations(range(len(state)),2):
        a,b = state[i],state[j]
        other = state[:i]+state[i+1:j]+state[j+1:]
        sep = 0
        for w in other:
            sep |= separates(w)
        for operation,computed in enumerate((a&b,a|b)):
            if computed in (0,ones) or computed in state:
                continue
            sep_out=sep | separates(computed)
            for keep in range(4):
                tail = (computed,) + ((a,) if keep & 1 else ()) + ((b,) if keep & 2 else ())
                if len(other) + len(tail) > child_budget + 1:
                    continue
                accepted = sep_out | (separates(a) if keep & 1 else 0) | (separates(b) if keep & 2 else 0)
                if accepted == required:
                    yield i,j,operation,keep,tuple(sorted(other+tail))

root=Path(__file__).resolve().parent
table=json.loads((root/'states94.json').read_text())
layers=table['layers']
indexed={}
total=0
for left in range(1,table['budget']+1):
    children={tuple(state):i for i,state in enumerate(layers[str(left-1)])}
    reached=set()
    counts=0
    out=[]
    for state in layers[str(left)]:
        row=[]
        assert target not in state
        for i,j,operation,keep,child in actions(tuple(state),left-1):
            index=children[child]
            counts+=1
            reached.add(child)
            row.append([i,j,operation,keep,index])
        out.append(row)
    assert reached==set(children)
    total+=counts
    indexed[str(left)]=out
    print(left,len(out),counts,flush=True)

proof={'actions':'indices i < j into sorted state, operation 0 AND 1 OR, two-bit keep mask, 0-based child index in sorted layer left-1','layers':indexed}
(root/'actions94.json').write_text(json.dumps(proof,separators=(',',':'))+'\n')
print('feasible actions',total,flush=True)
