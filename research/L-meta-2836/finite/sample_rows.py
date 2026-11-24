from finite_probe import P,N,I,inputs,EDGES
from itertools import combinations
import json
B=['d043','d401','d405']+['t'+str(x) for x in [1,2,3,5,6,7,8]]
P1=[x for x in range(512) if x.bit_count()<=3 and any(x&e==e for e in P)]
def pairs(branch,ps,ns):
    raw=[k for k,v in inputs(0,branch)]
    vec=lambda x:sum(v<<i for i,(k,v) in enumerate(inputs(x,branch)))
    enc={x:vec(x) for x in ps+ns}
    priv=[(p,n,(enc[p]^enc[n]).bit_length()-1) for p in ps for n in ns if (enc[p]^enc[n]).bit_count()==1]
    return {k:next(((p,n) for p,n,i in priv if k==raw[i]),None) for k in raw}
if __name__=='__main__':
    print('pair sets',len(P),len(N),len(P1),len(I))
    for b in B:
        print(b, 'extrema', [k for k,v in pairs(b,P,N).items() if v], 'augmented',pairs(b,P1,I))
