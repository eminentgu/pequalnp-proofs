"""Search signed formulas on all graph extrema, check models on the full truth table."""
from functools import lru_cache
import json,sys,time
EDGES = [3,6,12,24,17,33,66,132,264,160,320,288]
I = [x for x in range(512) if not any(x & p == p for p in EDGES)]
N = [x for x in I if all(x==y or x & y != x for y in I)]
P = EDGES
F = lambda x: x not in I
def inputs(x,branch):
    if branch[0]=='d':
        c,a,b=map(int,branch[1:])
        return [(i, bool(x & (1<<i))) for i in range(9) if i!=c]+[(9,bits_or(x,c,a)),(10,bits_or(x,c,b))]
    j=int(branch[1])
    return [(i,bool(x&(1<<i))) for i in range(9)]+[(10,bits_or(x,0,4,j))]
def bits_or(x,*idx): return any(x&(1<<i) for i in idx)
def eval_f(q,src):
    if isinstance(q,int):return src[q]
    if q[0]=='!':return not eval_f(q[1],src)
    a,b=eval_f(q[1],src),eval_f(q[2],src)
    return (a or b) if q[0]=='|' else (a and b)
def terms(branch,mono=False,depth=4):
    rows=P+N; target=(1<<len(P))-1; allmask=(1<<len(rows))-1
    sig={key:sum(dict(inputs(x,branch))[key]<<i for i,x in enumerate(rows)) for key,v in inputs(0,branch)}
    seen={v:k for k,v in sig.items()};cost={v:0 for v in seen}
    layers=[list(seen)]
    for d in range(1,depth+1):
        new={}
        if not mono:
            for v in layers[d-1]:
                b=allmask^v
                if b not in seen:new[b]=('!',seen[v])
        for a in range((d-1)//2+1):
            b=d-1-a
            for x in layers[a]:
                for y in layers[b]:
                    for op,v in (('&',x&y),('|',x|y)):
                        if v not in seen and v not in new:new[v]=(op,seen[x],seen[y])
        seen.update(new);cost.update({v:d for v in new});layers.append(list(new))
    def optimize(mask,positive):
        pure={}
        for sig,item in seen.items():
            v=sig if positive else allmask^sig
            if v and v&~mask==0 and cost[sig]+1<pure.get(v,(1<<20,))[0]:
                pure[v]=cost[sig]+1,item
        @lru_cache(None)
        def go(left):
            if not left:return 0,None
            best=(1<<20,None);bit=left&-left
            for cover,(base,item) in pure.items():
                if not bit & cover:continue
                price,end=go(left&~cover);total=base+price
                if total<best[0]:best=(total,item if end is None else ('|' if positive else '&',item,end))
            return best
        price,q=go(mask)
        return price-1,q
    k,q=min((optimize(target,True),optimize(allmask^target,False)),key=lambda p:p[0])
    bad=[x for x in range(512) if eval_f(q,dict(inputs(x,branch)))!=F(x)] if q else []
    assert q and not any(x in rows for x in bad)
    return dict(branch=branch,mono=mono,sizes=list(map(len,layers)),found=k,formula=q,bad512=len(bad),first_bad=bad[:6])
if __name__=='__main__':
    print('minpos',P,'maxneg',N,'negatives',len(I),flush=True)
    for branch in sys.argv[1:] or ['d043','d401','d405']+['t'+str(x) for x in [1,2,3,5,6,7,8]]:
        for mono in (False,True):
            t=time.monotonic();ans=terms(branch,mono)
            ans['seconds']=round(time.monotonic()-t,3)
            print(json.dumps(ans),flush=True)
