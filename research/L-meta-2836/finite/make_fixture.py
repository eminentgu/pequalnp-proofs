"""Print the explicit row lists and per-coordinate witnesses for FiniteSamples.lean."""
from sample_rows import B,P1,I,pairs
from finite_probe import P,N
def line(name,rows):
    return f"def {name} : List Row := ["+", ".join(map(str,rows))+"]"
if __name__=='__main__':
    print(line('edgeRows',P)); print(line('maximalIndependentRows',N))
    print(line('smallPositive',P1)); print(line('independentRows',I))
    print("private def witnessTable : Array (Array (Row × Row)) := #[")
    for n,b in enumerate(B):
        w=pairs(b,P1,I)
        print("  #["+", ".join(f"({p}, {q})" for p,q in [w.get(i) or (0,0) for i in range(11)])+"]"+("," if n+1<len(B) else "]"))
