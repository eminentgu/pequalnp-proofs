# Seven physical AND gates for the Heawood edge function

For the Heawood graph, the minimum number of physical AND gates in a binary monotone circuit is seven, when OR gates and fanout are unrestricted. The lower bound uses a finite abstraction of circuit evaluations and an independently checked LRAT refutation. The encoding from the graph to the CNF is written in Python. The general combinatorial implications used to justify it have Lean proofs. The resulting lower bound counts AND gates alone. The seven-star circuit gives a total-size upper bound of 27 gates.

## Graph and circuit tests

Number the seven points 0 through 6 and the lines 7 through 13. Line 7+j meets points j, j+1 and j+3 modulo seven. The graph has 21 edges and 37 maximal independent sets. Each vertex occurs in 12 of those sets. To enumerate them, choose the selected points, include all lines missing those points, and retain the selection when every omitted point touches an included line. The generator checks these counts, the existence of a private neighbor of x against every other vertex y, and the seven-star upper bound on all 16,384 inputs. [Generator](heawood_and_ports.py)

Assume there are at most six AND gates. Record both operand bits for each AND on each of the 14 singleton inputs and the 37 maximal independent inputs. Pad the records with zero-valued columns to reach six gate labels. The following constraints are necessary.

1. When a test contains a vertex, a true operand on that singleton stays true on the test by monotonicity.
2. Two distinct maximal independent sets have an edge in their union. The two endpoints of a graph edge also give two singleton tests whose union is positive. In both cases the output is false on the individual tests and true on a subset of their union. Some AND must have operand values (1,0) and (0,1) on the two tests, in one order. [Lean opposing-ancestor lemma](AndSeparation.lean)
3. A vertex x has a neighbor missing from each other vertex y. A private neighbor forces some AND to have exactly one true port on x, with that same port false on y. [Lean private-port lemma](PivotDistinct.lean)
4. All 12 maximal independent extensions of a singleton must have distinct bit patterns on ANDs with both ports false on the singleton. If a port is already true there, monotonicity rules out opposite orientations on two extensions. Thus at least four ANDs must still have both ports false, giving at most two ANDs with a true port on this singleton. [Lean extension bound](ExtensionPatterns.lean)

The generator represents these four properties with Boolean variables and clauses. Port names can be swapped within a gate. It orients each gate so its first singleton with unequal ports has its left port true. The six labels can then be sorted in descending lexicographic order by their singleton records. These choices preserve all four properties. No circuit is required to realize the records admitted by the abstraction.

## Reproduce the finite lower bound

Using CaDiCaL 2.1.2, the Python generator produced 11,876 variables and 37,181 clauses. CaDiCaL returned UNSAT. An independent run of lrat-trim verified the result, and verified the trimmed certificate again against the regenerated CNF. The trimmed proof has 962,616 additional clauses. The CNF SHA-256 on this run was `b9c56757ffcef9bbc2dd64822f5f2b1ce7d7ab0e901b4e788da4b3cf5e504570`. The trimmed binary LRAT SHA-256 was `c87cdfea125b1a6894bfa07acec8712e06afd1dfde4945d43321c67a1fd6767e`. The certificate is regenerated locally by the commands below. [LRAT checker version used](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12)

From this directory, with `cadical` and `lrat-trim` on the path, run

```sh
set -e
python3 heawood_and_ports.py > /tmp/heawood-ports.cnf
cadical --lrat /tmp/heawood-ports.cnf /tmp/heawood-ports.lrat || test "$?" -eq 20
lrat-trim /tmp/heawood-ports.cnf /tmp/heawood-ports.lrat /tmp/heawood-ports-trim.lrat
lrat-trim /tmp/heawood-ports.cnf /tmp/heawood-ports-trim.lrat
```

The final checker reports `s VERIFIED`. The upper bound groups the edges by point. For each point, OR its three line variables and AND the resulting value with the point variable. OR the seven results. This uses seven AND gates and twenty OR gates.
