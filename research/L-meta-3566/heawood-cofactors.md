# Semantic gate merging on the Heawood graph

The degree-two proof uses a zero cofactor and omits a gate when its restricted Boolean function is identically false or equals an earlier restricted wire. Two such gates suffice when deletion preserves cover number. The same counting argument, by itself, cannot establish the charge on every cubic graph.

Consider the Fano incidence graph, with seven point vertices and seven line vertices. Line i is incident to points i, i+1 and i+3 modulo seven. Every pair of points lies on one line. The graph is C4-free and cubic. A perfect matching gives cover number seven. Deleting any vertex leaves six disjoint matching edges, and the six surviving vertices on its side cover the residual graph. Thus every vertex requires a charge of four in L-meta-3566.

Use the points as star centers. For each point OR its three adjacent line coordinates with two gates, then AND the result with the point coordinate. OR the seven stars with six further gates, for a total of 27. Every gate in this original circuit is live and computes a distinct nonzero function.

| Vertex set to zero | Number tested | Semantically distinct nonzero gate functions new at their wire | Gates in the output cone after merging | Saving after both operations |
| --- | ---: | ---: | ---: | ---: |
| Point | 7 | 25 | 23 | 4 |
| Line | 7 | 24 | 24 | 3 |

Setting a point to zero eliminates its star AND and one output OR by semantic merging. The two OR gates that formed its neighborhood still compute distinct, nonzero functions. Both can then be removed because the output no longer depends on their wires. Setting a line to zero eliminates one OR reader in each of its three incident stars. All remaining gates are live.

The accompanying Python program evaluates every intermediate wire on the complete truth table of 16,384 assignments, both before restriction and for all 14 restrictions. It compares the output to the 21-edge disjunction and checks the reported gate counts. From this directory run `python3 heawood_cofactors.py`.

This circuit rules out a proof that seeks four semantically nonmerging gates in the zero cofactor of some vertex of every circuit. The point restrictions satisfy the requested saving once dead gates are removed. Establishing the charge for an arbitrary minimum circuit still requires proof that some vertex permits enough such pruning, or a construction of a sufficiently small replacement circuit.
