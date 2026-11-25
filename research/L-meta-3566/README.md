# Vertex deletion and the global cover bound

`Equivalence.lean` proves that the posted L-meta-3566 statement is equivalent to the following global assertion. Every fan-in-two AND/OR circuit computing the edge function of a bipartite graph with no four-cycle and at least two edges has size at least its number of edges plus its minimum vertex cover size minus one.

The implication from vertex deletion to the size bound is a strong induction on the edge count. A cover for the graph after deleting the incident edges can be extended by the deleted vertex. When this increases the minimum cover size, the additional gate in the posted statement pays for that vertex.

For the reverse implication, take two distinct edges and choose an endpoint found on only one of them. The remaining graph has an edge. A minimum cover of that graph gives an explicit circuit by grouping its edges into stars. The construction strengthens the published circuit builder from L-meta-4320 to use exactly two earlier wires per gate.

Reproduce from the pinned `lean` directory with `lake env lean ../research/L-meta-3566/Equivalence.lean`. The axiom audit of `VertexPeel.exactPeel_iff_globalLower` reports `propext`, `Classical.choice` and `Quot.sound`. Proving the universal size bound remains open in this branch.
