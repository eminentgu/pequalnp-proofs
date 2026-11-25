# Masking and edge ownership in L-meta-1774

The file [Masking.lean](Masking.lean) proves necessary conditions for a circuit appearing in L-meta-1774. Here *ready* means every AND gate owns at least one graph edge, with ownership as defined in the project.

1. In any ready circuit, an AND cannot read an earlier AND directly. On an edge owned by the later gate, all its inputs are true and all earlier ANDs in its cone are false.
2. Suppose an AND of a minimum ready circuit computing the edge function owns two vertex-disjoint edges of a four-cycle-free graph. A later AND in its cone rejects a nonedge that the initial gate accepts. The later gate owns a third edge distinct from both original edges, and the initial gate is false on that third edge.

3. On a path to the mask, the last true gate is an OR strictly between the initial AND and the mask. This OR is true both on the leaking input and on the mask’s owned edge. A distinct second input to the mask is false on the leak and true on the owned edge. The theorem identifies both input wires.
4. If the graph has at most two edges, each pair of edges owned by the same AND in the original minimum ready circuit shares an endpoint.

5. In a triangle-free graph, choose the last bad gate in topological order. A later AND masks it, owns at least one edge, and all edges owned by that later AND have a common endpoint. The proof chooses the last gate from a finite set and supplies the star centre.

The proof uses checked upstream L-meta-4846 to obtain the leaking nonedge. It proves that each gate of a minimum circuit is either the output or read by a later gate. The deletion argument permits references to unavailable wires under the project's default-false semantics. Following later readers on the leaking assignment eventually gives an AND where the signal becomes false.

Completing L-meta-1774 still requires constructing a circuit of at most the initial size with fewer gates owning disjoint edges.

From the repository's `lean/` directory, run the following commands.

```sh
lake build PEqualNP.Outside.L_meta_4846
lake env lean ../research/L-meta-1774/Masking.lean
```
