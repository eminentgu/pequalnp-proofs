# Masking and edge ownership in L-meta-1774

The file [Masking.lean](Masking.lean) proves two necessary conditions for a circuit appearing in L-meta-1774. Here *ready* means every AND gate owns at least one graph edge, with ownership as defined in the project.

1. In any ready circuit, an AND cannot read an earlier AND directly. On an edge owned by the later gate, all its inputs are true and all earlier ANDs in its cone are false.
2. Suppose an AND of a minimum ready circuit computing the edge function owns two vertex-disjoint edges of a four-cycle-free graph. A later AND in its cone rejects a nonedge that the initial gate accepts. The later gate owns a third edge distinct from both original edges, and the initial gate is false on that third edge.

The proof uses checked upstream L-meta-4846 to obtain the leaking nonedge. It proves that each gate of a minimum circuit is either the output or read by a later gate. The deletion argument permits references to unavailable wires under the project's default-false semantics. Following later readers on the leaking assignment eventually gives an AND where the signal becomes false.

Completing L-meta-1774 still requires constructing a circuit of at most the initial size with fewer gates owning disjoint edges.

From the repository's `lean/` directory, run the following commands.

```sh
lake build PEqualNP.Outside.L_meta_4846
lake env lean ../research/L-meta-1774/Masking.lean
```
