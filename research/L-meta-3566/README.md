# Vertex deletion and the global cover bound

`Equivalence.lean` proves that the posted L-meta-3566 statement is equivalent to the following global assertion. Every fan-in-two AND/OR circuit computing the edge function of a bipartite graph with no four-cycle and at least two edges has size at least its number of edges plus its minimum vertex cover size minus one.

The implication from vertex deletion to the size bound is a strong induction on the edge count. A cover for the graph after deleting the incident edges can be extended by the deleted vertex. When this increases the minimum cover size, the additional gate in the posted statement pays for that vertex.

For the reverse implication, take two distinct edges and choose an endpoint found on only one of them. The remaining graph has an edge. A minimum cover of that graph gives an explicit circuit by grouping its edges into stars. The construction strengthens the published circuit builder from L-meta-4320 to use exactly two earlier wires per gate.

Reproduce from the pinned `lean` directory with `lake env lean ../research/L-meta-3566/Equivalence.lean`. The axiom audit of `VertexPeel.exactPeel_iff_globalLower` reports `propext`, `Classical.choice` and `Quot.sound`. Proving the universal size bound remains open in this branch.

## Pair-sound circuits and peelable graphs

[Normalization.lean](Normalization.lean) combines the cover circuit with the upstream proof of [L-meta-7241](https://github.com/open-goat/pequalnp-proofs/blob/b85b175cfdd07efa25e93e670367d51906eb2b22/lean/PEqualNP/Outside/L_meta_7241.lean). On a graph without four-cycles and for any gate budget, a cover meeting the numerical bound exists exactly when that budget can compute the edge function with a circuit whose AND gates stay off on every nonedge pair. For the whole graph class of L-meta-3566, the stated peel is therefore equivalent to the existence of such a replacement of at most the original circuit size. The existence of a replacement for every circuit is open.

The same file proves the entire vertex-deletion conclusion for every graph satisfying the upstream peelability criterion. In fact, every vertex whose deletion leaves at least one edge satisfies both requested size bounds. This applies to forests and cyclic examples including the six-cycle. The proof uses the upstream peelable-graph lower bound and does not require an extra assumption about the circuit.

These modular results were independently compiled with the project toolchain at upstream commit `b85b175cfdd07efa25e93e670367d51906eb2b22`. To reproduce starting in the repository root, use the following commands.

```sh
research_dir="$(pwd)/research/L-meta-3566"
cd lean
lake build PEqualNP.Outside.L_meta_7241 PEqualNP.Library.Helpers.PeelableSanity
lake env lean -R "$research_dir" -o "$research_dir/Equivalence.olean" "$research_dir/Equivalence.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean "$1/Normalization.lean"' sh "$research_dir"
```

## Subdivisions and leaves

[SubdivisionPeel.lean](SubdivisionPeel.lean) proves the exact two savings bounds for a bipartition with degree two on one side and minimum degree three on the opposite side. [ConnectedSubdivision.lean](ConnectedSubdivision.lean) also permits degree two on the opposite side when the graph is connected and that side contains a vertex of degree at least three. These results apply to the incidence graphs obtained by subdividing every edge of the corresponding simple graph once.

[Leaves.lean](Leaves.lean) proves that a leaf whose deletion preserves the minimum vertex cover size satisfies the exact conclusion, independently of the rest of the graph. Two leaves with the same neighbor ensure this condition. [Pendant.lean](Pendant.lean) gives the exact conclusion when the graph has an isolated edge and at least one further edge. Its circuit argument proves that setting the endpoints of an edge to zero saves two gates whenever a disjoint edge survives.

[ZeroFold.lean](ZeroFold.lean) constructs an actual replacement circuit with two-input AND/OR gates after a restriction. [SideReaders.lean](SideReaders.lean) and [SidePeel.lean](SidePeel.lean) prove the two-gate bound for the degree-two side and produce one vertex that works for every original circuit. [The Heawood calculation](heawood-cofactors.md) gives the exact gate counts that prevent the same merging argument alone from establishing the bound on cubic incidence graphs.

To check these files after building `Equivalence.olean` above, work from the same `lean` directory and run:

```sh
for module in ZeroFold SideReaders SidePeel Leaves Pendant SubdivisionPeel ConnectedSubdivision
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
python3 "$research_dir/heawood_cofactors.py"
```
