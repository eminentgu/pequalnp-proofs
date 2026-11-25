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

## A leaf adjacent to a degree-two vertex

[PendantPathPeel.lean](PendantPathPeel.lean) proves the complete vertex-deletion conclusion for any finite simple graph with a leaf `a` adjoining a vertex `b` of degree two. Any edge surviving deletion of `b` makes `b` a valid choice for every circuit, including when deletion lowers the minimum vertex cover size. If every edge touches `b`, deleting `a` preserves the cover size.

[ThreeGatePeel.lean](ThreeGatePeel.lean) proves the three-gate saving at `b` even when its degree exceeds two, provided another neighbor and a surviving edge exist. Fixing `b` to zero makes the output independent of `a`. The proof chooses `a`'s value to force a gate reading it to a constant. [PendantCross.lean](PendantCross.lean) finds a second reader even if the first gate reads both endpoints. A change of input that alters the original output must cross a cut containing the fixed inputs and constant gates. This gives a third gate omitted by the circuit construction. [MixedFold.lean](MixedFold.lean) constructs a two-input AND/OR circuit for the nonconstant cofactor, omitting gates whose restricted function is constant or equals an earlier wire.

After compiling the dependencies in the preceding section, run the following from the same `lean` directory.

```sh
for module in MixedFold PendantCross ThreeGatePeel PendantPathPeel
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
```

The axiom audit for `peel_pendant_path`, `cut_joint` and `MixedFold.compile` reports only `propext`, `Classical.choice` and `Quot.sound`.

## Counting readers at a higher-degree neighbor

[CountReaders.lean](CountReaders.lean) counts the distinct gates that use a raw input. Suppose a leaf `a` has a single such gate, an OR. Its neighbor `b` feeds `q` distinct gates. If an edge survives deletion of `b`, the mixed cofactor `a=1, b=0` saves at least `q+2` gates. All `q` readers fold, and the unique OR reading `a` becomes constant. A change in `a` that distinguishes two original outputs must reach another gate outside these. The proof follows this change across the cut formed by `a`, its OR, and the readers of `b` that became constant.

[PendantObstruction.lean](PendantObstruction.lean) uses a minimum circuit to obtain a graph-level conclusion. Suppose `b` has another neighbor and deleting `b` leaves an edge. If neither `a` nor `b` satisfies both vertex-deletion inequalities for every implementation of the original graph, **every** minimum circuit reads `a` at a single OR gate, that gate does not read `b`, and at most `degree(b) − 2` gates read `b`. A degree-three neighbor must therefore have exactly one reader in every such circuit.

[CubicJoint.lean](CubicJoint.lean) determines how the two unique readers can connect when the neighbor has degree three. If its reader is an AND, its other operand must be the leaf's OR gate. An indirect connection would yield three constant gates after fixing the leaf to one and its neighbor to zero, and a change in the leaf detects a fourth gate to omit. If the neighbor's reader is `b OR u`, the wire `u` implies an edge of the graph surviving deletion of `b` on every input. These conditions restrict the minimum circuits that can obstruct deletion at the two endpoints.

[pendant_share.py](pendant_share.py) checks what can happen in a fixed, nonminimum implementation. Start with an eight-cycle and add a vertex adjacent to vertices 0 and 4 and to one new leaf. The resulting bipartite graph has no four-cycle, has a cover of size five, and either vertex of the pendant edge lowers the minimum cover size to four. A 22-gate implementation reuses the signal `0 OR 4` in a conjunctive normal form for the disjunction of two disjoint cycle edges. Exhaustive truth tables give 21 live gates after setting the leaf to zero. Setting the degree-three neighbor to zero and the leaf to either value leaves 19 live gates. Merging identical signals and pruning dead gates therefore saves one and three respectively in this implementation. The optimal-budget statement for the vertex pair remains a separate question.

After building the modules in the preceding section:

```sh
for module in CountReaders PendantObstruction CubicJoint
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
python3 "$research_dir/pendant_share.py"
```

The audits for `CountReaders.cut_joint_readers`, `PendantObstruction.peel_or_few_readers`, `CubicJoint.cubic_reader_shape` and `CubicJoint.single_or_core` report `propext`, `Classical.choice` and `Quot.sound`.

## Relation to L-meta-1774

[Descent.lean](Descent.lean) proves that the precise descent in L-meta-1774 is equivalent to the ability to replace any minimum circuit meeting the ownership hypothesis by an equal-size minimum with zero disjoint-edge-owning gates. The equivalence uses minimization over the number of such gates. The cover construction proves descent at every size budget reaching the canonical cover circuit.

[CrossCard.lean](CrossCard.lean) proves that L-meta-3566 implies L-meta-1774 on every bipartite graph satisfying the latter card's hypotheses. A positive defect supplies two distinct edges. The upstream [L-meta-1527](../../lean/PEqualNP/Outside/L_meta_1527.lean) converts the original at-most-two-input circuit to the exact two-input model at the same or smaller size. The lower bound equivalent to L-meta-3566 then pays for a replacement for the original circuit. The unrestricted L-meta-1774 also allows graphs with odd cycles.

To check these modules from the same `lean` directory:

```sh
lake build PEqualNP.Outside.L_meta_1527 PEqualNP.Research.L_meta_1774.CoveredOwnership
for module in Descent CrossCard
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
```

## Counting OR gates with a fixed row

For a vertex `u` opposite an independent set `R`, turn on `u` and all its non-neighbors in `R`. This input contains no edge. Each pair `{u,v}` for a neighbor `v` gives a positive test. A splitting OR is false on the negative input and each operand accepts a positive test missed by the other. [RowCharge.lean](RowCharge.lean) counts distinct physical gates even with fanout. Its induction bounds the union of positive tests distinguished by an arbitrary set of wires. [RowGraph.lean](RowGraph.lean) gives at least `degree(u) − 1` such OR gates. On a graph without four-cycles, a gate accepting at least two right singleton inputs can split at most one row.

[RowOverlap.lean](RowOverlap.lean) sums over any set of rows. If the sum of degrees exceeds the number of rows plus the total number of OR gates, there is a physical OR gate that splits multiple rows and accepts at most one right singleton. [ReusedRows.lean](ReusedRows.lean) and [ReusedCone.lean](ReusedCone.lean) charge those rows and the union of their hit columns to the distinct ancestor gates of that individual gate, including the gate itself. This bound applies to a single cone. Cones of different gates can overlap.

[ReusedExample.lean](ReusedExample.lean) certifies an eleven-gate globally minimum monotone binary circuit on two disjoint five-vertex paths. Its final OR splits two different rows. Thus even restricting to minimum circuits leaves a real overlap to account for.

After compiling `ZeroFold`, use the same `research_dir` and `lean` directory as above.

```sh
lake build PEqualNP.MetaComplexity.L104
for module in RowCharge RowGraph RowOverlap ReusedCone ReusedRows ReusedExample
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
```

## Separating negative tests with physical AND gates

[AndSeparation.lean](AndSeparation.lean) proves that a wire false on two inputs but true on a probe contained in their union must have an AND ancestor whose operands take opposite values on the two inputs. The proof follows a single path backward in the physical circuit. Recording the first operand at each AND therefore distinguishes all negative inputs whose pairwise unions contain positive probes. If one OR gate splits `k` rows in a graph without four-cycles, the AND gates in its own ancestor cone yield at least `k` distinct bit patterns. Distinct gates may still share ancestors.

[CoverPatterns.lean](CoverPatterns.lean) applies this principle to the whole circuit. A correct circuit has at least as many bit patterns on the AND gates in its output cone as the graph has maximal independent sets. An induced matching of `k` edges requires at least `k` physical AND gates in the output cone, irrespective of vertices elsewhere in the graph.

Compile `AndSeparation` and then `CoverPatterns` with the command in the preceding section after building `ReusedRows`.
