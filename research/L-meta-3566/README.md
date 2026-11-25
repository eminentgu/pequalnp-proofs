# Vertex deletion and the global cover bound

`Equivalence.lean` proves that the posted L-meta-3566 statement is equivalent to the following global assertion. Every fan-in-two AND/OR circuit computing the edge function of a bipartite graph with no four-cycle and at least two edges has size at least its number of edges plus its minimum vertex cover size minus one.

The implication from vertex deletion to the size bound is a strong induction on the edge count. A cover for the graph after deleting the incident edges can be extended by the deleted vertex. When this increases the minimum cover size, the additional gate in the posted statement pays for that vertex.

For the reverse implication, take two distinct edges and choose an endpoint found on only one of them. The remaining graph has an edge. A minimum cover of that graph gives an explicit circuit by grouping its edges into stars. The construction strengthens the published circuit builder from L-meta-4320 to use exactly two earlier wires per gate.

Reproduce from the pinned `lean` directory with `lake env lean ../research/L-meta-3566/Equivalence.lean`. The axiom audit of `VertexPeel.exactPeel_iff_globalLower` reports `propext`, `Classical.choice` and `Quot.sound`. Proving the universal size bound remains open in this branch.

## Square-free pseudoforests

[AllPseudoforests.lean](AllPseudoforests.lean) proves the sharp edge-plus-cover lower bound, ownership descent and uniform vertex deletion for every graph without a four-cycle whose induced subgraphs all have at most as many edges as vertices. Each component may be a tree or a single cycle with arbitrary trees attached. Odd cycles, including triangles, can occur in arbitrarily many components. The statements allow isolated circuit inputs.

Fix a vertex to one and all its neighbors to zero. Any AND gate with an operand activated by that singleton input can be removed from the residual circuit. A leaf pays for its only neighbor. In a nonempty leafless pseudoforest every active vertex has degree two. Pick consecutive edges a–b–c. If each singleton activated a port at only one AND gate, both positive edge tests would require the same gate, with a and c activating the same port opposite b. The absence of four-cycles gives a neighbor of a outside the neighborhood of c. Testing that edge against two rejected inputs proves that a and c cannot activate the same port at their unique gate. Thus one of the three vertices pays for both of its neighbors. Induction proves the AND lower bound, and L-meta-599 supplies the OR lower bound. The local two-edge argument is [path_two_lit](SubdivisionAND.lean).

The public conclusions are `all_pseudoforest_ands`, `all_pseudoforest_numerical`, `all_pseudoforest_ownership` and `all_pseudoforest_vertex`. The Lean source prints the axiom audit. [PseudoforestAND.lean](PseudoforestAND.lean) also gives an independent bipartite proof and the general restriction induction.

## Both desk conclusions for vertex cover number at most four

[CoverFour.lean](cover-four/CoverFour.lean) proves L-meta-1774 and L-meta-3566 for all graphs satisfying the respective desk hypotheses and having minimum vertex cover size at most four. There is no bound on the number of circuit inputs, circuit size or isolated vertices. For cover number exactly four, the numerical lower bound is the edge count plus three gates. The formal classification and reconstruction of arbitrary graphs are described in the [proof directory](cover-four/README.md).

## Both desk conclusions for vertex cover number at most three

[CoverThree.lean](CoverThree.lean) proves the full ownership descent of L-meta-1774 and both size inequalities of L-meta-3566 for any graph in the respective card with a vertex cover of size at most three. The number of vertices and the incoming circuit are unrestricted. The public theorems are `ownership_descent` and `bipartite_vertex_deletion`. The latter has one vertex that works for every correct circuit. `vertex_deletion` also covers triangle-free graphs without a four-cycle outside the bipartite case.

For a cyclic graph with such a cover, `cyclic_lower` proves that every monotone circuit of fan-in at most two has at least the number of edges plus two gates. A cycle forces every cover to have size at least three. Deleting the incident edge of a leaf preserves a cycle and allows at least one gate to be removed. Restore that edge to lift the lower bound by one. At the end of this induction a leafless cyclic graph with a three-vertex cover has at most six non-isolated vertices. Every active degree equals two, and its entire edge set forms a five-cycle or a six-cycle. Relabeling the circuit inputs into this cycle preserves its gate count, including any sharing. The numerical base bounds are seven and eight gates. In the acyclic case the upstream forest bound applies.

[CoverThreeCore.lean](CoverThreeCore.lean) proves the leafless classification. [CycleSize.lean](CycleSize.lean) and [IsolatedCore.lean](IsolatedCore.lean) supply the base bounds and relabeling. [StableExtension.lean](StableExtension.lean) proves the lower-bound transfer for one leaf and for arbitrary chains with a fixed minimum cover. [CycleCover.lean](CycleCover.lean) and [CycleLeaf.lean](CycleLeaf.lean) describe how deleting a leaf affects cyclicity and minimum covers. For general cover size `t`, [CoverKernel.lean](CoverKernel.lean) reduces the numerical bound to graphs without two leaves sharing a neighbor and at most `2t + t(t−1)/2` non-isolated vertices. This reduction does not in itself certify those finite cases.

After building `Leaves`, `Normalization`, `Descent` and `ShortCycle` in this directory, reproduce these results from `lean` with `research_dir` set to the absolute path of this directory.

```sh
lake build PEqualNP.Outside.L_meta_579 PEqualNP.Outside.L_meta_1527 PEqualNP.Research.L_meta_1774.Forest PEqualNP.MetaComplexity.Helpers.PermInputs
for module in CycleSize IsolatedCore CoverThreeCore StableExtension CycleCover CycleLeaf CoverKernel CoverThree
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
```

## Critical leaves and finite graph order

[CriticalSupport.lean](CriticalSupport.lean) proves that for minimum cover size `t ≥ 3`, deleting leaves whose removal preserves `t` gives a core on at most `t + choose(t,2)` non-isolated vertices. The result applies to every graph without a four-cycle. For two minimum covers, a vertex outside both has all its neighbors in their intersection. When all minimum covers differ in at most one place, any exterior critical leaf is the only exterior neighbor of its hub. Counting single neighbors and pairs gives the bound. At cover size four the bound is ten.

[FiniteCritical.lean](FiniteCritical.lean) transfers the circuit lower bound to a graph on that many inputs, preserving the edge count, minimum cover size and criticality. The theorem `of_small_order` quantifies over all correct circuits. [RowFold.lean](RowFold.lean) proves that a gate evaluating to zero on any prescribed family of rows and a gate reading its wire can both be removed while preserving the output on those rows.

After the dependencies in the preceding section have been compiled, replay the three modules with the same command loop in the order `CriticalSupport FiniteCritical RowFold`. Each public theorem audited in these files uses `propext`, `Classical.choice` and `Quot.sound`.

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

[FreeChoices.lean](FreeChoices.lean) strengthens the AND count at a shared OR. For each negative row test, an AND with equal operand values leaves its orientation free. With `a` AND ancestors and `f(u)` such free choices on row `u`, the sum of `2^f(u)` over the splitting rows is at most `2^a`. The row tests occupy disjoint sets of orientation patterns. This still counts a single ancestor cone.

## Cycles force three AND gates

[ShortCycle.lean](ShortCycle.lean) extracts an induced five-cycle, six-cycle or six-vertex path from any graph containing a cycle but no triangle or four-cycle. [FiveTests.lean](FiveTests.lean) supplies five independent sets on each induced graph. The union of any two contains an edge. The input assignments extend by zero to the original graph, so the separation theorem forces at least three AND gates in the output cone of every exact binary circuit for its edge function.

[TwoAndForest.lean](TwoAndForest.lean) applies this to both desk statements. If the graph admits even one exact circuit with at most two AND gates in its output cone, the graph is a forest. The vertex-deletion conclusion then holds for all circuits, and the ownership descent holds for every eligible minimum circuit. Larger circuits on that graph are included. The general cyclic case is open.

After the preceding builds, compile `FreeChoices`, `FiveTests` and `ShortCycle`, then build `PEqualNP.Research.L_meta_1774.Forest` and compile `TwoAndForest` after `Descent` and `Normalization`.

[WeakPatterns.lean](WeakPatterns.lean) also counts the physical AND gates in the original `Monotone2` model with fan-in at most two. Its proof evaluates each wire against the prefix available when it was read, including missing wire references. Compile it before `TwoAndForest`. The theorems `peel_of_two_ands` and `descent_of_two_ands` apply when any circuit in this more general model has at most two AND gates.

## Computations beyond cover size three

[Cover-four enumeration and replay](cover-four/README.md) gives the graph generator and the records of two live-wire searches for 17 residual graphs with minimum vertex cover size four. The searches agreed on all 17 cases. Independent Lean certificates now establish the full classification and size bounds. The numerical search transcripts document the earlier computational cross-check.

[Two-supergraph factorization](factor-notes.md) studies an attempted counterexample using an AND of two graph functions. It includes three checked structural obstructions and a reproducible search with explicitly shared physical gates.
