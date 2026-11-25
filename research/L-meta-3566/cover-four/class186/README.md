# Classifying the 186 canonical four-cover graphs

For each index in `Canonical186.lean`, the Lean theorem `VertexPeel.CoverFourClass.classified` proves a disjunction about the decoded graph. The graph is a forest, it has a degree-one vertex whose deletion leaves every vertex cover of size at least four, or it is isomorphic to a graph in the 17-row residual table. Deletion removes incident edges and keeps the vertex set.

| Selected certificate | Number of graphs | Lean check |
|---|---:|---|
| Forest | 35 | For each edge a subtree cut separates its endpoints, and no other edge crosses the cut. Each edge is therefore a bridge. |
| Stable leaf with a matching | 125 | Four vertex-disjoint edges survive deletion. Any cover must choose four distinct endpoints. |
| Stable leaf verified by enumeration | 9 | The kernel checks all 256 subsets of the eight vertices. These are canonical indices 21 through 29. |
| Named residual graph | 17 | The identity map between the given vertex labels preserves and reflects adjacency. |

The generator proposes a witness for each code. Lean checks every witness against `Mask4.graph`. For a cyclic graph with cover number at most four in which every leaf deletion strictly decreases the cover number, `VertexPeel.CoverFourClass.criticalExit` selects the isomorphism branch.

Run `python3 research/L-meta-3566/cover-four/class186/verify.py --jobs 2` from the project root with the pinned Lean toolchain and mathlib cache available. The script generates the 24 proof modules and the final theorem under `lean/.lake/build/cover-four-classes`. The final axiom audit reports `propext`, `Classical.choice` and `Quot.sound`.
