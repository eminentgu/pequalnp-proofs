# Lean bounds for the labelled cover-four graphs

For each of the seventeen rows of `critical.txt`, `listedLower` proves that every fan-in-two monotone circuit computing the graph's edge function uses at least the number of edges plus three gates. The function is true exactly when both endpoints of some edge are true. The upper-bound circuit in `listedOptimum` uses exactly that many gates. The theorem `listedExact` supplies one nonisolated vertex per graph satisfying the full deletion conclusion of L-meta-3566 for every legal circuit. The theorem `listedOwnership` gives the ownership-descent conclusion of L-meta-1774 for every row.

| Row IDs | Input to the proof |
|---|---|
| 0, 1, 3, 5, 6, 7, 9 | L-meta-579. Lean checks the girth, degrees, minimum cover size and the good-leaf or run witnesses for every induced subgraph. |
| 2, 8, 11, 12, 14 | L-meta-615. The graphs consist of three internally disjoint paths between two vertices. Lean checks the path labellings and the cover sizes. |
| 4, 10, 13 | L-meta-8493, L-meta-550 and L-meta-1007, respectively. Explicit input relabellings transport their full-basis lower bounds. |
| 15 | Five zero cofactors, a kernel-checked circuit lower bound on sixteen assignments, and a two-gate restriction at an exclusive OR reader. |
| 16 | L-meta-723. The graph is the once-subdivided complete graph on four vertices. |

The graph labels are part of the Lean statements. An application to arbitrary graphs of cover number four additionally requires a proof that the reductions reach one of the listed labels up to isomorphism.

## Reproduction

From a checkout of this branch with the repository Lean toolchain and mathlib cache installed, run:

```sh
research/L-meta-3566/cover-four/check_bounds.sh
```

The script uses Lake to build the upstream lemmas, compiles the research modules into a temporary directory and prints the axioms for the four table-wide conclusions and the row-15 lower bound. The expected axiom list is `propext`, `Classical.choice` and `Quot.sound`.

## Row 15

For row 15, `forcedPair15` shows how a circuit of at most 13 gates would lose two gates simultaneously. It assumes the 12-gate lower bound for each of the five zero cofactors. Under that assumption each subdivision input occurs in a single OR gate. At the earliest such gate, the other input can be true only when both endpoints of the unsubdivided edge are true. On any collection of assignments excluding that edge, the other input is constantly zero and the OR returns the subdivision bit. The theorem `lower15_of_rows` converts a 12-gate lower bound on those assignments, the cofactor bounds and a two-gate deletion lemma into the 14-gate lower bound for legal AO₂ circuits. The module `ResidualFifteen.lean` discharges all three hypotheses and uses L-meta-4342 to extend the result to every monotone circuit. The reproduction script generates the sample certificate and checks it with Lean.

## Relabelling the finite graphs

`RawTaggedIso.lean` checks an explicit permutation from each of the 4,704 labelled cover presentations in `raw4704` to a member of `tagged292`. `TaggedIso.lean` checks a second permutation to one of the 186 unlabelled representatives. Both checks preserve the order of the graph, verify that the forward and inverse maps undo one another, and check every pair of vertices for adjacency. The second permutation can change which vertices form the distinguished cover.

`ResidualTransport.lean` transports the cover number, critical-leaf condition, triangle and four-cycle exclusions, and numerical circuit bound across these isomorphisms. `ListedNumerical.lean` supplies the bound in the form used by the leaf-removal induction.
