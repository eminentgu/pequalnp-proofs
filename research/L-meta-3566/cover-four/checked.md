# Lean bounds for the labelled cover-four graphs

For each row of `critical.txt` except row 15, `listedLower` proves that every fan-in-two monotone circuit computing the graph's edge function uses at least the number of edges plus three gates. The function is true exactly when both endpoints of some edge are true. The upper-bound circuit in `listedOptimum` uses exactly that many gates. The theorem `listedExact` supplies one nonisolated vertex per graph satisfying the full deletion conclusion of L-meta-3566 for every legal circuit. These sixteen rows include all eight bipartite rows in the table.

| Row IDs | Input to the proof |
|---|---|
| 0, 1, 3, 5, 6, 7, 9 | L-meta-579. Lean checks the girth, degrees, minimum cover size and the good-leaf or run witnesses for every induced subgraph. |
| 2, 8, 11, 12, 14 | L-meta-615. The graphs consist of three internally disjoint paths between two vertices. Lean checks the path labellings and the cover sizes. |
| 4, 10, 13 | L-meta-8493, L-meta-550 and L-meta-1007, respectively. Explicit input relabellings transport their full-basis lower bounds. |
| 16 | L-meta-723. The graph is the once-subdivided complete graph on four vertices. |

The graph labels are part of the Lean statements. An application to arbitrary graphs of cover number four additionally requires a proof that the reductions reach one of the listed labels up to isomorphism. The search transcript for row 15 is recorded in `direct-pinned.log`.

## Reproduction

From a checkout of this branch with the repository Lean toolchain and mathlib cache installed, run:

```sh
research/L-meta-3566/cover-four/check_bounds.sh
```

The script uses Lake to build the upstream lemmas, compiles the research modules into a temporary directory and prints the axioms for all three conclusions. The expected axiom list is `propext`, `Classical.choice` and `Quot.sound`.

## The remaining nine-vertex graph

For row 15, `forcedPair15` shows how a circuit of at most 13 gates would lose two gates simultaneously. It assumes the 12-gate lower bound for each of the five zero cofactors. Under that assumption each subdivision input occurs in a single OR gate. At the earliest such gate, the other input can be true only when both endpoints of the unsubdivided edge are true. On any collection of assignments excluding that edge, the other input is constantly zero and the OR returns the subdivision bit. The theorem `lower15_of_rows` converts a 12-gate lower bound on those assignments, the cofactor bounds and a two-gate deletion lemma into the 14-gate lower bound for legal AO₂ circuits. The reproduction script also checks both steps.
