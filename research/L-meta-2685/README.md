# Star forests and the cost of an incidence circuit

For a bipartite graph with edge set E, the incidence function accepts an input when the two endpoints of some edge are both true. A gate in the circuit may feed several later gates.

`active_budget` proves that the number of vertices incident to an edge is at most the circuit size plus one. Every such vertex is essential. Turning off that vertex in the two-endpoint assignment for one of its edges changes the output. The proof uses the support bound from the merged project lemma L-meta-1660.

`star_forest_charge` proves that every matching M in a bipartite star forest satisfies |E| + |M| ≤ size(C) + 1. Each edge contributes a distinct leaf. Each matched edge contributes one more endpoint. Distinct matched edges have different endpoints, and the proof handles components consisting of one edge, isolated vertices and the empty graph.

`last_star` settles the terminal case of a recursive proof for L-meta-2685. If every edge of a nonempty graph shares a point or every edge shares a line, then size(C) ≥ |E|. Take any edge for M.

The open question in the recursion concerns a nonempty graph with no 4-cycle that does not have a common endpoint for all its edges. Can one remove a nonempty star, leave a nonempty edge set F, and construct a circuit D for F with size(D) + |E ∖ F| + 1 ≤ size(C)?

Check this file from the `lean` directory of the upstream checkout.

```sh
lake build PEqualNP.Outside.L_meta_1660
lake env lean ../research/L-meta-2685/StarForestCharge.lean
```
