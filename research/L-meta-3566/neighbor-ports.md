# Singleton inputs at AND gates

[NeighborPorts.lean](NeighborPorts.lean) considers an arbitrary exact binary AND/OR circuit for a bipartite graph with no four-cycle. For each vertex x, either one AND input accepts x alone and rejects every other singleton from its side, or at least degree(x) distinct physical AND gates have a true input on the singleton x. In the second case forcing x to one makes at least that many ANDs redundant.

For a neighbor t, compare the singleton x with the independent set formed by t and the vertices on x's side outside the neighborhood of t. Their union contains the edge xt. An AND in the output cone has one port true on x and false on the independent set. Every other singleton on the same side that lights this port must neighbor t. If there is such a singleton y, square-freeness gives x and y at most one common neighbor, so the same port cannot serve a second t. Choosing the port by a fixed rule on x makes the count a count of distinct gates.

[PortTransversal.lean](PortTransversal.lean) gives a stronger conclusion on arbitrary square-free graphs. If fewer than degree(x) AND gates are lit on the singleton x, choose for each such gate a different-from-x singleton that activates its designated port. At least two chosen vertices must be adjacent. Indeed, each alternative vertex blocks at most one neighbor of x. If the chosen vertices were independent, one could add an unblocked neighbor t and still have an independent set. It would light every designated port, contradicting the opposite AND inputs needed to distinguish that independent set from the singleton x on the positive edge xt. A port with no alternative makes the universal implication vacuous and singles out x globally.

After compiling the earlier AndSeparation module, run the following from the repository root.

```sh
proof_dir="$(pwd)/research/L-meta-3566"
cd lean
for module in NeighborPorts PortTransversal
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$proof_dir" "$module" || exit 1
done
```
