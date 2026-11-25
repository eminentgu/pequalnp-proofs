# Cutting unsafe AND gates

For a wire of a circuit computing the edge function, call it safe on small inputs if its activation on any input with at most two selected vertices implies that the selected vertices contain an edge. Preserve all OR gates and replace each unsafe AND by an empty OR. The new circuit can only lose positive outputs. It still computes the full edge function if it retains every two-vertex input that is an edge. The retained AND gates satisfy the pair-clean counting theorem in upstream L-meta-7241, so correctness of the new circuit gives the original circuit the sharp budget |E| + τ(G) − 1.

[GuardCut.lean](GuardCut.lean) proves a sufficient condition for retaining all edges. On each actual edge, consider an active, safe AND gate. For each input wire, either that wire is safe, or a path of OR gates from an active input already makes it true. Induction in gate order preserves the values needed on every positive edge. Correctness on all input sets follows by monotonicity and the downward change in the circuit.

[SyntacticSharp.lean](SyntacticSharp.lean) proves this condition for every normalized binary syntactically multilinear circuit, even with shared gates and unbounded depth. On a true edge input, the two disjoint operand supports of a firing AND must each contain a different active endpoint. A true wire with no active OR-only path would need two active endpoints of its own. This also gives a necessary obstruction for arbitrary circuits: any counterexample to the size bound has an edge input on which a firing AND reads two supports sharing an active endpoint.

[BoundaryTransfer.lean](BoundaryTransfer.lean) proves ownership descent at the certified gate budget and the full uniform vertex-deletion conclusion whenever one least circuit passes the boundary condition. The latter uses a vertex selected before quantifying over circuits, including the extra gate when the minimum cover shrinks. Existence of a qualifying least circuit for every graph of the two cards remains open.

With the research dependencies Equivalence, Normalization, ZeroFold and Descent built as in the main research README, run from the repository root:

```sh
proof_dir="$(pwd)/research/L-meta-3566"
cd lean
lake build PEqualNP.Outside.L_meta_2573 PEqualNP.Outside.L_meta_7241 PEqualNP.Defs.SyntacticMultilinear
for module in GuardCut SyntacticSharp BoundaryTransfer
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$proof_dir" "$module" || exit 1
done
```
