# Removing an output AND after forcing a set of inputs to zero

Suppose a binary AND computes the edge function of a graph without a four-cycle. Its two operands may be arbitrary monotone circuits with shared gates. Let their respective AND depths be d and e, and set p = 2^d and q = 2^e. The indegree of each gate is exactly two. There is no bound on OR depth.

[WrongSupports.lean](WrongSupports.lean) proves that setting at most pq inputs to zero makes the left operand compute the restricted graph function on every assignment, or setting at most binom((q+1)p, 2) inputs to zero gives that conclusion for the right operand. Its semantic version allows arbitrary monotone predicates with positive witness widths p and q.

An error for a child is an independent set on which the child accepts. An error X for the left and an error Y for the right must have an edge between them, because their union satisfies the AND. Choose a maximum disjoint family of left errors of size at most p. If the family has at most q members, its union hits all such errors. Otherwise take q+1 disjoint errors, with union U. A right error of size at most q must contain a vertex adjacent to two distinct vertices of U. Each pair in U has at most one common neighbor. All their common neighbors therefore hit the small right errors with the stated bound. Every positive input contains a positive witness within the respective size limit, giving exactness after the chosen set is zeroed.

[WrongSupportCircuit.lean](WrongSupportCircuit.lean) verifies the witness-width bound and constructs a new circuit for the restricted graph function. If the original output AND has zero-based gate index j and r earlier gates directly read a forced input, the new circuit has at most j − r gates. The theorem leaves open the comparison between the gates saved and the edge and cover counts lost when deleting the chosen vertices.

Run from the repository root. The last command prints the axiom audits.

```sh
proof_dir="$(pwd)/research/L-meta-3566"
cd lean
lake build PEqualNP.Outside.L_meta_615 PEqualNP.Defs
for module in ZeroFold WrongSupports WrongSupportCircuit
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$proof_dir" "$module" || exit 1
done
```
