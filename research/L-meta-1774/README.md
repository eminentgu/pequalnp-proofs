# Masking and edge ownership in L-meta-1774

The file [Masking.lean](Masking.lean) proves necessary conditions for a circuit appearing in L-meta-1774. Here *ready* means every AND gate owns at least one graph edge, with ownership as defined in the project.

1. In any ready circuit, an AND cannot read an earlier AND directly. On an edge owned by the later gate, all its inputs are true and all earlier ANDs in its cone are false.
2. Suppose an AND of a minimum ready circuit computing the edge function owns two vertex-disjoint edges of a four-cycle-free graph. A later AND in its cone rejects a nonedge that the initial gate accepts. The later gate owns a third edge distinct from both original edges, and the initial gate is false on that third edge.

3. On a path to the mask, the last true gate is an OR strictly between the initial AND and the mask. This OR is true both on the leaking input and on the mask’s owned edge. A distinct second input to the mask is false on the leak and true on the owned edge. The theorem identifies both input wires.
4. If the graph has at most two edges, each pair of edges owned by the same AND in the original minimum ready circuit shares an endpoint.

5. In a triangle-free graph, choose the last bad gate in topological order. A later AND masks it, owns at least one edge, and all edges owned by that later AND have a common endpoint. The proof chooses the last gate from a finite set and supplies the star centre.

The proof uses checked upstream L-meta-4846 to obtain the leaking nonedge. It proves that each gate of a minimum circuit is either the output or read by a later gate. The deletion argument permits references to unavailable wires under the project's default-false semantics. Following later readers on the leaking assignment eventually gives an AND where the signal becomes false.

## A shared bad gate with two good masks

[SharedMask.lean](SharedMask.lean) gives a six-vertex tree with edges ab, ad, cd, ap, dq. An eight-gate circuit uses the shared signal `j = (a ∨ c) ∧ (b ∨ d)` and outputs
`(a ∧ (j ∨ p)) ∨ (d ∧ (j ∨ q))`. The gate j owns the disjoint edges ab and cd. Both downstream ANDs reject the leak on bc. They own only ap and dq respectively.

The circuit is ready, computes the exact graph function, and resists replacing any one of its eight gates by any earlier wire or either constant. The proof supplies a distinguishing input for every such replacement. A six-gate equivalent circuit establishes that the eight-gate example fails global minimality. The example therefore constrains arguments based on single-gate bypass or clamping. It does not refute L-meta-1774.

Two explicit rewrites show how global savings arise here. First replace the OR input of the a-mask by b∨p while the d-mask continues to cover ad. Then replace the OR input of the d-mask by (a∨c)∨q. Each intermediate circuit computes the same function, and the shared bad wire then has no readers.

## Shared readers and downstream cofactors

[Guarded](shared-readers/Guarded.lean) treats a shared gate `J = L ∧ R` read through any number of branches `Hᵢ ∧ (J ∨ Bᵢ)`. Later branches and the final AND/OR circuit can reuse earlier guarded results and the original prefix wires. Choose independently whether each reader gets `L` or `R`. The compiler emits a physical monotone circuit with exactly one fewer gate. On graph-positive inputs this change can only increase the output. It therefore suffices to check independent inputs, where a reader can change only if its guard and chosen operand are true, its alternative is false, and the other operand is false.

[Shannon](shared-readers/Shannon.lean) gives a necessary and sufficient test for a fixed choice. When a reader changes on an independent assignment, compare the downstream circuit with that reader's output clamped to false and true. The theorem uses the original outputs for earlier readers and the selected rewiring for later readers. The edge function is preserved exactly when these cofactors agree at every changed reader. A globally minimum circuit in this layout must have an independent assignment with unequal cofactors somewhere for every proposed choice.

[GuardedTree](shared-readers/GuardedTree.lean) reconstructs the existing eight-gate tree circuit gate for gate. Its two readers can use opposite parents, reducing the count to seven while preserving the edge function. [GuardedCycle](shared-readers/GuardedCycle.lean) gives a five-cycle with three pendant vertices and a ready 14-gate circuit. Its gate 2 owns the disjoint edges `{0,1}` and `{2,3}` and has three guarded readers. For all eight choices of parents, reader three causes either `{2,4}` or `{1,4}` to be accepted. A separate 10-gate circuit computes the same graph function. This locates the remaining issue for this route to 1774: global minimality must supply additional structure, or an exchange must change more than the parent choice at each reader.

## Omitting individual reads and using global minimality

[Omit](shared-readers/Omit.lean) also allows a reader to omit `J`, replacing `Hᵢ ∧ (J ∨ Bᵢ)` by `Hᵢ ∧ Bᵢ`. The compiler saves one gate for the common AND and one OR for each omission. Testing the emitted circuit on the graph's edge assignments and its independent assignments suffices. [CycleRepair](shared-readers/CycleRepair.lean) applies this to the five-cycle example described above: the first two readers use opposite parents, and the third reader omits `J`. The exact circuit drops from 14 to 12 gates.

[ThreeRows](shared-readers/ThreeRows.lean) gives a necessary condition for a globally minimum circuit in this layout. A reader is *influential* on an input when varying the signal supplied to that reader can flip the final output with every other reader signal held fixed. One fixed reader must be influential on all three of the following kinds of input, possibly using different settings of the other reader signals.

- An independent input on which `L = 1` and `R = 0`.
- An independent input on which `L = 0` and `R = 1`.
- A genuine two-vertex edge input on which both `L` and `R` are true.

If each reader misses one of these kinds, it can receive the left operand, the right operand or no signal according to the missing kind. For each relevant input, the resulting assignments agree with the original circuit on every coordinate that influences the output. All choices can be made simultaneously, giving a strictly smaller exact circuit. [Opposite](shared-readers/Opposite.lean) proves the corresponding two-input condition for routing to parents alone.

[LiteralGuards](shared-readers/LiteralGuards.lean) constructs the smaller circuit explicitly when the operands are disjunctions of disjoint sets of primary inputs and each reader has a vertex that must be true whenever the reader is influential. A reader guarded by a vertex in one operand takes the other operand; a reader guarded by a vertex outside both operands omits the signal. On a true edge row on which both operands are true, the two endpoints already lie in opposite operand sets. A third guard vertex is therefore false. [GuardWires](shared-readers/GuardWires.lean) proves that a literal primary-input guard wire supplies the required vertex, even when its guarded result has multiple downstream uses. These statements allow any graph and any monotone suffix. For application to the full 1774 statement, general circuits can have overlapping operands, gates other than primary disjunctions as operands, or readers lacking such a vertex.

Run `research/L-meta-1774/shared-readers/check.sh` from the checkout to replay the examples and the [axiom audit](shared-readers/AuditGuarded.lean). The audit prints only `propext`, `Classical.choice`, and `Quot.sound`; the rowwise cofactor equivalence uses only `propext`.

Completing L-meta-1774 still requires constructing a circuit of at most the initial size with fewer gates owning disjoint edges.

From the repository's `lean/` directory, run the following commands.

```sh
lake build PEqualNP.Outside.L_meta_4846
lake env lean ../research/L-meta-1774/Masking.lean
lake env lean ../research/L-meta-1774/SharedMask.lean
```
