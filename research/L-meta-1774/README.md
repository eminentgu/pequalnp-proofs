# Masking and edge ownership in L-meta-1774

The file [Masking.lean](Masking.lean) proves necessary conditions for a circuit appearing in L-meta-1774. Here *ready* means every AND gate owns at least one graph edge, with ownership as defined in the project.

1. In any ready circuit, an AND cannot read an earlier AND directly. On an edge owned by the later gate, all its inputs are true and all earlier ANDs in its cone are false.
2. Suppose an AND of a minimum ready circuit computing the edge function owns two vertex-disjoint edges of a four-cycle-free graph. A later AND in its cone rejects a nonedge that the initial gate accepts. The later gate owns a third edge distinct from both original edges, and the initial gate is false on that third edge.

3. On a path to the mask, the last true gate is an OR strictly between the initial AND and the mask. This OR is true both on the leaking input and on the mask’s owned edge. A distinct second input to the mask is false on the leak and true on the owned edge. The theorem identifies both input wires.
4. If the graph has at most two edges, each pair of edges owned by the same AND in the original minimum ready circuit shares an endpoint.

5. In a triangle-free graph, choose the last bad gate in topological order. A later AND masks it, owns at least one edge, and all edges owned by that later AND have a common endpoint. The proof chooses the last gate from a finite set and supplies the star centre.

The proof uses checked upstream L-meta-4846 to obtain the leaking nonedge. It proves that each gate of a minimum circuit is either the output or read by a later gate. The deletion argument permits references to unavailable wires under the project's default-false semantics. Following later readers on the leaking assignment eventually gives an AND where the signal becomes false.

## Complete case for vertex covers of size at most three

The independent theorem `ownership_descent` proves L-meta-1774 for every graph of girth at least five that has a vertex cover of size at most three. It allows arbitrarily many vertices and applies to every minimum monotone circuit satisfying the posted hypotheses. [Checked proof at commit 57345d4a](https://github.com/eminentgu/pequalnp-proofs/blob/57345d4a/research/L-meta-3566/CoverThree.lean)

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

## Pinning a gate in an arbitrary circuit

A graph edge is *critical for a gate* when the circuit rejects that edge's two-vertex input after the gate is clamped to false. This test includes every wire that reads the gate, however far downstream. [Pin](gate-pinning/Pin.lean) proves that narrowing one AND gate pointwise and retaining only primary inputs or original operands preserves all the old owned edges at every other AND gate. If the changed gate lies in the cone of an owner, ownership requires the changed gate to be false on that particular edge already. Gates earlier than the changed site keep precisely their former ownership. The proof accommodates forward references and out-of-range references under the public model's default-false semantics.

[StarPin](gate-pinning/StarPin.lean) gives an equal-size edit for either operand of an AND gate. Suppose the primary input at vertex `v` implies that operand and every critical edge contains `v`. Replace that operand with `v`. The new circuit computes the same graph function. Its edited gate owns only edges containing `v`, and it retains each of its formerly owned edges that contains `v`. The other operand may be any earlier wire. When at least one owned edge meets `v`, every formerly productive gate remains productive.

[PinDescent](gate-pinning/PinDescent.lean) permits a repair to introduce defects at later gates. At each step it fixes the first defective gate and preserves the earlier clean prefix. After at most the original number of gates the entire circuit is clean. [PinDesk](gate-pinning/PinDesk.lean) applies this induction to the posted statement of 1774. Its remaining premise asks for a suitable vertex, operand and retained edge at the earliest disjoint owner of every eligible minimum circuit. This premise remains open.

[PinTree](gate-pinning/PinTree.lean) checks the edit on a five-vertex tree. Gate 2 owns `{0,1}` and `{2,3}`. Only `{0,1}` disappears from the output when gate 2 is clamped to false. Pinning its first operand to vertex 0 keeps all seven gates, every AND still owns an edge, and no gate owns disjoint edges afterward. An independent five-gate construction shows the example is nonminimal. Run `research/L-meta-1774/gate-pinning/check.sh` to reproduce the proofs and the [axiom audit](gate-pinning/AuditPin.lean).

## Gates with a single critical edge

[CriticalCases](gate-pinning/CriticalCases.lean) proves that every gate of a globally minimum monotone circuit computing a graph edge function has a critical edge. If clamping the gate to false retained every edge, the clamped circuit would still reject every independent set and the gate could be deleted. When a defective AND has just one unordered critical edge, replacing both of its operands by the two primary endpoints preserves the output. The replacement gate owns that edge even if another gate owned it in the original circuit. Every other productive gate stays productive and earlier gates keep their ownership.

The conditional theorem `exact_of_remaining_critical_cases` reduces the posted statement of 1774 to circuits whose earliest defective gate has at least two distinct unordered critical edges and admits no certified one-operand star pin. The two critical edges may share an endpoint. The proof of an exchange for this remaining case is open.

[CriticalTree](gate-pinning/CriticalTree.lean) checks a seven-vertex tree and a 14-gate circuit. Gate 5 owns the disjoint edges {0,1} and {2,3}. Its sole critical edge is {4,5}, originally owned by gate 1 and unowned by gate 5. Pinning gate 5 to inputs 4 and 5 makes it own that edge, preserves the graph function and productivity, and leaves every gate free of disjoint owners. A separate eight-gate circuit computes the same function, so the example does not satisfy global minimality.


## What every earlier wire must miss in a minimum circuit

[Sensitive](gate-pinning/Sensitive.lean) proves an exact test for replacing one arbitrary gate in a monotone circuit computing the graph function, allowing every downstream use of that gate. Clamp the gate low and record each true two-vertex edge that the circuit loses. Clamp it high and record each independent assignment that the circuit accepts. The physical replacement computes the graph function exactly when it turns on for every recorded edge and stays off on every recorded independent assignment. The replacement's behavior on other assignments follows from monotonicity of the complete circuit.

In a globally minimum circuit, every wire available before the gate must fail one side of this test. Otherwise all readers can be redirected to that wire and the gate deleted. This gives separate witnesses for the two operands of any binary gate whose operands are earlier wires.

- For an AND, each operand fires alone on some independent input where clamping the gate high makes the output true. Thus neither operand can imply the graph function.
- For an OR, each operand fires alone on some true edge lost by clamping the gate low. The proof establishes that the two unordered graph edges are distinct. Thus neither operand can already accept every graph edge.

[LocalRigidity](gate-pinning/LocalRigidity.lean) exhausts the one-gate edits of the defective AND in the six-vertex tree above. Its three critical unordered edges are {0,1}, {0,3} and {2,3}. The singleton inputs {0} and {3} are both sensitive to clamping it high. Every monotone gate of arity at most two that can replace it without changing the output has the original AND operation and the original pair of wires, in either order. This classification includes constants, unary gates, repeated operands, forward references and out-of-range wires. The verified smaller circuit for the same tree changes multiple sites.

These necessary constraints apply to a defective gate's operands regardless of fanout. Producing a successful equal-size exchange in every remaining case of L-meta-1774 is open.

## Equal-size repairs with several critical edges

[CriticalOr](gate-pinning/CriticalOr.lean) proves two repairs of a productive AND in a minimum circuit. If every critical edge meets one of two vertices that individually activate the gate, replace it by the OR of those primary inputs. If every critical edge lies in a two-edge star and the gate owns both spokes, the repair always exists. Ownership makes each active operand depend on one endpoint of an owned pair. Either the centre alone forces a parent, or each leaf forces both parents. The second case uses the new OR. The conditional theorem `exact_of_remaining_beyond_two_spokes` removes both cases from the general proof obligation.

[CriticalPairOr](gate-pinning/CriticalPairOr.lean) covers two critical edges already computed by earlier ANDs of their respective primary endpoints. Replacing the bad gate by the OR of those two wires works even when the edges are disjoint and the wires lie outside the old fan-in cone. A newly introduced AND ancestor can activate only on a pair that already activated the bad gate. Every downstream gate with the bad gate in its cone was already unable to own that pair. [CriticalPairTree](gate-pinning/CriticalPairTree.lean) checks this exchange on all 64 inputs of a six-vertex tree. Exactly two disjoint edges are critical, both primary ANDs enter the cone for the first time, and a six-gate circuit certifies nonminimality of the 12-gate example.

[GroupedStar](gate-pinning/GroupedStar.lean) handles any number of critical edges with a common endpoint. The prefix must provide a wire with exclusively OR ancestry that accepts every critical pair. Intersecting this wire with the centre must imply the old gate. The new AND then owns a critical edge and retains productivity throughout the circuit. In particular, two critical spokes only need an earlier OR of their leaves. The old gate may own neither spoke, and the earlier OR can lie outside its original cone.

[CriticalOrTree](gate-pinning/CriticalOrTree.lean) checks the 64 inputs of a six-vertex forest. Its two critical spokes are owned by the defective gate and the old one-operand star pin is provably unavailable. [GroupedStarTree](gate-pinning/GroupedStarTree.lean) checks the 256 inputs of an eight-vertex tree. Its defective gate owns neither critical spoke and acquires both after reusing an OR outside its original cone. Both examples certify equal output, productivity, elimination of all defects, and a strictly smaller circuit witnessing that the original example is nonminimal.

Run `research/L-meta-1774/gate-pinning/check.sh` from any directory using the script's full or relative path. It builds the research modules in a fresh temporary directory and runs the [axiom audit](gate-pinning/AuditPin.lean). The remaining open case includes disjoint critical edges for which the two earlier primary ANDs are unavailable.

From the repository's `lean/` directory, run the following commands.

```sh
lake build PEqualNP.Outside.L_meta_4846
lake env lean ../research/L-meta-1774/Masking.lean
lake env lean ../research/L-meta-1774/SharedMask.lean
```
