# Sharp size and deletion for bipartite graphs with one side of degree at most two

Let G be a finite bipartite graph without a four-cycle. Suppose every vertex in one color class has degree at most two. The other color class can have arbitrary degrees. For at least two edges, [side_degree_two_sharp](SideDegreeTwoSharp.lean) proves all three statements in Lean.

* Every monotone circuit of fan-in at most two computing the full edge function has at least |E| + τ(G) − 1 gates. A minimum cover gives a circuit of exactly that size.
* If a minimum useful circuit has an AND owning two disjoint edges, another useful circuit of at most the same size has fewer such gates. This is the ownership conclusion of L-meta-1774.
* One positive-degree vertex works for every correct binary AND/OR circuit. Deleting its incident edges saves at least its degree in gates, with one extra gate when the minimum cover shrinks. This is the conclusion of L-meta-3566.

This includes subdividing every edge of any simple graph once. The original vertices can have arbitrary degree, the graph may be disconnected, and the number of cycles in one component is unbounded.

## How the proof handles shared gates

First take a minimum circuit in which any OR gate with a sound operand is itself sound. A wire is sound if every input that activates it contains an edge. A size-preserving exchange moves a sound operand straight to the output and decreases the count of gates which activate on independent inputs. The upstream project already proves existence of a related top form. [SafeTail.lean](SafeTail.lean)

In the leafless branching case choose degree-two candidates in a branching component. Deleting any candidate leaves the cover number unchanged. For each candidate a there is a neighbor t outside the candidate set whose neighbors are all candidates. [ComponentStability.lean](ComponentStability.lean)

Examine the first gate to read a candidate. An AND reading a becomes zero when a is zero. Correctness forces another gate to be eliminated. For an OR reading a and another candidate, the square-free graph distinguishes their neighborhoods. If the other operand is outside the candidate set, it must activate on some independent input since the OR activates on the singleton a. Turn off every candidate on this input. Earlier wires ignore that change. Add t, which creates no edge, and then add a, which creates the edge ta. The OR is already on before adding a, so a distinct gate must read a and change value. Both raw readers disappear upon fixing a to zero. This argument permits arbitrary sharing with other components. [LocalReaders.lean](LocalReaders.lean)

The construction gives a deletion at one least circuit's gate budget. That budget works for every circuit. The remaining leaf and cycle cases, followed by induction over edge deletion, give the numerical bound and ownership descent. [SubdivisionAssembly.lean](SubdivisionAssembly.lean)

An additional theorem, stable_neighborhood, gives the full vertex-deletion conclusion on any square-free graph with a nonisolated vertex whose neighbors all have degree two and whose individual deletions preserve the cover number. [SideDegreeTwoSharp.lean](SideDegreeTwoSharp.lean)

## An AND count under a different graph assumption

For any bipartite graph of maximum degree three and girth greater than six, [subcubic_girth](SubcubicAND.lean) proves that every correct binary monotone circuit needs at least τ(G) physical AND gates. When too few ANDs are available to pay for a vertex, its singleton input selects at most two labeled gate ports. Choosing another user at each port must produce an edge. A failure to assign distinct ports forces a six-cycle. Counting both ports per physical gate then pays for a vertex, and the bound follows by restriction. The total gate lower bound on all such graphs is open. [CubicPorts.lean](CubicPorts.lean) [PortHall.lean](PortHall.lean)

For a square-free subcubic graph, take a vertex set Z whose deletion makes the graph bipartite and a set T meeting every six-cycle. Every monotone circuit of fan-in at most two computing the edge function has at least τ(G) − ⌊(|Z| + |T|)/2⌋ physical AND gates. In particular, the full AND bound holds if deleting a single vertex makes the graph bipartite and the graph has no six-cycle. [SubcubicTransversals.lean](SubcubicTransversals.lean)

To replay after building the research dependencies SafeTail, ComponentStability, SubdivisionAssembly, PortHallGirth, PortTransversal and PseudoforestAND, use the repository root.

```sh
proof_dir="$(pwd)/research/L-meta-3566"
cd lean
for module in LocalReaders SideDegreeTwoSharp CubicPorts SubcubicAND
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$proof_dir" "$module" || exit 1
done
```
