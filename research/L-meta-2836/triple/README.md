# The three-input OR branch of L-meta-2836

Let $G$ be the nine-vertex graph with edges $01,12,23,34,40,05,16,27,38,57,68,85$. The output is one exactly when the chosen vertices contain an edge. The supplied inputs are the nine vertex indicators, constant false, and $h=x_0\lor x_4\lor x_j$, where $j$ differs from 0 and 4. This note and the accompanying exhaustive searches exclude circuits of at most 13 two-input AND, OR and unary NOT gates on these inputs. They address the three-input OR branch only. The finite searches are ordinary Python. The small Lean module verifies the cofactor identities and the sensitivity witnesses.

## Eliminate all circuits containing a NOT

Absorb each NOT into the sign of the wire it reads, compose signs through any chain of NOTs, and apply De Morgan's law to OR gates. This gives a circuit of AND gates with freely complemented input wires and output. Constant zero and one may also be used. Nullary AND and OR gates give constants, unary AND and OR give copies, and the project’s NOT reads only its first pin. Missing pins or wires read false as specified by the circuit model. Thus a 13-gate circuit containing at least one NOT has at most 12 binary AND gates after conversion, even if that NOT was outside the output cone.

Suppose two assignments give opposite outputs and agree on every supplied input except one raw coordinate $x_i$. In the output cone of a signed AND circuit, $x_i$ must reach the output. If the output were a signed input wire, the witness pair would force it to be $x_i$ or its complement. For the uses below the edge output is false at both the empty assignment and the singleton $i$, so neither literal suffices. Hence some binary gate reads a signed occurrence of $x_i$. On fixing $x_i=0$, this gate receives a constant. Its output is a constant or a signed copy of its other input, and all its consumers can be rewired. At least one binary gate disappears. This proof also applies after previously fixing inputs and after removing resulting constant gates.

1. Set $x_4=0$. The negative singleton $\{0\}$ and positive edge $\{0,4\}$ have $h=1$ and differ only at raw input 4. The restricted helper becomes $x_0\lor x_j$.
2. Now set $x_0=0$. Take $k=5$ when $j$ is 2 or 6, and $k=1$ otherwise. Both $k$ values are neighbors of 0. The set $\{j,k\}$ is independent, allowing $j=k$. Adding 0 makes it positive. Both rows have $x_4=0$ and $h=1$, and only raw input 0 changes. So the restricted circuit loses a second binary gate.

What remains has at most ten binary AND gates, free complements, and seven raw variables. The helper is now a copy of $x_j$. The remaining edges are $12,23,16,27,38,57,68,85$. On all 128 assignments the signed search rejects a budget of ten gates in 107,828 distinct states. The bound is sharp. Eleven binary gates suffice for the following expression.

```text
(x1 AND (x2 OR x6)) OR (x2 AND (x3 OR x7)) OR
(x5 AND x7) OR (x8 AND (x3 OR x6 OR x5))
```

The parent reduction also describes the residual function on nine input positions, with positions 0 and 4 ignored. Fixing these two dummy inputs to false turns any such circuit into a seven-input circuit. Constant propagation adds no binary gates. Conversely, the eleven-gate expression above can use the other seven positions directly. `ThetaCircuit.lean` gives the explicit eleven gates in the project’s circuit datatype and proves their output on every nine-position input. From the project’s `lean/` directory, run `lake env lean /absolute/path/to/ThetaCircuit.lean`.

## The remaining monotone circuits

For a monotone circuit it suffices to check the 12 assignments consisting of one edge and the 12 maximal independent sets. Every positive assignment extends an edge and every negative assignment is contained in a maximal independent set. All nine raw wires are necessary even with the OR helper. For each omitted raw wire the script finds an edge row whose values on all remaining inputs are componentwise at most those of a maximal independent set. No monotone circuit on those inputs can separate the rows. The helper itself is optional, so a separate search checks the nine-wire initial state.

With the helper present, the search rejects a 13-gate budget for each of the seven choices. Enumerating all 12 graph automorphisms gives equivalence classes $\{1,5\},\{2,8\},\{3\},\{6,7\}$. The existing reduction R-meta-2836-17 already uses these four representatives. The replay checks all seven directly.

| Helper index | Search calls on cache misses |
| --- | ---: |
| No helper | 323,565 |
| 1 or 5 | 80,544 each |
| 2 or 8 | 120,801 each |
| 3 | 75,154 |
| 6 or 7 | 98,105 each |

## Why the searches cover every circuit

Represent each wire by its truth vector on the fixed rows. The signed search identifies a vector with its complement by choosing the representative whose first bit is zero. Boolean operations on truth vectors agree with circuit evaluation. Constants and outputs equal to a currently available wire can be bypassed, with a possible sign change in the signed model. Remove the bypassed gates and any gates outside the output cone. In the signed seven-variable search, each raw input is essential because selecting one of its neighbors witnesses an output change.

Consider the resulting circuit in topological order. At every step keep exactly the inputs or previous gates that will still be read. A binary gate reads two distinct current values, produces a fresh value, and either retains or discards each operand according to whether it has another use. All other values remain. The search enumerates precisely these choices for both possible monotone operations or all four choices of signed AND operands. Starting with $m$ live values requires at least $m-1$ further binary gates to finish with just the output. Sorting the live vectors and caching the remaining budget preserves all choices. Equality with the target can finish before the budget is exhausted.

Both searches reject a live state if its wires cannot distinguish some positive row from some negative row. In the monotone case the distinction must run in the direction one on the positive and zero on the negative. In the signed case either direction is available.

When the budget equals $m-1$, every step must discard both operands. The continuation is a read-once formula in the live values. A signed read-once formula can be put in negation normal form. Each live value then has a single leaf polarity. If one wire alone distinguishes two positive-negative row pairs in opposite directions, both required polarities cannot fit that leaf.

For a monotone read-once formula, its Karchmer–Wigderson protocol partitions the positive-by-negative grid into disjoint rectangles, one per used leaf. At an OR gate the positive row chooses a true child. At an AND gate the negative row chooses a false child. A fixed deterministic tie rule makes each resulting leaf domain a rectangle, and the leaf’s variable separates every pair in that rectangle. If a cell has only one possible separating wire it must belong to that wire's leaf. The Cartesian product of the row and column projections of these forced cells must therefore be contained in its rectangle. Intersecting forced products for two distinct wires rule out such a formula. This is the only additional tight-budget test in the monotone search.

## Replay

Run in this directory with Python 3.10 or later. No external packages are required.

```sh
python3 reproduce.py
```

The script checks all seven helper choices and the case where the helper is unused. It also checks the sensitivity witnesses, cofactor, matching upper bound, and orbits. A reference run is in `results.txt`. To replay the small semantic lemmas with Lean 4.36 and its standard library, run the following command. The two exhaustive search exclusions are outside this Lean module.

```sh
lean -j1 Restrictions.lean
```
