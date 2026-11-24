# A 29-row lower bound for the seven-variable theta graph

Even with freely complemented wires, ten binary AND gates cannot compute the edge function of the graph with edges $12,23,16,27,38,57,68,85$. The check uses 16 positive assignments and 13 negative assignments. These 29 rows already rule out ten gates. An explicit eleven-gate circuit agrees with the edge function on all 128 assignments, so the unrestricted signed AND complexity is exactly eleven.

Run the following command from this directory with Python 3.10 or newer. The folder is self-contained and needs only the standard library.

```sh
python3 replay.py
```

The additional command `python3 certificate/check.py` checks the supplied finite closure table by inspecting each listed state and every successor. It independently rejects the ten-gate budget. The table format and induction argument are in `certificate/README.md`.

The replay regenerates the JSON bank, verifies that all seven input variables are essential on the selected rows, checks all bit permutations, runs the exhaustive search, and verifies the eleven-gate upper bound. It visits 23,484 distinct states. Of these, 1,616 need expansion and 21,868 are excluded immediately at a tight gate budget. The counts of expanded states at remaining budgets 5 through 10 are 4, 189, 836, 558, 28 and 1. This certificate is checked by Python. The Lean pinning theorems in the adjacent directory address the reduction to this graph.

## Reading the bank

Each assignment is a seven-bit unsigned integer. The bit positions from least to most significant represent vertices $1,2,3,5,6,7,8$. A truth vector stores a wire's value on each selected assignment in another integer. Its least significant bit represents the first positive assignment.

| JSON field | Meaning |
| --- | --- |
| `vertex_order` | Vertex corresponding to each assignment bit. |
| `positives`, `negatives` | The selected assignments, in the order used to pack truth vectors. The negatives follow the positives. |
| `full_mask` | The low 29 bits set. Exclusive OR with this mask complements a truth vector. |
| `positive_mask` | The low 16 bits set. This is the target truth vector before complement normalization. |
| `raw` | The seven unnormalized input truth vectors, in vertex order. |
| `permutations` | The four graph automorphisms acting on assignment bit positions. Each entry specifies the destination of every source bit. |
| `swap_masks` | For each automorphism, two bit masks implementing its action on the 29 truth-vector positions. First swap pairs at distance one, then at distance two. |

For a distance $s$ and mask $m$, put $d=(z\mathbin{\mathrm{xor}}(z\gg s))\mathbin{\&}m$. The new value is $z\mathbin{\mathrm{xor}}d\mathbin{\mathrm{xor}}(d\ll s)$. The bank generator checks the result on each individual bit for every automorphism. It also verifies that every permutation preserves the edge list. This gives a direct check of the small integer masks in the JSON.

## Why the search is exhaustive

Treat complements as free. Store one representative per pair of complementary truth vectors by choosing the member with first bit zero. Each binary gate combines two distinct current wires in one of the four input polarities. AND suffices because De Morgan's law implements OR by changing polarities. A gate that yields a constant or a copy of an already available wire can be removed. Each of the seven original wires must occur in the reduced circuit: for every variable the replay finds a positive and a negative assignment differing in that coordinate alone.

Slice this reduced circuit at each gate in evaluation order, retaining exactly the wires that have another use in the output cone. On consuming two wires, a gate may drop both, retain either, or retain both. The search enumerates these choices. To finish with one output from $m$ live wires takes at least $m-1$ more binary gates. At each state every positive-negative pair must be distinguished by some live wire. Equal states can be cached, and a graph automorphism maps every possible continuation to an equivalent one of the same size.

## Two exclusions at a tight budget

With exactly $m-1$ gates for $m$ live wires, each gate must drop both operands. Its continuation is a read-once formula on those wires. Push complements to the leaves by De Morgan's law so that each wire occurs with one fixed polarity.

1. Consider all $16\times13$ pairs consisting of a positive row and a negative row. A pair distinguished by only one wire is forced to use that wire. If two pairs forced to the same wire require opposite polarities, a read-once continuation is impossible.
2. The Karchmer–Wigderson protocol of the formula partitions the pairs into disjoint rectangles. At an OR gate the positive row picks a true child. At an AND gate the negative row picks a false child. Fix a deterministic rule for ties. Each leaf receives a Cartesian product of positive and negative rows and reports a separating signed wire. All pairs forced to a given wire must lie in its one leaf rectangle. That rectangle must contain the Cartesian product of the row and column projections of its forced pairs. If these products for two different wires intersect, the required disjoint rectangles cannot exist.

The search uses the two exclusions only at a tight budget. For an additional replay without automorphism identification, run `python3 rows.py tiny --no-symmetry`. It rejects the same ten-gate bound with 5,689 expanded states. For an independent variation of the row bank, `python3 rows.py three full` checks 64 and 128 rows, respectively. The optional `python3 compact.py 0` reconstructs the 29-row choice by bounded trials that remove complete graph-automorphism orbits from the 64-row bank.

## A 64-row check using separation alone

`python3 rows.py three --coverage-only` uses the 37 positive assignments with at most three selected vertices and all 27 negative assignments. It disables both tight-budget shortcuts. The only data-dependent rejection is a positive-negative pair on which all live wires agree. With the same four graph automorphisms the search rejects ten gates after 26,698 states, including states with no admissible successor. This option gives a second route to a checker with fewer semantic prerequisites.
