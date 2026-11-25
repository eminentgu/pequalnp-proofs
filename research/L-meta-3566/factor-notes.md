# Factoring an edge function through two bipartite supergraphs

Let G, H and K be bipartite relations on the same row and column vertices. Selecting any sets of rows and columns defines an input. Each relation outputs true exactly when the selection contains one of its edges. The Lean files use this full-input semantics.

[FactorMatching.lean](FactorMatching.lean) proves `VertexPeel.FactorMatching.exact_iff`. The conjunction of the H and K outputs equals the G output on every input exactly when both factors contain G and every pair of extra edges (a,b) in H and (c,d) in K satisfies G(a,d) or G(c,b). Selecting just their endpoints proves necessity. Choosing one edge from each active branch proves sufficiency.

For G with no four-cycle, the following constraints apply regardless of sharing between the circuits computing H and K.

* `not_two_matchings` proves that the two extra-edge sets cannot both have five-edge matchings. Two such matchings would give a red/blue coloring of a five-by-five grid. A red cell records the crossing edge from the first matching's row and a blue cell forces the opposite crossing edge. A monochromatic rectangle gives a four-cycle in G. The proof kernel evaluates a pruned search over possible rows to verify the finite coloring assertion.
* [BicliqueFactor.lean](BicliqueFactor.lean) proves `rectangle_overlap`. Any two bicliques, one in each factor and each having at least two rows and columns, intersect in at most two edges. The intersection lies in G and is therefore a star if nonempty. At a common row, take a further row in each rectangle. Within the common columns, each further row can have at most one edge, since the center meets all columns. Every common column must meet at least one of the two further rows, by the crossing criterion. Transposition gives the column case.
* [CoalescedFactors.lean](CoalescedFactors.lean) proves `no_two_row_pairs` and `no_row_column_pairs`. Suppose one factor completes a pair of rows to their full joint neighborhood. The other factor cannot do the same to a pair of rows or a pair of columns if all four selected vertices have at least two true neighbors each. With two row pairs, each completed pair supplies a missing edge whose column avoids both rows of the opposite pair. Those two extra edges violate the crossing criterion. With a row pair and a column pair, their two-by-two block must be empty. The crossing criterion then forces a four-cycle between the private neighbors of the selected rows and columns.

Compile the sources with the project Lean toolchain. Starting at the repository root, run:

```sh
research_dir="$(pwd)/research/L-meta-3566"
cd lean
for module in FactorMatching BicliqueFactor CoalescedFactors
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$research_dir" "$module" || exit 1
done
python3 "$research_dir/find_factors.py"
```

## Seeded circuit search

[find_factors.py](find_factors.py) uses 52 square-free bipartite graphs on 12–20 vertices. These include Heawood and the order-three affine points versus nonvertical lines. The other 50 come from adding shuffled pairs unless they create a four-cycle. Each sampled factor adds one or two proper rectangles with two rows or two columns and at most five vertices on the other side. The search requires each rectangle to contain at least one more original edge than its larger dimension, and limits it to five extra edges.

The circuit factors out the common residual edge function, computes the remaining true-edge groups by minimum star covers, and builds all raw-variable OR sums jointly. Identical subexpressions share an actual gate in the emitted two-input AND/OR circuit. For each graph the script checks its best candidate on every edge, and on the largest independent column set for each choice of rows. By monotonicity these inputs verify the entire truth table.

The default seeded run examined 11,104 distinct candidates. Each factor contained two rectangles in 9,284 of them. The smallest observed gate count exceeded the edge-plus-cover-minus-one target by four gates. For Heawood the best count was 34 against a target of 27; for the affine graph it was 41 against 35. The search samples rectangle choices and uses a heuristic OR-sharing schedule. These numerical results do not bound arbitrary circuits or unsampled constructions.
