# Small bipartite cases for L-meta-3566

Every bipartite C4-free graph through 11 vertices is consistent with the exact gate minimum |E| + τ − 1 when E is nonempty. These results use an exhaustive C++ search and a prior computational bound. They are independent of the Lean proof checker.

The starting result covers arbitrary C4-free graphs with vertex cover number at most four. Its proof and enumerator are available in the [L-meta-612 finite checks](https://github.com/helloitswill/pequalnp-research-notes/blob/894ed421c9bccac0310ab9a270902798c2aec00c/L-meta-612/FiniteChecks.md). An ordinary bipartition of a graph on at most nine vertices already gives a cover of size at most four.

On ten and eleven vertices, cover number at least five forces a bipartition of size 5×5 or 5×6. After removing isolates, König's theorem gives a matching saturating the five-vertex part. Represent the other part by their nonempty neighbor sets in the five-vertex part. Two sets may intersect in at most one vertex, precisely the absence of four-cycles. Exhaustion of sorted row multisets, simultaneous column permutations, and transposition in the square case yields 64 classes on ten vertices and 307 classes on eleven. The two Python enumerators and a separate C++ incidence-matrix generator give the same counts.

| Vertices | Classes | Circuits searched | Result | Expanded states |
| --- | ---: | --- | --- | ---: |
| 10 | 64 | At most edge count + 3 gates | All excluded | 11,793,111 |
| 11 | 307 | At most edge count + 3 gates | All excluded | 4,203,780 |

The tables use the author's live-circuit search and the vertex-deletion bounds. Every deletion in the first row has cover at most four. Every deletion in the second row has at most ten vertices. Changes to the search source only extend its storage bounds for sample rows and separation pairs. Positive controls use |E| + 4 gates. All 64 search-generated ten-vertex positive controls were checked on the complete truth tables. Explicit five-star controls were separately checked on all 1,024 or 2,048 assignments for every ten- or eleven-vertex graph respectively.

For the desk's deletion claim choose a positive-degree vertex whose deletion leaves an edge. Two distinct edges guarantee such a vertex. Across this deletion the tested optimum falls by deg(z) + τ(G) − τ(G−z). Thus these calculations exclude a counterexample to L-meta-3566 on at most eleven vertices, conditional on the stated computation and its smaller-graph input.

The accompanying `verify_small.py` reproduces both rows. Pass the path to the pinned upstream `L-meta-612/kernel_search.cpp` as its sole argument, with Python 3.10+ and a C++17 compiler. The script checks the digest of the input source, enumerates the classes, checks the upper-bound witnesses against every assignment and runs the exclusions.
