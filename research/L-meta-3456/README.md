# Singleton behavior of small bipartite incidence circuits

This computational result addresses the finite cases of L-meta-3456. For every C4-free incidence matrix with at most four rows and four columns, the search finds that the minimum fan-in-two monotone circuit size equals the size of an explicit circuit whose AND gates are false on every singleton. The general statement remains open in this work. The search is implemented in Python and has been checked by rerunning it. These finite results have no Lean certificate here.

| Side length | Labelled C4-free matrices | Classes under relabelling and transposition |
| ---: | ---: | ---: |
| 1 | 2 | 2 |
| 2 | 15 | 5 |
| 3 | 334 | 16 |
| 4 | 18,521 | 59 |

For every nonempty graph the size found is its number of edges plus the size of a minimum vertex cover minus one. The empty graph uses the constant-false output with zero gates. The enumeration includes square matrices with isolated rows or columns; a rectangular matrix can therefore be padded to square.

## Upper bound

Assign every edge to an incident vertex in a minimum vertex cover. Each cover vertex contributes the AND of its input with the OR of its assigned neighbors. A final OR joins those contributions. The program constructs the actual gate list for each representative, checks that each input wire exists before its gate, and verifies the output on every Boolean assignment. It also checks every AND on every singleton.

## Lower bound search

The target is monotone. Its minimal positive assignments are the edges and its maximal negative assignments are the maximal independent sets. A monotone candidate accepts exactly the target if it labels these boundary assignments correctly.

A search state records the signals that have been produced and will still be used in the output's dependency graph. Each signal is represented by its values on the boundary assignments. All nonisolated inputs are essential. Isolated inputs may be fixed to false. In a smallest circuit for a nonconstant target, unused gates, copies, constants and newly produced signals equal to an available signal can be removed or bypassed. These simplifications preserve the boundary values and keep the circuit monotone.

The search tries AND and OR of every pair of distinct live signals. For each result it tries retaining neither, either or both operands for later gates. This accounts for arbitrary reuse. A gate reduces the number of live signals by at most one, so a state with more than one plus the remaining number of gates cannot finish. A second necessary condition discards a state when some positive-negative pair has no live wire that is true on the positive and false on the negative. Subsequent monotone gates cannot create that distinction. The exhaustive run tests a budget one below each constructed circuit's size.

## Reproduction

Run with Python 3.10 or later, from this directory.

```sh
python3 check_incidence.py > reproduced.json
diff -u census_results.json reproduced.json
```

The driver independently compares its decision routine against forward circuit enumeration on full truth tables for all 16 labelled 2-by-2 matrices and every budget from zero to three. This includes the four-cycle, where it finds the optimal three-gate circuit even though the cover construction uses five. In the results file, bit `n*i+j` of a key represents edge `(i,j)`.
