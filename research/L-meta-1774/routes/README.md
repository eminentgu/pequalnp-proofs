# The three registered routes to L-meta-1774

The exact conjecture asks for a smaller count of AND gates owning disjoint edges without increasing circuit size. Each source AND must own an edge, and the replacement must have this property too.

| Registered route | Result |
| --- | --- |
| R-meta-1774-1 | Premise 4848 is false. A minimum 12-gate circuit accepts a nonedge at an internal AND. This graph satisfies L-meta-1774. [Nine-vertex kernel proof](../finite-witness/Conclusion.lean) · [Earlier accepted eight-vertex counterexample](https://github.com/open-goat/pequalnp-proofs/pull/11915) |
| R-meta-1774-642 | The crossed-nonedge premise 7406 is proved. With it, the outstanding exchange statement 7408 is equivalent to L-meta-1774. [Equivalence](ExchangeRoute.lean) · [Upstream 7406](https://github.com/open-goat/pequalnp-proofs/pull/12060) |
| R-meta-1774-583 | The OR-path premise 8073 is proved. With it, the outstanding repair statement 8075 is equivalent to L-meta-1774. [Equivalence](Equivalent8075.lean) · [Upstream 8073](https://github.com/open-goat/pequalnp-proofs/pull/12434) |

The forward direction for 7408 chooses a minimum replacement with zero defects, using L-meta-1774 repeatedly. In a triangle-free graph, a pairwise-intersecting nonempty family of edges has a shared endpoint. The replacement therefore satisfies the star alternative at every gate. The identity permutation suffices. The reverse direction applies the registered cut and 7406. [Zero-defect normalization](Descent.lean)

For 8075, the bad indices are a finite set of actual gate indices. One bad index makes its cardinality positive, so L-meta-1774 gives the requested smaller circuit defect count. The reverse direction applies the registered cut and 8073.

With upstream commit `224cd9f334bd046ba1a45201bda1251a114b4fb4` or its research-branch descendant, run the following from the repository root.

```sh
routes="$(pwd)/research/L-meta-1774/routes"
cd lean
lake build PEqualNP.Research.L_meta_1774.CoveredOwnership PEqualNP.Outside.L_meta_7406 PEqualNP.Outside.L_meta_8073 PEqualNP.Outside.R_meta_1774_642 PEqualNP.Outside.R_meta_1774_583
for module in Descent ExchangeRoute Equivalent8075
do
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/$2.olean" "$1/$2.lean"' sh "$routes" "$module" || exit 1
done
```
