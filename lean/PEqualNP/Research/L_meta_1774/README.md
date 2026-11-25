# Ownership descent for forests

For a graph edge function, an AND *owns* an edge when the gate is true on its two endpoints and no earlier AND in its cone is true on that input. [L-meta-1774](https://pequalnp.com/lemma#L-meta-1774) asks for a same-size-or-smaller circuit with fewer ANDs that own disjoint edges, while retaining an owned edge at each AND.

`forestDescent` proves this for every finite forest, including disconnected forests and isolated vertices. Starting from any correct monotone circuit of fan-in at most two with a positive defect count, it constructs a circuit of at most the original size with **zero** defective ANDs. The source circuit need not be minimum and can have ANDs that own no edge.

## Proof

1. `buildCoveredStar` groups each edge under one endpoint in a chosen vertex cover. It builds one OR chain per nonempty group, ANDs the result with its centre, and ORs the groups. Each AND owns a true edge, and every edge it owns contains its centre. The total size is at most the number of edges plus the size of the cover minus one.
2. `coveredDescent` applies this construction to any graph and circuit when some vertex cover meets that gate budget.
3. For forests, the upstream [forest lower bound L104](../../MetaComplexity/L104.lean) supplies the budget for a minimum vertex cover. This proves `forestDescent` in [Forest.lean](Forest.lean).
4. [CoveredOwnership.lean](CoveredOwnership.lean) also gives a proof for star forests using only active-input counting. An input with a neighbor must affect the output, and a fan-in-two circuit with `s` gates depends on at most `s + 1` inputs.

The cover compiler strengthens the invariant of [L-meta-5355](../../Outside/L_meta_5355.lean) to record a common centre for all the edges owned by each AND. The support-counting argument adapts [the project support lemmas](../../MetaComplexity/Helpers/Support.lean).

## Scope and verification

The general card allows graphs containing cycles of length five or greater. The forest result and the conditional budget result leave that general case open. These are modular research files. The core uses `Mathlib` and `PEqualNP.Defs`. The forest corollary also imports the upstream proof module `PEqualNP.MetaComplexity.L104`. The claimed desk card lists only `PEqualNP.Defs` as its project import.

From the repository root, use the pinned Lean toolchain and run

```sh
cd lean
lake build PEqualNP.Research.L_meta_1774.Forest
```
