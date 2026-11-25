# Ownership descent for forests and peelable graphs

For a graph edge function, an AND *owns* an edge when the gate is true on its two endpoints and no earlier AND in its cone is true on that input. [L-meta-1774](https://pequalnp.com/lemma#L-meta-1774) asks for a same-size-or-smaller circuit with fewer ANDs that own disjoint edges, while retaining an owned edge at each AND.

`forestDescent` proves this for every finite forest, including disconnected forests and isolated vertices. Starting from any correct monotone circuit of fan-in at most two with a positive defect count, it constructs a circuit of at most the original size with **zero** defective ANDs. The source circuit need not be minimum and can have ANDs that own no edge.

`peelableDescent` extends this to every [peelable graph](../../Defs/Peelable.lean). Every induced subgraph with an edge must have a good leaf or a prescribed six-vertex run. The result includes the six-cycle and graphs whose cycles all have length at least seven and whose vertices of degree at least three are pairwise at distance at least seven. In particular it includes cycles of all lengths at least seven. [Peelable.lean](Peelable.lean) states the general theorem and the two corollaries.

[CycleFive.lean](CycleFive.lean) handles the five-cycle separately. The four successive internal vertices each have degree two. The weaker run in [L-meta-579](../../Outside/L_meta_579.lean) permits both ends of the run to coincide at the fifth vertex. This gives the seven-gate lower bound needed by a cover of three vertices.

## Proof

1. `buildCoveredStar` groups each edge under one endpoint in a chosen vertex cover. It builds one OR chain per nonempty group, ANDs the result with its centre, and ORs the groups. Each AND owns a true edge, and every edge it owns contains its centre. The total size is at most the number of edges plus the size of the cover minus one.
2. `coveredDescent` applies this construction to any graph and circuit when some vertex cover meets that gate budget.
3. For forests, the upstream [forest lower bound L104](../../MetaComplexity/L104.lean) supplies the budget for a minimum vertex cover. This proves `forestDescent` in [Forest.lean](Forest.lean).
4. [CoveredOwnership.lean](CoveredOwnership.lean) also gives a proof for star forests using only active-input counting. An input with a neighbor must affect the output, and a fan-in-two circuit with `s` gates depends on at most `s + 1` inputs.

The peelable case uses [the project's peelable-graph lower bound](../../Library/Helpers/PeelableSanity.lean) to supply the same gate budget.

The cover compiler strengthens the invariant of [L-meta-5355](../../Outside/L_meta_5355.lean) to record a common centre for all the edges owned by each AND. The support-counting argument adapts [the project support lemmas](../../MetaComplexity/Helpers/Support.lean).

## Scope and verification

The general card allows graphs containing cycles of length five or greater. Peelability and the separated-vertex criterion leave part of the general case open. For example, a nonempty cubic graph of girth five has neither a good leaf nor a degree-two run. These are modular research files. The core uses `Mathlib` and `PEqualNP.Defs`. The forest corollary also imports the upstream proof module `PEqualNP.MetaComplexity.L104`. The peelable result imports `PEqualNP.Library.Helpers.PeelableSanity` in addition to the local core. The five-cycle result imports `PEqualNP.Outside.L_meta_579` and the local peelable module. The claimed desk card lists only `PEqualNP.Defs` as its project import.

From the repository root, use the pinned Lean toolchain and run

```sh
cd lean
lake build PEqualNP.Research.L_meta_1774.Forest PEqualNP.Research.L_meta_1774.CycleFive
```
