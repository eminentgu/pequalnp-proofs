# L-meta-4387 — 25 more gates after joining two Fano point columns

The desk supplies 14 raw vertex columns, the constant columns, and the OR of the first two point columns. Each column is a 58-bit truth table. The target has bits 0 through 20 set. The question is whether a straight-line program of at most 25 additional bitwise AND/OR operations can produce it.

`Normalize.lean` proves a generic compiler for any bit width. A nonconstant target outside the seed list can be reached by an equally short or shorter program that starts with the nonconstant seeds, adds a new nonconstant value on every step, and ends at the target. No retained gate repeats an earlier column or equals one of its operands. Repeated wires and unused trailing instructions in the input program are allowed.

From this branch's `lean/` directory, after installing the pinned project toolchain and cache, run:

```sh
lake build PEqualNP.Defs
lake env lean ../research/L-meta-4387/Normalize.lean
```

Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for `PEqualNP.Research4387.normalizeChain`. The finite lower bound is open here.

The packed-column compiler also constructs an actual 14-input circuit whose first gate is OR of inputs 0 and 1. Any successful 25-operation chain yields a circuit of at most 26 gates computing the Heawood incidence function on all 16,384 inputs. It contains nested AND gates, and at least one AND accepts a two-vertex assignment the output rejects. See [PhysicalHeawood.lean](PhysicalHeawood.lean) and the [four supporting files from the plane investigation](https://github.com/eminentgu/pequalnp-proofs/tree/c8b745f/research/L-meta-2583). The prerequisites are included in this branch.

The finite [SAT search](search.py) uses the desk's 15 nonconstant masks directly and rechecks each returned trace using integer bit operations. A 26-operation line-star circuit gives a positive control. The normalizer justifies omitting the two constant seeds. A shorter trace can be padded at its output by AND or OR with itself.

## What is proved

[UpperWitness.lean](UpperWitness.lean) supplies a 26-operation trace and verifies every operand against the exact desk bank. The target is the last column. Line 0 combines that signal with point 3, the six other lines each require three operations, and the seven results require six ORs.

[LastAnd.lean](LastAnd.lean) proves that if the last operation is AND, one operand must exhibit a truth-table dependence on every one of the 14 raw variables. Its stronger statement supplies at least seven distinguishable negative tests per variable for that operand. [TerminalCut.lean](TerminalCut.lean) also reduces a hypothetical shortest trace to a normalized prefix of at most 24 operations and two generated operands whose AND or OR is the target. The finite bound remains open for both last operations. With PySAT 1.9.dev25 and a budget of two million conflicts per branch, both searches returned UNKNOWN.

[Conditional4387.lean](Conditional4387.lean) applies the submitted reduction to the two proved premises. The one remaining mathematical question is whether a Heawood circuit with the specified first OR, at most 26 gates, and the two necessary AND-gate properties exists. The complete replay from this branch's `lean/` directory is:

```sh
python3 ../research/L-meta-4387/replay.py
```

The quantitative interval currently proved for the minimum additional gate count is **19 through 26**. The 19-gate lower bound follows from the existing 20-gate lower bound for an ordinary Heawood circuit and the cost of adding the prepaid OR. The 26-gate upper bound is constructive. [Translation and lower bound](PhysicalHeawood.lean), [explicit upper bound](UpperWitness.lean).

The [standalone proof of the second premise](standalone/L_meta_physical.lean) depends only on the project's definitions. The placeholder theorem name can be set to the eventual official child ID. Its SHA-256 is `ae0f6a42b3143b13e491ef8d60d97c43322a869951888c2a03a9ab5f009b140e`.

All 14 raw columns are individually indispensable even with the extra OR, both constants and an unlimited gate budget. Each erased column has a positive/negative row pair that every remaining seed preserves under AND and OR. [Certificate](EssentialRaw.lean).

For a terminal AND, an operand generated in at most five steps has only one possible value: the OR of all point inputs. If the other operand is fresh and differs from the target, it must be the target with bit 57 set. [Five-gate classification](SmallOperand.lean).
