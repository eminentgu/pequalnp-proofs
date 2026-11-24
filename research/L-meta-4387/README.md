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
