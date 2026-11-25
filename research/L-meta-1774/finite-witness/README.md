# A minimum circuit refuting L-meta-4848

[Conclusion.lean](Conclusion.lean) proves the literal negation of L-meta-4848 and proves the entire descent asserted by L-meta-1774 on this nine-vertex graph. The general L-meta-1774 remains open.

The desk lists the negated statement as L-meta-4849. An earlier, independently submitted eight-vertex counterexample by miz0139m1023-hue received the upstream checker's acceptance on 25 November 2026 at 04:34 UTC. The nine-vertex proof here gives a second witness and also certifies a top-form minimum on it. [Earlier upstream PR 11915](https://github.com/open-goat/pequalnp-proofs/pull/11915) · [Upstream checker verdict](https://github.com/open-goat/pequalnp-proofs/actions/runs/45539058631)

The graph has edges 01, 12, 13, 24, 28, 35, 58, 68 and 78. It is triangle-free and four-cycle-free. Its smallest vertex cover has size four. The explicit 12-gate monotone circuit computes the graph's edge function on all 512 Boolean inputs. Gate 8 accepts the nonedge pair {1,6}. Its genuine owned edges are 68 and 78, which share vertex 8. Every AND gate owns a nonempty star of edges. A second minimum circuit meets the project's additional top-form condition and retains the same nonedge behavior. [Circuit and graph](../../../lean/PEqualNP/Research/L_meta_1774/WitnessNine.lean) · [Top-form circuit](TopWitness.lean)

Every correct monotone circuit of fan-in at most two needs at least 12 gates on this graph. The lower bound holds even with empty, one-input or invalid reads allowed by the project model. [Extraction from the project's circuit model](Extract.lean) · [Bridge to the posted statement](WitnessBridge.lean)

## Proof of the lower bound

The nine edge inputs and seven maximal independent sets define 16 evaluation rows. Any correct circuit must separate every positive row from every negative row. The Lean extraction converts a circuit into a computation on sets of wire signatures, with at most one step per circuit gate. The support at the start must include each of the nine raw input signatures. [Live computations](Live.lean) · [Extraction](Extract.lean)

The Python enumerator proposes reachable sets of live signals for an 11-gate budget. There are 16,021 distinct layer states and 45,844 admissible operations including choices of which operands stay live. For each state the Lean checker considers all binary operands, AND/OR choices, and possible retained operands. It verifies cutoffs from the width bound and missing positive/negative separation, and checks membership in a certified child list for every remaining successor. Each generated theorem uses kernel evaluation. The transitive axiom audit of the final minimum, counterexample, and graph-specific descent lists only `propext`, `Classical.choice` and `Quot.sound`. [Checker](Checker.lean) · [Packing](Packing.lean) · [Induction on the remaining gate budget](Node94.lean)

The backward circuit extraction draws on the direct upstream proof of L-meta-3967 by leoli001031-blip. The independent finite search uses the live-signature representation. [Upstream L-meta-3967](https://github.com/open-goat/pequalnp-proofs/pull/8875)

## Reproduce

From a checkout of this research branch with the project's pinned Lean toolchain and the Mathlib cache, run the following command from the repository root.

```sh
python3 research/L-meta-1774/finite-witness/verify.py --jobs 3
```

The command regenerates all 256 proof modules, checks them in dependency order, then checks the final statements and prints their axiom audits. It keeps the generated files and logs in `lean/.lake/build/finite-witness-1774`. An alternative build directory can be supplied with `--build-dir`. [Case generator](certify94.py) · [Successor indices](index94.py) · [Lean proof generator](emit94.py) · [Replay command](verify.py)
