# Removing binary gates when fixing inputs

The upstream module `PEqualNP.Outside.L_meta_2904` implements constant propagation and rewiring for the project's circuit model. Its `gate_elim` theorem proves a reduction in the total number of gates. The modules here use its simplifier to count every AND or OR gate while allowing any number of NOT gates.

`PinOne.lean` uses a wiring diagram whose entries are constants or indices into the new input. Two witness rows are *tracked* if every coordinate at which they disagree has a constant entry in the diagram. Assume that their original circuit outputs disagree, and that the circuit still takes both output values after specialization. The theorem `Triple2836.Pinning.pin_circuit` constructs a new fan-in-two circuit that computes the specialization and has at least one fewer non-NOT gate.

The budget proof follows the two rows through the original gate list. While every non-NOT gate is kept, any wire on which the rows disagree must specialize to a constant. A NOT gate propagates this invariant through its first pin. For AND or OR, any unequal output requires an unequal input. That input specializes to a constant, so the upstream simplifier eliminates the gate. Thus if zero charged gates were saved, the output would specialize to a constant, contrary to the hypothesis. The statement permits out-of-range pins, zero- or one-input AND and OR, any NOT arity allowed by the project, shared gates, and arbitrary NOT chains.

`PinTwo.lean` applies the theorem to input 4 and then 0, using the witness rows in the adjacent `Restrictions.lean`. The intermediate circuit still accepts the helper $x_0\lor x_j$. The final wiring diagram replaces it by the raw input $x_j$. The final theorem uses the non-NOT gate count in the reduction R-meta-2836-412.

`PairPins.lean` treats all three two-OR input encodings. Where the missing raw input is 0, it fixes 4 and then the helper $x_0$. Where the missing raw input is 4, it fixes 0 and then the helper $x_4$. In the latter cases the other helper is $x_4\lor x_1$ or $x_4\lor x_5$. The output in every case is the same seven-variable graph. `CheckedPinTwo.lean` packages these constructions and the triple construction as the exact `pinTwo` premise in the uniform reduction. `CheckedPinTwoCtor.lean` proves the same statement using the computational discriminator `h.op.ctorIdx != GateOp.not.ctorIdx` in the gate count. Its single parameter $k$ encodes the first two pair cases at 0 and 4 and a three-input OR at every other vertex.

From the upstream repository's `lean/` directory, with `PEqualNP.Defs.MetaComplexity` built, run the following command. Change the script path to the location of this research directory.

```sh
lake env python3 ../research/L-meta-2836/triple/pinning/replay_pinning.py
```

The replay uses a temporary directory, compiles the unchanged definitions and proofs it needs from the upstream source, and checks the research files with one Lean thread.
