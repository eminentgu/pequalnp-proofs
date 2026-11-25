# L-meta-4873 shared prefix

The reduction searches for two wires H and G in one 14-input circuit with at most 24 gates. Raw wire 2 selects the point with label 2. When that point is absent, H must compute incidence. When it is present, H OR G must compute incidence. G must vanish on the two marked singletons. Gates in the prefix can feed both wires, and G is unconstrained wherever H already accepts, except for the explicit singleton tests.

Given such a prefix, append OR(H,2), OR(H,G), and the AND of their outputs. Distributivity gives the required output value. The prefix proposition enforces distinct gate inputs and references to available wires. The Lean proof in Extension.lean appends one gate, proves that all earlier wires keep their values, and verifies topology and distinctness. Applying it three times proves the submitted reduction. It uses propext, Classical.choice and Quot.sound.

## Reproduction

From the project’s pinned Lean environment run `lake env lean /absolute/path/to/Extension.lean`. From this directory run `python3 star_prefix.py` and `python3 repair.py`. Both Python scripts use the standard library.

The control uses six point stars to compute H in 23 gates. Two more gates compute G as the union of the three lines through point 2. The resulting 28-gate circuit passes all 16,384 inputs and both marked predecessor tests. This construction was previously described in [PR 10812](https://github.com/open-goat/pequalnp-proofs/pull/10812).

Starting from this particular 25-gate prefix, the first script tries all 650 ways to remove a gate by redirecting its uses to an earlier wire. The second also permits changing any one surviving gate to an arbitrary AND or OR of two distinct earlier wires. For each changed gate, forcing it first to zero and then to one determines which replacement truth bits can satisfy the 60 boundary tests. Surviving candidates are checked on all 16,384 assignments. Neither neighborhood yielded a 24-gate prefix. Other topologies and larger changes remain open.
