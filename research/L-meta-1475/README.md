# The order-four plane, with its seven subplane triples available

The full incidence circuit search allows 124 binary AND/OR gates. Select rows 0, 3, …, 18 and the seven columns congruent to 2 modulo 3 in the project's cyclic labelling of the 21 lines. Each selected point lies on three selected lines, and any two selected points share exactly one of them.

`FanoPrefix.lean` constructs fourteen binary OR gates. Seven gates form pairs of line inputs and seven complete the triples. The kernel proof `prefix_exists` identifies the value of every intermediate wire for every 42-bit input. The theorem `triples_form_fano` verifies the incidence counts.

These fourteen intermediate wires and the 42 raw inputs are available to a 110-gate residual search. Appending such a circuit would give the desired 124-gate witness. The residual search is open. The file can be checked from the project's `lean` directory with `lake env lean ../research/L-meta-1475/FanoPrefix.lean`.

`python3 one_gate_gap.py` constructs a reference circuit with exactly 111 residual gates after the same prefix. It propagates minimal positive input sets through every gate and checks that the output has precisely the 105 point-line incidences as its minterms. This verifies the baseline on all Boolean inputs and leaves one gate to save.
