# First-gate symmetry for the labelled Fano incidence circuit

Vertices 0 through 6 are points. Vertex $7+l$ is line $l$. The pair $(p,7+l)$ is incident precisely when $(p+l)\bmod 7$ belongs to $\{0,1,3\}$. Reordering wires within a commutative gate lets us treat its inputs as an unordered pair, allowing repetition.

| First-gate inputs | Representative | Orbit size | Stabilizer size |
| --- | --- | ---: | ---: |
| Repeated input | (0, 0) | 14 | 24 |
| Distinct, both on the same side | (0, 1) | 42 | 8 |
| Incident point and line | (0, 7) | 21 | 16 |
| Nonincident point and line | (0, 9) | 28 | 12 |

Run `python3 first_gate_orbits.py` from this directory. It uses the standard library and verifies all 105 unordered input pairs, including the 14 repetitions.

The incidence graph is connected. Each pair of distinct points has a common line, and every line meets a point. Therefore any automorphism preserves the point and line sides or exchanges them. A permutation of the seven points determines at most one permutation of the lines because the seven line neighborhoods are distinct. The verifier tries all $7!$ point permutations, retaining the 168 that permute these neighborhoods. Exchanging $p$ with $7+p$ preserves incidence since $p+l=l+p$. Composing this duality with the 168 permutations gives all 336 automorphisms. The verifier checks that every permutation preserves all 21 edges and that each representative maps onto exactly the input pairs in its stated category.

To normalize a candidate, choose an automorphism taking its first pair to the representative and apply it to every input-wire reference throughout the circuit. References to gate outputs keep their indices. This renames the variables of the computed Boolean function, which is invariant under the automorphism. Gate types and circuit size are preserved. Commutativity then permits sorting both references within each gate.

If the first gate uses $(u,u)$, either operation computes $u$. Redirect its consumers and the output to $u$ and remove that gate, decrementing later gate indices. Thus a minimum circuit for the Fano function cannot start with a repeated pair. Its output also cannot be a raw input since the function is false on each singleton and true on all 21 incident pairs. When testing an exact positive gate budget, a shorter circuit for this function can be padded at the output by repeating $y\mathbin{\land}y$. The three distinct pair representatives and both gate operations therefore suffice for a search for circuits of at most that budget. An exact-size solver that forbids repeated inputs everywhere needs its own padding argument, or it must check every relevant smaller size individually.
