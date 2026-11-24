# L-meta-2583 — read-1 replacement for incidence circuits

For a projective plane of order (q), write (N=q^2+q+1). Inputs are one bit per point and one bit per line. The function asks whether any selected point lies on any selected line. In a read-1 circuit, each minimal true input admits a single proof tree reading both of its variables at most once.

`Threshold.lean` proves the desk statement on each fixed plane equivalent to an unrestricted lower bound of (N(q+2)-1) gates. The equivalence holds pointwise for each circuit. The unrestricted lower bound is open here.

| Verified result | Source |
| --- | --- |
| The prime implicants are exactly the incident point–line pairs, even for a rectangular incidence relation. Joint READ-k can be tested on just those pairs. | [IncidenceReadPairs.lean](IncidenceReadPairs.lean) |
| A line-star circuit computes incidence, meets the project's AO2 and read-1 conditions, and uses exactly (N(q+2)-1) gates. | [LineStarUpper.lean](LineStarUpper.lean) |
| Every read-1 realization needs at least that many gates. The incidence graph has (N(q+1)) edges, girth at least six, and minimum vertex cover (N). | [PlaneReadOne.lean](lower/PlaneReadOne.lean) |
| A size-preserving replacement exists if and only if the given circuit meets the threshold. | [Threshold.lean](Threshold.lean) |
| Every unrestricted AO2 circuit computing the plane incidence function uses at least (3N-1) gates. | [UnrestrictedRange.lean](lower/UnrestrictedRange.lean) |
| For an explicit Fano plane, any counterexample must use 20–26 gates, have nested ANDs, and lack a joint read-1 proof tree on at least one incident pair. | [FanoReadOne.lean](fano/FanoReadOne.lean) |

The upper bound ORs the (q+1) points on each line, ANDs that term with the line variable, and ORs the (N) results. Each incident pair has a joint witness in the compiled circuit. For the sharp lower bound on read-1 circuits, we use the existing C4-free cover theorem L-meta-2237 and the projective-plane counting results L-meta-1955. The separate unrestricted estimate uses L-meta-2988.

The Lean 4.36.0 files use upstream revision `369e26de683a661a3d3e2a685f8a651444912c50`. From the `lean/` directory of this branch, after fetching the Mathlib cache, run:

```sh
python3 ../research/L-meta-2583/replay.py
```
