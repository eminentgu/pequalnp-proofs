# Finite tests for L-meta-2836

Number vertex masks from 0 through 511, with vertex 0 in the low bit. The target is true if a mask contains an edge of the nine-vertex graph in the problem. All encodings keep their eleven physical wire positions. The three double-OR encodings come first, in the order in the gap, followed by the triple-OR encodings with third vertex 1, 2, 3, 5, 6, 7, or 8.

## Which rows to use

The twelve edge masks and twelve maximal independent sets determine every monotone response by inclusion. They admit a seven-gate counterexample with a NOT gate on each double-OR encoding. Put y = x0 ∨ x4. The response is

```
¬(((x1 ∨ x3) ∧ (x5 ∨ x7)) ∨ (y ∧ (x2 ∨ x7))).
```

Each double encoding supplies y on wire 9. Each triple encoding has raw wires 0 and 4 and can build y in an eighth gate. The circuits accept the empty mask, and exhaustive evaluation finds they disagree with the target on 398 of 512 masks.

The enlarged tests use all 58 independent sets and all 75 positive masks of weight at most three. Every nonconstant input of every double-OR encoding has a pair of these masks which differ only at that physical address. Every original raw input of each triple-OR encoding has such a pair. Its auxiliary OR is optional. The Lean theorem `gate_reads_required` concludes that some gate must read each required physical address in any circuit passing these tests. It applies to all gate operations and all circuit sizes. `passes_of_correct` links the tests to the original all-input specification.

## Files

- `FiniteSamples.lean` features the explicit test sets, witness pairs, native project circuits, the monotone extremal argument, and necessity of an input read. It imports the project’s circuit definitions and Mathlib.
- `finite_probe.py` enumerates inexpensive signed and monotone formulas, solves a weighted cover on the 24 extreme rows, and checks every model on all 512 inputs.
- `sample_rows.py` constructs the 133 rows and finds witnesses for every required physical address. `make_fixture.py` prints the matching Lean data.
- `signed_probe.py` traverses the finite live-signal states on the enlarged tests. It prunes states where a positive and negative row coincide and uses signed rectangle constraints when the remaining binary gates form a read-once formula. The Python counts are computational research evidence. The Lean file separately verifies the test set, wire necessity, and extremal counterexample.

## Reproduce

From the project’s Lean directory, substitute an absolute source path for FILE.

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 FILE
```

From this directory, using Python 3.10 or later with its standard library:

```sh
python3 finite_probe.py
python3 sample_rows.py
python3 monotone_double.py
python3 ../triple/monotone_search.py 1 2 3 6
python3 signed_probe.py d405 all 4,3,2,1
python3 signed_probe.py t1 all 4,3,2,1
python3 signed_probe.py t1 no-seed 5,4,3,2,1
```

The ten nonconstant, indispensable double-OR inputs allow up to four NOTs in the normalized 13-gate trace. The same bound applies when the triple seed is used. With only the nine raw inputs at the root, the extra NOT count five must also be tested. A no-seed run is identical for all choices of the third vertex.

### Search counts

The following are expanded ordinary live states. Each positive NOT-count run terminated without reaching the target. Triple entries retain the auxiliary initially. The common no-seed case has 12,782, 3,548, 146, 141, and 0 expanded states at one through five NOTs. The monotone lower bound does not follow from these counts.

| Encoded inputs | 1 NOT | 2 NOTs | 3 NOTs | 4 NOTs |
| --- | ---: | ---: | ---: | ---: |
| d043 | 3,047 | 525 | 106 | 0 |
| d401 | 2,855 | 518 | 106 | 0 |
| d405 | 2,855 | 518 | 106 | 0 |
| t1 | 3,331 | 463 | 58 | 0 |
| t2 | 3,960 | 652 | 58 | 0 |
| t3 | 3,513 | 460 | 79 | 0 |
| t6 | 3,604 | 582 | 58 | 0 |

The monotone search on the 24 extremal rows visits 124,336, 108,616, and 108,616 states on the three double-OR banks, and 323,565 states without a seed. All four return false. The wrapper imports the adjacent monotone researcher’s checker and changes only the initial input bank.
