# Partial result for L-meta-1593

Let T be a minimum vertex cover of G and let z belong to T. Deleting all edges incident to z leaves T without z as a minimum cover. Under the cubic-degree assumptions of L-meta-1593, the deletion lowers the vertex-cover circuit construction's gate budget by exactly four.

The remaining question concerns the minimum size of an unrestricted fan-in-two AND/OR/NOT circuit. Let the savings of a minimum circuit be the difference between the cover budget and its actual size. A vertex for which these savings stay the same or increase after deletion would give the requested four-gate lower bound. The local theorem formalizes this arithmetic condition. The original lower bound remains open in this work.

The accompanying experiment constructs one 24-vertex cubic graph of girth seven and verifies its circuit and each of the 24 deletion circuits by symbolic DNF expansion. The full construction uses 49 gates. Every deletion construction uses 45 gates.

From the repository's `lean/` directory, with its pinned Lean 4.36.0 and Mathlib installed, run both checks.

```sh
lake env lean ../research/L-meta-1593/CubicCoverDeletion.lean
python3 ../research/L-meta-1593/cubic_cover.py
```
