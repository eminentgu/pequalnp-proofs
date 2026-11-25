# Gate substitutions on edges and maximal independent sets

For a graph edge function, the minimal positive assignments select the two endpoints of an edge. The maximal negative assignments select maximal independent sets. In this directory, gate supports are evaluated in the original circuit on those assignments.

- `BatchExchange.lean` cuts any number of gates, including gates with shared outputs. If the circuit was minimum and the genuine edges it loses form a graph L, the number cut is at most |E(L)| + τ(L).
- `SupportPacking.lean` assigns distinct resources to all gates of a minimum circuit. For every chosen cover T, a gate can receive an edge where it fires, or a vertex of T incident to such an edge.
- `InducedSupport.lean` gives a lower bound in the other direction on induced subgraphs. For any W, let A be the gates that are true on some edge of G[W] in the original circuit. There is an exact circuit for G[W] of size |A|. This result applies to every correct monotone circuit. Consequently, any lower bound known for G[W] applies to |A|.
- `SignedPivots.lean` shows that, in a minimum circuit, each replacement of a gate by an earlier wire fails on a genuine edge or a maximal independent set. It identifies both wire values and the erroneous output on the witness.
- `SignedExchange.lean` repairs an arbitrary monotone alternative D. If L consists of its missed edges and F consists of the maximal independent sets it accepts, there is an exact circuit of size at most |D| + |E(L)| + τ(L) + ∑_{I∈F} |V∖I|. A clause over V∖I rejects I and its subsets while preserving every positive graph input.
- `NegativePacking.lean` uses simultaneous gate replacements. Suppose each selected gate has an earlier replacement wire that is true whenever the original gate is true on a genuine edge. The gates inject into distinct pairs (I,v), where I is a maximal independent set on which the replacement turns the old gate from false to true, and v lies outside I. This applies in particular to selecting either input independently at every AND gate in a minimum backward-reading circuit.

The direction of these matchings alone does not give the numerical lower bound for all G. `SupportPackingExample.lean` provides a kernel-checked four-vertex path example for the constraints using positive edges and singleton inputs. `affine_pair_promise.py` checks a stronger obstruction on the 128-vertex incidence graph of the points and nonvertical lines over GF(8). Its 401-gate circuit passes all 8,257 assignments of size at most two, and all 401 gates can receive distinct genuine edge labels. The target size for the exact function is 575. Two points (0,0) and (0,3) together with the line y=1 form an independent triple accepted by this circuit.

## Bounded input size

The GF(8) script checks the case of two selected vertices. The same obstruction extends mathematically to every fixed input weight k ≥ 2.

Let q = 2ʳ and take the points and the nonvertical lines of the affine plane over GF(q). There are 2q² vertices and q³ edges. Two distinct points have at most one common nonvertical line. Matching each point (x,y) to the line of slope x through it gives a perfect matching, so the cover number is q².

A monotone circuit can test incidence exactly on all assignments of weight at most two with O(q² + qr + r³) gates. For each of the four coordinates, make q ORs of the vertices with the given coordinate value. These flags give both rails of each binary digit in O(qr) further gates. On an input consisting of a point and a line every digit has its correct value and complement. Schoolbook multiplication modulo an irreducible polynomial of degree r uses O(r³) dual-rail Boolean gates, including reduction and comparison with y. Requiring the presence of both a point and a line handles inputs from a single part. The circuit is monotone on all assignments and therefore accepts every set containing an incident pair.

Assign distinct binary labels of length L = 2r+1 to the vertices. For each set of at most k−1 bit positions, hash a label to its string on those positions. Given any set of ≤k distinct vertices, start with the empty choice. Whenever two vertices still collide, add a position on which their labels differ. Each addition increases the number of distinguishable classes, so one of the enumerated hashes is injective on that set.

For a fixed hash, evaluate a copy of the two-vertex circuit for each point-color and line-color pair, setting every input outside those two buckets to zero. OR the outputs for all color pairs. This accepts every set containing an edge. If the selected vertices are independent and the hash is injective on them, each copy sees at most one point and one line, so every copy rejects. AND the outputs of all hashes. For all inputs of weight at most k the result equals the graph function. It uses Oₖ(Lᵏ⁻¹ (q² + qr + r³)) gates, since each hash has at most 2ᵏ⁻¹ colors. This is o(q³) as r tends to infinity with k fixed. Consequently no fixed maximum weight suffices to derive the exact-function lower bound solely from correctness on those inputs.

## Reproduction

From the repository root, the following commands build the Lean results into a fresh directory and run the finite diagnostic.

```sh
root=$(pwd)
out=$(mktemp -d)
cd "$root/lean"
lake build PEqualNP.Outside.L_meta_2668 PEqualNP.Outside.L_meta_2573 PEqualNP.MetaComplexity.Helpers.LocGraph
lake env sh -c '
  set -eu
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$2"
  for m in Equivalence BatchExchange SupportPacking InducedSupport SupportPackingExample SignedPivots SignedExchange NegativePacking
  do
    lean -R . -o "$1/$m.olean" "$m.lean"
  done
' sh "$out" "$root/research/L-meta-3566"
python3 "$root/research/L-meta-3566/affine_pair_promise.py"
```
