# Petersen edge function with two OR inputs

L-meta-3561 gives a circuit eleven input positions. Position four is fixed to zero. The two added positions contain x₀ ∨ x₄ and x₄ ∨ x₁. The target is the edge function of the nine-vertex Petersen graph with one vertex removed.

`EncodedBank.lean` proves that any fan-in-two AND/OR/NOT circuit computing the target induces a normalized computation that uses all ten nonconstant signals. For a normalized computation with k gates and t negations, k is at least 9 + t. A circuit with at most thirteen gates therefore leaves only five negation counts to check, from zero through four. The result concerns negations retained in the normalized computation.

The proof reuses the live-signal extraction and paired assignments from the project's public Petersen certificates. The `necessarySignals` lemma checks, for each input signal, that a positive and a negative example become indistinguishable when the signal is omitted. `bankTarget` verifies the encoding against the original circuit semantics. The final result is `extractedBank`.

Run `lake env lean ../research/L-meta-3561/EncodedBank.lean` from the project's `lean` directory to check the proof.

## Checking the five cases

`SearchCore.lean` proves that exclusion of all five roots implies the required circuit lower bound. Its search and soundness proof are adapted from the public Petersen checker. `CheckRoots.lean` executes the search using Lean's interpreter. A computational result from this command still needs a kernel certificate for the upstream submission.

From the checkout's `lean` directory run

```sh
lake env bash -c '
  set -eu
  sources=$(cd ../research/L-meta-3561 && pwd)
  output=$(mktemp -d)
  export LEAN_PATH="$output:$LEAN_PATH"
  cd "$sources"
  for module in EncodedBank SearchCore; do
    lean -j1 -R . -o "$output/$module.olean" "$module.lean"
  done
  lean -j1 --run CheckRoots.lean
'
```

## Structural lower bounds

`CofactorPrune.lean` proves that an encoded circuit needs at least 13 gates, using the merged L-meta-2913 checker. It also rules out 26 unordered first-AND operand pairs in the sampled live computation. Build the prerequisite with `lake build PEqualNP.Outside.L_meta_2913`.

`CubicObstruction.lean` proves that every correct monotone extension has a restriction to three independent wires equal to their AND. Consequently a disjunction of terms of degree at most two cannot compute that extension. It also checks a 13-gate witness for the restricted eight-input graph in which input wires 0 and 1 are both reused.

`ReadOnceKW.lean` develops a rectangle obstruction for saturated monotone traces. `SignedReadOnceKW.lean` proves `no_four_nots`, excluding the 13-gate case with four retained negations. These three modules and the cofactor proof all import `EncodedBank`. Check them using the same temporary output directory and `LEAN_PATH` as above.

## Kernel certificates for two, three and four negations

The theorems `Memo2.root`, `Memo3.root` and `kw_impossible_four` exclude normalized computations with exactly two, three and four retained negations. The two-negation certificate checks 428 search states and the three-negation certificate checks 106. Each finite check runs with `decide +kernel`. The four-negation proof uses the rectangle obstruction directly. The remaining cases have zero and one retained negations.

To check these certificates, use the temporary output directory in the command above and run the following loop from the research directory with the same `LEAN_PATH`.

```sh
for module in EncodedBank SearchCore SignedReadOnceKW VerifiedCore Memo2Data CheckedTwo CheckedThree Root4; do
  lean -j1 -R . -o "$output/$module.olean" "$module.lean" || exit 1
done
```

## Checking several rectangle obstructions at once

`BulkKW.lean` proves `BulkKW.excludes_sound`. A saturated trace must assign a distinguishing wire to each positive–negative sample pair. All pairs assigned to one wire form a rectangle. Four pairs can force two different wire labels onto the same intersection. The checker tests many such configurations at once by putting their differences in bit masks and accumulating the masks over the wires.

After compiling `VerifiedCore` as above, run `lean -j1 -R . BulkKW.lean` from the research directory with that output directory in `LEAN_PATH`.

## Restricting input x₄ to zero

`MacroDominance.lean` proves a substitution rule for a monotone suffix. A replacement signal may cover every required positive success and introduce no failure on the selected negative assignments. `ExtremalFirst.lean` uses the merged L-meta-2913 lower bound to exclude 27 different first AND gates. The list includes 18 pairs of raw inputs and 9 pairs that use one of the two encoded OR inputs. The theorem permits any subset of the old signals to be discarded.

`PortableMacro.lean` proves a related rule on the original input bank. If a monotone prefix can be shortened while preserving the needed positive and negative assignments, it suffices to exclude a circuit on the original bank with at most 12 gates.

To check the first two files, build PEqualNP.Outside.L_meta_2913, then compile `MacroDominance` and `ExtremalFirst` in that order. `PortableMacro` uses `EncodedBank`.

## A monotone computation with one shared signal

`OneShareCertificate.lean` proves a structural restriction for a normalized monotone computation with at most as many gates as live inputs. At the tight budget the computation gives a read-once formula. With one extra gate it can be described by an inner formula and an outer formula in which only the inner result can occur twice. The proof counts the leaves of both formulas. A finite certificate can then exclude every possible set of inputs to the inner formula.

`covered_sound` checks such certificates with bit masks. The file ends with a kernel-checked seven-gate example. It imports `EncodedBank` and can be checked in the same temporary output directory used above.
