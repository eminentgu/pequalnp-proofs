# Moving a sound operand to the output

A wire is sound if every input on which it is true contains a graph edge. In a least binary AND/OR circuit, suppose an OR gate has operands a and b, the gate is unsound and b is sound. The theorem `exchange_or` bypasses the gate with a, then appends b as an OR operand at the output. On inputs where b is false, the original OR agreed with a. Where b is true, the required output is true. Bypassing the gate can only decrease the values at surviving gates, so each surviving unsound gate corresponds to a distinct old unsound gate. The newly appended output is sound. This gives the same size and strictly fewer unsound gates for arbitrary fanout. [Lean source](SafeTail.lean)

Choosing a least circuit that minimizes its number of unsound gates rules out these mixed ORs. A least circuit already excludes an AND with a sound child, since replacing it by that child can enlarge its output only on positive inputs. The resulting `CleanReaders` predicate says that every gate reading a sound wire is itself a sound OR. The theorem `sound_above` propagates that property along every path. [Internal AND bypass](InternalSoundAnd.lean)

For nonempty graphs, the project previously established existence of a least circuit in its `TopForm`, preserving the count of unsound AND gates. It also proved that a sound non-output gate in this form has a unique reader, a sound OR. The direct exchange here additionally gives a rewrite at a specified mixed OR and a strictly decreasing count of all unsound gates. [L-meta-1501](../../lean/PEqualNP/Outside/L_meta_1501.lean) · [L-meta-1491](../../lean/PEqualNP/Outside/L_meta_1491.lean)

After compiling the modules in `wrong-supports.md`, run from the repository root

```sh
proof_dir="$(pwd)/research/L-meta-3566"
cd lean
lake build PEqualNP.Outside.L_meta_1491
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1" -o "$1/SafeTail.olean" "$1/SafeTail.lean"' sh "$proof_dir"
```

## The exchange can create a defective owner

[MixedOwnershipExample.lean](MixedOwnershipExample.lean) checks the physical bypass on the seven-vertex tree with edges ab, bc, cd, be, cf and bt. Put A = a OR c, Q = b OR d and B = b AND (a OR t). B is sound. In the original circuit let h = (A OR B) AND Q, and let the output be the OR of b AND (h OR e) and c AND (h OR f). The exchange bypasses A OR B with A and connects B to the output. B is necessary for this particular reconnection, since bypassing alone loses the edge bt.

Both eleven-gate circuits compute the stated graph, and every AND in both owns an edge. Every original AND has a star profile. The original h owns cd, and its ancestor B prevents h from owning ab. After the exchange h owns both ab and cd, two disjoint edges. A correct seven-gate competitor is provided explicitly, so the example tests the domain of the exchange and leaves open the effect of minimum size.

This distinguishes two witness directions in L-meta-1774. To prove descent via its upstream exchange reduction, a replacement must stay within budget, every replacement AND must still own a graph edge, and each replacement owner that is nonstar must map injectively back to a surviving old owner whose old owned edges contain its new owned edges. Obtaining pure OR paths at the two operands of a gate with an ownership witness does not prove this containment. A sound AND's two sets of pure raw inputs form a complete bipartite subgraph and hence a star in a four-cycle-free graph, while an unsound AND can own disjoint edges and be masked at higher gates. [Upstream exchange statement](../../lean/PEqualNP/Outside/R_meta_1774_642.lean)
