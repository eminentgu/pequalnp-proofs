# L-meta-2836 and its second case, L-meta-3561

`ResearchConclusions.lean` gives the full 13-gate lower bound across all four input encodings in L-meta-2836. It applies the three verified components to the accepted uniform reduction R-meta-2836-412. The theorem for L-meta-3561 then uses the second alternative of the parent statement. Both declarations use the exact desk statements. Lean 4.36.0 reports only `propext`, `Classical.choice`, and `Quot.sound` for each theorem.

| Declaration | Role |
| --- | --- |
| `PEqualNP.Research2836.Monotone.checked` | Rules out candidates containing no NOT gate using upstream L-meta-1922. |
| `Triple2836.checkedPinTwoCtor` | Specializes the 13-gate candidates containing a NOT to a common nine-input cofactor with at most ten non-NOT gates. |
| `Triple2836.checkedThetaBound` | Removes the two dummy inputs and applies upstream L-meta-2960 to the seven remaining variables. |
| `PEqualNP.Research2836.full2836` | Fills all three hypotheses in R-meta-2836-412. |
| `PEqualNP.Research2836.exact3561` | Selects the encoded circuit bank with raw input 4 fixed to false and the helpers $x_0\lor x_4$ and $x_4\lor x_1$. |

## Replay with the upstream libraries

Use the project's Lean toolchain and a checkout of `open-goat/pequalnp-proofs` containing `L_meta_1922.lean`, `L_meta_2904.lean`, and `L_meta_2960.lean`. The sources are present at upstream commit `df1e5f845e1fb7a44b69914f39b6dba3c3f07fa3`. Place this research directory next to the upstream `lean/` directory, keeping the relative paths of `monotone/`, `triple/`, and `parent/`. From the upstream `lean/` directory, run the following command.

```sh
python3 ../research/L-meta-2836/parent/replay.py
```

The script asks Lake to build the two upstream lower bounds and the rewiring library, then compiles the research modules in a temporary directory. It also checks `Triple2836.signedSeven`, the constructive signed B premise used by the separate 3561 reduction. A first run may spend most of its time on the two upstream numerical certificates. Lake reuses verified build artifacts on later runs.

`AcceptedReduction.lean` is the accepted R-meta-2836-412 source at fork commit `66753ba597a8b0659ca5b71bacfcd933c33bb027`. Its SHA-256 is `6a2bc34f83ba7b55143b59f2ea3726354a5dd7311daf5f6c7f52da4592849ce0`. It is bundled because the upstream snapshot above already contains both numerical lower bounds while the R-meta-2836-412 file is still carried separately in the research branch. [Accepted reduction source](https://github.com/eminentgu/pequalnp-proofs/blob/66753ba597a8b0659ca5b71bacfcd933c33bb027/lean/PEqualNP/Outside/R_meta_2836_412.lean)
