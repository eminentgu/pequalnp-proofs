# L-meta-2836 and its second case, L-meta-3561

`ResearchConclusions.lean` gives the full 13-gate lower bound across all four input encodings in L-meta-2836. It applies the three verified components to the locally checked uniform reduction submitted in [PR #8269](https://github.com/open-goat/pequalnp-proofs/pull/8269). The theorem for L-meta-3561 then uses the second alternative of the parent statement. Both declarations use the exact desk statements. Lean 4.36.0 reports only `propext`, `Classical.choice`, and `Quot.sound` for each theorem.

| Declaration | Role |
| --- | --- |
| `PEqualNP.Research2836.Monotone.checked` | Rules out candidates containing no NOT gate using upstream L-meta-1922. |
| `Triple2836.checkedPinTwoCtor` | Specializes the 13-gate candidates containing a NOT to a common nine-input cofactor with at most ten non-NOT gates. |
| `Triple2836.checkedThetaBound` | Removes the two dummy inputs and applies upstream L-meta-2960 to the seven remaining variables. |
| `PEqualNP.Research2836.full2836` | Fills all three hypotheses in R-meta-2836-412. |
| `PEqualNP.Research2836.exact3561` | Selects the encoded circuit bank with raw input 4 fixed to false and the helpers $x_0\lor x_4$ and $x_4\lor x_1$. |

## Replay with the upstream libraries

The following checkout contains all three upstream dependencies and the research proof. It uses Lean 4.36.0 via elan. From a directory for the new checkout, run

```sh
git clone --branch research/L-meta-2836 --single-branch https://github.com/eminentgu/pequalnp-proofs.git pnp-replay
cd pnp-replay
git switch --detach db5478068992f2720f930714dab72ca3b2069848
cd lean
lake exe cache get
python3 ../research/L-meta-2836/parent/replay.py
```

The pinned commit includes upstream revision `df1e5f845e1fb7a44b69914f39b6dba3c3f07fa3`.

The script asks Lake to build the two upstream lower bounds and the rewiring library, then compiles the research modules in a temporary directory. It also checks `Triple2836.signedSeven`, the constructive signed B premise used by the separate 3561 reduction. A first run may spend most of its time on the two upstream numerical certificates. Lake reuses verified build artifacts on later runs.

`AcceptedReduction.lean` is the R-meta-2836-412 source that passed the project checker locally at fork commit `66753ba597a8b0659ca5b71bacfcd933c33bb027`. Its SHA-256 is `6a2bc34f83ba7b55143b59f2ea3726354a5dd7311daf5f6c7f52da4592849ce0`. It is bundled because the upstream snapshot above already contains both numerical lower bounds while the R-meta-2836-412 file is still carried separately in the research branch. [Accepted reduction source](https://github.com/eminentgu/pequalnp-proofs/blob/66753ba597a8b0659ca5b71bacfcd933c33bb027/lean/PEqualNP/Outside/R_meta_2836_412.lean)

## Direct proof for L-meta-3561

The two hypotheses of [PR #8765](https://github.com/open-goat/pequalnp-proofs/pull/8765) are the exact statements of the merged L-meta-1922 and L-meta-2960. `Closed3561.lean` applies that reduction directly to the two upstream theorems. From the branch checkout containing this file, run these additional commands in the `lean/` directory.

```sh
lake build PEqualNP.Outside.R_meta_3561_214 PEqualNP.Outside.L_meta_1922 PEqualNP.Outside.L_meta_2960
lake env lean ../research/L-meta-2836/parent/Closed3561.lean
```

The resulting theorem is `PEqualNP.Research.Closed3561`. Its axioms are `propext`, `Classical.choice`, and `Quot.sound`.
