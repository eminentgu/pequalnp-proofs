# Petersen-minus-a-vertex circuit bound, L-meta-2114

This proof uses the project's canonical first-gate theorem. It rules out every circuit with at most fifteen gates computing this edge function. The circuit described in L-meta-2114 is one such circuit by its size and computation hypotheses.

The nine direct theorems and the original first-gate reduction are in upstream commit `2a70ad26c5fa2ad93aec5ded5dd437cdfb481185`.

| Part of the proof | Upstream result |
| --- | --- |
| Replace a circuit by a representative of at most the same size | L-meta-2440 |
| Lower bound of 16 gates after either representative NOT | L-meta-2442 |
| Lower bound of 16 gates after any of the six representative ANDs | L-meta-2444 |
| Lower bound after OR on (0,1), (0,2), (0,3), (0,4), (0,6) or (4,6), respectively | L-meta-1673 through L-meta-1678 |
| Combine the first-gate bounds for this exact desk statement | R-meta-2114-713 in [PR 12172](https://github.com/open-goat/pequalnp-proofs/pull/12172), adapted from R-meta-670-713 |

`Proof.lean` supplies all four premises of the reduction and derives exactly the posted L-meta-2114 statement. The lemma `PetersenFirstGate.orBound` proves the exact fourth premise printed by the verifier. Its proof uses list membership and the six corresponding published theorems. All first-gate certificates and the normalization argument are the work of their upstream authors.

## Reproduction

From the repository's `lean` directory use the pinned toolchain and Mathlib.

```sh
lake exe cache get
lake build +PEqualNP.Outside.L_meta_2440 +PEqualNP.Outside.L_meta_2442 +PEqualNP.Outside.L_meta_2444 +PEqualNP.Outside.L_meta_1673 +PEqualNP.Outside.L_meta_1674 +PEqualNP.Outside.L_meta_1675 +PEqualNP.Outside.L_meta_1676 +PEqualNP.Outside.L_meta_1677 +PEqualNP.Outside.L_meta_1678 +PEqualNP.Outside.R_meta_2114_713
lake env lean ../research/L-meta-2114/Proof.lean
```

The current desk row authorizes only `PEqualNP.Defs` and Mathlib for a direct submission. This branch provides the modular proof for review.

## Local verification on 25 November 2026

The project verifier returned `ACCEPTED (reduce)` for the exact file in PR 12172. It rechecked 1,661 constants using the definitions from the submission base. The normalized four child statements match L-meta-2440, L-meta-2442, L-meta-2444 and L-meta-2446.

All nine direct proof modules were recompiled from source with the pinned Lean toolchain. An independent Lean audit matched `PetersenFirstGate.orBound` against the published grouped OR statement and `PEqualNP.Outside.L_meta_2114` against the exact desk statement. Both reported exactly `[propext, Classical.choice, Quot.sound]` as their transitive axioms. A second composition using the earlier reduction R-meta-670-713 also checked the same final statement.

| Audited source | SHA-256 |
| --- | --- |
| Single-file reduction in PR 12172 | `9f5650f83a06cb560ace9f70059ff57beab1577323de8afcee62b0c8b6462b0f` |
| Complete modular proof in this directory | `4e60a9f1bfcf73e9f4caed15ca70e10da6527a08c0d3d187526e0410e2a986d8` |

The project records its own acceptance and merge status on [PR 12172](https://github.com/open-goat/pequalnp-proofs/pull/12172) and the [L-meta-2114 desk page](https://pequalnp.com/lemma#L-meta-2114).
