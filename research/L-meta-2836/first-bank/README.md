# First double-OR bank of L-meta-2836

The original graph is the Petersen graph with one vertex removed. In its
first double-OR encoding, raw input 0 is hidden. Independent raw inputs 1
through 8 and the outputs of the two gates `x0 ∨ x4` and `x0 ∨ x3` are
supplied to the candidate circuit. One additional input slot is fixed to false.

Together, the Lean-checked extraction and exclusion theorems imply that
every circuit of size at most 13 computing this encoding induces a sampled
live trace with at most one negation. This count refers to
the extracted trace. The search rules can discard irrelevant gates from the
original circuit. The zero- and one-negation cases remain open in this package.

## Checked modules

| Module | Result |
| --- | --- |
| `FirstBank` | Extracts a live trace on 414 paired samples. All ten variable signals are indispensable. The budget inequality excludes five or more negations. A signed rectangle conflict excludes four. |
| `FirstMemo3`, `FirstCert3` | Prove `FirstMemo3.root : Impossible 13 3 firstWires` with 106 internal search states. |
| `FirstMemo2`, `FirstCert2` | Prove `FirstMemo2.root : Impossible 13 2 firstWires` with 449 internal search states. |

All five modules passed a local sequential Lean 4.36.0 run. Their common
certificate checker is pinned to [eminentgu/pequalnp-proofs, commit
497d90c](https://github.com/eminentgu/pequalnp-proofs/tree/497d90c67a354aa0f43bdbf623a768e4051b8bd4/research/L-meta-3561).

## Reproduce

Run from this directory in a normal checkout of the project with Python 3.9+
and the project’s Lean toolchain installed through elan.

```sh
python3 replay.py
```

The script obtains four small Lean source files from the pinned commit. It
reads a local Git object when available and otherwise downloads that file
from GitHub. It verifies SHA-256 hashes and assembles the same three shared
modules used by the successful run. The two declaration blocks in
`SignedReadOnceKW.lean` and `VerifiedCore.lean` are joined under the original
single-module layout. The resulting file also has a pinned hash.

The checker builds the project’s standard definitions, compiles each source
into a fresh temporary directory with one Lean worker, and reports the
axioms of the extraction and three exclusion theorems. A prepared Mathlib
cache considerably reduces setup time. To verify only the public sources
and their assembly, run `python3 replay.py --sources-only`. Use
`--project /path/to/pequalnp-proofs` if this directory was copied outside
the checkout.

## Independent finite calculation

`python3 bank_orbits.py` enumerates 512 raw assignments and the 12 graph
automorphisms. The second and third banks have equivalent labeled rows. No
permutation of the ten independent inputs identifies the first bank with
the other two. Among the 390 distinct positive rows, the most frequent
column is true 298 times in the first bank and 294 times in each of the
others. Even complementing individual columns preserves a distinguishing
invariant, the smallest minority count in any column (92 versus 96).

The same script checks all sixteen points of the following four-input restriction.
Set raw input 1 to `a`, raw input 5 to `b`, the two OR outputs to `c,d`,
and all remaining inputs to false. Every monotone extension of the edge
function must then compute `(a ∨ b) ∧ c ∧ d`. Each true face point dominates
the encoding of either {0,1} or {0,5}. Each false face point lies below the
encoding of one of the independent sets {1,3,5}, {1,4,5}, or {0}. This part
is a direct monotonicity argument with Python-checked witnesses.
