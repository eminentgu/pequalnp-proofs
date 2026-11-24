# The monotone premise of L-meta-2836

The first premise of the uniform reduction in PR #8269 is a consequence of
the merged L-meta-1922 theorem. That theorem gives a 15-gate lower bound for
monotone circuits even when the original nine raw inputs are supplemented
by a free `x0 ∨ x4` signal. Its lower bound already applies to 24 specified
assignments. [Uniform reduction](https://github.com/open-goat/pequalnp-proofs/pull/8269)
and [public predecessor](https://github.com/open-goat/pequalnp-proofs/blob/f5b0e4e43b029c6b9fc316bbc8fdf6fcfa4c8a46/lean/PEqualNP/Outside/L_meta_1922.lean#L7515).

For each bank in the premise, prepend its second OR to the proposed circuit.
This produces a circuit on the ten inputs of L-meta-1922. Its first gate
provides the wire at index 10. All later gate indices align with the original
circuit on eleven inputs. Redirect each use of the bank’s constant-false
slot, including the circuit output, to index 24. A circuit with ten inputs
and at most fourteen gates has no wire at index 24, so every such read
evaluates to false. This also covers forward references and default reads.
The new circuit is monotone, uses at most fourteen gates and agrees with the
target on each of the 24 predecessor assignments, a contradiction.

`MonotoneTransport.lean` contains the wire simulation, the finite row checks
and the cost bound. `MonotoneExact.lean` exports `from_raw_statement`, with
the exact printed statement of L-meta-1922 as its hypothesis and the
verbatim first premise of PR #8269 as its conclusion. `CheckedMonotone.lean`
imports the public predecessor and proves the unconditional theorem
`PEqualNP.Research2836.Monotone.checked`.

Run `python3 replay.py` in this directory from a checkout with the project’s
Lean 4.36.0 toolchain and standard Mathlib cache. The script rebuilds the
shared predecessor from its SHA-256-verified public source, checks the
three local files in dependency order with one Lean worker, and prints the
axioms used by the conclusion. If this directory was copied separately,
supply `--project /path/to/pequalnp-proofs`.
