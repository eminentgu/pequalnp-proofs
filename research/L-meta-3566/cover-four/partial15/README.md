# A sixteen-assignment lower bound for row 15

The sampled Boolean function has nine input variables. A positive example is any one of the bit masks `17, 65, 34, 130, 20, 36, 72, 136, 264`. The negative masks are `13, 26, 41, 56, 133, 196, 496`. Bit zero represents vertex zero. Every sample excludes the simultaneous presence of vertices zero and one.

The theorem `VertexPeel.CoverFour.Case15Partial.lower` asserts that every binary monotone circuit assigning the indicated values on these sixteen inputs has at least twelve gates. It applies regardless of the output on the other 496 inputs. The positive examples are nine edges of row 15 and the negatives are independent sets in row 15.

Run `python3 verify.py --jobs 2` in this directory within a proof checkout, or give `--project /path/to/checkout/lean`. The generator writes into the Lean build directory by default. The same command verifies the row-15 false cofactors against the previously proved lower bounds for rows 11 and 12. It also checks the sampled outputs against the row-15 edge predicate. Add `--reuse` to reuse current Lean modules in the same build directory.

The proof checks 9,577 states and 27,211 feasible transitions across 155 generated Lean modules. At the root, every one of the nine input signatures is forced by a pair of sample rows. Lean checks the root proof and reports its dependencies with `#print axioms`.

The live-wire checker and search scheme are based on the [earlier finite-witness proof](https://github.com/eminentgu/pequalnp-proofs/tree/2862b340e48a60017bb500110105597294c8fec9/research/L-meta-1774/finite-witness). Its circuit-to-live-plan extraction credits [upstream PR 8875](https://github.com/open-goat/pequalnp-proofs/pull/8875).
