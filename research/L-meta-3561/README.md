# Petersen edge function with two OR inputs

L-meta-3561 gives a circuit eleven input positions. Position four is fixed to zero. The two added positions contain x₀ ∨ x₄ and x₄ ∨ x₁. The target is the edge function of the nine-vertex Petersen graph with one vertex removed.

`EncodedBank.lean` proves that any fan-in-two AND/OR/NOT circuit computing the target induces a normalized computation that uses all ten nonconstant signals. For a normalized computation with k gates and t negations, k is at least 9 + t. A circuit with at most thirteen gates therefore leaves only five negation counts to check, from zero through four. The result concerns negations retained in the normalized computation.

The proof reuses the live-signal extraction and paired assignments from the project's public Petersen certificates. The `necessarySignals` lemma checks, for each input signal, that a positive and a negative example become indistinguishable when the signal is omitted. `bankTarget` verifies the encoding against the original circuit semantics. The final result is `extractedBank`.

Run `lake env lean ../research/L-meta-3561/EncodedBank.lean` from the project's `lean` directory to check the proof.
