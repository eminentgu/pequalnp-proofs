# A finite closure certificate

The supplied table contains all 1,616 nonterminal states needed for the ten-gate lower bound. It occupies 87,820 bytes. From the containing `theta/` directory, run the following command.

```sh
python3 certificate/check.py
```

Each line of `frontier.txt` begins with a remaining gate budget in decimal. Its remaining fields are hexadecimal packed states. Start an accumulator at 1 and, in ascending wire order, shift it left by 29 bits and insert the next truth vector. The leading 1 is a length sentinel, so decoding is injective.

The verifier processes budgets in ascending order. For every listed state it enumerates all unordered pairs of wires, all four choices of polarities, and all four choices of which operands to keep. It examines 565,172 nondegenerate transitions. A successor must satisfy a rejection rule described in the parent README or be equivalent under a checked graph automorphism to a previously verified entry with one fewer gate. The verifier then locates the initial state at budget ten. Since every transition decreases the budget, these tests imply by induction that the initial state is impossible.

The checker implements its own pair enumeration, cell coverage, rectangle products, and transition loop. It does not call the search in `rows.py`. It regenerates the sample bank and permutations to validate the data. The optional command `python3 certificate/make.py` reproduces `frontier.txt` from the search.
