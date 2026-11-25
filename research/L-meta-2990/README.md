# L-meta-2990 — sparse soundness for plane incidence

L-meta-2990 concerns circuits with no bound on repeated reads. They must accept every incident point–line pair and reject each incidence-free assignment containing at most $q$ active lines. The proposed lower bound is $Nq \le 100|C|$, where $N=q^2+q+1$ and $q\ge300$.

[SparseRows.lean](SparseRows.lean) gives an equivalent family of negative tests. For every set $Y$ of at most $q$ lines, turn on exactly those lines and every point lying on none of them. Rejecting these rows is sufficient: every promised negative input is coordinatewise below its corresponding row and every AO circuit is monotone. Together with acceptance of the incident pairs, these tests determine the full function on the sparse slice, even on assignments with many active points. The equivalence holds for arbitrary finite incidence relations.

The general gate lower bound remains open here.

For the plane in the desk statement, an omitted line has at least $q+1-|Y|$ points outside all the selected lines. Even when $|Y|=q$, the canonical negative row has at least $q$ active points. These are geometric properties of the rejection tests. [Omitted-line bound](PrivatePoints.lean), [active-point bound](NegativeSize.lean).

[SparsePrimes.lean](SparsePrimes.lean) characterizes the minimal accepting inputs on the promised slice. Each is an incident point–line pair. Any other minimal accepting input is incidence-free and contains at least $q+1$ lines. A monotone example attains this cutoff.

The read-2 accounting argument counts incident pairs admitting a joint proof tree in which each endpoint occurs at most twice. Write $H$ for the number of incident pairs without such a tree. The estimate is $N(q+1) \le 50|C| + 2N + H$. Thus any counterexample to L-meta-2990 must satisfy $200H > 99N(q+1)$. The remaining case is a circuit in which strictly more than 49.5% of the incident pairs fail the read-2 test.

The proof specializes the counting argument in L-meta-2466 to the sparse negative tests and retains the exceptional pairs in the L-meta-2673 count. From the root of this research branch, with the project's Lean cache installed, run:

```sh
python3 research/L-meta-2990/accounting/replay.py .
```

The replay checks the specialized local count, the full inequality and the numerical consequence. The density consequence is a necessary condition on counterexamples.
