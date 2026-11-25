# L-meta-2990 — sparse soundness for plane incidence

L-meta-2990 concerns circuits with no bound on repeated reads. They must accept every incident point–line pair and reject each incidence-free assignment containing at most $q$ active lines. The proposed lower bound is $Nq \le 100|C|$, where $N=q^2+q+1$ and $q\ge300$.

[SparseRows.lean](SparseRows.lean) gives an equivalent family of negative tests. For every set $Y$ of at most $q$ lines, turn on exactly those lines and every point lying on none of them. Rejecting these rows is sufficient: every promised negative input is coordinatewise below its corresponding row and every AO circuit is monotone. Together with acceptance of the incident pairs, these tests determine the full function on the sparse slice, even on assignments with many active points. The equivalence holds for arbitrary finite incidence relations.

The general gate lower bound remains open here.

For the plane in the desk statement, an omitted line has at least $q+1-|Y|$ points outside all the selected lines. Even when $|Y|=q$, the canonical negative row has at least $q$ active points. These are geometric properties of the rejection tests. [Omitted-line bound](PrivatePoints.lean), [active-point bound](NegativeSize.lean).
