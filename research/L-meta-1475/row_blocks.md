# Small row blocks in the order-four projective plane

L-meta-1475 asks for a monotone binary circuit with at most 124 gates for the plane's point–line incidence function. The ordinary circuit uses 125. **Every block of one to four of the fourteen rows outside the Fano subplane already has optimal row-star size.** This rules out replacing such a block on its own. Circuits that share gates across blocks remain possible.

Label rows and columns modulo 21. The project numbers the columns 21 through 41, so subtract 21 from those labels. Row $r$ meets the five columns $r+\{0,5,7,17,20\}$. The rows congruent to 0 and columns congruent to 2 modulo 3 form a Fano subplane. For a nonempty set of $k$ outside rows, the block function reports whether any selected row meets any selected column. Computing the five-column OR and then the AND for each row costs $5k$ gates. Joining the row outputs costs $k-1$.

| Rows | Geometry | Blocks | Minimum gates |
|---:|---|---:|---:|
| 1 | Any | 14 | 5 |
| 2 | Any | 91 | 11 |
| 3 | All three contain one column | 56 | 17 |
| 3 | No three contain one column | 308 | 17 |
| 4 | All four contain one column | 14 | 23 |
| 4 | Exactly one triple contains one column | 560 | 23 |
| 4 | No three contain one column | 427 | 23 |

## Reproduce the finite checks

Run `python3 -I -B row_blocks.py` with Python 3.10 or later. The script uses only the standard library. It enumerates all row subsets of sizes one through five, counts the column intersection patterns, and checks each core through four rows up to relabeling. A core retains only columns incident to at least two block rows. For five rows, 98 blocks have no triple, 1,008 have one triple, 756 have two triples and 140 have four rows through one column.

As a separate check through three rows, the script retains one private column per row and exhausts smaller monotone circuits for these compressed functions. It tracks wire values on edge assignments and maximal independent sets, which determine a monotone edge function. Every useful binary gate reads two live wires, each of which can be released after its last read. A state can be discarded when no live wire separates some positive assignment from a negative assignment or when its remaining gates cannot combine all live wires. These checks give compressed minima of 1, 5, 8 and 11 gates.

## Lower-bound argument for the full blocks

A column used by exactly one selected row is private. Fixing an essential private input to false saves at least one gate while the restricted function remains nonconstant. Prune unused gates and propagate constants and copies. The first gate reading the fixed input then becomes a constant or a copy. Repeating this argument adds one to the lower bound for every deleted private column. This deduction and the core identifications below are mathematical arguments. The cited project theorems provide the Lean-checked core bounds.

- The one-row, two-row and fully concurrent blocks are forests. Their $5k$ edges and $k$ disjoint private row–column edges give a minimum vertex cover of size $k$. The forest bound gives $5k+k-1$. [L104](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/MetaComplexity/L104.lean#L9)
- A nonconcurrent triple has nine private columns. Its core is a six-cycle, which needs eight gates. [L106](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/MetaComplexity/L106.lean#L7)
- Four rows with one concurrent triple have eleven private columns. Their core has three length-three paths joining the same two endpoints and needs twelve gates. [L-meta-516](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_516.lean#L3006)
- Four rows with no concurrent triple have eight private columns. Their core is $K_4$ with each edge subdivided once and needs fifteen gates. [L-meta-723](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_723.lean#L3448)

For a five-row block with four concurrent rows, the core consists of four paths $a$–$u_i$–$v_i$–$b$. The fifteen-gate expression $\bigvee_i ((u_i\lor b)\land(v_i\lor a))$ accepts one extra assignment, when only $a$ and $b$ are active. The script checks all 1,024 assignments. The existence of a 124-gate plane circuit remains open.
