# Triangle- and four-cycle-free graphs with cover number four

After excluding forests, duplicate leaves, and any leaf whose deletion preserves the cover number, exactly **17** graphs remain up to isomorphism. A direct C++ synthesis search excluded circuits of size at most `|E|+2` for all 17. The star construction gives size `|E|+3` for a graph with cover number four. Lean independently proves the exact minimum circuit size and the full vertex-deletion conclusion for all 17 labelled graphs. It also proves the ownership-descent conclusion of L-meta-1774 for each row. The classification up to isomorphism remains a separate step for a cover-four corollary. [Lean statements and reproduction](checked.md)

| Stage | 7 vertices | 8 | 9 | 10 | 11 | 12 | 13 | 14 | Total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| No isolates or duplicate leaves | 4 | 29 | 56 | 52 | 30 | 11 | 3 | 1 | 186 |
| Forests | 0 | 10 | 15 | 8 | 2 | 0 | 0 | 0 | 35 |
| Cyclic, with a cover-preserving leaf | 0 | 9 | 39 | 43 | 28 | 11 | 3 | 1 | 134 |
| Cyclic, every existing leaf lowers the cover number | 4 | 10 | 2 | 1 | 0 | 0 | 0 | 0 | 17 |
| Same, after the isolated-edge and pendant-path rules | 2 | 8 | 2 | 1 | 0 | 0 | 0 | 0 | 13 |

The 17 classes include ten without leaves and eight bipartite classes. The complete list identifies two cases with an isolated-edge reduction and two further cases with a pendant two-edge path. The other 13 coincide with the triangle-free part of the previously published 44 core graphs. The 17 direct searches cover the four extra cases explicitly. The earlier 12-vertex bipartite core table concerns cover numbers five or six. [Graph classes](critical.tsv) · [Published finite checks](https://github.com/helloitswill/pequalnp-research-notes/blob/894ed421c9bccac0310ab9a270902798c2aec00c/L-meta-612/FiniteChecks.md)

## Generation and isomorphism

Choose a minimum cover of four vertices numbered 0–3. Every remaining vertex has a nonempty neighborhood among these four. Outside vertices with the same singleton neighborhood are duplicate leaves. Any pair of cover vertices occurs in at most one outside neighborhood, since two such vertices would supply a four-cycle. Thus each nonempty neighborhood type occurs at most once. Four singleton types and at most six larger types give at most fourteen nonisolated vertices overall. Covering vertices can themselves be leaves, so the implementation also checks for duplicate leaves across the completed graph. [Checked graph and reduction bounds](../CoverKernel.lean)

The enumerator tries every simple internal graph on the four cover vertices, discarding those with triangles or four-cycles. A candidate outside neighborhood is valid only when it contains no adjacent internal pair and no pair with a common internal neighbor. These two tests exclude, respectively, triangles and four-cycles having one outside vertex. Rejecting an internal pair used in two outside neighborhoods excludes four-cycles having two outside vertices. The outside set is independent by definition of a cover. This exhausts the possible short cycles.

For each subset of the four distinguished vertices that covers every internal edge, the omitted vertices force precisely their outside neighbors into the cover. Minimizing cardinality over these sixteen possibilities finds the exact minimum and all attaining covers. For each attaining cover the program tries every ordering of its four vertices, encodes internal edges and sorts the outside neighborhood masks. The least complete encoding is invariant under every graph isomorphism. Conversely, an equal encoding constructs an explicit isomorphism. The 292 presentations up to cover-preserving relabelling yield 186 unlabelled graphs. The script also checks nonexistence of a three-vertex cover and tests every single leaf deletion by a separate brute-force search over all triples of vertices.

The four internal vertices can be inside different minimum covers of isomorphic representative graphs. The `inside_mask` column uses bit positions for the pairs 01, 02, 03, 12, 13, 23. Each outside mask records its set of neighbors in bit positions 0–3. The edge-list file gives a second explicit representation. [Generator](enumerate_four.py) · [Edge lists](critical.txt) · [Full counts](counts.txt)

## Reproduction

Run from this directory with Python 3.10 or later. These commands prepare a fresh temporary checkout of the published source.

```sh
REFERENCE=$(mktemp -d)
git clone --quiet --no-checkout https://github.com/helloitswill/pequalnp-research-notes.git "$REFERENCE"
git -C "$REFERENCE" checkout --quiet --detach 894ed421c9bccac0310ab9a270902798c2aec00c
PUBLISHED="$REFERENCE/L-meta-612"
python3 -B enumerate_four.py . --published published-44.txt
python3 -B "$PUBLISHED/cover_four.py" > /tmp/cover-four-reference.txt
diff -u published-44.txt /tmp/cover-four-reference.txt
python3 -B compare_generator.py "$PUBLISHED"
c++ -O3 -std=c++17 "$PUBLISHED/kernel_search.cpp" -o /tmp/published-cover-kernel
python3 -B run_direct.py /tmp/published-cover-kernel critical.txt --seconds 60
```

Use source commit `894ed421c9bccac0310ab9a270902798c2aec00c`. The SHA-256 digest of its `kernel_search.cpp` is `ba51eae17193196fd3f1f60da98c45db5299a292bcfa6a6422825439ad22f677`. The two generators agreed on all 186 normalized graphs. The local extended and original pinned C++ solvers produced identical per-case direct transcripts, expanding 2,876,063 states altogether. All 17 finished within an eight-second per-instance limit on the test machine. The direct mode uses the minimal positive and maximal negative truth-table rows and can retain either operand for later uses. It takes no smaller-instance optimum as input. [Pinned source](https://github.com/helloitswill/pequalnp-research-notes/blob/894ed421c9bccac0310ab9a270902798c2aec00c/L-meta-612/kernel_search.cpp) · [Direct search transcript](direct-pinned.log)
