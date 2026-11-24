# A terminal AND in a circuit for a C4-free bipartite graph

Let the two sides be $P,L$, and let $F(S)$ be true exactly when the selected vertices $S$ contain an edge. Suppose an AND gate has inputs $g,h$ and reaches the output along a path of OR gates. Then $g(S)\land h(S)\Rightarrow F(S)$. The argument below uses this implication and monotonicity. It allows either input signal, and the AND gate itself, to have additional consumers.

## At most one accepted nonedge pair

Suppose $g$ is true on each of four singleton assignments $x,x'\in P$ and $y,y'\in L$, with $x\ne x'$ and $y\ne y'$. The sibling $h$ must be false on every assignment supported on one side. For instance, if it were true on a set of left vertices, adding $x$ would make both inputs true while leaving every right vertex absent.

Now suppose $h$ accepts a nonedge pair $\{p,\ell\}$. Adding $x$ forces an edge on $\{p,x,\ell\}$. Since $p\ell$ is absent, $x\ell$ must be an edge. Adding $x'$, $y$, and $y'$ in turn forces $x'\ell$, $py$, and $py'$. The two left witnesses have at most one common right neighbor in a C4-free graph. The two right witnesses likewise have at most one common left neighbor. Consequently at most **one** nonedge pair can make $h$ true.

If every minterm of $h$ has size at most two, this gives a gate elimination test. Look up the two common neighbors. If either is missing, they form an edge, or $h$ rejects their pair, then every positive minterm of $h$ contains an edge. It follows that $h\Rightarrow F$. Bypassing the terminal AND with $h$ preserves the output. It can only increase gate values, and on every negative assignment the replacement and the original AND are both false. The argument applies even if the gate is shared. For a sibling with larger minterms the uniqueness conclusion still holds for pairs.

The Lean file proves the semantic statements as `no_one_side`, `unique_bad_pair`, and `sibling_safe`. The latter assumes that every positive input contains a positive one-side input or a positive mixed pair, a condition implied by the minterm bound. The path implication and circuit rewiring above are paper arguments.

## An example attaining the bound

Use left vertices $p,x_1,x_2,u$, right vertices $\ell,y_1,y_2,v$, and edges $x_1\ell,x_2\ell,py_1,py_2,uv$. This is a disjoint union of two two-edge stars and one edge. The following gate expressions define the circuit. Each repeated subexpression can be shared, and each multiway OR can be realized with binary OR gates.

```text
X = (x1 OR x2) OR (y1 OR y2)
A = X OR u                      B = X OR v
g = A AND B                     h = p AND (l OR y1)
H = g AND h
R = (l AND (x1 OR x2)) OR (p AND y2) OR (u AND v)
output = H OR R
```

The dirty gate $g$ fires on the four singletons in $X$. Its operands attain all four Boolean patterns. Its sibling $h$ accepts exactly one nonedge pair, $\{p,\ell\}$. Four attempted replacements of $g$ change the output.

| Replacement | Selected vertices | Correct output | Modified output |
| --- | --- | --- | --- |
| $A$ | $p,\ell,u$ | false | true |
| $B$ | $p,\ell,v$ | false | true |
| Constant false | $p,y_1$ | true | false |
| Constant true | $p,\ell$ | false | true |

The graph itself admits the clean seven-gate circuit $ (\ell\land(x_1\lor x_2))\lor(p\land(y_1\lor y_2))\lor(u\land v) $. The example shows why this local rewiring test can stop before reaching a clean circuit.

`mixed_frontier.py` checks both circuits on all 256 assignments and verifies the four counterexamples. To reproduce the two independent checks, run these commands in this directory with Python 3 and Lean 4.36.

```sh
python3 mixed_frontier.py
lean -j1 MixedFrontier.lean
```
