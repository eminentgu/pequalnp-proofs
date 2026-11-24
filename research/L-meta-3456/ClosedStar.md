# When a shared AND gate can be bypassed

Let a monotone circuit compute edge containment in a bipartite graph. Let $g$ be the output of an AND gate. Suppose there is a vertex $v$ such that $g$ accepts the singleton $v$ and the singleton of every neighbor of $v$. Replacing $g$ by either operand at all of its consumers preserves the circuit output. The graph may contain four-cycles.

To prove this, take any independent set $S$. If $S$ meets the neighborhood of $v$, monotonicity gives $g(S)=1$. Otherwise, $T=S\cup\{v\}$ is independent and $g(T)=1$. In both cases there is an independent extension of $S$ where the original gate and its replacement already agree. If the modified circuit were true on $S$, monotonicity would make it true on this extension, where the original circuit is false. Every assignment containing an edge remains accepted because bypassing an AND can only increase its value.

`ClosedStar.lean` proves the independent-extension claim for vertices on either side and the semantic substitution theorem `safe_increase`. The two circuit facts supplied to that theorem are preservation of positive outputs and agreement on inputs where the gate is already true.

Place both Lean files in one directory. Using Lean 4.36, run from that directory:

```sh
artifacts=$(mktemp -d)
export LEAN_PATH="$artifacts${LEAN_PATH:+:$LEAN_PATH}"
lean -j1 -R . -o "$artifacts/MixedFrontier.olean" MixedFrontier.lean
lean -j1 -R . ClosedStar.lean
```
