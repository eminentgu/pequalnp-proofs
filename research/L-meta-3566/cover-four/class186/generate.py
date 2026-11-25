"""Emit a checkable witness for each graph in the canonical 186-entry table."""
from collections import Counter
from pathlib import Path
from itertools import combinations
import sys
import argparse

parser = argparse.ArgumentParser(description="Generate the 186 row witnesses and the Lean modules that check them.")
parser.add_argument('output', type=Path)
args = parser.parse_args()
here = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(here.parent))
import enumerate_four as e

rows = sorted({key for _, key in e.candidates()}, key=lambda k: (len(k[1]), k))
if len(rows) != 186:
    raise ValueError(f"expected 186 canonical cover graphs, got {len(rows)}")

def encode(inside, cols):
    return inside + 64 * sum(1 << (s - 1) for s in cols)

def lean_vector(values, domain, codomain):
    entries = ','.join(map(str, values))
    return f'(![{entries}] : Fin {domain} → {codomain})'


def subtrees(graph):
    masks = [0] * len(graph)

    def visit(vertex, parent):
        masks[vertex] = 1 << vertex
        for other in e.vertices(graph[vertex]):
            if other != parent:
                masks[vertex] |= visit(other, vertex)
        return masks[vertex]

    for vertex, mask in enumerate(masks):
        if not mask:
            visit(vertex, None)
    return masks


def surviving_matching(edges, leaves):
    for leaf in leaves:
        remaining = [edge for edge in edges if leaf not in edge]
        for selection in combinations(remaining, 4):
            vertices = {vertex for edge in selection for vertex in edge}
            if len(vertices) == 8:
                return leaf, selection
    return leaves[-1], None


output = args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
proofs = []
counts = Counter()
next_residual = 0
for index, (inside, columns) in enumerate(rows):
    bits = e.graph(inside, columns)
    n = len(bits)
    edges = e.edges(bits)
    z = hex(encode(inside, columns))
    lines = [f'theorem row{index} : Exit {z} := by']
    stable = [v for v, row in enumerate(bits) if row.bit_count() == 1 and
              e.minimum_covers(e.induced_without(bits, v))[0] == 4]
    if len(edges) == n - e.structure(bits)[0]:
        kind = 'forest'
        masks = subtrees(bits)
        lines += ['  apply Or.inl', f'  exact forestCert _ {lean_vector(masks, n, "Nat")} (by decide +kernel)']
    elif stable:
        leaf, matching = surviving_matching(edges, stable)
        lines += ['  apply Or.inr (Or.inl ?_)',f'  refine ⟨({leaf} : Fin {n}), by decide +kernel, ?_⟩']
        if matching is not None:
            kind = 'matching'
            left, right = zip(*matching)
            lines += [f'  let l : Fin 4 → Fin {n} := {lean_vector(left, 4, "Fin "+str(n))}',
                      f'  let r : Fin 4 → Fin {n} := {lean_vector(right, 4, "Fin "+str(n))}',
                      '  apply matchingCert _ _ l r',
                      f'  · change ∀ i : Fin 4, Mask4.adjB {z} (l i).val (r i).val = true ∧ l i ≠ ({leaf} : Fin {n}) ∧ r i ≠ ({leaf} : Fin {n})',
                      '    unfold l r', '    decide +kernel',
                      '  · change ∀ i j : Fin 4, i ≠ j → l i ≠ l j ∧ l i ≠ r j ∧ r i ≠ l j ∧ r i ≠ r j',
                      '    unfold l r', '    decide +kernel']
        else:
            kind = 'small'
            lines += ['  apply smallCert',f'  change ∀ S : Finset (Fin {n}), (∀ x y : Fin {n}, Mask4.adjB {z} x.val y.val = true → x ≠ {leaf} → y ≠ {leaf} → x ∈ S ∨ y ∈ S) → 4 ≤ S.card', '  decide +kernel']
    else:
        kind = 'residual'
        residual = next_residual
        next_residual += 1
        es = '[' + ','.join(f'({a},{b})' for a,b in edges) + ']'
        lines += [f'  refine Or.inr (Or.inr ⟨{residual}, isoCert _ _ ?_⟩)',f'  let edges : List (ℕ × ℕ) := {es}',f'  change ∀ u v : Fin {n}, Mask4.adjB {z} u.val v.val = true ↔ u ≠ v ∧ ((u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges)', '  unfold edges', '  decide +kernel']
    counts[kind] += 1
    proofs.append('\n'.join(lines))
prefix='''namespace VertexPeel.CoverFourClass
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
batch_size = 8
modules = []
for start in range(0, len(rows), batch_size):
    name = f'Exits186_{start // batch_size}'
    modules.append(name)
    body = '\n\n'.join(proofs[start:start + batch_size])
    (output / f'{name}.lean').write_text('import ExitCore\n\n' + prefix + '\n' + body +
                                      '\n\nend VertexPeel.CoverFourClass\n')

imports = 'import Canonical186\n' + ''.join(f'import {name}\n' for name in modules)
conclusion = ('theorem classified : ∀ i : Fin 186, Exit (canonicalCode i) := by\n'
              '  intro i\n  fin_cases i\n' +
              ''.join(f'  · exact row{i}\n' for i in range(len(rows))))
(output / 'Classified186.lean').write_text(imports + '\n' + prefix + '\n' + conclusion +
    '\nend VertexPeel.CoverFourClass\n#print axioms VertexPeel.CoverFourClass.classified\n')
print(dict(counts))
