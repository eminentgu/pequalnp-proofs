import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenTheta

/-- Positions 0 and 4 are unused after the two restrictions. -/
def edge (x : Fin 9 → Bool) : Bool :=
  x 1 && x 2 || x 2 && x 3 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def upper : Circuit :=
  ⟨[⟨.or, [2, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [2, 11]⟩,
    ⟨.and, [5, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [14, 5]⟩, ⟨.and, [8, 15]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 16]⟩], 19⟩

theorem size_upper : upper.size = 11 := rfl

theorem legal_upper : FanInTwo upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst_vars <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

set_option maxHeartbeats 4000000 in
theorem eval_upper (x : Fin 9 → Bool) : upper.eval (List.ofFn x) = edge x := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
  rw [hx]
  simp [upper, Circuit.eval, Circuit.wires, GateOp.eval, edge, List.getD_eq_getElem?_getD,
    Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

end PetersenTheta
