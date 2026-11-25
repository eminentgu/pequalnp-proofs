import Extract15
import Case15.L11B0
namespace VertexPeel.CoverFour.Case15Partial
open Mono94 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem rootKey : (Packing.unpack 12 0x1e088c04298249411810062302a031fc0040c).toFinset = roots.toFinset := by decide +kernel

/-- Every binary monotone circuit fitting these nine positive and seven negative assignments
needs at least twelve gates. -/
theorem lower (C : Circuit) (legal : Monotone2 C)
    (correct : ∀ r : Fin 16, C.eval (List.ofFn (sample r)) = bit r goal) : 12 ≤ C.size := by
  obtain ⟨k,hk,plan⟩ := extractExact C legal correct
  by_contra! small
  apply x11_0 k (by omega)
  rw [rootKey]
  exact plan

end VertexPeel.CoverFour.Case15Partial
#print axioms VertexPeel.CoverFour.Case15Partial.lower
