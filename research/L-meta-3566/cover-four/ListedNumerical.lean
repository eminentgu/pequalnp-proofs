import ResidualBounds
import StableExtension

namespace VertexPeel.CoverFourResidual

private theorem count (i : Fin 17) : (graph i).edgeFinset.card = (table i).2.length := by
  fin_cases i <;> decide +kernel

/-- Numeric form used in the induction that removes cover-preserving leaves. -/
theorem listedNumerical (i : Fin 17) : StableExtension.Numerical (graph i) 4 := by
  let base : DecidableRel (graph i).Adj := inferInstance
  intro inst C mono correct
  have same : inst = base := Subsingleton.elim _ _
  subst inst
  have lower := listedLower i C mono correct
  have edges := count i
  omega

end VertexPeel.CoverFourResidual
#print axioms VertexPeel.CoverFourResidual.listedNumerical
