import ResidualThetas
import CofactorCore15

namespace VertexPeel.CoverFourResidual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem falseCofactor15 (z : Fin 9) (hz : 4 ≤ z.val) (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 9 → Bool, circuitFun 9 C x =
      graphFun (graph 15) ∅ (Function.update x z false)) : 12 ≤ C.size :=
  falseCofactorOfLower lower11 lower12 z hz C mono correct

end VertexPeel.CoverFourResidual
#print axioms VertexPeel.CoverFourResidual.falseCofactor15
