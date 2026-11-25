import Extract15
import ResidualGraphs

namespace VertexPeel.CoverFourResidual
open PEqualNP.MetaComplexity.NestedCover
open VertexPeel.CoverFour.Case15Partial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sample15_noZeroOne : ∀ r : Fin 16, ¬ (sample r 0 = true ∧ sample r 1 = true) := by
  decide +kernel

theorem sample15_correct : ∀ r : Fin 16, graphFun (graph 15) ∅ (sample r) = bit r goal := by
  decide +kernel

end VertexPeel.CoverFourResidual
