import ResidualPrivateReaders
import RowFold
import FalseCofactor15
import PartialSamples15
import Partial15
import PEqualNP.Outside.L_meta_4342

namespace VertexPeel.CoverFourResidual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.TopForm VertexPeel.CoverFour.Case15Partial

/-- Five zero cofactors exclude repeated readers and AND readers. On the remaining
    private OR, the partial-domain certificate forces a second gate of savings. -/
theorem lower15 : Lower (graph 15) 14 := by
  intro C mono ok
  have allZero : circuitFun 9 C (fun _ => false) = false := by
    exact (congrFun ok (fun _ => false)).trans (by simp [graphFun])
  obtain ⟨E,ao,size,ev⟩ := PEqualNP.Outside.L_meta_4342 9 C mono allZero
  have bound := lower15_of_rows sample sample15_noZeroOne falseCofactor15
    (fun D legal fit => VertexPeel.CoverFour.Case15Partial.lower D legal (fun r =>
      (fit r).trans (sample15_correct r))) (RowFold.erase_zero_and_reader sample) E ao (ev.trans ok)
  exact bound.trans size

end VertexPeel.CoverFourResidual
#print axioms VertexPeel.CoverFourResidual.lower15
