import WitnessBridge

namespace PEqualNP.Outside.L_meta_1774.WitnessNine

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mono94

/-- On this whole graph, the same 12-gate circuit works as the replacement for
every correct monotone circuit with a positive ownership-defect count. -/
theorem descentFromLive (noSmall : ∀ k, k ≤ 11 → ¬ Live 511 k roots.toFinset)
    (C : Circuit) (legalC : Monotone2 C) (correctC : circuitFun 9 C = graphFun G ∅)
    (hasDefect : 0 < (disjointOwners G C).ncard) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun 9 D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns 9 D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard := by
  refine ⟨dirty,legal,correct,?_,productive,?_⟩
  · rw [size]
    exact lowerFromLive noSmall C legalC correctC
  · simpa only [zeroDefects] using hasDefect

end PEqualNP.Outside.L_meta_1774.WitnessNine
