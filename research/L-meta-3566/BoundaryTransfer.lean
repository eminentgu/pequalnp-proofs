import SyntacticSharp
import Descent

namespace VertexPeel.BoundaryTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.ReadTwo PEqualNP.TopForm PEqualNP.MetaComplexity.CoverPromise
  PEqualNP.Outside.L_meta_1774
open VertexPeel.GuardCut VertexPeel.CoverCircuit

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- An equal-budget boundary witness suffices for the posted ownership conclusion,
even when the circuit being repaired uses constants or non-backward references. -/
theorem ownership (sq : NoFourCycle G) (C M : Circuit)
    (ao : IsAO2 n M) (ok : circuitFun n M = graphFun G ∅) (bd : Boundary G M)
    (budget : M.size ≤ C.size) (positive : 0 < Defects G C) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ AllUseful G D ∧ Defects G D < Defects G C := by
  obtain ⟨T,c,low⟩ := cover_bound G M ao ok sq bd
  apply coveredDescent G C T c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + T.card - 1 ≤ C.size
  omega

/-- One least circuit satisfying the boundary test gives a single graph vertex
with the full deletion and cover bonus for every circuit in the card. -/
theorem vertex (sq : NoFourCycle G) (edges : 2 ≤ G.edgeFinset.card) (M : Circuit)
    (ao : IsAO2 n M) (ok : circuitFun n M = graphFun G ∅) (bd : Boundary G M)
    (least : ∀ C, IsAO2 n C → circuitFun n C = graphFun G ∅ → M.size ≤ C.size) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      SavesAt G z C := by
  obtain ⟨T,c,b⟩ := cover_bound G M ao ok sq bd
  obtain ⟨z,deg,rem⟩ := nonemptyCut G edges
  refine ⟨z,deg,fun C cc eval => atVertexOfCoverBound G z rem C ⟨T,c,?_⟩⟩
  have := least C cc eval
  omega

#print axioms ownership
#print axioms vertex
end VertexPeel.BoundaryTransfer
