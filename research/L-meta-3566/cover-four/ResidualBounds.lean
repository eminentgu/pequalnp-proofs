import ResidualRuns
import ResidualThetas
import ResidualExplicit
import ResidualFifteen
import Descent

namespace VertexPeel.CoverFourResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Each of the seventeen labelled graphs has the canonical monotone lower bound. -/
theorem listedLower (i : Fin 17) : Lower (graph i) ((table i).2.length + 3) := by
  fin_cases i
  · exact lower0
  · exact lower1
  · exact lower2
  · exact lower3
  · exact lower4
  · exact lower5
  · exact lower6
  · exact lower7
  · exact lower8
  · exact lower9
  · exact lower10
  · exact lower11
  · exact lower12
  · exact lower13
  · exact lower14
  · exact lower15
  · exact lower16

private abbrev cover (i : Fin 17) : Finset (Fin (table i).1) :=
  Finset.univ.filter fun v => v.val < 4

private theorem counts (i : Fin 17) :
    (graph i).edgeFinset.card = (table i).2.length ∧ (cover i).card = 4 ∧
    (2 ≤ (graph i).edgeFinset.card) ∧ (∀ u v, (graph i).Adj u v → u ∈ cover i ∨ v ∈ cover i) := by
  fin_cases i <;> decide +kernel

/-- The upper-bound star circuit attains the lower bound for every certified row. -/
theorem listedOptimum (i : Fin 17) :
    ∃ C : Circuit, IsAO2 (table i).1 C ∧ circuitFun _ C = graphFun (graph i) ∅ ∧
      C.size = (graph i).edgeFinset.card + 3 := by
  obtain ⟨m,t,_,hc⟩ := counts i
  obtain ⟨C,ao,eval,upper,_⟩ := CoverCircuit.main _ (graph i) (cover i) hc
  have cor : circuitFun _ C = graphFun (graph i) ∅ := by
    funext x
    simpa [circuitFun,graphFun] using eval x
  have mono : Monotone2 C := by
    intro g hg
    obtain h | h := ao.1 g hg <;> simp [h,ao.2.2 g hg]
  have lower := listedLower i C mono cor
  exact ⟨C,ao,cor,by omega⟩

/-- On every certified row, this is the full contraction conclusion with one
    vertex working for every legal circuit. -/
theorem listedExact (i : Fin 17) : Exact (graph i) := by
  obtain ⟨m,t,edges,hc⟩ := counts i
  exact lowerExact (graph i) (cover i) hc (by omega) edges (listedLower i)

/-- The exact ownership-descent conclusion of L-meta-1774 for each listed graph. -/
theorem listedOwnership (i : Fin 17) : PEqualNP.Outside.L_meta_1774.StepAt (graph i) := by
  intro C minimum correct _ positive
  obtain ⟨m,t,_,hc⟩ := counts i
  have lower := listedLower i C minimum.1 correct
  apply PEqualNP.Outside.L_meta_1774.coveredDescent (graph i) C (cover i) hc _ positive
  rw [Set.ncard_eq_toFinset_card']
  change (graph i).edgeFinset.card + (cover i).card - 1 ≤ C.size
  omega

end VertexPeel.CoverFourResidual

#print axioms VertexPeel.CoverFourResidual.listedLower
#print axioms VertexPeel.CoverFourResidual.listedExact

#print axioms VertexPeel.CoverFourResidual.listedOptimum

#print axioms VertexPeel.CoverFourResidual.listedOwnership
