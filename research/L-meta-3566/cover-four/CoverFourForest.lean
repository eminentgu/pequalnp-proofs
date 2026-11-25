import CoverFour
import ForestExtension

namespace VertexPeel.CoverFourForest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774
open StableExtension CoverCircuit CoverThreeCore ForestExtension

variable {n : ℕ}

private theorem core_numerical (H : SimpleGraph (Fin n)) [base : DecidableRel H.Adj]
    (tri : NoTriangles H) (sq : NoFourCycle H) (small : Loc.tau H ≤ 4) :
    Numerical H (Loc.tau H) := by
  intro inst C mono correct
  have same : inst = base := Subsingleton.elim _ _
  subst inst
  by_cases forest : H.IsAcyclic
  · exact forest_numerical H forest C mono correct
  by_cases three : Loc.tau H ≤ 3
  · obtain ⟨T,c,count⟩ := Loc.tau_attained H
    have low := CoverThree.cyclic_lower H tri sq T c (by omega) forest C mono correct
    omega
  have four : Loc.tau H = 4 := by omega
  have low := CoverFour.numerical_four H tri sq four C mono correct
  omega

/-- A girth-at-least-five core with cover number at most four, together with any
vertex-disjoint forest, obeys the edge-plus-cover bound at the cover number of the union. -/
theorem numerical (H F : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (tri : NoTriangles H) (sq : NoFourCycle H) (small : Loc.tau H ≤ 4)
    (sep : Apart H F) (acyc : F.IsAcyclic) : Numerical (H ⊔ F) (Loc.tau (H ⊔ F)) :=
  @add_forest n H F sep acyc (@core_numerical n H _ tri sq small)

/-- Card 1774 for the core and forest, without a bound on the union's cover number. -/
theorem ownership (H F : SimpleGraph (Fin n)) [DecidableRel H.Adj] [DecidableRel (H ⊔ F).Adj]
    (tri : NoTriangles H) (sq : NoFourCycle H) (small : Loc.tau H ≤ 4)
    (sep : Apart H F) (acyc : F.IsAcyclic) : StepAt (H ⊔ F) := by
  intro C minimum correct _ positive
  obtain ⟨T,c,count⟩ := Loc.tau_attained (H ⊔ F)
  have low := numerical H F tri sq small sep acyc C minimum.1 correct
  apply coveredDescent (H ⊔ F) C T c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change (H ⊔ F).edgeFinset.card + T.card - 1 ≤ C.size
  omega

/-- Card 3566 for the core and forest, with the same chosen vertex for every circuit. -/
theorem vertex (H F : SimpleGraph (Fin n)) [DecidableRel H.Adj] [DecidableRel (H ⊔ F).Adj]
    (tri : NoTriangles H) (sq : NoFourCycle H) (small : Loc.tau H ≤ 4)
    (sep : Apart H F) (acyc : F.IsAcyclic) (edges : 2 ≤ (H ⊔ F).edgeFinset.card) :
    ∃ z : Fin n, 0 < (H ⊔ F).degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun (H ⊔ F) ∅ → SavesAt (H ⊔ F) z C := by
  obtain ⟨z,pos,remaining⟩ := nonemptyCut (H ⊔ F) edges
  refine ⟨z,pos,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  obtain ⟨T,c,count⟩ := Loc.tau_attained (H ⊔ F)
  have low := numerical H F tri sq small sep acyc C mono correct
  exact atVertexOfCoverBound (H ⊔ F) z remaining C ⟨T,c,by omega⟩

end VertexPeel.CoverFourForest

#print axioms VertexPeel.CoverFourForest.numerical
#print axioms VertexPeel.CoverFourForest.ownership
#print axioms VertexPeel.CoverFourForest.vertex
