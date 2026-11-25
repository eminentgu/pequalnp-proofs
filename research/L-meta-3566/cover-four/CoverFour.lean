import FourInduction
import MaskGirth
import RawComplete
import RawTrim
import RawTaggedIso
import TaggedIso
import Classified186

namespace VertexPeel.CoverFour

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774
open VertexPeel.CoverThreeCore VertexPeel.CoverFourTransport VertexPeel.CoverCircuit

private theorem classified_codes : Classifies := by
  intro z tri sq size
  have raw := Mask4.raw_complete z (Mask4.girth_bits z tri sq)
  have valid := Mask4.minimum_four_codes raw size
  obtain ⟨w,mem,⟨e⟩⟩ := Mask4.raw_to_tagged z valid
  obtain ⟨i,⟨f⟩⟩ := Mask4.tagged_to_canonical mem
  exact ⟨i,⟨e.trans f⟩,CoverFourClass.classified i⟩

/-- Every monotone fan-in-two circuit for the edge function has at least |E|+3 gates
when the graph has girth at least five and its minimum vertex cover has size four. -/
theorem numerical_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : NoTriangles G) (sq : NoFourCycle G) (size : Loc.tau G = 4) :
    StableExtension.Numerical G 4 :=
  @from_classification classified_codes _ G _ tri sq size

/-- Card 1774 for arbitrary input size and every graph with a cover of size at most four. -/
theorem ownership_at_most_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : NoTriangles G) (sq : NoFourCycle G) (bound : Loc.tau G ≤ 4) : StepAt G := by
  obtain ⟨T,c,count⟩ := Loc.tau_attained G
  by_cases three : T.card ≤ 3
  · exact CoverThree.ownership_descent G tri sq T c three
  have four : Loc.tau G = 4 := by omega
  intro C minimum correct _ positive
  have low := numerical_four G tri sq four C minimum.1 correct
  apply coveredDescent G C T c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + T.card - 1 ≤ C.size
  omega

/-- One non-isolated vertex works for all correct AO₂ circuits, with the extra saving
whenever the minimum cover drops. Covers of size at most four may be anywhere in the graph. -/
theorem vertex_at_most_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : NoTriangles G) (sq : NoFourCycle G) (bound : Loc.tau G ≤ 4) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨T,c,count⟩ := Loc.tau_attained G
  by_cases three : T.card ≤ 3
  · exact CoverThree.vertex_deletion G tri sq T c three edges
  have four : Loc.tau G = 4 := by omega
  obtain ⟨z,pos,remaining⟩ := nonemptyCut G edges
  refine ⟨z,pos,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have low := numerical_four G tri sq four C mono correct
  exact atVertexOfCoverBound G z remaining C ⟨T,c,by omega⟩

/-- Specialization to the two-coloring and edge hypotheses on card 3566. -/
theorem bipartite_vertex_at_most_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ color : Fin n → Bool, ∀ u v, G.Adj u v → color u ≠ color v)
    (sq : NoFourCycle G) (bound : Loc.tau G ≤ 4) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨color,proper⟩ := bip
  apply vertex_at_most_four G _ sq bound edges
  intro a b c ab bc ca
  exact (by decide : ∀ x y z : Bool, x ≠ y → y ≠ z → z ≠ x → False)
    (color a) (color b) (color c) (proper a b ab) (proper b c bc) (proper c a ca)

#print axioms numerical_four
#print axioms ownership_at_most_four
#print axioms vertex_at_most_four
#print axioms bipartite_vertex_at_most_four
end VertexPeel.CoverFour
