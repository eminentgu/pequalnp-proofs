import Equivalence
import Descent
import PEqualNP.Outside.L_meta_1527

namespace VertexPeel
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1774

theorem twoEdgesOfPositive {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (positive : 0 < Defects G C) : 2 ≤ G.edgeFinset.card := by
  classical
  have ne : (disjointOwners G C).ncard ≠ 0 := Nat.ne_of_gt positive
  obtain ⟨j,a,b,c,d,ab,cd,_,_,ac,ad,_,_⟩ :=
    (Set.ncard_pos (Set.finite_of_ncard_ne_zero ne)).mp positive
  apply Finset.one_lt_card.mpr
  refine ⟨s(a,b),by simpa using ab,s(c,d),by simpa using cd,?_⟩
  intro same
  rcases Sym2.eq_iff.mp same with h | h
  · exact ac h.1
  · exact ad h.1

-- L-meta-3566 suffices to solve the whole bipartite restriction of L-meta-1774.
theorem bipartiteDescentOfPeel (peel : ExactPeel) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (square : NoFourCycle G) : StepAt G := by
  classical
  intro C hmin correct _ positive
  obtain ⟨D,ao,ev,small⟩ := PEqualNP.Outside.L_meta_1527 n G inferInstance C hmin.1 (by
    intro x
    change circuitFun n C x = true ↔ _
    rw [correct]
    simp [graphFun])
  have edges := twoEdgesOfPositive positive
  obtain ⟨T,cover,bound⟩ := (exactPeel_iff_globalLower.mp peel) n G color square edges D ao ev
  apply coveredDescent G C T cover _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + T.card - 1 ≤ C.size
  omega

end VertexPeel

#print axioms VertexPeel.bipartiteDescentOfPeel
