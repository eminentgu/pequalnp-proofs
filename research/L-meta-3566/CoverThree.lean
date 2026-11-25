import IsolatedCore
import CycleSize
import CoverThreeCore
import StableExtension
import CycleCover
import Normalization
import Descent
import PEqualNP.Research.L_meta_1774.Forest

namespace VertexPeel.CoverThree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774
open VertexPeel.CoverCircuit VertexPeel.StableExtension VertexPeel.CoverThreeCore

private abbrev CycleCost (k s : ℕ) := ∀ C : Circuit, Monotone2 C →
  circuitFun k C = graphFun (SimpleGraph.cycleGraph k) ∅ → s ≤ C.size

private theorem leafless_bound {n : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (tri : NoTriangles G) (square : NoFourCycle G) (noleaf : ∀ u, G.degree u ≠ 1)
    (K : Finset (Fin n)) (cover : IsVertexCover G K) (small : K.card ≤ 3) (cyclic : ¬ G.IsAcyclic)
    (five : CycleCost 5 7) (six : CycleCost 6 8) : Numerical G 3 := by
  obtain ⟨k,hk,f,inj,iffAdj,support,edges⟩ := classify G tri square noleaf K cover small cyclic
  let emb : SimpleGraph.cycleGraph k ↪g G := ⟨⟨f,inj⟩,fun {i j} => iffAdj i j⟩
  have active : ∀ a b, G.Adj a b → a ∈ Set.range emb ∧ b ∈ Set.range emb := support
  intro inst C mono ok
  have instEq : inst = base := Subsingleton.elim _ _
  subst inst
  rcases hk with rfl|rfl
  · have bound := IsolatedCore.core_lower _ G emb active five C mono ok
    rw [edges]
    omega
  · have bound := IsolatedCore.core_lower _ G emb active six C mono ok
    rw [edges]
    omega

/-- In the cyclic case the constant offset 3 survives deletion of every leaf. -/
theorem cyclic_lower {n : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (tri : NoTriangles G) (square : NoFourCycle G) (K : Finset (Fin n)) (cover : IsVertexCover G K)
    (small : K.card ≤ 3) (cyclic : ¬ G.IsAcyclic) : Numerical G 3 := by
  intro inst C mono ok
  have e : inst = base := Subsingleton.elim _ _
  subst inst
  suffices main : ∀ m (H : SimpleGraph (Fin n)) [d : DecidableRel H.Adj], H.edgeFinset.card = m →
      NoTriangles H → NoFourCycle H → IsVertexCover H K → ¬ H.IsAcyclic →
      ∀ A : Circuit, Monotone2 A → circuitFun n A = graphFun H ∅ → H.edgeFinset.card + 3 ≤ A.size + 1 by
    exact main G.edgeFinset.card G rfl tri square cover cyclic C mono ok
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro H d he triH sqH covH cyH A am ao
    by_cases leaf : ∃ a, H.degree a = 1
    · obtain ⟨a,deg⟩ := leaf
      obtain ⟨u,edge,only⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp deg
      let R := H.deleteIncidenceSet a
      let instR : DecidableRel R.Adj := inferInstance
      have fewer : R.edgeFinset.card < m := by
        have dpos := H.degree_le_card_edgeFinset a
        change (H.deleteIncidenceSet a).edgeFinset.card < m
        rw [H.card_edgeFinset_deleteIncidenceSet,deg]
        omega
      have old : Numerical R 3 := by
        intro ir D dm dc
        have same : ir = instR := Subsingleton.elim _ _
        subst ir
        exact ih R.edgeFinset.card fewer R rfl
          (fun x y z xy yz zx => triH x y z (H.deleteIncidenceSet_le a xy) (H.deleteIncidenceSet_le a yz) (H.deleteIncidenceSet_le a zx))
          (square_cut H a sqH) (fun x y xy => covH x y (H.deleteIncidenceSet_le a xy))
          (CycleCover.cyclic_delete_leaf edge only cyH) D dm dc
      exact step_numerical edge only old A am ao
    · exact leafless_bound H triH sqH (fun i hi => leaf ⟨i,hi⟩) K covH small cyH
        CycleSize.cycle5_size CycleSize.cycle6_size A am ao

/-- The original ownership descent for every graph with a cover of cardinality at most three. -/
theorem ownership_descent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : NoTriangles G) (square : NoFourCycle G) (K : Finset (Fin n))
    (cover : IsVertexCover G K) (small : K.card ≤ 3) : StepAt G := by
  intro C hmin correct _ positive
  by_cases forest : G.IsAcyclic
  · exact forestDescent G forest C hmin.1 correct positive
  · have lower := cyclic_lower G tri square K cover small forest C hmin.1 correct
    apply coveredDescent G C K cover _ positive
    rw [Set.ncard_eq_toFinset_card']
    change G.edgeFinset.card + K.card - 1 ≤ C.size
    omega

/-- Both size inequalities of the vertex-deletion statement, with a single vertex valid
for every circuit. -/
theorem vertex_deletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : NoTriangles G) (square : NoFourCycle G) (K : Finset (Fin n)) (cover : IsVertexCover G K)
    (small : K.card ≤ 3) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  by_cases forest : G.IsAcyclic
  · exact peelableGraph G (PEqualNP.Library.Peel.Scratch.peelable_of_isAcyclic forest) edges
  obtain ⟨z,hz,keep⟩ := nonemptyCut G edges
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have lower := cyclic_lower G tri square K cover small forest C mono correct
  exact atVertexOfCoverBound G z keep C ⟨K,cover,by omega⟩

/-- Specialization to the bipartiteness hypothesis appearing verbatim on card 3566. -/
theorem bipartite_vertex_deletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (square : NoFourCycle G)
    (K : Finset (Fin n)) (cover : IsVertexCover G K) (small : K.card ≤ 3) (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨color,proper⟩ := bip
  apply vertex_deletion G _ square K cover small edges
  intro a b c ab bc ca
  have p := proper a b ab
  have q := proper b c bc
  have r := proper c a ca
  exact (by decide : ∀ x y z : Bool, x ≠ y → y ≠ z → z ≠ x → False) _ _ _ p q r

end VertexPeel.CoverThree
