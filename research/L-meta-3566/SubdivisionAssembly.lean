import LocalizedPeel
import BicyclicSupport

namespace VertexPeel.LocalizedPeel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.CoverCircuit
variable {n : ℕ}

/-- The exact deletion statement with the chosen vertex outside the circuit quantifier. -/
abbrev Uniform (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∃ z : Fin n, 0<G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C

/-- Only leafless branching graphs need a localized argument. The graph on its
ambient input type can have arbitrary isolated vertices. -/
theorem subdivision_vertex_of_branch (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v) (low : ∀ v, c v=false → G.degree v≤2)
    (sq : NoFourCycle G) (many : 2≤G.edgeFinset.card)
    (branchCut : (∀ v, G.degree v≠1) → (∃ u, 2<G.degree u) → Uniform G) : Uniform G := by
  classical
  by_cases leaf : ∃ v, G.degree v=1
  · exact PivotAND.side_degree_two_leaf_vertex G c proper low leaf many
  have leafless : ∀ v, G.degree v≠1 := fun v h => leaf ⟨v,h⟩
  by_cases branch : ∃ u, 2<G.degree u
  · exact branchCut leafless branch
  have same : G.support.toFinset = CoverThreeCore.active G := by
    ext v
    simp [CoverThreeCore.active,G.degree_pos_iff_mem_support]
  have lower (v : Fin n) (hv : v∈G.support.toFinset) : G.degree v=2 := by
    have pos := (G.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv)
    have ne := leafless v
    have lim : ¬2<G.degree v := fun h => branch ⟨v,h⟩
    omega
  have sum := G.sum_degrees_support_eq_twice_card_edges
  have const : ∑ i ∈ G.support.toFinset, G.degree i = ∑ _i ∈ G.support.toFinset, 2 :=
    Finset.sum_congr rfl lower
  rw [const,same] at sum
  simp only [Finset.sum_const,smul_eq_mul] at sum
  exact Bicyclic.support_vertex_deletion G ⟨c,proper⟩ sq leafless (by omega) many

/-- Supplying the leafless branching case for the subgraphs of G proves both desk
conclusions and the sharp numerical bound on the original graph. -/
theorem subdivision_from_branch (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u ≠ c v) (low : ∀ v, c v=false → G.degree v≤2)
    (sq : NoFourCycle G) (many : 2≤G.edgeFinset.card)
    (branchCut : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → 2≤H.edgeFinset.card →
      (∀ v, H.degree v≠1) → (∃ u, 2<H.degree u) → Uniform H) :
    (Uniform G ∧ StepAt G) ∧ (∀ [_d : DecidableRel G.Adj] (C : Circuit), Monotone2 C → circuitFun n C = graphFun G ∅ →
      G.edgeFinset.card + Loc.tau G ≤ C.size+1) := by
  have every (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (sub : H≤G) (size : 2≤H.edgeFinset.card) : Uniform H :=
    subdivision_vertex_of_branch H c (fun _ _ e => proper _ _ (sub e))
      (fun v h => (H.degree_le_of_le sub).trans (low v h)) (PivotAND.square_mono sub sq) size (branchCut H sub size)
  have sharp : StableExtension.Numerical G (Loc.tau G) := @sharp_of_subgraph_peels n G (fun H _ sub size => every H sub size)
  exact ⟨⟨every G le_rfl many,ownership_of_sharp G (@sharp)⟩,@sharp⟩

#print axioms subdivision_vertex_of_branch
#print axioms subdivision_from_branch
end VertexPeel.LocalizedPeel
