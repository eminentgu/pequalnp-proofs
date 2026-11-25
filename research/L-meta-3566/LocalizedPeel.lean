import SubdivisionLeaves
import ForestExtension

namespace VertexPeel.LocalizedPeel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.CoverCircuit VertexPeel.ZeroFold
variable {n : ℕ}

/-- Two eliminated gates in a single size-minimum realization give the same vertex,
and indeed the same residual circuit, for every other correct realization. -/
theorem uniform_of_minimum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (minimum : ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → C.size ≤ E.size)
    (z : Fin n) (degree : G.degree z=2) (stable : ¬SidePeel.Drops G z)
    {j k : ℕ} (hj : j < C.size) (hk : k < C.size) (ne : j≠k) (badj : ¬Mg C {z} j) (badk : ¬Mg C {z} k) :
    ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → SavesAt G z E := by
  classical
  obtain ⟨D,dao,ev,bound⟩ := ZeroFold.compile C ao {z}
  let F := (Finset.range C.size).filter (Mg C {z})
  have sub : insert j (insert k F) ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|h
    · exact Finset.mem_range.mpr hj
    rcases Finset.mem_insert.mp h with rfl|h
    · exact Finset.mem_range.mpr hk
    · exact (Finset.mem_filter.mp h).1
  have count := Finset.card_le_card sub
  simp [F,ne,badj,badk] at count
  intro E eao ec
  have mins := minimum E eao ec
  refine ⟨D,dao,ev.trans (SidePeel.restrict_correct G C ok z),?_,fun h => (stable h).elim⟩
  omega

/-- Consume the output of the localized first-reader argument for the chosen optimum. -/
theorem of_localized_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (minimum : ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → C.size ≤ E.size)
    (B : Finset ℕ) (degree : ∀ a : Fin n, a.val∈B → G.degree a=2)
    (stable : ∀ a : Fin n, a.val∈B → ¬SidePeel.Drops G a)
    (two : ∃ a : Fin n, a.val∈B ∧ ∃ j<C.size, ∃ k<C.size, k≠j ∧ ¬Mg C {a} j ∧ ¬Mg C {a} k) :
    ∃ z : Fin n, 0<G.degree z ∧ ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → SavesAt G z E := by
  obtain ⟨z,member,j,hj,k,hk,ne,badj,badk⟩ := two
  exact ⟨z,by rw [degree z member]; decide,
    uniform_of_minimum G C ao ok minimum z (degree _ member) (stable _ member) hj hk ne.symm badj badk⟩

private theorem same_card (G : SimpleGraph (Fin n)) (a b : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G a).card = (@SimpleGraph.edgeFinset _ G b).card := by rw [Subsingleton.elim a b]

private structure Sharp (G : SimpleGraph (Fin n)) : Prop where
  bound : StableExtension.Numerical G (Loc.tau G)

/-- A uniform peel in each nontrivial subgraph suffices for the sharp numerical bound.
The induction keeps the graph on the same input type, including isolated vertices. -/
theorem sharp_of_subgraph_peels (G : SimpleGraph (Fin n))
    (peels : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → 2≤H.edgeFinset.card →
      ∃ z : Fin n, 0<H.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun H ∅ → SavesAt H z C) :
    StableExtension.Numerical G (Loc.tau G) := by
  suffices sharp : Sharp G from @sharp.bound
  classical
  generalize size : G.edgeFinset.card = k
  induction k using Nat.strong_induction_on generalizing G with
  | ind k ih =>
    by_cases acyc : G.IsAcyclic
    · exact ⟨@ForestExtension.forest_numerical n G acyc⟩
    obtain ⟨v,w,cy⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp acyc
    have many : 2≤G.edgeFinset.card := by
      have hi := cy.isTrail.length_le_card_edgeFinset
      have lo := cy.three_le_length
      omega
    obtain ⟨z,pos,cut⟩ := peels G le_rfl many
    let H := G.deleteIncidenceSet z
    have small : H.edgeFinset.card < k := by
      change (G.deleteIncidenceSet z).edgeFinset.card < k
      rw [G.card_edgeFinset_deleteIncidenceSet]
      have hd := G.degree_le_card_edgeFinset z
      omega
    have residual : Sharp H := ih H.edgeFinset.card small H (fun K _ sk => peels K (sk.trans (G.deleteIncidenceSet_le z))) (same_card _ _ _)
    exact ⟨@ForestExtension.lift_cut n G _ z cut (@Sharp.bound _ _ residual)⟩

/-- Pass any sharp numerical bound to the ownership card. -/
theorem ownership_of_sharp (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sharp : StableExtension.Numerical G (Loc.tau G)) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,cover,card⟩ := Loc.tau_attained G
  have bound := sharp C minimum.1 correct
  apply coveredDescent G C S cover _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

#print axioms of_localized_two
#print axioms uniform_of_minimum
#print axioms sharp_of_subgraph_peels
#print axioms ownership_of_sharp
end VertexPeel.LocalizedPeel
