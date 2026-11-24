import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

namespace CubicCoverDeletion

def Covers {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T

def MinimumCover {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  Covers G T ∧ ∀ U, Covers G U → T.card ≤ U.card

-- The two covers differ by exactly one vertex, even without degree assumptions.
theorem minimumCover_erase {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (minimum : MinimumCover G T) (z : Fin n) (member : z ∈ T) :
    MinimumCover (G.deleteIncidenceSet z) (T.erase z) := by
  classical
  constructor
  · intro i j adj
    obtain ⟨orig, hi, hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp adj
    rcases minimum.1 i j orig with h | h
    · exact Or.inl (Finset.mem_erase.mpr ⟨hi, h⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hj, h⟩)
  · intro U cover
    have lift : Covers G (insert z U) := by
      intro i j adj
      by_cases hi : i = z
      · exact Or.inl (by simp [hi])
      by_cases hj : j = z
      · exact Or.inr (by simp [hj])
      rcases cover i j (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨adj, hi, hj⟩) with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr (Finset.mem_insert_of_mem h)
    have hmin := minimum.2 (insert z U) lift
    have hsize := Finset.card_erase_add_one member
    have hins : (insert z U).card ≤ U.card + 1 := Finset.card_insert_le _ _
    omega

-- The budget counts gates in the usual construction that groups edges under cover vertices.
noncomputable def coverBudget {n : ℕ} (G : SimpleGraph (Fin n)) (A T : Finset (Fin n)) : ℕ :=
  A.card + G.edgeSet.ncard + T.card - 1

theorem cubic_cover_budget_drop_at {n : ℕ} (G : SimpleGraph (Fin n))
    (A T : Finset (Fin n)) (minimum : MinimumCover G T)
    (cubic : ∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3)
    (unmarked : ∀ i j : Fin n, G.Adj i j → i ∉ A)
    (z : Fin n) (member : z ∈ T) (ordinary : z ∉ A) :
    MinimumCover (G.deleteIncidenceSet z) (T.erase z) ∧
      coverBudget G A T = coverBudget (G.deleteIncidenceSet z) A (T.erase z) + 4 := by
  classical
  refine ⟨minimumCover_erase G T minimum z member, ?_⟩
  have degree (v : Fin n) (h : v ∉ A) : G.degree v = 3 := by
    simpa only [SimpleGraph.ncard_neighborSet] using cubic v h
  have hzdeg := degree z ordinary
  have nz : (G.neighborFinset z).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hzdeg]
    decide
  obtain ⟨v, hv⟩ := nz
  have hzv : G.Adj z v := by simpa using hv
  have hvdeg := degree v (unmarked v z hzv.symm)
  have nsub : ¬ G.neighborFinset v ⊆ {z} := by
    intro hs
    have hh := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree, hvdeg, Finset.card_singleton] at hh
    omega
  obtain ⟨w, hw, hwz⟩ := Finset.not_subset.mp nsub
  have hvw : G.Adj v w := by simpa using hw
  have hwne : w ≠ z := by simpa using hwz
  let K := G.deleteIncidenceSet z
  have hsurvives : K.Adj v w :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hvw, G.ne_of_adj hzv.symm, hwne⟩
  have positive : 0 < K.edgeSet.ncard := by
    have card_eq : K.edgeFinset.card = K.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [← card_eq]
    exact Finset.card_pos.mpr ⟨s(v,w), by simpa using hsurvives⟩
  have hEdges : K.edgeSet.ncard = G.edgeSet.ncard - 3 := by
    simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hzdeg]
      using G.card_edgeFinset_deleteIncidenceSet z
  have hT := Finset.card_erase_add_one member
  change A.card + G.edgeSet.ncard + T.card - 1 = A.card + K.edgeSet.ncard + (T.erase z).card - 1 + 4
  omega

theorem cubic_cover_budget_drop {n : ℕ} (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
    (minimum : MinimumCover G T)
    (cubic : ∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3)
    (unmarked : ∀ i j : Fin n, G.Adj i j → i ∉ A)
    (edge : ∃ u v : Fin n, G.Adj u v) :
    ∃ z : Fin n, z ∈ T ∧ z ∉ A ∧ MinimumCover (G.deleteIncidenceSet z) (T.erase z) ∧
      coverBudget G A T = coverBudget (G.deleteIncidenceSet z) A (T.erase z) + 4 := by
  obtain ⟨u, v, h⟩ := edge
  rcases minimum.1 u v h with hu | hv
  · exact ⟨u, hu, unmarked u v h, cubic_cover_budget_drop_at G A T minimum cubic unmarked u hu (unmarked u v h)⟩
  · exact ⟨v, hv, unmarked v u h.symm, cubic_cover_budget_drop_at G A T minimum cubic unmarked v hv (unmarked v u h.symm)⟩

-- For circuit minima s and t, their savings over the cover construction may be positive.
-- The desired deletion holds precisely when those savings do not shrink after deletion.
theorem circuit_savings_criterion {fullBudget deletedBudget s t : ℕ}
    (drop : fullBudget = deletedBudget + 4) (fullUpper : s ≤ fullBudget)
    (deletedUpper : t ≤ deletedBudget) :
    t + 4 ≤ s ↔ fullBudget - s ≤ deletedBudget - t := by
  omega

end CubicCoverDeletion
