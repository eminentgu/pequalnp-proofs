import ShortCycle
import PEqualNP.Defs.CoverPromise
import PEqualNP.MetaComplexity.Helpers.LocGraph

namespace VertexPeel.CycleCover

open SimpleGraph PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity PEqualNP.TopForm

/-- Restrict a cover along a graph embedding. -/
theorem cover_bound_of_embedding {m n k : ℕ} {H : SimpleGraph (Fin m)} {G : SimpleGraph (Fin n)}
    (e : H ↪g G) (bound : ∀ T, CoverPromise.IsVertexCover H T → k ≤ T.card)
    (S : Finset (Fin n)) (cover : CoverPromise.IsVertexCover G S) : k ≤ S.card := by
  classical
  let T := Finset.univ.filter (fun v => e v ∈ S)
  have member (i : Fin m) : i ∈ T ↔ e i ∈ S := by simp [T]
  have c : CoverPromise.IsVertexCover H T := by
    intro i j h
    exact (cover (e i) (e j) (e.map_rel_iff.mpr h)).imp (member i).mpr (member j).mpr
  exact (bound T c).trans (Finset.card_le_card_of_injOn e
      (fun v hv => (member v).mp hv) e.injective.injOn)

private theorem lower_five : ∀ S, CoverPromise.IsVertexCover (cycleGraph 5) S → 3 ≤ S.card := by
  unfold CoverPromise.IsVertexCover; decide +kernel

private theorem lower_six : ∀ S, CoverPromise.IsVertexCover (cycleGraph 6) S → 3 ≤ S.card := by
  unfold CoverPromise.IsVertexCover; decide +kernel

private theorem lower_path : ∀ S, CoverPromise.IsVertexCover (pathGraph 6) S → 3 ≤ S.card := by
  unfold CoverPromise.IsVertexCover; decide +kernel

theorem three_of_pattern {n : ℕ} (G : SimpleGraph (Fin n)) (pattern : ShortCycle.Pattern G)
    (S : Finset (Fin n)) (cover : CoverPromise.IsVertexCover G S) : 3 ≤ S.card := by
  rcases pattern with p | p | p <;> obtain ⟨e⟩ := p
  · exact cover_bound_of_embedding e lower_five S cover
  · exact cover_bound_of_embedding e lower_six S cover
  · exact cover_bound_of_embedding e lower_path S cover

theorem three_of_cyclic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G) (cyclic : ¬G.IsAcyclic)
    (S : Finset (Fin n)) (cover : CoverPromise.IsVertexCover G S) : 3 ≤ S.card :=
  three_of_pattern G (ShortCycle.of_cycle G tri square cyclic) S cover

theorem tau_three_of_cyclic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G) (cyclic : ¬G.IsAcyclic) :
    3 ≤ Loc.tau G := by
  obtain ⟨T,cover,size⟩ := Loc.tau_attained G
  exact size ▸ three_of_cyclic G tri square cyclic T cover

/-- The edge from a leaf is a bridge. Removing it preserves every cycle. -/
theorem cyclic_delete_leaf {n : ℕ} {G : SimpleGraph (Fin n)} {a u : Fin n}
    (au : G.Adj a u) (only : ∀ v, G.Adj a v → v = u) (cyclic : ¬G.IsAcyclic) :
    ¬(G.deleteIncidenceSet a).IsAcyclic := by
  intro acyclic
  have rebuild : (G.deleteIncidenceSet a) ⊔ SimpleGraph.edge a u = G := by
    ext i j
    change ( (G.deleteIncidenceSet a).Adj i j ∨ (SimpleGraph.edge a u).Adj i j ) ↔ _
    rw [SimpleGraph.deleteIncidenceSet_adj,SimpleGraph.edge_adj]
    constructor
    · rintro (⟨h,_,_⟩ | ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,_⟩)
      · exact h
      · exact au
      · exact au.symm
    · intro h
      by_cases ia : i = a
      · subst i; exact Or.inr ⟨Or.inl ⟨rfl,only j h⟩,h.ne⟩
      by_cases ja : j = a
      · subst j; exact Or.inr ⟨Or.inr ⟨only i h.symm,rfl⟩,h.ne⟩
      exact Or.inl ⟨h,ia,ja⟩
  have separate : ¬(G.deleteIncidenceSet a).Reachable a u := by
    intro reach
    obtain ⟨v,edge⟩ := reach.nonempty_neighborSet_left au.ne
    exact (SimpleGraph.deleteIncidenceSet_adj.mp edge).2.1 rfl
  exact cyclic (rebuild ▸ acyclic.sup_edge_of_not_reachable separate)

#print axioms three_of_cyclic
#print axioms cyclic_delete_leaf

end VertexPeel.CycleCover
