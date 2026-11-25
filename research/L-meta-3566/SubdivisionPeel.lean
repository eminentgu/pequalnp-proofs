import SidePeel
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace VertexPeel.SubdivisionPeel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm VertexPeel.SidePeel

/-- If the smaller color class has minimum degree at least d+1 and the other
    has maximum degree d, deleting one vertex of the latter preserves cover
    number. After deletion each omitted vertex of the former still has d
    neighbors in the cover, and each can serve at most d omitted vertices. -/
theorem stable_of_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (cross : ∀ u v : Fin n, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (d : ℕ) (positive : 0 < d) (lower : ∀ u ∈ A, d+1 ≤ G.degree u)
    (upper : ∀ v ∉ A, G.degree v ≤ d) (z : Fin n) (outside : z ∉ A) :
    ¬Drops G z := by
  classical
  rintro ⟨S,cover,smaller⟩
  have coverA : IsVertexCover G A := by
    intro u v uv
    by_cases h : u ∈ A
    · exact Or.inl h
    · exact Or.inr (not_not.mp (fun nv => h ((cross _ _ uv).mpr nv)))
  have lo (u : Fin n) (hu : u ∈ A \ S) : d ≤ ((S \ A).bipartiteAbove G.Adj u).card := by
    obtain ⟨ua,us⟩ := Finset.mem_sdiff.mp hu
    have uz : u ≠ z := fun e => outside (e ▸ ua)
    have sub : (G.neighborFinset u).erase z ⊆ (S \ A).bipartiteAbove G.Adj u := by
      intro v hv
      obtain ⟨vz,hv⟩ := Finset.mem_erase.mp hv
      have uv := (G.mem_neighborFinset u v).mp hv
      have vs := (cover u v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,uz,vz⟩)).resolve_left us
      exact (Finset.mem_bipartiteAbove G.Adj).mpr ⟨Finset.mem_sdiff.mpr ⟨vs,(cross _ _ uv).mp ua⟩,uv⟩
    apply le_trans _ (Finset.card_le_card sub)
    have h := lower _ ua
    rw [← G.card_neighborFinset_eq_degree] at h
    by_cases zmem : z ∈ G.neighborFinset u
    · have := Finset.card_erase_add_one zmem
      omega
    · rw [Finset.erase_eq_of_notMem zmem]
      omega
  have hi (v : Fin n) (hv : v ∈ S \ A) : ((A \ S).bipartiteBelow G.Adj v).card ≤ d := by
    have sub : (A \ S).bipartiteBelow G.Adj v ⊆ G.neighborFinset v := by
      intro u hu
      exact (G.mem_neighborFinset v u).mpr ((Finset.mem_bipartiteBelow G.Adj).mp hu).2.symm
    exact (Finset.card_le_card sub).trans (by simpa using upper _ (Finset.mem_sdiff.mp hv).2)
  have count := Finset.card_nsmul_le_card_nsmul G.Adj lo hi
  have bound : (A \ S).card ≤ (S \ A).card := by
    simpa [Nat.nsmul_eq_mul, Nat.mul_le_mul_right_iff positive] using count
  exact (Nat.not_lt_of_ge (Finset.card_sdiff_le_card_sdiff_iff.mp bound)) (smaller A coverA)

/-- Every C4-free bipartite graph with degrees exactly two on one side and
    at least three on the opposite side satisfies the exact one-vertex peel. -/
theorem peel_subdivision {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (nonempty : ∃ b : Fin n, b ∉ A)
    (cross : ∀ u v : Fin n, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (square : NoFourCycle G) (lower : ∀ u ∈ A, 3 ≤ G.degree u)
    (two : ∀ b ∉ A, G.degree b = 2) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = (fun y : Fin n → Bool =>
        @decide (∃ u v : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj u v ∧ y u = true ∧ y v = true)
          (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
          (Drops G z → D.size + G.degree z + 1 ≤ C.size) := by
  classical
  let B := Aᶜ.image Fin.val
  have mem (z : Fin n) : z.val ∈ B ↔ z ∉ A := by
    simp [B,Fin.val_inj]
  obtain ⟨b,hb⟩ := nonempty
  apply SidePeel.peel G B
  · intro t ht
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ht
    exact v.isLt
  · exact ⟨b.val,(mem b).mpr hb⟩
  · intro u v hu hv uv
    exact (cross u v uv).mp (not_not.mp (fun e => hu ((mem u).mpr e))) (not_not.mp (fun e => hv ((mem v).mpr e)))
  · intro a ha
    have out := (mem a).mp ha
    have pos : 0 < G.degree a := by simp [two a out]
    obtain ⟨v,e⟩ := (G.degree_pos_iff_exists_adj a).mp pos
    exact ⟨v,fun h => (mem v).mp h ((cross v a e.symm).mpr out),e.symm⟩
  · exact square
  · exact fun a h => two a ((mem a).mp h)
  · exact fun a h => stable_of_degrees G A cross 2 (by decide) lower (fun v hv => (two v hv).le)
      a ((mem a).mp h)

end VertexPeel.SubdivisionPeel
