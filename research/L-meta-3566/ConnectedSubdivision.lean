import SubdivisionPeel
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace VertexPeel.ConnectedSubdivision
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm VertexPeel.SidePeel

/-- Strict neighbor expansion follows from connectedness and one vertex of
    degree greater than d when the degrees on the two sides straddle d. -/
theorem expand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (cross : ∀ u v : Fin n, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (connected : G.Preconnected) (d : ℕ) (lower : ∀ a ∈ A, d ≤ G.degree a)
    (upper : ∀ b ∉ A, G.degree b ≤ d) (branch : ∃ a ∈ A, d < G.degree a)
    (X : Finset (Fin n)) (sub : X ⊆ A) (someX : X.Nonempty) :
    X.card < (X.biUnion (fun u => G.neighborFinset u)).card := by
  classical
  let Y := X.biUnion (fun u => G.neighborFinset u)
  change X.card < Y.card
  have ya (y : Fin n) (hy : y ∈ Y) : y ∉ A := by
    obtain ⟨x,hx,xy⟩ := Finset.mem_biUnion.mp hy
    exact (cross x y ((G.mem_neighborFinset x y).mp xy)).mp (sub hx)
  let f (x : Fin n) := (Y.bipartiteAbove G.Adj x).card
  let g (y : Fin n) := (X.bipartiteBelow G.Adj y).card
  have whole (x : Fin n) (hx : x ∈ X) : Y.bipartiteAbove G.Adj x = G.neighborFinset x := by
    ext y
    simp only [Finset.mem_bipartiteAbove,G.mem_neighborFinset]
    exact ⟨And.right,fun xy => ⟨Finset.mem_biUnion.mpr ⟨x,hx,(G.mem_neighborFinset x y).mpr xy⟩,xy⟩⟩
  have part (y : Fin n) : X.bipartiteBelow G.Adj y ⊆ G.neighborFinset y := by
    intro x hx
    exact (G.mem_neighborFinset y x).mpr ((Finset.mem_bipartiteBelow G.Adj).mp hx).2.symm
  have fu (x : Fin n) (hx : x ∈ X) : f x = G.degree x := by simp [f,whole x hx]
  have gg (y : Fin n) : g y ≤ G.degree y := by simpa [g] using Finset.card_le_card (part y)
  have flo : ∀ x ∈ X, d ≤ f x := fun x hx => (lower x (sub hx)).trans_eq (fu x hx).symm
  have ghi : ∀ y ∈ Y, g y ≤ d := fun y hy => (gg y).trans (upper y (ya y hy))
  by_contra! no
  have fsum : (∑ _ ∈ X, d) ≤ ∑ x ∈ X, f x := Finset.sum_le_sum flo
  have gsum : (∑ y ∈ Y, g y) ≤ ∑ _ ∈ Y, d := Finset.sum_le_sum ghi
  have same : (∑ x ∈ X, f x) = ∑ y ∈ Y, g y := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
  have oppos : (∑ _ ∈ Y, d) ≤ ∑ _ ∈ X, d := by simpa using Nat.mul_le_mul_right d no
  have feq := (Finset.sum_eq_sum_iff_of_le flo).mp (le_antisymm fsum (same.le.trans (gsum.trans oppos)))
  have geq := (Finset.sum_eq_sum_iff_of_le ghi).mp (le_antisymm gsum (oppos.trans (fsum.trans same.le)))
  have yop (y : Fin n) (hy : y ∈ Y) : X.bipartiteBelow G.Adj y = G.neighborFinset y := by
    apply Finset.eq_of_subset_of_card_le (part y)
    change _ ≤ g y
    rw [G.card_neighborFinset_eq_degree,geq y hy]
    exact upper y (ya y hy)
  have closed (u v : Fin n) (uv : G.Adj u v) (h : u ∈ X ∪ Y) : v ∈ X ∪ Y := by
    rcases Finset.mem_union.mp h with hx | hy
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u,hx,(G.mem_neighborFinset u v).mpr uv⟩)
    · have vhit : v ∈ X.bipartiteBelow G.Adj u := by
        rw [yop _ hy]
        exact (G.mem_neighborFinset u v).mpr uv
      exact Finset.mem_union_left _ ((Finset.mem_bipartiteBelow G.Adj).mp vhit).1
  obtain ⟨w,wa,high⟩ := branch
  obtain ⟨x,hx⟩ := someX
  have reached := (G.reachable_iff_reflTransGen x w).mp (connected x w)
  have wmem : w ∈ X ∪ Y := by
    clear wa high
    induction reached with
    | refl => exact Finset.mem_union_left _ hx
    | tail _ edge ih => exact closed _ _ edge ih
  have wx := (Finset.mem_union.mp wmem).resolve_right (fun h => ya w h wa)
  exact high.ne ((feq w wx).trans (fu w wx))

/-- The Hall inequalities survive deletion of any one vertex of the right
    side if all nonempty left sets have strictly more neighbors than members. -/
theorem stable_of_expand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (cross : ∀ u v : Fin n, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (exp : ∀ X ⊆ A, X.Nonempty → X.card < (X.biUnion (fun u => G.neighborFinset u)).card) (z : Fin n) (hz : z ∉ A) :
    ¬Drops G z := by
  classical
  rintro ⟨S,hs,small⟩
  have ca : IsVertexCover G A := by
    intro u v e
    by_cases hu : u ∈ A
    · exact Or.inl hu
    · exact Or.inr (not_not.mp (fun nv => hu ((cross _ _ e).mpr nv)))
  have sA := small A ca
  have lt : (S \ A).card < (A \ S).card := Finset.card_sdiff_lt_card_sdiff_iff.mpr sA
  let X := A \ S
  have nonempty : X.Nonempty := Finset.card_pos.mp (by change 0 < (A \ S).card; omega)
  have grow := exp X Finset.sdiff_subset nonempty
  have sub : X.biUnion (fun u => G.neighborFinset u) ⊆ insert z (S \ A) := by
    intro v hv
    obtain ⟨u,hu,uv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨ua,us⟩ := Finset.mem_sdiff.mp hu
    have adj := (G.mem_neighborFinset u v).mp uv
    by_cases vz : v = z
    · simp [vz]
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
        ⟨(hs _ _ (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨adj,fun e => hz (e ▸ ua),vz⟩)).resolve_left us,
          (cross u v adj).mp ua⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  change (A \ S).card < _ at grow
  omega


/-- One branching vertex suffices on a connected graph with minimum degree two. -/
theorem peel_connected_subdivision {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (nonempty : ∃ b : Fin n, b ∉ A)
    (cross : ∀ u v : Fin n, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (connected : G.Preconnected) (square : NoFourCycle G) (lower : ∀ u ∈ A, 2 ≤ G.degree u)
    (branch : ∃ u ∈ A, 2 < G.degree u)
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
  · exact fun a h => stable_of_expand G A cross
      (expand G A cross connected 2 lower (fun v hv => (two v hv).le) branch) a ((mem a).mp h)

end VertexPeel.ConnectedSubdivision
