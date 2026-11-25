import CycleCover
import StableExtension

namespace VertexPeel.CycleLeaf
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm

/-- A cover of size at most three on a cyclic girth-five graph is a minimum cover after every
leaf deletion. It contains the support vertex and excludes the leaf. -/
theorem restrict_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G) (cyclic : ¬G.IsAcyclic)
    {a u : Fin n} (au : G.Adj a u) (only : ∀ v, G.Adj a v → v = u)
    (T : Finset (Fin n)) (cover : IsVertexCover G T) (atMost : T.card ≤ 3) :
    a ∉ T ∧ u ∈ T ∧ T.card = 3 ∧ StableExtension.Minimum (G.deleteIncidenceSet a) T := by
  classical
  have sub := G.deleteIncidenceSet_le a
  have tri' : ShortCycle.TriangleFree (G.deleteIncidenceSet a) :=
    fun _ _ _ p q r => tri _ _ _ (sub p) (sub q) (sub r)
  have low := CycleCover.three_of_cyclic (G.deleteIncidenceSet a) tri'
    (square_cut G a square) (CycleCover.cyclic_delete_leaf au only cyclic)
  have er : IsVertexCover (G.deleteIncidenceSet a) (T.erase a) := by
    intro i j edge
    obtain ⟨e,ih,jh⟩ := SimpleGraph.deleteIncidenceSet_adj.mp edge
    exact (cover i j e).imp (fun h => Finset.mem_erase.mpr ⟨ih,h⟩)
      (fun h => Finset.mem_erase.mpr ⟨jh,h⟩)
  have small := low _ er
  have absent : a ∉ T := by
    intro ha
    have := Finset.card_erase_add_one ha
    omega
  have c : IsVertexCover (G.deleteIncidenceSet a) T := fun i j h => cover i j (sub h)
  exact ⟨absent,(cover a u au).resolve_left absent, Nat.le_antisymm atMost (low T c),
    c, fun S hs => atMost.trans (low S hs)⟩

#print axioms restrict_three
end VertexPeel.CycleLeaf
