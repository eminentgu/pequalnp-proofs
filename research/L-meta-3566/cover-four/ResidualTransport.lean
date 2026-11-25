import CriticalSupport
import IsolatedCore
import CoverThreeCore

namespace VertexPeel.CoverFourTransport

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open VertexPeel.CriticalSupport VertexPeel.StableExtension VertexPeel.CoverThreeCore

/-- A minimum cover and its image cover have the same cardinality. -/
theorem tau_of_iso {m n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) : Loc.tau G = Loc.tau H := by
  classical
  have le {m n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)} (f : G ≃g H) :
      Loc.tau H ≤ Loc.tau G := by
    obtain ⟨T,cover,card⟩ := Loc.tau_attained G
    have c : IsVertexCover H (T.map f.toEquiv.toEmbedding) := by
      intro v w edge
      have pre : G.Adj (f.symm v) (f.symm w) := f.symm.map_rel_iff.mpr edge
      rcases cover _ _ pre with hv | hw
      · exact Or.inl (Finset.mem_map.mpr ⟨f.symm v,hv,f.apply_symm_apply v⟩)
      · exact Or.inr (Finset.mem_map.mpr ⟨f.symm w,hw,f.apply_symm_apply w⟩)
    simpa [← card] using Loc.tau_le H _ c
  exact le_antisymm (le e.symm) (le e)

/-- Cutting all edges at a vertex commutes with relabelling. -/
def cutIso {m n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) (v : Fin n) : G.deleteIncidenceSet v ≃g H.deleteIncidenceSet (e v) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    change (H.deleteIncidenceSet (e v)).Adj (e a) (e b) ↔ (G.deleteIncidenceSet v).Adj a b
    simp only [SimpleGraph.deleteIncidenceSet_adj,e.map_rel_iff,e.injective.ne_iff]

theorem critical_of_iso {m n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (critical : AllLeavesCritical G) :
    AllLeavesCritical H := by
  intro y deg
  let x := e.symm y
  have xy : e x = y := e.apply_symm_apply _
  have dx : G.degree x = 1 := (e.degree_eq x).symm.trans (xy ▸ deg)
  have cut := tau_of_iso (cutIso e x)
  rw [xy] at cut
  rw [← cut,← tau_of_iso e]
  exact critical x dx

theorem triangle_of_iso {m n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) (tri : NoTriangles G) : NoTriangles H := by
  intro a b c ab bc ca
  exact tri (e.symm a) (e.symm b) (e.symm c)
    (e.symm.map_rel_iff.mpr ab) (e.symm.map_rel_iff.mpr bc) (e.symm.map_rel_iff.mpr ca)

theorem square_of_iso {m n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (sq : NoFourCycle G) : NoFourCycle H := by
  intro a b ne
  apply le_trans _ (sq (e.symm a) (e.symm b) (e.symm.injective.ne ne))
  apply Finset.card_le_card_of_injOn e.symm
  · intro v hv
    obtain ⟨av,bv⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.symm.map_rel_iff.mpr av,e.symm.map_rel_iff.mpr bv⟩
  · exact e.symm.injective.injOn

/-- Circuit relabelling preserves size, and graph isomorphism preserves the edge count. -/
theorem numerical_of_iso {m n t : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) (bound : Numerical H t) : Numerical G t := by
  intro gd C mono ok
  classical
  obtain ⟨D,dm,dc,size⟩ := IsolatedCore.retract_circuit H G e.symm.toRelEmbedding
    e (fun x => e.apply_symm_apply x) (fun _ _ ab => e.map_rel_iff.mpr ab) C mono ok
  have lo := bound D dm dc
  rw [size,← e.card_edgeFinset_eq] at lo
  exact lo
end VertexPeel.CoverFourTransport
#print axioms VertexPeel.CoverFourTransport.tau_of_iso
#print axioms VertexPeel.CoverFourTransport.critical_of_iso
#print axioms VertexPeel.CoverFourTransport.numerical_of_iso
#print axioms VertexPeel.CoverFourTransport.triangle_of_iso
#print axioms VertexPeel.CoverFourTransport.square_of_iso
