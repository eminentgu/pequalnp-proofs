import FiniteCritical
import MaskEncode
import Canonical186
import ExitCore
import ResidualTransport
import ListedNumerical
import CoverThree

namespace VertexPeel.CoverFour

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774
open VertexPeel.CoverThreeCore VertexPeel.CoverFourClass VertexPeel.CoverFourTransport

/-- The published forest bound in the numerical form used by the leaf induction. -/
private theorem forest_four {n : ℕ} (G : SimpleGraph (Fin n)) (forest : G.IsAcyclic)
    (size : Loc.tau G = 4) : StableExtension.Numerical G 4 := by
  intro inst C mono correct
  classical
  have edge : ∃ a b, G.Adj a b := by
    by_contra! none
    have zero := Loc.tau_le G ∅ (fun a b h => (none a b h).elim)
    simp at zero
    omega
  have minc (T : Finset (Fin n)) (c : IsVertexCover G T) : 4 ≤ T.card := size ▸ Loc.tau_le G T c
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨op,arity⟩ := mono g hg
    refine ⟨?_,arity⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    tauto
  have has : HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) C.size := by
    refine ⟨C,fan,le_rfl,?_⟩
    intro x
    simpa [circuitFun,graphFun] using congrFun correct x
  have lo := PEqualNP.MetaComplexity.L104 n 4 C.size G forest edge minc has
  have edges : G.edgeSet.ncard = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  omega

/-- The predicates used below concern graph codes only; circuit sizes and numbers of
isolated vertices in the input graph are unrestricted. -/
def Classifies : Prop := ∀ z : Mask4.Code, NoTriangles (Mask4.graph z) → NoFourCycle (Mask4.graph z) →
    Loc.tau (Mask4.graph z) = 4 → ∃ i : Fin 186,
      Nonempty (Mask4.graph z ≃g Mask4.graph (canonicalCode i)) ∧ Exit (canonicalCode i)

theorem from_classification (classification : Classifies) {n : ℕ} (G : SimpleGraph (Fin n))
    [base : DecidableRel G.Adj] (tri : NoTriangles G) (sq : NoFourCycle G) (size : Loc.tau G = 4) :
    StableExtension.Numerical G 4 := by
  intro inst C mono correct
  have same : inst = base := Subsingleton.elim _ _
  subst inst
  apply FiniteCritical.of_small_order G tri sq size (by decide) _ C mono correct
  intro m _ H decH triH squareH coverSize crit activeH dec D dm dc
  have same' : dec = decH := Subsingleton.elim _ _
  subst dec
  obtain ⟨T,c,count⟩ := Loc.tau_attained H
  obtain ⟨z,⟨e⟩⟩ := Mask4.exists_code H T c (count.trans coverSize) squareH
    (CriticalSupport.no_twins H crit) activeH
  have sizeZ := (tau_of_iso e).symm.trans coverSize
  obtain ⟨i,⟨e'⟩,exit⟩ := classification z (triangle_of_iso e triH) (square_of_iso e squareH) sizeZ
  let iso := e.trans e'
  let J := Mask4.graph (canonicalCode i)
  have sizeJ : Loc.tau J = 4 := (tau_of_iso iso).symm.trans coverSize
  have criticalJ : CriticalSupport.AllLeavesCritical J := critical_of_iso iso crit
  have lower : StableExtension.Numerical J 4 := by
    rcases exit with forest|stable|remaining
    · exact @forest_four _ J forest sizeJ
    · obtain ⟨a,leaf,lower⟩ := stable
      obtain ⟨U,coverU,sz⟩ := Loc.tau_attained (J.deleteIncidenceSet a)
      have aBound := lower U coverU
      have drops := criticalJ _ leaf
      omega
    · obtain ⟨r,⟨eq⟩⟩ := remaining
      exact @numerical_of_iso _ _ _ J (CoverFourResidual.graph r) eq (@CoverFourResidual.listedNumerical r)
  exact numerical_of_iso iso lower D dm dc

end VertexPeel.CoverFour
