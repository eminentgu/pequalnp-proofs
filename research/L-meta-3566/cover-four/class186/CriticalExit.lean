import ExitCore
import PEqualNP.MetaComplexity.Helpers.LocGraph

namespace VertexPeel.CoverFourClass
open PEqualNP.MetaComplexity
/-- A cyclic minimum-cover-four graph whose leaves all lower the minimum
    cover size can only use the named-representative branch of the certificate. -/
theorem criticalExit {z : Mask4.Code} (classified : Exit z)
    (cyclic : ¬ (Mask4.graph z).IsAcyclic) (bound : Loc.tau (Mask4.graph z) ≤ 4)
    (crit : ∀ a, (Mask4.graph z).degree a = 1 →
      Loc.tau ((Mask4.graph z).deleteIncidenceSet a) < Loc.tau (Mask4.graph z)) :
    ∃ i : Fin 17, Nonempty (Mask4.graph z ≃g CoverFourResidual.graph i) := by
  rcases classified with forest | ⟨a, degree, stable⟩ | named
  · exact (cyclic forest).elim
  · obtain ⟨S, covers, size⟩ := Loc.tau_attained ((Mask4.graph z).deleteIncidenceSet a)
    have four := stable S covers
    have drop := crit a degree
    exact (Nat.not_lt_of_ge (four.trans_eq size) (drop.trans_le bound)).elim
  · exact named
end VertexPeel.CoverFourClass
