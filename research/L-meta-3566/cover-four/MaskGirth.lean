import MonoMask
import Raw8144

namespace VertexPeel.Mask4
open PEqualNP.TopForm VertexPeel.CoverThreeCore
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

local instance (m : Code) : Decidable (NoTriangles (graph m)) := by unfold NoTriangles; infer_instance

/-- Each mask has its own explicit triangle or square in its decoded graph. -/
private theorem invalid_masks : ∀ m ∈ girthMasks,
    ¬ (NoTriangles (graph m) ∧ NoFourCycle (graph m)) := by
  have checked : girthMasks.all (fun m => decide (¬ (NoTriangles (graph m) ∧ NoFourCycle (graph m)))) = true := by decide +kernel
  exact fun m mem => of_decide_eq_true (List.all_eq_true.mp checked m mem)

theorem girth_bits (z : Code) (tri : NoTriangles (graph z)) (sq : NoFourCycle (graph z)) :
    smallGirthB z = true := by
  apply List.all_eq_true.mpr
  intro m mem
  apply bne_iff_ne.mpr
  intro eq
  obtain ⟨f,hom⟩ := mono_embedding eq
  exact invalid_masks m mem (girth_of_injection f hom tri sq)

#print axioms girth_bits
end VertexPeel.Mask4
