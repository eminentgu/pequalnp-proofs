import Fano27
import BoundaryRows

namespace PEqualNP.Research2583.Fano
open Boundary

-- Count the positive and negative boundary tests from the verified incidence table.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem boundary_counts :
    flags.length = 21 ∧
    ((Finset.univ : Finset (Fin 7)).powerset.filter
      (fun X => X = farPoints I (farLines I X))).card = 37 := by
  decide +kernel

#print axioms boundary_counts
end PEqualNP.Research2583.Fano
