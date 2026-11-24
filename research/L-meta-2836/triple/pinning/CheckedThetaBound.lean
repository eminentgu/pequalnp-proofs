import Theta2960Core
import PEqualNP.Outside.L_meta_2960

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Triple2836

/-- The uniform thetaBound subproblem, discharged by the merged L-meta-2960 theorem. -/
theorem checkedThetaBound : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let q := fun x : Fin 9 → Bool => f (Function.update (Function.update x 0 false) 4 false)
      ∀ D : Circuit, FanInTwo D ∧ D.gates.countP (fun h => h.op.ctorIdx != GateOp.not.ctorIdx) ≤ 10 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = q x) → False :=
  theta_of_2960 PEqualNP.Outside.L_meta_2960

end Triple2836
