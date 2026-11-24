import MonotoneExact
import PEqualNP.Outside.L_meta_1922

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Research2836.Monotone

/-- Unconditional discharge of the monotone premise in R_meta_2836_412. -/
theorem checked :
    let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
      ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ h ∈ C.gates, h.op ≠ GateOp.not) → (∀ x, C.eval (bank k x) = f x) → False := from_raw_statement PEqualNP.Outside.L_meta_1922

#print axioms checked
end PEqualNP.Research2836.Monotone
