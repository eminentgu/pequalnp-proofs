import MonotoneTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Research2836.Monotone

/-- The first premise of #8269 follows from the exact public statement of L-meta-1922. -/
theorem from_raw_statement
    (raw : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size) :
    let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
      ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ h ∈ C.gates, h.op ≠ GateOp.not) → (∀ x, C.eval (bank k x) = f x) → False := transport raw

end PEqualNP.Research2836.Monotone
