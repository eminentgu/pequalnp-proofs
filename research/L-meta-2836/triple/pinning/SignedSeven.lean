import Theta2960Core

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Triple2836.Pinning

namespace Triple2836

/-- The B input encoding with a NOT gate yields a seven-input circuit with at most ten charged gates. -/
theorem signedSeven : let edge := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        (∃ g ∈ C.gates, g.op = GateOp.not) →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = edge x) →
        ∃ D : Circuit, FanInTwo D ∧ (circuitFun 7 D = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) ∧
          List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) D.gates ≤ 10 := by
  intro f C fan size hasNot computes
  have graphEq (x : Fin 9 → Bool) : f x = edge x := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.or_assoc, Bool.or_false]
  obtain ⟨D,fanD,bound,computed⟩ := PairPins.pair_two_13 .right C fan size hasNot (by
    intro x
    rw [PairPins.bank_right]
    exact (computes x).trans (graphEq x))
  obtain ⟨E,fanE,nonincrease,evalE⟩ := strip_theta_dummies D fanD computed
  have ten : cost D.gates ≤ 10 := by simpa only [cost_spec] using bound
  refine ⟨E,fanE,evalE,?_⟩
  have eq : (fun g : Gate => GateOp.rec (motive := fun _ => Bool)
      true true false (fun _ => true) true g.op) = charged := by
    funext g
    obtain ⟨op,pins⟩ := g
    cases op <;> rfl
  rw [eq]
  change cost E.gates ≤ 10
  omega

end Triple2836
