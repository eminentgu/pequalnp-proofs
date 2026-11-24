import PairPins

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Triple2836

/-- The pinTwo premise of the uniform L-meta-2836 reduction. -/
theorem checkedPinTwo : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
      let q := fun x : Fin 9 → Bool => f (Function.update (Function.update x 0 false) 4 false)
      ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∃ h ∈ C.gates, h.op = GateOp.not) → (∀ x, C.eval (bank k x) = f x) →
        ∃ D : Circuit, FanInTwo D ∧ D.gates.countP (fun h => @decide (h.op ≠ GateOp.not) (Classical.propDecidable _)) ≤ 10 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = q x) := by
  intro f bank q k C fan size hasNot exactC
  have graphEq (x : Fin 9 → Bool) : f x = edge x := by
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.or_assoc, Bool.or_false]
  have normalized (x : Assignment) : C.eval (bank k x) = edge x := (exactC x).trans (graphEq x)
  have thetaEq (x : Assignment) : q x = theta x := by
    change f (Function.update (Function.update x 0 false) 4 false) = _
    rw [graphEq]
    simp [edge,theta,Function.update]
  obtain ⟨D,fanD,charged,computed⟩ : ∃ D : Circuit, FanInTwo D ∧
      D.gates.countP (fun h => @decide (h.op ≠ GateOp.not) (Classical.propDecidable _)) ≤ 10 ∧
      ∀ x : Assignment, D.eval (List.ofFn x) = theta x := by
    by_cases h0 : k = 0
    · subst k
      apply PairPins.pair_two_13 .left C fan size hasNot
      intro x
      rw [PairPins.bank_left]
      exact normalized x
    by_cases h4 : k = 4
    · subst k
      apply PairPins.pair_two_13 .right C fan size hasNot
      intro x
      rw [PairPins.bank_right]
      exact normalized x
    · apply pin_two_13 k h0 h4 C fan size hasNot
      intro x
      have ordinary : ¬(k = 0 ∨ k = 4) := fun h => h.elim h0 h4
      simpa only [bank, ite_eq_right ordinary] using normalized x
  exact ⟨D,fanD,charged,fun x => (computed x).trans (thetaEq x).symm⟩

end Triple2836
