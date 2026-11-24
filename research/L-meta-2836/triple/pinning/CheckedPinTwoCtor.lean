import CheckedPinTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Triple2836.Pinning

namespace Triple2836

theorem cost_ctorIdx (gs : List Gate) :
    cost gs = gs.countP (fun h => h.op.ctorIdx != GateOp.not.ctorIdx) := by
  have eq : charged = (fun h : Gate => h.op.ctorIdx != GateOp.not.ctorIdx) := by
    funext g
    obtain ⟨op,pins⟩ := g
    cases op <;> rfl
  simp only [cost, eq]

/-- The uniform pinning theorem with a computable gate discriminator. -/
theorem checkedPinTwoCtor : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e))
      let bank := fun (k : Fin 9) (x : Fin 9 → Bool) =>
        let p := k = 0 ∨ k = 4
        List.ofFn (if p then Function.update x k false else x) ++
          [if p then x 0 || x 4 else false, if p then x k || x (if k = 0 then 3 else 1) else x 0 || x 4 || x k]
      let q := fun x : Fin 9 → Bool => f (Function.update (Function.update x 0 false) 4 false)
      ∀ (k : Fin 9) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∃ h ∈ C.gates, h.op = GateOp.not) → (∀ x, C.eval (bank k x) = f x) →
        ∃ D : Circuit, FanInTwo D ∧ D.gates.countP (fun h => h.op.ctorIdx != GateOp.not.ctorIdx) ≤ 10 ∧ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = q x) := by
  intro f bank q k C fan size hasNot computes
  obtain ⟨D,fanD,bound,output⟩ := checkedPinTwo k C fan size hasNot computes
  exact ⟨D,fanD,by rwa [← cost_ctorIdx, cost_spec],output⟩

end Triple2836
