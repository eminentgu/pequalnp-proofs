import PEqualNP.Defs

namespace SingletonPathExample
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

deriving instance DecidableEq for GateOp

/-- The third right vertex is isolated. The nonisolated vertices form a five-vertex path. -/
def edge (p l : Fin 3) : Prop :=
  (p = 0 ∧ (l = 0 ∨ l = 1)) ∨ (p = 1 ∧ l = 1) ∨ (p = 2 ∧ l = 0)

instance : DecidableRel edge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def dirtyCircuit : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.and,[6,7]⟩, ⟨.and,[8,3]⟩,
    ⟨.and,[2,3]⟩, ⟨.and,[6,4]⟩, ⟨.or,[9,10]⟩, ⟨.or,[12,11]⟩], 13⟩

def cleanCircuit : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.and,[6,4]⟩, ⟨.and,[7,3]⟩, ⟨.or,[8,9]⟩], 10⟩

theorem four_free : ∀ p q l k : Fin 3, p ≠ q → l ≠ k →
    ¬ (edge p l ∧ edge p k ∧ edge q l ∧ edge q k) := by decide

def target (z : Fin 6 → Bool) : Prop :=
  ∃ p l : Fin 3, edge p l ∧ z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true
instance (z : Fin 6 → Bool) : Decidable (target z) := inferInstanceAs (Decidable (∃ _ _, _))

theorem dirty_value : ∀ z : Fin 6 → Bool, circuitFun 6 dirtyCircuit z = true ↔ target z := by
  decide

theorem clean_value : ∀ z : Fin 6 → Bool, circuitFun 6 cleanCircuit z = true ↔ target z := by
  decide

theorem dirty_singleton :
    (gateAt dirtyCircuit 2).op = .and ∧
    (dirtyCircuit.wires (List.ofFn (fun i : Fin 6 => decide (i = 0)))).getD 8 false = true := by
  decide

theorem shared_source :
    ((dirtyCircuit.gates.map Gate.inputs).flatten.count 6) = 2 ∧
    ((dirtyCircuit.gates.map Gate.inputs).flatten.count 7) = 1 := by decide

/-- Treat wire h=x∨y as an independent input. On the resulting formal singleton
assignments the two operands of the dirty AND, h and x∨z, never both hold. -/
theorem no_common_formal_atom : ∀ i : Fin 3,
    (decide (i = 0) && (decide (i = 1) || decide (i = 2))) = false := by decide

theorem clean_singletons : ∀ j : Fin 5, (gateAt cleanCircuit j).op = .and →
    ∀ i : Fin 6, (cleanCircuit.wires (List.ofFn (fun k : Fin 6 => decide (k = i)))).getD (6+j) false = false := by
  decide

end SingletonPathExample
