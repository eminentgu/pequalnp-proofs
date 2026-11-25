import PEqualNP.Outside.R_meta_1774_583
import PEqualNP.Outside.L_meta_8073

namespace PEqualNP.Outside.RepairEquivalence

abbrev Card1774 : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8

abbrev Card8075 : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : ℕ → ℕ → Prop := fun (x5 x6 : ℕ) => ∃ x7 < x4.size, x5 = x1 + x7 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x7).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 < x1 + x7 ∧ x6 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x7).inputs;   have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => ∃ (x8 : Fin x1) (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1), x2.Adj x8 x9 ∧ x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 ∧ x8 ≠ x10 ∧ x8 ≠ x11 ∧ x9 ≠ x10 ∧ x9 ≠ x11;   have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x8 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12;   (∀ (x8 x9 x10 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → ¬x2.Adj x10 x8) → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x7 x4 → ∀ (x13 : ℕ), x6 x4 x13 → (∀ x15 < x13, ¬x6 x4 x15) → ¬Relation.ReflTransGen x5 x4.output (x1 + x13) → ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x17 ∧ PEqualNP.MetaComplexity.circuitFun x1 x17 = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧ x17.size ≤ x4.size ∧ x7 x17 ∧ {x18 : ℕ | x6 x17 x18}.ncard < {x18 : ℕ | x6 x4 x18}.ncard

theorem repair_of_descent (descent : Card1774) : Card8075 := by
  intro n G inst C _readOR bad useful triangle square minimum correct ready j witnessed _first _masked
  classical
  have bounded : {i | bad C i} ⊆ Set.Iio C.size := by
    rintro i ⟨u,v,p,q,_,_,owned,_⟩
    exact owned.1
  have finite : {i | bad C i}.Finite := (Set.finite_Iio C.size).subset bounded
  have positive : 0 < {i | bad C i}.ncard :=
    (Set.ncard_pos finite).2 ⟨j,witnessed⟩
  obtain ⟨D,legal,agrees,budget,productive,fewer⟩ :=
    descent n G triangle square C minimum correct ready positive
  exact ⟨D,legal,agrees.trans correct.symm,budget,productive,fewer⟩

theorem descent_iff_repair : Card1774 ↔ Card8075 :=
  ⟨repair_of_descent, PEqualNP.Outside.R_meta_1774_583 PEqualNP.Outside.L_meta_8073⟩

#print axioms descent_iff_repair

end PEqualNP.Outside.RepairEquivalence
