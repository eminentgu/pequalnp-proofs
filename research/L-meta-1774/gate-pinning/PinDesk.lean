import PinDescent

namespace PEqualNP.Research.GatePinning

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

set_option linter.unusedVariables false in
/-- The unmodified public desk statement for L-meta-1774. -/
abbrev Exact1774 : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8

/-- It is enough to pin the earliest bad AND of each eligible circuit. The model does not
require any individual gate edit to decrease the total number of bad gates. -/
theorem exact_of_critical_stars
    (hyp : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → TopForm.NoFourCycle G →
      ∀ C : Circuit, Eligible G C → ∀ k < C.size,
        (∀ j < k, ¬BadAt G C j) → BadAt G C k → AdmitsStarPin G C k) : Exact1774 := by
  intro n G dec tri four useful count C minimal computes ready positive
  obtain ⟨D,eligible,equal,normal⟩ := normal_of_critical_stars G (hyp n G tri four) C ⟨minimal,computes,ready⟩
  refine ⟨D,eligible.1.1,eligible.2.1,equal.le,eligible.2.2,?_⟩
  change {j | BadAt G D j}.ncard < _
  have empty : {j | BadAt G D j} = ∅ := Set.eq_empty_iff_forall_notMem.mpr normal
  simpa only [empty,Set.ncard_empty] using positive

end PEqualNP.Research.GatePinning
