import Extract
import PEqualNP.Research.L_meta_1774.WitnessNine

namespace PEqualNP.Outside.L_meta_1774.WitnessNine

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Mono94

/-- The signature of the graph edge function is one on the nine chosen edges
and zero on the seven maximal independent sets. -/
theorem edgeRows : ∀ r : Fin 16, graphFun G ∅ (sample r) = bit r goal := by decide +kernel

/-- An ownership defect counts two disjoint genuine edges. The nonedge accepted
by circuit gate 8 leaves this defect count at zero. -/
theorem witnessFacts :
    (disjointOwners G dirty).ncard = 0 ∧
    (∀ j < dirty.size, (gateAt dirty j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns 9 dirty j u v) ∧
    ¬ G.Adj 1 6 ∧ (gateAt dirty 8).op = GateOp.and ∧ gateVal 9 dirty 8 (pairInput 1 6) = true :=
  ⟨zeroDefects,productive,acceptsNonedge⟩

theorem lowerFromLive
    (noSmall : ∀ k, k ≤ 11 → ¬ Live 511 k roots.toFinset)
    (C : Circuit) (legalC : Monotone2 C) (correctC : circuitFun 9 C = graphFun G ∅) :
    12 ≤ C.size := by
  by_contra! short
  obtain ⟨k,budget,plan⟩ := extractExact C legalC (fun r =>
    (congrFun correctC (sample r)).trans (edgeRows r))
  exact noSmall k (by omega) plan

theorem minimalFromLive (noSmall : ∀ k, k ≤ 11 → ¬ Live 511 k roots.toFinset) :
    IsMinimalMonoCircuit 9 dirty := by
  refine ⟨legal,?_⟩
  intro C legalC same
  rw [size]
  exact lowerFromLive noSmall C legalC (same.trans correct)

theorem neg4848FromLive (noSmall : ∀ k, k ≤ 11 → ¬ Live 511 k roots.toFinset) :
    ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13) := by
  intro claim
  have actual := claim 9 G triangleFree squareFree dirty (minimalFromLive noSmall) correct
    8 (by decide) acceptsNonedge.2.1 1 6 acceptsNonedge.2.2
  exact acceptsNonedge.1 actual

end PEqualNP.Outside.L_meta_1774.WitnessNine
