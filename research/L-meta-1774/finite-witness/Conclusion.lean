import Case94.L11B0
import WitnessDescent
import TopWitness

namespace Mono94.Case94

theorem noSmall : ∀ k, k ≤ 11 → ¬ Live 511 k roots.toFinset := by
  have same : (Packing.unpack 12 0x1f408c1d09e01862460073f003e8038600a1a).toFinset = roots.toFinset := by
    decide +kernel
  intro k hk
  rw [← same]
  exact x11_0 k hk

end Mono94.Case94

namespace PEqualNP.Outside.L_meta_1774.WitnessNine

theorem lower (C : PEqualNP.CircuitLowerBounds.Circuit) (legalC : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) :
    12 ≤ C.size := lowerFromLive Mono94.Case94.noSmall C legalC computes

theorem minimum : PEqualNP.MetaComplexity.IsMinimalMonoCircuit 9 dirty :=
  minimalFromLive Mono94.Case94.noSmall

theorem topFormMinimum : PEqualNP.MetaComplexity.IsMinimalMonoCircuit 9 topCircuit ∧
    PEqualNP.TopForm.IsLeastAO G topCircuit := topMinimalFromLive Mono94.Case94.noSmall

theorem graphDescent (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legalC : PEqualNP.MetaComplexity.Monotone2 C)
    (correctC : PEqualNP.MetaComplexity.circuitFun 9 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (positive : 0 < (disjointOwners G C).ncard) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ C.size ∧ (∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and → ∃ u v, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns 9 D j u v) ∧
        (disjointOwners G D).ncard < (disjointOwners G C).ncard :=
  descentFromLive Mono94.Case94.noSmall C legalC correctC positive

theorem negates4848 : ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13) :=
  neg4848FromLive Mono94.Case94.noSmall

end PEqualNP.Outside.L_meta_1774.WitnessNine

#print axioms Mono94.Case94.noSmall
#print axioms PEqualNP.Outside.L_meta_1774.WitnessNine.lower
#print axioms PEqualNP.Outside.L_meta_1774.WitnessNine.minimum
#print axioms PEqualNP.Outside.L_meta_1774.WitnessNine.negates4848

#print axioms PEqualNP.Outside.L_meta_1774.WitnessNine.graphDescent
#print axioms PEqualNP.Outside.L_meta_1774.WitnessNine.topFormMinimum
