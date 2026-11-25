import PEqualNP.Research.L_meta_1774.CoveredOwnership
import PEqualNP.Outside.L_meta_7241

/-! A single pair-sound comparator at the target budget supplies a fully productive
star circuit. Conversely, failure of the claimed descent forces every equally
small exact-binary implementation to contain an AND which accepts a nonedge pair. -/

namespace PEqualNP.Outside.L_meta_1774

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def SoundOnPairs {n : ℕ} (G : SimpleGraph (Fin n)) (S : Circuit) : Prop :=
  ∀ j < S.gates.length, (gateAt S j).op = GateOp.and → ∀ u v,
    ¬G.Adj u v → gateVal n S j (pairInput u v) = false

/-- A comparator may have different gates from the defective circuit. No minimality or
ownership assumption on that comparator is needed. -/
theorem starAtComparatorSize {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (squareFree : NoFourCycle G) (S : Circuit) (legal : IsAO2 n S)
    (correct : circuitFun n S = graphFun G ∅) (sound : SoundOnPairs G S) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ S.size ∧
      HasStarProfile n G D ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n D j u v) := by
  obtain ⟨T,cover,budget⟩ := PEqualNP.Outside.L_meta_7241 n G S squareFree legal correct sound
  obtain ⟨D,mono,funD,size,profile,useful⟩ := buildCoveredStar n G T cover
  have edges : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  exact ⟨D,mono,funD,by omega,profile,useful⟩

/-- A failure on the claimed input witnesses a semantic obstruction in *every* alternative
implementation at that size. The witnesses may be different for different circuits. -/
theorem obstructionForEveryComparator {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (squareFree : NoFourCycle G) (C : Circuit) (positive : 0 < (disjointOwners G C).ncard)
    (stuck : ¬ ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n D j u v) ∧
      (disjointOwners G D).ncard < (disjointOwners G C).ncard)
    (S : Circuit) (legal : IsAO2 n S) (correct : circuitFun n S = graphFun G ∅)
    (size : S.size ≤ C.size) :
    ∃ j < S.gates.length, (gateAt S j).op = GateOp.and ∧
      ∃ u v, ¬ G.Adj u v ∧ gateVal n S j (pairInput u v) = true := by
  classical
  by_contra! clean
  have sound : SoundOnPairs G S := by
    intro j hj op u v missing
    simpa using clean j hj op u v missing
  obtain ⟨D,mono,funD,bound,profile,useful⟩ := starAtComparatorSize G squareFree S legal correct sound
  exact stuck ⟨D,mono,funD,bound.trans size,useful,by simpa [noDisjointOwners profile] using positive⟩

end PEqualNP.Outside.L_meta_1774
