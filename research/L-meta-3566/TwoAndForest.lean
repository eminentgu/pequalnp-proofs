import ShortCycle
import FiveTests
import WeakPatterns
import Normalization
import Descent
import PEqualNP.Research.L_meta_1774.Forest

namespace VertexPeel.TwoAndForest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_1774 PEqualNP.Library.Peel.Scratch
open VertexPeel.AndSeparation VertexPeel.FiveTests VertexPeel.CoverCircuit

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem forest_of_small_cone (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = graphFun G ∅)
    (few : (andCone (n := n) C C.output).card ≤ 2) : G.IsAcyclic := by
  by_contra cyclic
  have := three_ands_of_obstruction G (ShortCycle.of_cycle G tri square cyclic) C ao correct
  omega

/-- For this entire class the same vertex works for every AO2 circuit computing the graph. -/
theorem peel_of_small_cone (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G)
    (edges : 2 ≤ G.edgeFinset.card) (witness : Circuit) (ao : IsAO2 n witness)
    (correct : circuitFun n witness = graphFun G ∅) (few : (andCone (n := n) witness witness.output).card ≤ 2) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C :=
  peelableGraph G (peelable_of_isAcyclic (forest_of_small_cone G tri square witness ao correct few)) edges

/-- Every ready minimum in the same graph class admits the descent required by L-meta-1774. -/
theorem descent_of_small_cone (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G)
    (witness : Circuit) (ao : IsAO2 n witness) (correct : circuitFun n witness = graphFun G ∅)
    (few : (andCone (n := n) witness witness.output).card ≤ 2) : StepAt G := by
  intro C hmin ok _ positive
  exact forestDescent G (forest_of_small_cone G tri square witness ao correct few) C hmin.1 ok positive

/-- The same forest conclusion in the original at-most-two-input model of L-meta-1774,
including empty gates, unary gates, and references outside the available prefix. -/
theorem forest_of_two_ands (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G)
    (C : Circuit) (mono : Monotone2 C) (ok : circuitFun n C = graphFun G ∅)
    (few : WeakPatterns.andCount C ≤ 2) : G.IsAcyclic := by
  by_contra cyclic
  obtain ⟨test,off,sep⟩ := family_of_obstruction G (ShortCycle.of_cycle G tri square cyclic)
  have h := WeakPatterns.pattern_bound C mono test (by simpa [ok] using off) (by simpa [ok] using sep)
  have upper := Nat.pow_le_pow_right (by decide : 0 < 2) few
  omega

theorem peel_of_two_ands (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G)
    (edges : 2 ≤ G.edgeFinset.card) (witness : Circuit) (mono : Monotone2 witness)
    (correct : circuitFun n witness = graphFun G ∅) (few : WeakPatterns.andCount witness ≤ 2) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C :=
  peelableGraph G (peelable_of_isAcyclic (forest_of_two_ands G tri square witness mono correct few)) edges

theorem descent_of_two_ands (tri : ShortCycle.TriangleFree G) (square : NoFourCycle G)
    (witness : Circuit) (mono : Monotone2 witness) (correct : circuitFun n witness = graphFun G ∅)
    (few : WeakPatterns.andCount witness ≤ 2) : StepAt G := by
  intro C hmin ok _ positive
  exact forestDescent G (forest_of_two_ands G tri square witness mono correct few) C hmin.1 ok positive

end VertexPeel.TwoAndForest
