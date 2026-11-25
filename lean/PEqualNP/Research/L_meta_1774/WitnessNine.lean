import PEqualNP.Research.L_meta_1774.CoveredOwnership

namespace PEqualNP.Outside.L_meta_1774.WitnessNine

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
attribute [local instance] gateOpDecEq

abbrev G := edgeGraph 9 [(0,1),(1,2),(1,3),(2,4),(2,8),(3,5),(5,8),(6,8),(7,8)]

def dirty : Circuit := ⟨[⟨.or,[0,3]⟩,
  ⟨.and,[1,9]⟩,
  ⟨.or,[10,2]⟩,
  ⟨.or,[1,8]⟩,
  ⟨.or,[3,8]⟩,
  ⟨.or,[12,4]⟩,
  ⟨.and,[11,14]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.and,[12,16]⟩,
  ⟨.or,[17,5]⟩,
  ⟨.and,[13,18]⟩,
  ⟨.or,[15,19]⟩],20⟩

theorem legal : Monotone2 dirty := by simp [Monotone2,dirty]
theorem correct : circuitFun 9 dirty = graphFun G ∅ := by
  funext x
  exact (by decide +kernel : ∀ x : Fin 9 → Bool, circuitFun 9 dirty x = graphFun G ∅ x) x

theorem triangleFree : ∀ a b c : Fin 9, G.Adj a b → G.Adj b c → ¬ G.Adj c a := by decide
theorem squareFree : NoFourCycle G := by decide
theorem size : dirty.size = 12 := rfl

theorem acceptsNonedge : ¬ G.Adj 1 6 ∧
    (gateAt dirty 8).op = GateOp.and ∧ gateVal 9 dirty 8 (pairInput 1 6) = true := by decide

theorem cover : CoverPromise.IsVertexCover G ({0,2,3,8} : Finset (Fin 9)) := by
  unfold CoverPromise.IsVertexCover
  decide +kernel

theorem minCover : ∀ T : Finset (Fin 9), CoverPromise.IsVertexCover G T → 4 ≤ T.card := by
  unfold CoverPromise.IsVertexCover
  decide +kernel

theorem productive : ∀ j < dirty.size, (gateAt dirty j).op = GateOp.and →
    ∃ u v : Fin 9, G.Adj u v ∧ Owns 9 dirty j u v := by
  intro j hj
  exact (by decide +kernel : ∀ i : Fin 12, (gateAt dirty i).op = GateOp.and →
      ∃ u v : Fin 9, G.Adj u v ∧ Owns 9 dirty i u v) ⟨j,hj⟩

private def centre (j : Fin 12) : Fin 9 :=
  if j = 1 then 1 else if j = 6 then 2 else if j = 8 then 8 else 5

theorem star : HasStarProfile 9 G dirty := by
  intro j hj hAND
  let i : Fin 12 := ⟨j,hj⟩
  refine Or.inr ⟨centre i,?_⟩
  exact (by decide +kernel : ∀ t : Fin 12, (gateAt dirty t).op = GateOp.and →
      ∀ a b : Fin 9, G.Adj a b → Owns 9 dirty t a b → a = centre t ∨ b = centre t) i hAND

theorem zeroDefects : (disjointOwners G dirty).ncard = 0 := by
  simp [noDisjointOwners star]

end PEqualNP.Outside.L_meta_1774.WitnessNine
