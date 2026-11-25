import WitnessBridge

namespace PEqualNP.Outside.L_meta_1774.WitnessNine

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm Mono94

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
attribute [local instance] gateOpDecEq

/-- Moving the first clean term outside its parent AND preserves the output,
while retaining the imperfect gate at index 8 in the other branch. -/
def topCircuit : Circuit := ⟨[
  ⟨.or,[0,3]⟩, ⟨.and,[1,9]⟩, ⟨.or,[1,8]⟩, ⟨.or,[3,8]⟩,
  ⟨.or,[11,4]⟩, ⟨.and,[2,13]⟩, ⟨.or,[10,14]⟩, ⟨.or,[6,7]⟩,
  ⟨.and,[11,16]⟩, ⟨.or,[17,5]⟩, ⟨.and,[12,18]⟩, ⟨.or,[15,19]⟩],20⟩

theorem topAO : IsAO2 9 topCircuit := by decide +kernel

theorem topCorrect : circuitFun 9 topCircuit = graphFun G ∅ := by
  funext x
  exact (by decide +kernel : ∀ y : Fin 9 → Bool, circuitFun 9 topCircuit y = graphFun G ∅ y) x

theorem topSize : topCircuit.size = 12 := rfl

theorem topLeak : ¬ G.Adj 1 6 ∧ (gateAt topCircuit 8).op = .and ∧
    gateVal 9 topCircuit 8 (pairInput 1 6) = true ∧ graphFun G ∅ (pairInput 1 6) = false :=
  by decide +kernel

theorem originalNotTop : ¬ TopForm G dirty := by
  intro h
  have clean : BelowF G dirty 1 := by decide +kernel
  exact h 1 (by decide) 6 (by decide) (by decide) clean (by decide) (by decide)

theorem inTopForm : TopForm G topCircuit := by
  have ancestors : ∀ i j : Fin 12, (gateAt topCircuit i).op = .and →
      (gateAt topCircuit j).op = .and → InCone 9 topCircuit i j → i.val = 8 := by decide +kernel
  intro i hi j hj hiop below hjop cone
  obtain rfl : i = 8 := ancestors ⟨i,hi⟩ ⟨j,hj⟩ hiop hjop cone
  have yes := below (pairInput 1 6) topLeak.2.2.1
  simp [topLeak.2.2.2] at yes

theorem topReady : ∀ j < topCircuit.size, (gateAt topCircuit j).op = .and →
    ∃ u v : Fin 9, G.Adj u v ∧ Owns 9 topCircuit j u v := by
  intro j hj
  exact (by decide +kernel : ∀ i : Fin 12, (gateAt topCircuit i).op = .and →
      ∃ u v : Fin 9, G.Adj u v ∧ Owns 9 topCircuit i u v) ⟨j,hj⟩

private def topCentre (j : Fin 12) : Fin 9 :=
  if j = 1 then 1 else if j = 5 then 2 else if j = 8 then 8 else 5

theorem topStar : HasStarProfile 9 G topCircuit := by
  intro j hj hand
  let i : Fin 12 := ⟨j,hj⟩
  refine Or.inr ⟨topCentre i,?_⟩
  exact (by decide +kernel : ∀ t : Fin 12, (gateAt topCircuit t).op = .and →
      ∀ a b : Fin 9, G.Adj a b → Owns 9 topCircuit t a b → a = topCentre t ∨ b = topCentre t) i hand

theorem topZeroDefects : (disjointOwners G topCircuit).ncard = 0 := by
  simp [noDisjointOwners topStar]

theorem topMinimalFromLive (noneSmall : ∀ k, k ≤ 11 → ¬ Live 511 k roots.toFinset) :
    IsMinimalMonoCircuit 9 topCircuit ∧ IsLeastAO G topCircuit := by
  have mono_of_ao (C : Circuit) (ao : IsAO2 9 C) : Monotone2 C :=
    fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  refine ⟨⟨mono_of_ao topCircuit topAO,?_⟩,⟨topAO,topCorrect,?_⟩⟩
  · intro C hm hf
    exact lowerFromLive noneSmall C hm (hf.trans topCorrect)
  · intro C hC hF
    exact lowerFromLive noneSmall C (mono_of_ao C hC) hF

end PEqualNP.Outside.L_meta_1774.WitnessNine
