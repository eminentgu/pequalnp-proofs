import SupportPacking

namespace VertexPeel.BatchExchange.Example

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev G := edgeGraph 4 [(0,2),(0,3),(1,2)]
abbrev T : Finset (Fin 4) := {0,1}
def C : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.and,[4,5]⟩],6⟩

theorem graph_hypotheses : (∃ color : Fin 4 → Bool, ∀ a b, G.Adj a b → color a ≠ color b) ∧
    NoFourCycle G ∧ G.edgeFinset.card=3 := by decide +kernel

theorem minimum_cover : IsVertexCover G T ∧ ∀ U, IsVertexCover G U → T.card ≤ U.card := by
  change (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧
    ∀ U : Finset (Fin 4), (∀ a b, G.Adj a b → a ∈ U ∨ b ∈ U) → T.card ≤ U.card
  decide +kernel

theorem agrees_on_edges_and_singletons : (∀ a b, G.Adj a b → circuitFun 4 C (pairInput a b)=true) ∧
    (∀ a, circuitFun 4 C (pairInput a a)=false) ∧ IsAO2 4 C ∧ EveryEdgeOwned 4 G C := by decide +kernel

private def assign (j : Fin C.size) : Sym2 (Fin 4) :=
  if j.val=0 then s(0,2) else if j.val=1 then s(0,3) else s(1,2)

/-- All gates can already use distinct genuine edge labels, for every choice of cover. -/
theorem assigns_all : Function.Injective assign ∧ ∀ j, assign j ∈ support G C j := by
  change (∀ a b, assign a = assign b → a=b) ∧ _
  decide +kernel

theorem obstruction : C.size+1 < G.edgeFinset.card + Loc.tau G ∧
    circuitFun 4 C (pairInput 1 3)=true ∧ graphFun G ∅ (pairInput 1 3)=false := by
  obtain ⟨U,hU,eq⟩ := Loc.tau_attained G
  have min := minimum_cover.2 U hU
  have two : T.card=2 := by decide +kernel
  have three : C.size=3 := rfl
  exact ⟨by have := graph_hypotheses.2.2; omega,by decide +kernel,by decide +kernel⟩

#print axioms obstruction
#print axioms assigns_all
end VertexPeel.BatchExchange.Example
