import SafeTail

namespace VertexPeel.MixedOwnershipExample
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_2668 (bypass)
open PEqualNP.Outside.L_meta_1491.S98 (appOr)
attribute [local instance] gateOpDecEq

set_option maxRecDepth 150000
set_option maxHeartbeats 2500000

abbrev G := edgeGraph 7 [(0,1),(1,2),(2,3),(1,4),(2,5),(1,6)]

def C : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[1,3]⟩, ⟨.or,[0,6]⟩, ⟨.and,[1,9]⟩,
  ⟨.or,[7,10]⟩, ⟨.and,[11,8]⟩, ⟨.or,[12,4]⟩, ⟨.and,[1,13]⟩,
  ⟨.or,[12,5]⟩, ⟨.and,[2,15]⟩, ⟨.or,[14,16]⟩],17⟩

def bypassed := bypass 7 C 4 7
def D := appOr 7 bypassed bypassed.output 10
def small : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[7,4]⟩, ⟨.or,[8,6]⟩, ⟨.and,[1,9]⟩,
  ⟨.or,[3,5]⟩, ⟨.and,[2,11]⟩, ⟨.or,[10,12]⟩],13⟩

abbrev Useful (E : Circuit) := ∀ j : Fin E.size, (gateAt E j).op = .and →
  ∃ u v : Fin 7, G.Adj u v ∧ Owns 7 E j u v

theorem legality : IsAO2 7 C ∧ IsAO2 7 D ∧ IsAO2 7 small := by decide +kernel

theorem correct : circuitFun 7 C = graphFun G ∅ ∧ circuitFun 7 D = graphFun G ∅ ∧
    circuitFun 7 small = graphFun G ∅ := by
  exact ⟨funext (by decide +kernel),funext (by decide +kernel),funext (by decide +kernel)⟩

theorem cost : C.size=11 ∧ D.size=C.size ∧ small.size=7 := by decide +kernel

theorem triangle_free : ∀ a b c : Fin 7, G.Adj a b → G.Adj b c → ¬ G.Adj c a := by decide +kernel
theorem square_free : NoFourCycle G := by decide +kernel

theorem before_useful : Useful C := by unfold Useful; decide +kernel
theorem after_useful : Useful D := by unfold Useful; decide +kernel

/-- The moved operand computes only edges. Removing it without appending the
final OR loses the edge (1,6). Its original OR also accepts singleton 0. -/
theorem genuine_mixed : VertexPeel.SafeTail.SoundAt G C 10 ∧
    wval C (pairInput (0 : Fin 7) 0) 11=true ∧ graphFun G ∅ (pairInput (0 : Fin 7) 0)=false ∧
    circuitFun 7 bypassed (pairInput 1 6)=false ∧ graphFun G ∅ (pairInput (1 : Fin 7) 6)=true := by
  refine ⟨?_,by decide +kernel⟩
  unfold VertexPeel.SafeTail.SoundAt
  decide +kernel

/-- Each input AND owns a star; the output computes a graph with no defective owner. -/
theorem stars_before : HasStarProfile 7 G C := by decide +kernel

/-- The same physical AND (old 5, new 4) acquires (0,1), while retaining
(2,3). Each endpoint of the former edge differs from both of the latter. -/
theorem new_defect : ¬ Owns 7 C 5 0 1 ∧ Owns 7 C 5 2 3 ∧
    Owns 7 D 4 0 1 ∧ Owns 7 D 4 2 3 ∧ G.Adj 0 1 ∧ G.Adj 2 3 := by decide +kernel

#print axioms correct
#print axioms stars_before
#print axioms new_defect
end VertexPeel.MixedOwnershipExample
