import GroupedStar

namespace PEqualNP.Research.GatePinning.GroupedStarTree

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover TopForm
attribute [local instance] gateOpDecEq

abbrev G := edgeGraph 8 [(0,1),(0,2),(0,3),(0,5),(0,7),(3,4),(5,6)]

def C : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.and,[0,1]⟩,⟨.and,[0,2]⟩,⟨.or,[9,10]⟩,
  ⟨.or,[3,5]⟩,⟨.or,[4,6]⟩,⟨.or,[11,12]⟩,⟨.or,[11,13]⟩,⟨.and,[14,15]⟩,
  ⟨.or,[16,7]⟩,⟨.and,[0,17]⟩,⟨.and,[3,4]⟩,⟨.and,[5,6]⟩,⟨.and,[0,12]⟩,
  ⟨.or,[18,19]⟩,⟨.or,[20,21]⟩,⟨.or,[22,23]⟩],24⟩
def D := pinSide C 8 (0 : Fin 8) 8

theorem correct : circuitFun 8 C = graphFun G ∅ ∧ circuitFun 8 D = graphFun G ∅ := by
  constructor <;> funext x <;> revert x <;> decide +kernel

theorem ready : Productive G C ∧ Productive G D := by
  constructor
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 17, (gateAt C i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 8 C i a b) ⟨j,bound⟩
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 17, (gateAt D i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 8 D i a b) ⟨j,bound⟩

theorem old_defect : BadAt G C 8 :=
  ⟨3,4,5,6,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem grouped_wire_outside : ¬InCone 8 C 0 8 ∧ InCone 8 D 0 8 := by decide +kernel

theorem critical_spokes : ∀ a b : Fin 8, needed G C 8 a b ↔
    ((a=0 ∨ b=0) ∧ (a=1 ∨ b=1 ∨ a=2 ∨ b=2)) := by
  unfold needed; decide +kernel

theorem both_unowned : ¬Owns 8 C 8 (0 : Fin 8) 1 ∧ ¬Owns 8 C 8 (0 : Fin 8) 2 ∧
    Owns 8 D 8 (0 : Fin 8) 1 ∧ Owns 8 D 8 (0 : Fin 8) 2 := by decide +kernel

theorem clean : ∀ j, ¬BadAt G D j := by
  intro j bad
  obtain ⟨a,b,c,d,h,e,p,q,dis⟩ := bad
  have ok : ∀ i : Fin 17, ¬BadAt G D i := by unfold BadAt; decide +kernel
  exact ok ⟨j,p.1⟩ ⟨a,b,c,d,h,e,p,q,dis⟩

theorem not_minimum : ¬IsMinimalMonoCircuit 8 C := by
  let small : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[3,5]⟩,⟨.or,[8,9]⟩,⟨.or,[10,7]⟩,
    ⟨.and,[0,11]⟩,⟨.and,[3,4]⟩,⟨.and,[5,6]⟩,⟨.or,[12,13]⟩,⟨.or,[15,14]⟩],16⟩
  have m : Monotone2 small := by simp [small,Monotone2]
  have eq : circuitFun 8 small = circuitFun 8 C := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 8 → Bool, circuitFun 8 small y = circuitFun 8 C y) x
  intro opt
  have bound := opt.2 small m eq
  change 17 ≤ 9 at bound
  omega

end PEqualNP.Research.GatePinning.GroupedStarTree
