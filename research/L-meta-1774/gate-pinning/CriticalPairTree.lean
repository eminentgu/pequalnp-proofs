import CriticalPairOr

namespace PEqualNP.Research.GatePinning.CriticalPairTree

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover TopForm
attribute [local instance] gateOpDecEq

abbrev G := edgeGraph 6 [(0,1),(0,3),(2,3),(0,4),(3,5)]

def C : Circuit := ⟨[⟨.and,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,
  ⟨.and,[8,9]⟩,⟨.or,[10,4]⟩,⟨.and,[0,11]⟩,⟨.or,[10,5]⟩,⟨.and,[3,13]⟩,
  ⟨.and,[0,3]⟩,⟨.or,[12,14]⟩,⟨.or,[16,15]⟩],17⟩
def D := replace C 4 ⟨.or,[6,7]⟩

theorem correct : circuitFun 6 C = graphFun G ∅ ∧ circuitFun 6 D = graphFun G ∅ := by
  constructor <;> funext x <;> revert x <;> decide +kernel

theorem ready : Productive G C ∧ Productive G D := by
  constructor
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 12, (gateAt C i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 6 C i a b) ⟨j,bound⟩
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 12, (gateAt D i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 6 D i a b) ⟨j,bound⟩

theorem old_defect : BadAt G C 4 :=
  ⟨0,1,2,3,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem both_outside : ¬InCone 6 C 0 4 ∧ ¬InCone 6 C 1 4 ∧ InCone 6 D 0 4 ∧ InCone 6 D 1 4 := by
  decide +kernel

theorem critical_matching : ∀ a b : Fin 6, needed G C 4 a b ↔
    ((a=0 ∧ b=1) ∨ (a=1 ∧ b=0) ∨ (a=2 ∧ b=3) ∨ (a=3 ∧ b=2)) := by
  unfold needed; decide +kernel

theorem clean : ∀ j, ¬BadAt G D j := by
  intro j bad
  obtain ⟨a,b,c,d,h,e,p,q,dis⟩ := bad
  have ok : ∀ i : Fin 12, ¬BadAt G D i := by unfold BadAt; decide +kernel
  exact ok ⟨j,p.1⟩ ⟨a,b,c,d,h,e,p,q,dis⟩

theorem not_minimum : ¬IsMinimalMonoCircuit 6 C := by
  let small : Circuit := ⟨[⟨.or,[1,4]⟩,⟨.and,[0,6]⟩,⟨.or,[0,2]⟩,⟨.or,[8,5]⟩,
    ⟨.and,[3,9]⟩,⟨.or,[7,10]⟩],11⟩
  have m : Monotone2 small := by simp [small,Monotone2]
  have eq : circuitFun 6 small = circuitFun 6 C := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 6 → Bool, circuitFun 6 small y = circuitFun 6 C y) x
  intro opt
  have bound := opt.2 small m eq
  change 12 ≤ 6 at bound
  omega

end PEqualNP.Research.GatePinning.CriticalPairTree
