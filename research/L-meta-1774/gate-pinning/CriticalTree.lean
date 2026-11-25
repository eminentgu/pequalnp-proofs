import CriticalCases

namespace PEqualNP.Research.GatePinning.CriticalTree

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover TopForm
attribute [local instance] gateOpDecEq

abbrev G := edgeGraph 7 [(0,1),(2,3),(4,5),(5,6),(5,0),(5,2)]

def C : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.and,[4,5]⟩,⟨.or,[7,8]⟩,⟨.or,[1,3]⟩,
  ⟨.or,[10,5]⟩,⟨.and,[9,11]⟩,⟨.or,[12,6]⟩,⟨.and,[5,13]⟩,
  ⟨.and,[0,1]⟩,⟨.and,[2,3]⟩,⟨.and,[5,7]⟩,⟨.or,[14,15]⟩,⟨.or,[16,17]⟩,⟨.or,[18,19]⟩],20⟩

def D := pin C 5 (4 : Fin 7) 5

theorem correct : circuitFun 7 C = graphFun G ∅ ∧ circuitFun 7 D = graphFun G ∅ := by
  constructor <;> funext x <;> revert x <;> decide +kernel

theorem ready : Productive G C ∧ Productive G D := by
  constructor
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 14, (gateAt C i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 7 C i a b) ⟨j,bound⟩
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 14, (gateAt D i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 7 D i a b) ⟨j,bound⟩

theorem old_defect : BadAt G C 5 := ⟨0,1,2,3,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem only_needed : ∀ a b : Fin 7, needed G C 5 a b ↔ (a=4 ∧ b=5) ∨ (a=5 ∧ b=4) := by
  unfold needed
  decide +kernel

/-- Gate 1 created the needed edge inside the old gate's cone. The pinned gate newly
owns this edge, while the earlier original owner retains it as well. -/
theorem changed_owners : ¬Owns 7 C 5 (4 : Fin 7) 5 ∧ Owns 7 C 1 (4 : Fin 7) 5 ∧
    Owns 7 D 5 (4 : Fin 7) 5 ∧ Owns 7 D 1 (4 : Fin 7) 5 := by decide +kernel

theorem new_clean : ∀ j, ¬BadAt G D j := by
  intro j bad
  obtain ⟨a,b,c,d,h,e,p,q,dis⟩ := bad
  have clean : ∀ i : Fin 14, ¬BadAt G D i := by unfold BadAt; decide +kernel
  exact clean ⟨j,p.1⟩ ⟨a,b,c,d,h,e,p,q,dis⟩

theorem not_minimum : ¬ IsMinimalMonoCircuit 7 C := by
  let small : Circuit := ⟨[⟨.or,[4,6]⟩,⟨.or,[0,2]⟩,⟨.or,[7,8]⟩,⟨.and,[5,9]⟩,
    ⟨.and,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[10,11]⟩,⟨.or,[12,13]⟩],14⟩
  have m : Monotone2 small := by simp [small,Monotone2]
  have eq : circuitFun 7 small = circuitFun 7 C := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 7 → Bool, circuitFun 7 small y = circuitFun 7 C y) x
  intro opt
  have bound := opt.2 small m eq
  change 14 ≤ 8 at bound
  omega

end PEqualNP.Research.GatePinning.CriticalTree
