import CriticalOr

namespace PEqualNP.Research.GatePinning.CriticalOrTree

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover TopForm
open Outside.L_meta_5465 (val)
attribute [local instance] gateOpDecEq

abbrev G := edgeGraph 6 [(0,1),(0,2),(0,5),(3,4)]

def C : Circuit := ⟨[⟨.or,[1,3]⟩,⟨.or,[6,2]⟩,⟨.or,[1,4]⟩,⟨.or,[8,2]⟩,
  ⟨.and,[7,9]⟩,⟨.or,[10,5]⟩,⟨.and,[0,11]⟩,⟨.and,[3,4]⟩,⟨.or,[12,13]⟩],14⟩

def D := primaryOr C 4 (1 : Fin 6) 2

theorem correct : circuitFun 6 C = graphFun G ∅ ∧ circuitFun 6 D = graphFun G ∅ := by
  constructor <;> funext x <;> revert x <;> decide +kernel

theorem ready : Productive G C ∧ Productive G D := by
  constructor
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 9, (gateAt C i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 6 C i a b) ⟨j,bound⟩
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 9, (gateAt D i).op = .and →
      ∃ a b, G.Adj a b ∧ Owns 6 D i a b) ⟨j,bound⟩

theorem old_defect : BadAt G C 4 :=
  ⟨0,1,3,4,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem owns_spokes : Owns 6 C 4 (0 : Fin 6) 1 ∧ Owns 6 C 4 (0 : Fin 6) 2 := by decide +kernel

theorem critical_spokes : ∀ a b : Fin 6, needed G C 4 a b ↔
    ((a=0 ∨ b=0) ∧ (a=1 ∨ b=1 ∨ a=2 ∨ b=2)) := by
  unfold needed; decide +kernel

theorem no_star_pin : ¬AdmitsStarPin G C 4 := by
  rintro ⟨s,t,z,site,_,_,force,star,_⟩
  have a := star 0 1 ((critical_spokes 0 1).2 (by decide))
  have b := star 0 2 ((critical_spokes 0 2).2 (by decide))
  have cz : z = 0 := by rcases a with h|h <;> rcases b with j|j <;> grind
  subst z
  have srange : s = 7 ∨ s = 9 := by
    have h : gateAt C 4 = ⟨.and,[7,9]⟩ := rfl
    rw [h] at site
    rcases site with h|h
    · exact Or.inl (by simpa using (congrArg (fun g : Gate => g.inputs.head?) h).symm)
    · exact Or.inr (by simpa using (congrArg (fun g : Gate => (g.inputs.drop 1).head?) h).symm)
  have h := force (pairInput 0 0) (by decide)
  rcases srange with rfl | rfl <;> revert h <;> decide +kernel

theorem new_clean : ∀ j, ¬BadAt G D j := by
  intro j bad
  obtain ⟨a,b,c,d,h,e,p,q,dis⟩ := bad
  have clean : ∀ i : Fin 9, ¬BadAt G D i := by unfold BadAt; decide +kernel
  exact clean ⟨j,p.1⟩ ⟨a,b,c,d,h,e,p,q,dis⟩

theorem not_minimum : ¬IsMinimalMonoCircuit 6 C := by
  let small : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[6,5]⟩,⟨.and,[0,7]⟩,
    ⟨.and,[3,4]⟩,⟨.or,[8,9]⟩],10⟩
  have m : Monotone2 small := by simp [small,Monotone2]
  have eq : circuitFun 6 small = circuitFun 6 C := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 6 → Bool, circuitFun 6 small y = circuitFun 6 C y) x
  intro opt
  have bound := opt.2 small m eq
  change 9 ≤ 5 at bound
  omega

end PEqualNP.Research.GatePinning.CriticalOrTree
