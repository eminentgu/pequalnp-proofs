import PinDescent

namespace PEqualNP.Research.GatePinning.Tree

open CircuitLowerBounds EdgeOwnership MetaComplexity MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5465 (val)
attribute [local instance] gateOpDecEq

abbrev G := edgeGraph 5 [(0,1),(1,2),(2,3),(1,4)]

def C : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,⟨.and,[5,6]⟩,⟨.or,[7,4]⟩,
  ⟨.and,[1,8]⟩,⟨.and,[2,6]⟩,⟨.or,[9,10]⟩],11⟩

def D := pinSide C 2 (0 : Fin 5) 6

theorem legal : Monotone2 C := by simp [C,Monotone2]

theorem correct : circuitFun 5 C = graphFun G ∅ := by
  funext x
  exact (by decide +kernel : ∀ x : Fin 5 → Bool, circuitFun 5 C x = graphFun G ∅ x) x

theorem precise_critical_edges : ∀ a b : Fin 5, needed G C 2 a b ↔
    (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) := by
  unfold needed
  decide +kernel

theorem bad : BadAt G C 2 := ⟨0,1,2,3,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem productive : Productive G C := by
  intro j bound
  exact (by decide +kernel : ∀ i : Fin 7, (gateAt C i).op = .and →
    ∃ a b : Fin 5, G.Adj a b ∧ Owns 5 C i a b) ⟨j,bound⟩

theorem admits : AdmitsStarPin G C 2 := by
  refine ⟨5,6,0,Or.inl rfl,by decide,by decide,?_,?_,0,1,by decide,by decide,Or.inl rfl⟩
  · decide +kernel
  · intro a b needed
    rcases (precise_critical_edges a b).1 needed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

theorem repaired : circuitFun 5 D = graphFun G ∅ ∧ D.size = C.size ∧ Productive G D ∧
    (∀ j, j ≠ 2 → ∀ a b, Owns 5 C j a b → Owns 5 D j a b) ∧ ∀ j, ¬BadAt G D j := by
  obtain ⟨dm,df,sz,transfer,star,keep⟩ := pin_critical_star G legal correct (k := 2) (by decide)
    (s := 5) (t := 6) (Or.inl rfl) (by decide) (by decide) (0 : Fin 5)
    (by decide +kernel) (fun a b hit => by rcases (precise_critical_edges a b).1 hit with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp)
  refine ⟨df,sz,?_,transfer,?_⟩
  · intro j bound
    exact (by decide +kernel : ∀ i : Fin 7, (gateAt D i).op = .and →
      ∃ a b : Fin 5, G.Adj a b ∧ Owns 5 D i a b) ⟨j,bound⟩
  · intro j defect
    obtain ⟨a,b,c,d,ea,ec,ab,cd,neq⟩ := defect
    have check : ∀ i : Fin 7, ¬ BadAt G D i := by unfold BadAt; decide +kernel
    exact check ⟨j,ab.1⟩ ⟨a,b,c,d,ea,ec,ab,cd,neq⟩

/-- This concrete example has a smaller five-gate implementation. -/
theorem not_minimum : ¬ IsMinimalMonoCircuit 5 C := by
  let small : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[5,4]⟩,⟨.and,[1,6]⟩,⟨.and,[2,3]⟩,⟨.or,[7,8]⟩],9⟩
  have hm : Monotone2 small := by simp [small,Monotone2]
  have hf : circuitFun 5 small = circuitFun 5 C := by
    funext x
    exact (by decide +kernel : ∀ y : Fin 5 → Bool, circuitFun 5 small y = circuitFun 5 C y) x
  intro least
  have bound := least.2 small hm hf
  change 7 ≤ 5 at bound
  omega

end PEqualNP.Research.GatePinning.Tree
