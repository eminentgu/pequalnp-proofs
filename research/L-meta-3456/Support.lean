import FormulaCircuit
import PEqualNP.Outside.L_meta_1660

namespace SingletonSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1660

/-- An input is essential if flipping only that input can change the output. -/
def Essential {n : Nat} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧ f x = true ∧ f y = false

theorem essential_card_le {n : Nat} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (V : Finset (Fin n)) (he : ∀ i ∈ V, Essential (circuitFun n C) i) :
    V.card ≤ C.size + 1 := by
  obtain ⟨Sup, hdep, hbound⟩ := fold_sup n C.gates hfan _ n (sup0 n) 0 (st_init n) (fun Q => by
    have h := Finset.card_biUnion_le_card_mul Q (sup0 n) 1 (fun a _ => sup0_card n a)
    omega)
  have bound := hbound {C.output}
  rw [Finset.singleton_biUnion, Finset.card_singleton] at bound
  have inc : V ⊆ Sup C.output := by
    intro i hi
    by_contra hn
    obtain ⟨x,y,eq,hx,hy⟩ := he i hi
    have obs : circuitFun n C x = circuitFun n C y :=
      hdep C.output x y (fun j hj => eq j (fun e => hn (e ▸ hj)))
    simp [hx,hy] at obs
  have card := Finset.card_le_card inc
  change V.card ≤ C.gates.length + 1
  omega

end SingletonSupport
