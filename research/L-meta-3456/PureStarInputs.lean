import OrPathNormalForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Local3456

/-- Any true wire in a side's OR closure must have received the unique active input
from that side. An AND with operands of opposite colors is therefore false. -/
theorem colored_singletons (n m : ℕ) (D : Circuit) (S : Bool → Finset ℕ)
    (back : ReadsBack (n+m) D)
    (closed : ∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
      ∃ i < D.size, w = n+m+i ∧ (gateAt D i).op = GateOp.or ∧
        ∀ u ∈ (gateAt D i).inputs, u ∈ S t)
    (separated : ∀ i < D.size, (gateAt D i).op = GateOp.and →
      ∃ a b t, (gateAt D i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ j < D.size, (gateAt D j).op = .and → ∀ k : Fin (n+m), singleWire D k (n+m+j) = false := by
  have color (k : Fin (n+m)) (w : ℕ) : ∀ t, w ∈ S t → singleWire D k w = true → decide (n ≤ k.val) = t := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro t hw on
      rcases closed t w hw with ⟨bound,side⟩ | ⟨j,hj,idx,op,parents⟩
      · have eq : (⟨w,bound⟩ : Fin (n+m)) = k :=
          of_decide_eq_true ((inputRule D k ⟨w,bound⟩).symm.trans on)
        subst k
        exact side
      · subst w
        rw [outRule D back k j hj] at on
        obtain ⟨u,hu,lit⟩ : ∃ u ∈ (gateAt D j).inputs, singleWire D k u = true := by
          simpa [op,GateOp.eval,List.any_eq_true] using on
        exact ih u (back j hj u hu) t (parents u hu) lit
  intro j hj op k
  obtain ⟨a,b,t,inputs,ha,hb⟩ := separated j hj op
  cases on : singleWire D k (n+m+j) with
  | false => rfl
  | true =>
    rw [outRule D back k j hj,op,inputs] at on
    have both : singleWire D k a = true ∧ singleWire D k b = true := by simpa [GateOp.eval] using on
    have clash := (color k a t ha both.1).symm.trans (color k b (!t) hb both.2)
    cases t <;> contradiction

end PEqualNP.Local3456
