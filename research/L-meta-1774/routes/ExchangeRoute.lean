import Descent
import PEqualNP.Outside.L_meta_7406
import PEqualNP.Outside.R_meta_1774_642

namespace PEqualNP.Outside.L_meta_1774.ExchangeRoute

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

/-- The public desk statement, including the permutation on all natural gate indices. -/
abbrev Exact7408 : Prop := ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Fin x1) (x12 : Fin x1), x6 x7 x8 x11 x12;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → x7 x8 → ∀ (x11 : ℕ) (x12 x13 x14 x15 : Fin x1), x6 x8 x11 x12 x13 → x6 x8 x11 x14 x15 → x12 ≠ x14 → x12 ≠ x15 → x13 ≠ x14 → x13 ≠ x15 → (∃ (x22 : Fin x1) (x23 : Fin x1), (x22 = x12 ∨ x22 = x13) ∧ (x23 = x14 ∨ x23 = x15) ∧ ¬x2.Adj x22 x23 ∧ PEqualNP.EdgeOwnership.gateVal x1 x8 x11 (PEqualNP.EdgeOwnership.pairInput x22 x23) = Bool.true) → ∃ (x23 : PEqualNP.CircuitLowerBounds.Circuit), x7 x23 ∧ x23.size ≤ x8.size ∧ ∃ (x24 : Equiv.Perm ℕ), ∀ (x25 : ℕ), (∃ (x26 : Fin x1), ∀ (x27 x28 : Fin x1), x6 x23 x25 x27 x28 → x27 = x26 ∨ x28 = x26) ∨ x24 x25 ≠ x11 ∧ ∀ (x26 x27 : Fin x1), x6 x23 x25 x26 x27 → x6 x8 (x24 x25) x26 x27

private lemma intersecting_star {n : ℕ} (G : SimpleGraph (Fin n))
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (E : Fin n → Fin n → Prop) (valid : ∀ u v, E u v → G.Adj u v)
    (ne : ∃ a b, E a b)
    (meet : ∀ a b c d, E a b → E c d → a=c ∨ a=d ∨ b=c ∨ b=d) :
    ∃ z, ∀ a b, E a b → a=z ∨ b=z := by
  obtain ⟨a,b,ab⟩ := ne
  by_cases ha : ∀ c d, E c d → c=a ∨ d=a
  · exact ⟨a,ha⟩
  push Not at ha
  obtain ⟨c,d,cd,hca,hda⟩ := ha
  refine ⟨b,?_⟩
  intro u v uv
  have m1 := meet a b c d ab cd
  have m2 := meet a b u v ab uv
  have m3 := meet c d u v cd uv
  have e1 := valid a b ab
  have e2 := valid c d cd
  have e3 := valid u v uv
  have e1' := e1.symm
  have e2' := e2.symm
  have e3' := e3.symm
  grind

/-- An exchange follows from repeated descent by choosing an entirely star-shaped optimum.
The permutation can be the identity because every index satisfies the first alternative. -/
theorem exchange_of_descent (descent : Exact1774) : Exact7408 := by
  classical
  intro n G inst tri square E ready C minimum usable j a b c d ab cd ac ad bc bd leak
  obtain ⟨D,dmin,correct,equal,alluseful,zero⟩ :=
    exact_iff_normal.mp descent n G tri square C minimum usable.2.1 usable.2.2
  refine ⟨D,⟨dmin.1,correct,alluseful⟩,equal.le,Equiv.refl ℕ,?_⟩
  have finite : (disjointOwners G D).Finite := by
    apply (Set.finite_Iio D.gates.length).subset
    rintro i ⟨p,q,r,s,_,_,owned,_⟩
    exact owned.1
  intro i
  left
  by_cases live : ∃ p q, E D i p q
  · apply intersecting_star G tri (E D i) (fun _ _ h => h.1) live
    intro p q r s pq rs
    by_contra! disjoint
    obtain ⟨pr,ps,qr,qs⟩ := disjoint
    have bad : i ∈ disjointOwners G D :=
      ⟨p,q,r,s,pq.1,rs.1,pq.2,rs.2,pr,ps,qr,qs⟩
    have positive := (Set.ncard_pos finite).2 ⟨i,bad⟩
    exact (Nat.ne_of_gt positive) zero
  · exact ⟨a,fun p q owned => False.elim (live ⟨p,q,owned⟩)⟩

/-- The merged location theorem supplies the other premise of the project's reduction. -/
theorem exact_iff_exchange : Exact1774 ↔ Exact7408 :=
  ⟨exchange_of_descent, R_meta_1774_642 L_meta_7406⟩

end PEqualNP.Outside.L_meta_1774.ExchangeRoute
