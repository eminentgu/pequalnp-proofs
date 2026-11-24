import PureStarInputs
import PEqualNP.Outside.L_meta_2874

namespace PEqualNP.Local3456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- A vertex cover gives a singleton-clean circuit for any rectangular incidence matrix.
The premise on the budget applies to an arbitrary reference circuit. -/
theorem normalize_at_cover_cost (n m : ℕ) (E : Finset (Fin n × Fin m))
    (A : Finset (Fin n)) (B : Finset (Fin m)) (C : Circuit)
    (cover : ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B)
    (budget : E.card + A.card + B.card - 1 ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (n+m) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (n+m) → Bool, circuitFun (n+m) D z = true ↔
        ∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) ∧
      SingletonClean (n+m) D := by
  obtain ⟨D,S,model,size,computes,closed,sep⟩ := PEqualNP.Outside.L_meta_2874 n m E A B cover
  refine ⟨D,fun g hg => ⟨model.1 g hg,(model.2.2 g hg).le⟩,model.2.1,size.trans budget,?_,?_⟩
  · intro z
    rw [computes z,decide_eq_true_eq]
  · exact colored_singletons n m D S model.2.1 closed sep

end PEqualNP.Local3456
