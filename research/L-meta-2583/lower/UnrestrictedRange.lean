import PlaneReadOne
import PEqualNP.Outside.L_meta_2988

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

namespace PlaneReadOne

/-- Merged L-meta-2988 only tests pairs of input positions and allows
    arbitrary reads. The full incidence function in L-meta-2583 implies
    those tests immediately. -/
theorem unrestricted {N : ℕ} (I : Fin N → Fin N → Prop) (q : ℕ) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C)
    (evaluates : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    3*N ≤ C.size+1 := by
  apply PEqualNP.Outside.L_meta_2988 q N I C hq order _ unique
  · intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ao.1 g hg,
      (ao.2.2 g hg).le⟩
  · intro a b
    rw [evaluates]
    simp
  · intro l
    simpa only [Fintype.card_subtype] using lines l

/-- If an unrestricted realization has fewer gates than the star threshold,
    every putative read-1 replacement is excluded. -/
theorem below_threshold {N : ℕ} (I : Fin N → Fin N → Prop) (q : ℕ) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (small : C.size+1 < N*(q+2)) :
    ¬ ∃ D : Circuit, IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
        decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 1 :=
  fun replace => (Nat.not_le.mpr small) (necessary I q C hq order lines unique replace)

end PlaneReadOne

#print axioms PlaneReadOne.unrestricted
#print axioms PlaneReadOne.below_threshold
