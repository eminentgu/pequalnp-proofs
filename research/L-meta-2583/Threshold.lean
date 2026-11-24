import LineStarUpper
import PlaneReadOne

/-! The exact numerical content of L-meta-2583 for each plane and each input circuit. -/
namespace PEqualNP.Research2583

open CircuitLowerBounds MetaComplexity ReadK TopForm

variable {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]

abbrev ComputesIncidence (C : Circuit) : Prop :=
  ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = decide
    (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

abbrev HasReplacement (C : Circuit) : Prop :=
  ∃ D : Circuit, IsAO2 (N+N) D ∧ ComputesIncidence I D ∧
    D.size ≤ C.size ∧ IsReadK (N+N) D 1

/-- The threshold applies independently to each circuit. The implication from
    its size to replacement even applies when the proposed input circuit is arbitrary. -/
theorem replacement_iff_threshold (C : Circuit) (hq : 2 ≤ q)
    (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    HasReplacement I C ↔ N*(q+2) ≤ C.size+1 := by
  constructor
  · exact PlaneReadOne.necessary I q C hq order lines unique
  · intro size
    have positive : 0 < N := by omega
    obtain ⟨D,ao,ev,hs,read⟩ := LineStars.regular_read_upper N q I positive lines
    exact ⟨D,ao,ev,by omega,read⟩

/-- On a fixed plane, the universal claim on the desk is exactly a lower
    bound for all fan-in-two monotone circuits computing incidence. -/
theorem normalization_iff_lower_bound (hq : 2 ≤ q)
    (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    (∀ C : Circuit, IsAO2 (N+N) C → ComputesIncidence I C → HasReplacement I C) ↔
    (∀ C : Circuit, IsAO2 (N+N) C → ComputesIncidence I C → N*(q+2) ≤ C.size+1) := by
  have h := fun C => replacement_iff_threshold q I C hq order lines unique
  exact ⟨fun replace C ao ev => (h C).mp (replace C ao ev),
    fun bound C ao ev => (h C).mpr (bound C ao ev)⟩

#print axioms replacement_iff_threshold
#print axioms normalization_iff_lower_bound

end PEqualNP.Research2583
