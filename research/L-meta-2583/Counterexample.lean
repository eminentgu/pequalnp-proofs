import Threshold
import UnrestrictedRange
import NoNestedPlane

namespace PEqualNP.Research2583
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover ReadK TopForm EdgeOwnership

/-- Necessary conditions on the *same* circuit that a counterexample must meet. -/
theorem counterexample_conditions {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (eval : ComputesIncidence I C) (bad : ¬HasReplacement I C) :
    3*N ≤ C.size+1 ∧ C.size+1 < N*(q+2) ∧ ¬NoNested.OnOutput (N+N) C ∧
    (∃ p l, I p l ∧ readsAtMost C (N+N) [p.val,N+l.val] 1 = false) ∧
    (∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ∃ u v : Fin (N+N), ¬(PlaneReadOne.graph I).Adj u v ∧
        gateVal (N+N) C k (pairInput u v) = true ∧
        circuitFun (N+N) C (pairInput u v) = false) := by
  have small : C.size+1 < N*(q+2) :=
    Nat.lt_of_not_ge (fun h => bad ((replacement_iff_threshold q I C hq order lines unique).mpr h))
  refine ⟨PlaneReadOne.unrestricted I q C hq order lines unique ao eval,small,
    fun ho => bad (NoNested.plane_normalization_on_output q I C hq order lines unique ao eval ho),
    ?_,PlaneReadOne.dirtyWitness I q C hq order lines unique ao eval small⟩
  by_contra missing
  apply bad
  refine ⟨C,ao,eval,le_rfl,(read_iff_pairs I C eval 1).mpr ?_⟩
  intro p l hi
  cases h : readsAtMost C (N+N) [p.val,N+l.val] 1 with
  | true => rfl
  | false => exact (missing ⟨p,l,hi,h⟩).elim

#print axioms counterexample_conditions
end PEqualNP.Research2583
