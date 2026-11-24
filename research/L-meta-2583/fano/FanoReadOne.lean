import FanoBounds
import IncidenceReadPairs

namespace PEqualNP.Research2583.Fano
open PEqualNP.CircuitLowerBounds

theorem joint_read_one : ReadK.IsReadK 14 stars 1 :=
  (PEqualNP.Research2583.read_iff_pairs I stars computes 1).2 each_flag

def Replacement (C : Circuit) : Prop :=
  ∃ D : Circuit, TopForm.IsAO2 14 D ∧ Computes D ∧ D.size ≤ C.size ∧ ReadK.IsReadK 14 D 1

theorem replace_at_27 (C : Circuit) (size : 27 ≤ C.size) : Replacement C :=
  ⟨stars,stars_ao,computes,stars_size ▸ size,joint_read_one⟩

theorem replace_one_layer (C : Circuit) (ao : TopForm.IsAO2 14 C) (correct : Computes C)
    (layer : ¬ Nested C) : Replacement C := replace_at_27 C (single_and_layer ao correct layer)

/-- Any counterexample in this Fano labeling has 20 to 26 gates, an AND ancestor of another
AND, and at least one prime implicant without a jointly single-read proof tree. -/
theorem remaining_window (C : Circuit) (ao : TopForm.IsAO2 14 C) (correct : Computes C)
    (counterexample : ¬ Replacement C) :
    20 ≤ C.size ∧ C.size ≤ 26 ∧ Nested C ∧ ¬ ReadK.IsReadK 14 C 1 := by
  refine ⟨twenty ao correct,?_,?_,?_⟩
  · by_contra! h
    exact counterexample (replace_at_27 C (by omega))
  · by_contra h
    exact counterexample (replace_one_layer C ao correct h)
  · intro h
    exact counterexample ⟨C,ao,correct,le_rfl,h⟩

theorem missing_flag (C : Circuit) (ao : TopForm.IsAO2 14 C) (correct : Computes C)
    (counterexample : ¬ Replacement C) :
    ∃ p l : Fin 7, I p l ∧ ReadK.readsAtMost C 14 [p.val,7+l.val] 1 = false := by
  have bad := (remaining_window C ao correct counterexample).2.2.2
  by_contra h
  apply bad
  apply (PEqualNP.Research2583.read_iff_pairs I C correct 1).2
  intro p l flag
  by_contra absent
  exact h ⟨p,l,flag,Bool.eq_false_iff.mpr absent⟩

#print axioms remaining_window
#print axioms missing_flag
end PEqualNP.Research2583.Fano
