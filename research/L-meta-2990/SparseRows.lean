import PEqualNP.Outside.L_meta_1716

/-! Canonical maximal negative rows, with as many point inputs active as soundness permits. -/
namespace PEqualNP.Research2990
open CircuitLowerBounds MetaComplexity

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def outsidePoints (Y : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter fun p => ∀ l ∈ Y, ¬I p l

def negativeRow (Y : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.append (fun p => decide (p ∈ outsidePoints I Y)) (fun l => decide (l ∈ Y))

def isPositive (z : Fin (N+N) → Bool) : Prop :=
  ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

theorem row_is_negative (Y : Finset (Fin N)) : ¬ isPositive I (negativeRow I Y) := by
  rintro ⟨p,l,hi,hp,hl⟩
  simp only [negativeRow,Fin.append_left,Fin.append_right,decide_eq_true_eq] at hp hl
  exact (Finset.mem_filter.mp hp).2 l hl hi

theorem sparse_sound_iff (q : ℕ) (C : Circuit) (mono : Monotone2 C) :
    (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      ¬ isPositive I z → circuitFun (N+N) C z = false) ↔
    (∀ Y : Finset (Fin N), Y.card ≤ q → circuitFun (N+N) C (negativeRow I Y) = false) := by
  constructor
  · intro safe Y size
    apply safe _ _ (row_is_negative I Y)
    have count : (Finset.univ.filter fun l : Fin N => negativeRow I Y (Fin.natAdd N l) = true) = Y := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, negativeRow,
        Fin.append_right, decide_eq_true_eq]
    simpa only [Fintype.card_subtype, count] using size
  · intro safe z size noEdge
    let Y := Finset.univ.filter fun l : Fin N => z (Fin.natAdd N l) = true
    have hY : Y.card ≤ q := by simpa [Y,Fintype.card_subtype] using size
    have extendsRow : ∀ v, z v = true → negativeRow I Y v = true := by
      intro v
      induction v using Fin.addCases with
      | left p =>
        intro hp
        simp only [negativeRow,Fin.append_left,decide_eq_true_eq]
        exact Finset.mem_filter.mpr ⟨by simp,fun l hl hi => noEdge ⟨p,l,hi,hp,(Finset.mem_filter.mp hl).2⟩⟩
      | right l =>
        intro hl
        exact (show negativeRow I Y (Fin.natAdd N l) = true by
          simpa only [negativeRow,Fin.append_right,decide_eq_true_eq,Y,Finset.mem_filter,
            Finset.mem_univ,true_and] using hl)
    cases hz : circuitFun (N+N) C z with
    | false => rfl
    | true =>
      have h := PEqualNP.Outside.L_meta_1716.eval_mono_fn C.gates (fun g hg => (mono g hg).1)
        z (negativeRow I Y) extendsRow C.output hz
      exact Bool.noConfusion (h.symm.trans (safe Y hY))

/-- On all promised inputs, sparse rejection plus acceptance of each incident pair
    determines the value of the entire circuit. -/
theorem correct_on_slice (q : ℕ) (C : Circuit) (mono : Monotone2 C)
    (flag : ∀ p l, I p l → circuitFun (N+N) C
      (fun x => decide (x = Fin.castAdd N p ∨ x = Fin.natAdd N l)) = true)
    (safe : ∀ Y : Finset (Fin N), Y.card ≤ q → circuitFun (N+N) C (negativeRow I Y) = false)
    (z : Fin (N+N) → Bool) (size : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q) :
    circuitFun (N+N) C z = true ↔ isPositive I z := by
  constructor
  · intro hz
    by_contra noEdge
    exact Bool.noConfusion (hz.symm.trans ((sparse_sound_iff I q C mono).mpr safe z size noEdge))
  · rintro ⟨p,l,hi,hp,hl⟩
    apply PEqualNP.Outside.L_meta_1716.eval_mono_fn C.gates (fun g hg => (mono g hg).1)
      (fun x => decide (x = Fin.castAdd N p ∨ x = Fin.natAdd N l)) z _ C.output (flag p l hi)
    intro v hv
    rcases of_decide_eq_true hv with rfl | rfl
    · exact hp
    · exact hl

#print axioms sparse_sound_iff
#print axioms correct_on_slice
end PEqualNP.Research2990
