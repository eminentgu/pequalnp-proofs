import PEqualNP.Outside.L_meta_1716

/-! Exact test rows for monotone incidence functions. On the explicit Fano plane there
    are 21 incident pairs and 37 distinct maximal nonincident rows. -/
namespace PEqualNP.Research2583.Boundary

open CircuitLowerBounds MetaComplexity TopForm

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
abbrev Bank (N : ℕ) := Finset (Fin N)

def farLines (X : Bank N) : Bank N := Finset.univ.filter fun l => ∀ p ∈ X, ¬I p l
def farPoints (Y : Bank N) : Bank N := Finset.univ.filter fun p => ∀ l ∈ Y, ¬I p l

theorem subset_closure (X : Bank N) : X ⊆ farPoints I (farLines I X) := by
  intro p hp
  simp only [farPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  intro l hl
  exact (Finset.mem_filter.mp hl).2 p hp

theorem stable (X : Bank N) :
    farLines I (farPoints I (farLines I X)) = farLines I X := by
  apply Finset.Subset.antisymm
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp =>
      (Finset.mem_filter.mp hl).2 p (subset_closure I X hp)⟩
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp =>
      (Finset.mem_filter.mp hp).2 l hl⟩

theorem exact_tests (F : Bank N → Bank N → Bool)
    (mono : ∀ {X X' Y Y'}, X ⊆ X' → Y ⊆ Y' → F X Y = true → F X' Y' = true) :
    (∀ X Y, F X Y = decide (∃ p ∈ X, ∃ l ∈ Y, I p l)) ↔
    (∀ p l, I p l → F {p} {l} = true) ∧
    (∀ X, X = farPoints I (farLines I X) → F X (farLines I X) = false) := by
  constructor
  · intro correct
    constructor
    · intro p l hi
      rw [correct, decide_eq_true_eq]
      exact ⟨p,by simp,l,by simp,hi⟩
    · intro X _
      rw [correct, decide_eq_false_iff_not]
      rintro ⟨p,hp,l,hl,hi⟩
      exact (Finset.mem_filter.mp hl).2 p hp hi
  · rintro ⟨yes,no⟩ X Y
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro on
      by_contra missing
      have hY : Y ⊆ farLines I X := by
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp hi => missing ⟨p,hp,l,hl,hi⟩⟩
      have on' := mono (subset_closure I X) hY on
      let closed := farPoints I (farLines I X)
      have hc : farLines I closed = farLines I X := stable I X
      have hold : closed = farPoints I (farLines I closed) := by rw [hc]
      have reject := no closed hold
      rw [hc] at reject
      exact Bool.noConfusion (on'.symm.trans reject)
    · rintro ⟨p,hp,l,hl,hi⟩
      exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
        (yes p l hi)

def onSets (C : Circuit) (X Y : Bank N) : Bool :=
  circuitFun (N+N) C (Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y)))

/-- For a legal AO2 circuit the gate model supplies the monotonicity needed above. -/
theorem circuit_tests (C : Circuit) (ao : IsAO2 (N+N) C) :
    (∀ X Y, onSets C X Y = decide (∃ p ∈ X, ∃ l ∈ Y, I p l)) ↔
    (∀ p l, I p l → onSets C {p} {l} = true) ∧
    (∀ X, X = farPoints I (farLines I X) → onSets C X (farLines I X) = false) := by
  apply exact_tests
  intro X X' Y Y' hX hY h
  exact PEqualNP.Outside.L_meta_1716.cf_mono C (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩)
    X X' Y Y' hX hY h

#print axioms circuit_tests
end PEqualNP.Research2583.Boundary
