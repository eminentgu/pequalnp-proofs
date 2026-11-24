import PEqualNP.Defs.ReadK
import Mathlib.Data.List.Sort

/-! Prime implicants and joint READ witnesses of any rectangular incidence function. -/
namespace PEqualNP.Research2583

open CircuitLowerBounds MetaComplexity ReadK

variable {P L : ℕ} (I : Fin P → Fin L → Prop) [∀ p l, Decidable (I p l)]

private theorem bank_disjoint (p : Fin P) (l : Fin L) :
    Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = P + l.val at he
  have := p.isLt
  omega

theorem prime_iff_pair (C : Circuit)
    (hC : ∀ z : Fin (P+L) → Bool, circuitFun (P+L) C z = decide
      (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P+L))) : IsPrimeImplicant (P+L) C S ↔
      ∃ p l, I p l ∧ S = {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  constructor
  · rintro ⟨hs, hmin⟩
    rw [hC, decide_eq_true_eq] at hs
    obtain ⟨p, l, hi, hp, hl⟩ := hs
    refine ⟨p, l, hi, ?_⟩
    have hsub : {Fin.castAdd L p, Fin.natAdd P l} ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro (of_decide_eq_true hp) (of_decide_eq_true hl)
    by_contra hne
    have hf := hmin _ (Finset.mem_ssubsets.mpr (lt_of_le_of_ne hsub (Ne.symm hne)))
    rw [hC, decide_eq_false_iff_not] at hf
    exact hf ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · rintro ⟨p, l, hi, rfl⟩
    constructor
    · rw [hC, decide_eq_true_eq]
      exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
    · intro T hT
      have hT' := Finset.mem_ssubsets.mp hT
      rw [hC, decide_eq_false_iff_not]
      rintro ⟨p', l', _, hp, hl⟩
      have hp' : Fin.castAdd L p' ∈ T := of_decide_eq_true hp
      have hl' : Fin.natAdd P l' ∈ T := of_decide_eq_true hl
      have pe : Fin.castAdd L p' = Fin.castAdd L p := by
        have := Finset.mem_insert.mp (hT'.subset hp')
        exact this.resolve_right (fun hm => bank_disjoint p' l (Finset.mem_singleton.mp hm))
      have le : Fin.natAdd P l' = Fin.natAdd P l := by
        have := Finset.mem_insert.mp (hT'.subset hl')
        exact Finset.mem_singleton.mp (this.resolve_left (fun e => bank_disjoint p l' e.symm))
      exact hT'.not_ge (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa only [pe] using hp'
        · rw [Finset.mem_singleton.mp hw, ← le]
          exact hl')

theorem setList_pair (p : Fin P) (l : Fin L) :
    setList ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P+L))) =
      [p.val, P+l.val] := by
  have hs : (setList ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P+L)))).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_finRange (P+L)).sublist (List.filter_sublist ..)
  apply hs.eq_of_mem_iff
  · have hlt : p.val < P+l.val := Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right _ _)
    exact List.Pairwise.cons (by simpa using hlt) (by simp)
  · intro j
    simp only [setList, List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
      true_and, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨i, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Fin.castAdd L p, Or.inl rfl, rfl⟩
      · exact ⟨Fin.natAdd P l, Or.inr rfl, rfl⟩

/-- A joint witness on each incident pair is necessary and sufficient for READ-k. -/
theorem read_iff_pairs (C : Circuit)
    (hC : ∀ z : Fin (P+L) → Bool, circuitFun (P+L) C z = decide
      (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (k : ℕ) : IsReadK (P+L) C k ↔
      ∀ p l, I p l → readsAtMost C (P+L) [p.val,P+l.val] k = true := by
  constructor
  · intro hr p l h
    simpa only [setList_pair] using
      hr _ ((prime_iff_pair I C hC _).mpr ⟨p,l,h,rfl⟩)
  · intro hr S hS
    obtain ⟨p,l,hi,rfl⟩ := (prime_iff_pair I C hC _).mp hS
    simpa only [setList_pair] using hr p l hi

#print axioms read_iff_pairs

end PEqualNP.Research2583
