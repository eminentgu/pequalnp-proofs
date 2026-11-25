/-- Incident flags for which no proof of their positive pair reads each of
    its two variables at most twice. -/
def heavy {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter fun e => I e.1 e.2 ∧
    PEqualNP.ReadK.readsAtMost C (N+N) [e.1.val, N+e.2.val] 2 = false

/-- Generalize L-meta-2673's final union bound to retain the incident flags
    that were formerly excluded by its all-pairs read hypothesis. -/
theorem accounting (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hS : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → circuitFun (N + N) C z = false) :
    N*(q+1) ≤ 50*C.size + 2*N + (heavy I C).card := by
  classical
  have hf := plane_four_free I hU
  have hf' := swapped_free I hf
  have hS0 : ∀ X Y : Set (Fin N), ∀ a, a ≤ 2 → OHom N C false C.output a 1 X Y →
      ∃ p ∈ X, ∃ l ∈ Y, I p l := fun X Y a ha hh => hom_output_safe2 I h hS hh ha (by omega)
  have hS1 : ∀ X Y : Set (Fin N), ∀ a, a ≤ 2 → OHom N C true C.output a 1 X Y →
      ∃ p ∈ X, ∃ l ∈ Y, (fun l p => I p l) p l := by
    intro X Y a ha hh
    obtain ⟨p', hp', l', hl', hi⟩ := hom_output_safe2 I h hS hh (by omega) ha
    exact ⟨l', hl', p', hp', hi⟩
  let U := onceB C I false
  let V := exchange (onceB C (fun l p => I p l) true)
  let W := twiceEdges N C I
  have hUcard : U.card ≤ 8 * C.size + N := once_budget_bound h I hf false hS0
  have hVcard : V.card ≤ 8 * C.size + N := by
    unfold V
    rw [exchange_card]
    exact once_budget_bound h (fun l p => I p l) hf' true hS1
  have hWcard : W.card ≤ 34 * C.size := IncidenceTwice2990.sparseTwice I h hf hS
  have hsub : allEdges I ⊆ heavy I C ∪ (U ∪ (V ∪ W)) := by
    rintro ⟨p, l⟩ he
    have hi : I p l := (Finset.mem_filter.mp he).2
    by_cases read : PEqualNP.ReadK.readsAtMost C (N+N) [p.val,N+l.val] 2 = true
    · apply Finset.mem_union_right
      obtain ⟨a, b, ha₁, ha₂, hb₁, hb₂, hh⟩ := plane_read_cover I h hS hi read
      by_cases hb : b = 1
      · subst b
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, a, ha₁, ha₂, hh⟩)
      by_cases ha : a = 1
      · subst a
        exact Finset.mem_union_right _ (Finset.mem_union_left _ (exchange_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, b, hb₁, hb₂, hh⟩)))
      obtain rfl : a = 2 := by omega
      obtain rfl : b = 2 := by omega
      exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hh⟩))
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,Bool.eq_false_iff.mpr read⟩
  have card := Finset.card_le_card hsub
  rw [allEdges_card I q hL] at card
  have h0 := Finset.card_union_le (heavy I C) (U ∪ (V ∪ W))
  have h1 := Finset.card_union_le U (V ∪ W)
  have h2 := Finset.card_union_le V W
  omega
