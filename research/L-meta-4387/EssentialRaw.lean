import PhysicalHeawood

namespace Packed4387

private def preservesRow (p n : ℕ) (w : Col) := w.getLsbD p = true → w.getLsbD n = true

private theorem propagate (p n : ℕ) (bank xs : List Col) (chain : Chain bank xs)
    (hb : ∀ w ∈ bank, preservesRow p n w) : ∀ w ∈ bank ++ xs, preservesRow p n w := by
  induction xs generalizing bank with
  | nil => simpa using hb
  | cons x tail ih =>
    have first := chain ⟨0,by simp⟩
    change Step (bank ++ []) x at first
    rw [List.append_nil] at first
    obtain ⟨a,ha,b,hc,op⟩ := first
    have xok : preservesRow p n x := by
      rcases op with rfl | rfl
      · intro h
        simp only [BitVec.getLsbD_and, Bool.and_eq_true] at h ⊢
        exact ⟨hb a ha h.1, hb b hc h.2⟩
      · intro h
        simp only [BitVec.getLsbD_or, Bool.or_eq_true] at h ⊢
        exact h.imp (hb a ha) (hb b hc)
    have hrest : Chain (bank ++ [x]) tail := by
      intro j
      have hj := chain ⟨j.val+1, by simp⟩
      simpa only [List.take_succ_cons, List.get_eq_getElem, List.getElem_cons_succ,
        List.append_assoc, List.singleton_append] using hj
    have hbank : ∀ w ∈ bank ++ [x], preservesRow p n w := by
      intro w hw
      rcases List.mem_append.mp hw with old | new
      · exact hb w old
      · simpa only [List.mem_singleton.mp new] using xok
    simpa only [List.append_assoc, List.singleton_append] using ih (bank ++ [x]) hrest hbank

private def witnessRows : List (ℕ × ℕ) :=
  [(1,23),(4,25),(6,23),(9,22),(12,28),(15,25),(18,23),
   (0,21),(1,21),(4,21),(2,21),(10,21),(7,21),(5,21)]

private theorem witnessed : ∀ i : Fin 14,
    let r := witnessRows.getD i.val (0,0)
    target.getLsbD r.1 = true ∧ target.getLsbD r.2 = false ∧
      (seeds.eraseIdx (i.val+2)).all (fun w =>
        decide (w.getLsbD r.1 = true → w.getLsbD r.2 = true)) = true := by
  decide +kernel

/-- Even with both constants and the extra OR, erasing any single raw input
    makes the target unreachable at *every* gate budget. -/
theorem allRawEssential (i : Fin 14) (xs : List Col) (chain : Chain (seeds.eraseIdx (i.val+2)) xs) :
    target ∉ seeds.eraseIdx (i.val+2) ++ xs := by
  obtain ⟨pos,neg,others⟩ := witnessed i
  intro hit
  have monotone := propagate _ _ _ xs chain
    (fun w hw => by unfold preservesRow; exact of_decide_eq_true (List.all_eq_true.mp others w hw))
  exact Bool.noConfusion ((monotone target hit pos).symm.trans neg)

#print axioms allRawEssential
end Packed4387
