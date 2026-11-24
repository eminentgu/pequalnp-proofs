import Normalize

namespace PEqualNP.Research4387

private theorem crossBit {w : ℕ} (a b v : BitVec w) (na : v ≠ a) (nb : v ≠ b)
    (op : v = a &&& b ∨ v = a ||| b) : ∃ i : Fin w, a[i.val] = true ∧ b[i.val] = false := by
  by_contra missing
  have incl (i : ℕ) (hi : i < w) (ha : a[i] = true) : b[i] = true := by
    cases hb : b[i] with
    | false => exact (missing ⟨⟨i,hi⟩,ha,hb⟩).elim
    | true => rfl
  rcases op with prod | sum
  · apply na
    rw [prod]
    ext i hi
    cases h : a[i] with
    | false => simp [h]
    | true => simp [h,incl i hi h]
  · apply nb
    rw [sum]
    ext i hi
    cases h : a[i] with
    | false => simp [h]
    | true => simp [h,incl i hi h]

/-- Each new binary mask has operand bit witnesses in both directions. Thus a
search may exclude every operand pair ordered by bitwise support inclusion. -/
theorem incomparableOperands {w : ℕ} {bank : List (BitVec w)} {a b v : BitVec w}
    (new : v ∉ bank) (ha : a ∈ bank) (hb : b ∈ bank) (op : v = a &&& b ∨ v = a ||| b) :
    (∃ i : Fin w, a[i.val] = true ∧ b[i.val] = false) ∧
      ∃ j : Fin w, b[j.val] = true ∧ a[j.val] = false := by
  have na : v ≠ a := fun e => new (e ▸ ha)
  have nb : v ≠ b := fun e => new (e ▸ hb)
  exact ⟨crossBit a b v na nb op,crossBit b a v nb na (by simpa only [BitVec.and_comm b a,BitVec.or_comm b a] using op)⟩

end PEqualNP.Research4387

#print axioms PEqualNP.Research4387.incomparableOperands
