import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Research4387

private def Chain {α : Type} (P : List α → α → Prop) (base xs : List α) :=
  ∀ i : Fin xs.length, P (base ++ xs.take i.val) (xs.get i)

private theorem chainPrefix {α : Type} {P : List α → α → Prop} {base xs tail : List α}
    (h : Chain P base (xs ++ tail)) : Chain P base xs := by
  intro i
  have := h ⟨i.val,by simp; omega⟩
  simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,
    List.take_append_of_le_length i.isLt.le] using this

private theorem chainLast {α : Type} {P : List α → α → Prop} {base xs : List α} {v : α}
    (h : Chain P base (xs ++ [v])) : P (base ++ xs) v := by
  have := h ⟨xs.length,by simp⟩
  simpa only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),
    Nat.sub_self,List.getElem_cons_zero,List.take_append_length] using this

private theorem chainPush {α : Type} {P : List α → α → Prop} {base xs : List α} {v : α}
    (h : Chain P base xs) (last : P (base ++ xs) v) : Chain P base (xs ++ [v]) := by
  rintro ⟨i,hi⟩
  by_cases before : i < xs.length
  · simpa only [List.get_eq_getElem,List.getElem_append_left before,List.take_append_of_le_length before.le]
      using (h ⟨i,before⟩)
  · have eq : i = xs.length := by simp at hi; omega
    subst i
    simpa only [List.get_eq_getElem,List.getElem_append_right (Nat.le_refl _),
      Nat.sub_self,List.getElem_cons_zero,List.take_append_length] using last

private def Step {w : Nat} (bank : List (BitVec w)) (v : BitVec w) : Prop :=
  ∃ a ∈ bank, ∃ b ∈ bank, v = a &&& b ∨ v = a ||| b

private def Fresh {w : Nat} (bank : List (BitVec w)) (v : BitVec w) : Prop :=
  v ∉ bank ∧ v ≠ 0 ∧ v ≠ BitVec.allOnes w ∧ Step bank v

private theorem eraseConstants {w : Nat} {bank : List (BitVec w)} {v : BitVec w}
    (new : v ∉ 0 :: BitVec.allOnes w :: bank)
    (h : Step (0 :: BitVec.allOnes w :: bank) v) : Fresh bank v := by
  simp only [List.mem_cons,not_or] at new
  refine ⟨new.2.2,new.1,new.2.1,?_⟩
  obtain ⟨a,ha,b,hb,op⟩ := h
  simp only [List.mem_cons] at ha hb
  rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
  all_goals first | exact ⟨a,ha,b,hb,op⟩ | rcases op with rfl | rfl <;> simp_all

/-- Scan in topological order. A value already available costs no additional
gate. Each discarded constant remains available solely in the bookkeeping. -/
private theorem scan {w : Nat} (base xs : List (BitVec w))
    (h : Chain Step (0 :: BitVec.allOnes w :: base) xs) :
    ∃ ys, ys.length ≤ xs.length ∧ Chain Fresh base ys ∧
      ∀ z ∈ (0 :: BitVec.allOnes w :: base) ++ xs,
        z ∈ 0 :: BitVec.allOnes w :: (base ++ ys) := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[],by simp,fun i => Fin.elim0 i,by simp⟩
  | append_singleton xs v ih =>
    obtain ⟨ys,budget,valid,cover⟩ := ih (chainPrefix h)
    have op := chainLast h
    have extended : Step (0 :: BitVec.allOnes w :: (base ++ ys)) v := by
      obtain ⟨a,ha,b,hb,eq⟩ := op
      exact ⟨a,cover _ ha,b,cover _ hb,eq⟩
    by_cases old : v ∈ 0 :: BitVec.allOnes w :: (base ++ ys)
    · refine ⟨ys,by simp; omega,valid,?_⟩
      intro z hz
      rw [← List.append_assoc] at hz
      rcases List.mem_append.mp hz with previous | last
      · exact cover _ previous
      · simpa only [List.mem_singleton.mp last] using old
    · refine ⟨ys ++ [v],by simpa using budget,chainPush valid (eraseConstants old extended),?_⟩
      intro z hz
      rw [← List.append_assoc] at hz
      rcases List.mem_append.mp hz with previous | last
      · have p := cover _ previous
        simp only [List.mem_cons,List.mem_append] at p ⊢
        tauto
      · simp [List.mem_singleton.mp last]

/-- An arbitrary-width AND/OR straight-line program for a nonconstant target
can omit constants, repeated masks, and every instruction after the target. -/
theorem normalizeChain {w : Nat} (base xs : List (BitVec w)) (target : BitVec w)
    (valid : ∀ i : Fin xs.length,
      let bank := (0 :: BitVec.allOnes w :: base) ++ xs.take i.val
      ∃ a ∈ bank, ∃ b ∈ bank, xs.get i = a &&& b ∨ xs.get i = a ||| b)
    (hit : target ∈ (0 :: BitVec.allOnes w :: base) ++ xs)
    (nonzero : target ≠ 0) (nonone : target ≠ BitVec.allOnes w) (new : target ∉ base) :
    ∃ ys : List (BitVec w), ys.length ≤ xs.length ∧ ys.getLast? = some target ∧
      ∀ i : Fin ys.length,
        let bank := base ++ ys.take i.val
        ys.get i ∉ bank ∧ ys.get i ≠ 0 ∧ ys.get i ≠ BitVec.allOnes w ∧
          ∃ a ∈ bank, ∃ b ∈ bank, ys.get i = a &&& b ∨ ys.get i = a ||| b := by
  obtain ⟨ys,budget,normal,cover⟩ := scan base xs valid
  have inYs : target ∈ ys := by
    have available := cover target hit
    simp only [List.mem_cons,List.mem_append] at available
    exact ((available.resolve_left nonzero).resolve_left nonone).resolve_left new
  obtain ⟨pre,tail,rfl⟩ := List.append_of_mem inYs
  refine ⟨pre ++ [target],?_,by simp,?_⟩
  · simp at budget ⊢; omega
  · apply chainPrefix (tail:=tail) (P:=Fresh)
    simpa only [List.append_assoc,List.singleton_append] using normal

end PEqualNP.Research4387

#print axioms PEqualNP.Research4387.normalizeChain
