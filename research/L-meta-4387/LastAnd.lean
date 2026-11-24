import Mathlib

namespace PEqualNP.Research4387.LastAnd

abbrev Row := BitVec 58

def raw (i : Fin 14) : Row :=
  (#[95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752] : Array Row)[i.val]!

def target : Row := 2097151

/-- For a maximal independent assignment missing input i, the selected
positive edge lies inside the assignment with i added. -/
private def witness (i : Fin 14) (t : Fin 37) : ℕ :=
  ((#[
    #[0, 0, 1, 0, 0, 0, 1, 2, 0, 1, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0],
    #[0, 3, 0, 3, 4, 3, 4, 0, 3, 0, 4, 0, 3, 0, 4, 0, 3, 0, 3, 0, 4, 3, 0, 0, 0, 5, 3, 5, 4, 5, 4, 5, 3, 5, 3, 4, 3],
    #[0, 0, 6, 6, 0, 0, 6, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 7, 7, 6, 7, 6, 7, 7, 6, 8, 8, 6, 8, 8, 6, 8, 6, 7, 7, 7, 6],
    #[0, 9, 0, 9, 0, 9, 0, 0, 9, 0, 0, 10, 9, 10, 10, 10, 9, 11, 9, 11, 11, 9, 11, 10, 10, 0, 9, 0, 0, 0, 0, 10, 9, 11, 9, 10, 9],
    #[0, 0, 0, 0, 0, 0, 0, 12, 12, 12, 12, 13, 13, 13, 13, 12, 12, 0, 0, 0, 0, 0, 12, 13, 12, 14, 14, 14, 14, 12, 12, 13, 13, 14, 12, 13, 12],
    #[0, 0, 0, 0, 15, 15, 15, 16, 16, 16, 15, 0, 0, 0, 15, 16, 15, 17, 17, 17, 15, 15, 16, 17, 16, 0, 0, 0, 15, 16, 15, 0, 0, 17, 16, 15, 15],
    #[0, 0, 18, 18, 19, 19, 18, 0, 0, 18, 19, 20, 20, 18, 19, 20, 19, 0, 0, 18, 19, 18, 0, 20, 18, 0, 0, 18, 19, 0, 18, 20, 18, 0, 0, 19, 18],
    #[0, 0, 3, 0, 0, 0, 9, 3, 0, 3, 9, 0, 0, 3, 0, 3, 0, 0, 0, 3, 0, 0, 3, 0, 3, 0, 0, 9, 0, 9, 9, 0, 0, 0, 0, 0, 0],
    #[1, 6, 0, 0, 1, 6, 0, 6, 6, 0, 6, 1, 6, 0, 1, 6, 6, 1, 18, 0, 1, 0, 18, 1, 0, 1, 18, 0, 1, 18, 0, 1, 0, 1, 18, 1, 0],
    #[4, 15, 4, 15, 0, 0, 0, 4, 19, 4, 0, 4, 15, 4, 0, 4, 0, 4, 19, 4, 0, 0, 4, 4, 4, 15, 15, 15, 0, 19, 0, 15, 15, 19, 19, 0, 0],
    #[2, 12, 12, 12, 2, 12, 12, 0, 0, 0, 0, 2, 16, 16, 2, 0, 0, 2, 12, 12, 2, 12, 0, 2, 0, 2, 16, 16, 2, 0, 0, 2, 16, 2, 0, 2, 0],
    #[10, 13, 10, 13, 10, 13, 10, 10, 20, 10, 10, 0, 0, 0, 0, 0, 0, 13, 13, 13, 13, 13, 20, 0, 0, 10, 20, 10, 10, 10, 10, 0, 0, 20, 20, 0, 0],
    #[7, 7, 11, 17, 7, 7, 11, 7, 7, 11, 7, 7, 7, 17, 7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 11, 17, 11, 11, 11, 11, 17, 17, 0, 0, 0, 0],
    #[5, 8, 5, 14, 8, 8, 14, 5, 8, 5, 8, 5, 8, 5, 8, 5, 8, 5, 14, 5, 14, 14, 5, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ] : Array (Array ℕ))[i.val]!)[t.val]!

private def absent (i : Fin 14) (t : Fin 37) :=
  (raw i).getLsbD (21+t.val) = false

private def respects (i : Fin 14) (z : Row) : Prop :=
  ∀ t : Fin 37, absent i t →
    z.getLsbD (witness i t) = true → z.getLsbD (21+t.val) = true

private instance (i : Fin 14) (z : Row) : Decidable (respects i z) := by
  unfold respects absent
  infer_instance

private theorem others : ∀ i j : Fin 14, i ≠ j → respects i (raw j) := by
  decide +kernel

private theorem posRows : ∀ i : Fin 14, ∀ t : Fin 37,
    target.getLsbD (witness i t) = true := by decide +kernel

private theorem negRows : ∀ t : Fin 37, target.getLsbD (21+t.val) = false := by decide

/-- A direct certificate for an essential input uses an edge that is accepted
and a maximal independent assignment that is rejected. They are related by
adding that one raw input and possibly deleting other inputs. -/
def certificates (i : Fin 14) (z : Row) : Finset (Fin 37) :=
  Finset.univ.filter fun t => (raw i).getLsbD (21+t.val) = false ∧
    z.getLsbD (21+t.val) = false ∧ z.getLsbD (witness i t) = true

private def commonRows (i j : Fin 14) : Finset (Fin 37) :=
  Finset.univ.filter fun t => (raw i).getLsbD (21+t.val) = false ∧
    (raw j).getLsbD (21+t.val) = false

private theorem commonMin : ∀ i j : Fin 14, 13 ≤ (commonRows i j).card := by
  decide +kernel

/-- At least one operand of a final AND has seven distinct certificates of
dependence for each of the fourteen raw inputs. -/
theorem sevenWitnesses {a b : Row} (last : a &&& b = target) :
    (∀ i, 7 ≤ (certificates i a).card) ∨ (∀ i, 7 ≤ (certificates i b).card) := by
  classical
  by_contra! bad
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := bad
  have sub : commonRows i j ⊆ certificates i a ∪ certificates j b := by
    intro t ht
    have hit (k : Fin 14) := congrArg (fun z : Row => z.getLsbD (witness k t)) last
    have miss := congrArg (fun z : Row => z.getLsbD (21+t.val)) last
    simp only [BitVec.getLsbD_and,negRows,Bool.and_eq_false_imp] at miss
    obtain ⟨_,ai,aj⟩ := Finset.mem_filter.mp ht
    by_cases ha : a.getLsbD (21+t.val) = false
    · have both := hit i
      simp only [BitVec.getLsbD_and,posRows,Bool.and_eq_true] at both
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ai,ha,both.1⟩)
    · have both := hit j
      simp only [BitVec.getLsbD_and,posRows,Bool.and_eq_true] at both
      have hb : b.getLsbD (21+t.val) = false := by
        cases h : a.getLsbD (21+t.val) <;> simp_all
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,aj,hb,both.2⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have := commonMin i j
  omega

/-- The finite bank generated without one physical raw input. The prepaid
first-point OR is represented by an OR of originals 0 and 1. -/
inductive Without (i : Fin 14) : Row → Prop where
  | rawInput (j : Fin 14) (ne : i ≠ j) : Without i (raw j)
  | zero : Without i 0
  | one : Without i (BitVec.allOnes 58)
  | conj {a b} : Without i a → Without i b → Without i (a &&& b)
  | disj {a b} : Without i a → Without i b → Without i (a ||| b)

private theorem withoutRespects {i z} (h : Without i z) : respects i z := by
  induction h with
  | rawInput j ne => exact others i j ne
  | zero => simp [respects]
  | one =>
    intro t _ _
    simp only [BitVec.getLsbD_allOnes,decide_eq_true_eq]
    omega
  | conj _ _ ihA ihB =>
    intro t ht both
    simp only [BitVec.getLsbD_and,Bool.and_eq_true] at both ⊢
    exact ⟨ihA t ht both.1,ihB t ht both.2⟩
  | disj _ _ ihA ihB =>
    intro t ht either
    simp only [BitVec.getLsbD_or,Bool.or_eq_true] at either ⊢
    exact either.imp (ihA t ht) (ihB t ht)

/-- At least one operand of every successful final AND needs all fourteen raw
inputs, regardless of the available gate budget or circuit sharing. -/
theorem fullOperand {a b : Row} (last : a &&& b = target) :
    (∀ i, ¬ Without i a) ∨ (∀ i, ¬ Without i b) := by
  have eliminate {z i} (many : 7 ≤ (certificates i z).card) (omitted : Without i z) : False := by
    obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0 < (certificates i z).card by omega)
    obtain ⟨_,miss,no,yes⟩ := Finset.mem_filter.mp ht
    have accepted := withoutRespects omitted t miss yes
    simp [no] at accepted
  exact (sevenWitnesses last).imp (fun h i => eliminate (h i)) (fun h i => eliminate (h i))

end PEqualNP.Research4387.LastAnd

#print axioms PEqualNP.Research4387.LastAnd.sevenWitnesses
#print axioms PEqualNP.Research4387.LastAnd.fullOperand
