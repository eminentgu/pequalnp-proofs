import LastAnd
import RootSupport

namespace PEqualNP.Research4387.LastAnd

def seed (j : Fin 15) : Row := if h : j.val < 14 then raw ⟨j.val,h⟩ else raw 0 ||| raw 1

theorem prepaid : seed 14 = 95274182876594239 := by decide

def points : Finset (Fin 15) := {2,3,4,5,6,14}

def Hits (S : Finset (Fin 15)) := ∀ k : Fin 21, ∃ j ∈ S, (seed j).getLsbD k.val = true

instance (S : Finset (Fin 15)) : Decidable (Hits S) := by unfold Hits; infer_instance

/-- A seven-edge packing after removing each of the six required sources.
Every source other than the removed one covers at most one selected edge. -/
private def packing (i : Fin 15) : Finset (Fin 21) :=
  match i.val with
  | 2 => {0,6,15,12,10,7,8}
  | 3 => {0,6,19,16,10,11,14}
  | 4 => {0,6,15,12,13,11,14}
  | 5 => {0,6,15,16,10,17,14}
  | 6 => {0,6,19,16,20,11,14}
  | _ => {0,6,4,16,20,11,14}

private def covered (i j : Fin 15) : Finset (Fin 21) :=
  (packing i).filter fun k => (seed j).getLsbD k.val = true

private theorem packingSize : ∀ i : Fin 15, (packing i).card = 7 := by decide

private theorem eachSource : ∀ i ∈ points, ∀ j : Fin 15, j ≠ i → (covered i j).card ≤ 1 := by
  decide +kernel

theorem sixSeeds (S : Finset (Fin 15)) (few : S.card ≤ 6) (hits : Hits S) : S = points := by
  have inc : points ⊆ S := by
    intro i hi
    by_contra absent
    have sub : packing i ⊆ S.biUnion (covered i) := by
      intro k hk
      obtain ⟨j,hj,on⟩ := hits k
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨hk,on⟩⟩
    have bound := Finset.card_biUnion_le_card_mul S (covered i) 1
      (fun j hj => eachSource i hi j (fun e => absent (e ▸ hj)))
    have size := Finset.card_le_card sub
    rw [packingSize] at size
    omega
  have size : S.card ≤ points.card := few.trans (show 6 ≤ points.card by decide)
  have equal : points = S := Finset.eq_of_subset_of_card_le inc size
  exact equal.symm

def allPoints : Row := 144115188075855871

def otherSide : Row := 144115188077953023

private theorem dataOn : ∀ t : Fin 58, allPoints.getLsbD t.val = true →
    ∃ k : Fin 21, ∀ j ∈ points,
      (seed j).getLsbD k.val = true → (seed j).getLsbD t.val = true := by decide +kernel

private theorem dataOff : ∀ t : Fin 58, allPoints.getLsbD t.val = false →
    ∀ j ∈ points, (seed j).getLsbD t.val = false := by decide +kernel

open PEqualNP.Research4387.RootSupport

private theorem inputOn {S z} (der : From seed S z) {k : ℕ} (on : z.getLsbD k = true) :
    ∃ j ∈ S, (seed j).getLsbD k = true := by
  induction der with
  | root mem => exact ⟨_,mem,on⟩
  | conj _ _ left _ =>
    rw [BitVec.getLsbD_and,Bool.and_eq_true] at on
    exact left on.1
  | disj _ _ left right =>
    rw [BitVec.getLsbD_or,Bool.or_eq_true] at on
    exact on.elim left right

private theorem propagates {S z} (der : From seed S z) {k t : ℕ}
    (ge : ∀ j ∈ S, (seed j).getLsbD k = true → (seed j).getLsbD t = true) :
    z.getLsbD k = true → z.getLsbD t = true := by
  induction der with
  | root mem => exact ge _ mem
  | conj _ _ left right => simp only [BitVec.getLsbD_and,Bool.and_eq_true]; exact fun h => ⟨left h.1,right h.2⟩
  | disj _ _ left right => simp only [BitVec.getLsbD_or,Bool.or_eq_true]; exact fun h => h.imp left right

private theorem allPos : ∀ k : Fin 21, target.getLsbD k.val = true := by decide

/-- With at most six original source wires, the only possible left operand
of a final AND is the OR of every point. -/
theorem smallSeedOperand {S a b} (der : From seed S a) (few : S.card ≤ 6)
    (last : a &&& b = target) : a = allPoints := by
  have accept (k : Fin 21) : a.getLsbD k.val = true := by
    have h := congrArg (fun z : Row => z.getLsbD k.val) last
    simp only [BitVec.getLsbD_and,Bool.and_eq_true,allPos] at h
    exact h.1
  have eq := sixSeeds S few (fun k => inputOn der (accept k))
  subst S
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  by_cases yes : allPoints.getLsbD t = true
  · obtain ⟨k,le⟩ := dataOn ⟨t,ht⟩ yes
    exact (propagates der le (accept k)).trans yes.symm
  · have no : allPoints.getLsbD t = false := by simpa using yes
    have none := dataOff ⟨t,ht⟩ no
    cases h : a.getLsbD t with
    | false => exact no.symm
    | true =>
      obtain ⟨j,hj,hit⟩ := inputOn der h
      simp [none j hj] at hit

/-- A normalized prefix of at most five binary gates admits exactly one
possible left operand and, for a fresh target, one possible right operand. -/
theorem fiveGates {xs : List Row} {a b : Row} (valid : Valid seed xs)
    (present : a ∈ List.ofFn seed ++ xs) (few : xs.length ≤ 5)
    (last : a &&& b = target) (fresh : b ≠ target) :
    a = allPoints ∧ b = otherSide := by
  obtain ⟨S,count,der⟩ := smallRoots seed xs valid {a} (by simpa using present)
  have gate : From seed S a := der a (by simp)
  simp only [Finset.card_singleton] at count
  have eq := smallSeedOperand gate (by omega) last
  refine ⟨eq,?_⟩
  subst a
  have data₁ : ∀ k : Fin 58, k.val ≠ 57 → allPoints.getLsbD k.val = true := by decide
  have data₂ : ∀ k : Fin 58, k.val ≠ 57 → target.getLsbD k.val = otherSide.getLsbD k.val := by decide
  have low (k : ℕ) (hk : k < 58) (ne : k ≠ 57) : b.getLsbD k = target.getLsbD k := by
    have bit := congrArg (fun z : Row => z.getLsbD k) last
    have one := data₁ ⟨k,hk⟩ ne
    simpa [BitVec.getLsbD_and,one] using bit
  have top : b.getLsbD 57 = true := by
    by_contra nf
    apply fresh
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    by_cases endBit : k = 57
    · subst k
      have val : target.getLsbD 57 = false := by decide
      rw [val]
      simpa only [Bool.not_eq_true] using nf
    · exact low k hk endBit
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases endBit : k = 57
  · subst k
    exact top.trans (by decide)
  · exact (low k hk endBit).trans (data₂ ⟨k,hk⟩ endBit)

end PEqualNP.Research4387.LastAnd

#print axioms PEqualNP.Research4387.LastAnd.fiveGates
