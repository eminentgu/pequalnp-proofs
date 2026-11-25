import PEqualNP.Defs.ReadK
import Mathlib

namespace PEqualNP.Research2990.SparsePrimes

open CircuitLowerBounds MetaComplexity ReadK

variable {P L : ℕ}

def pair (p : Fin P) (l : Fin L) : Finset (Fin (P+L)) := {Fin.castAdd L p, Fin.natAdd P l}

def active (S : Finset (Fin (P+L))) : Finset (Fin L) :=
  Finset.univ.filter fun l => Fin.natAdd P l ∈ S

def hasEdge (I : Fin P → Fin L → Prop) (S : Finset (Fin (P+L))) :=
  ∃ p l, I p l ∧ pair p l ⊆ S

def minimal (f : Finset (Fin (P+L)) → Prop) (S : Finset (Fin (P+L))) : Prop :=
  f S ∧ ∀ T, T ⊂ S → ¬ f T

private theorem separate (p : Fin P) (l : Fin L) : Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro eq
  have := congrArg Fin.val eq
  change p.val = P+l.val at this
  omega

private theorem pairLines (p : Fin P) (l : Fin L) : active (pair p l) = {l} := by
  ext t
  simp only [active,pair,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  simp [Ne.symm (separate p t)]

private theorem pairSubset {p p' : Fin P} {l l' : Fin L} (h : pair p' l' ⊆ pair p l) :
    pair p l ⊆ pair p' l' := by
  have hp := h (show Fin.castAdd L p' ∈ pair p' l' by simp [pair])
  have hl := h (show Fin.natAdd P l' ∈ pair p' l' by simp [pair])
  simp only [pair,Finset.mem_insert,Finset.mem_singleton] at hp hl
  have pe : Fin.castAdd L p' = Fin.castAdd L p := hp.resolve_right (separate p' l)
  have le : Fin.natAdd P l' = Fin.natAdd P l := hl.resolve_left (Ne.symm (separate p l'))
  simp [pair,pe,le]

theorem primeAlternatives (I : Fin P → Fin L → Prop) {q : ℕ} (one : 1 ≤ q)
    (f : Finset (Fin (P+L)) → Prop)
    (accept : ∀ p l, I p l → f (pair p l))
    (sound : ∀ S, (active S).card ≤ q → ¬ hasEdge I S → ¬ f S)
    (S : Finset (Fin (P+L))) :
    minimal f S ↔
      (∃ p l, I p l ∧ S = pair p l) ∨
      (minimal f S ∧ ¬ hasEdge I S ∧ q < (active S).card) := by
  constructor
  · intro prime
    by_cases edge : hasEdge I S
    · left
      obtain ⟨p,l,hit,sub⟩ := edge
      refine ⟨p,l,hit,?_⟩
      by_contra ne
      exact prime.2 _ (lt_of_le_of_ne sub (Ne.symm ne)) (accept p l hit)
    · right
      exact ⟨prime,edge,lt_of_not_ge (fun few => sound S few edge prime.1)⟩
  · rintro (⟨p,l,hit,rfl⟩ | ⟨prime,_,_⟩)
    · refine ⟨accept p l hit,?_⟩
      intro T sub
      have inc : active T ⊆ active (pair p l) := fun t ht =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub.subset (Finset.mem_filter.mp ht).2⟩
      have few := Finset.card_le_card inc
      rw [pairLines,Finset.card_singleton] at few
      apply sound T (few.trans one)
      rintro ⟨p',l',_,left⟩
      exact sub.not_ge ((pairSubset (left.trans sub.subset)).trans left)
    · exact prime

/-- This statement uses precisely the two truth-table promises in L2990.
Neither the incidence geometry nor the internal circuit model is needed. -/
theorem circuitPrimes (I : Fin P → Fin L → Prop) {q : ℕ} (one : 1 ≤ q) (C : Circuit)
    (accept : ∀ p l, I p l → circuitFun (P+L) C
      (fun k => decide (k = Fin.castAdd L p ∨ k = Fin.natAdd P l)) = true)
    (sound : ∀ z : Fin (P+L) → Bool,
      Fintype.card {l : Fin L // z (Fin.natAdd P l) = true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) →
      circuitFun (P+L) C z = false)
    (S : Finset (Fin (P+L))) :
    IsPrimeImplicant (P+L) C S ↔ (∃ p l, I p l ∧ S = pair p l) ∨
      (IsPrimeImplicant (P+L) C S ∧ ¬ hasEdge I S ∧ q < (active S).card) := by
  classical
  let f := fun S : Finset (Fin (P+L)) => circuitFun (P+L) C (setInput S) = true
  have prime (T : Finset (Fin (P+L))) : IsPrimeImplicant (P+L) C T ↔ minimal f T := by
    simp only [IsPrimeImplicant,minimal,f,Finset.mem_ssubsets,Bool.not_eq_true]
  rw [prime]
  apply primeAlternatives I one f _ _ S
  · intro p l hi
    have inputs : setInput (pair p l) = (fun k => decide (k = Fin.castAdd L p ∨ k = Fin.natAdd P l)) := by
      funext k
      simp [setInput,pair]
    change circuitFun (P+L) C (setInput (pair p l)) = true
    rw [inputs]
    exact accept p l hi
  · intro T few noedge on
    have num : Fintype.card {l : Fin L // setInput T (Fin.natAdd P l) = true} = (active T).card := by
      rw [Fintype.card_subtype]
      simp [active,setInput]
    have off := sound (setInput T) (num.trans_le few) (by
      rintro ⟨p,l,hit,pp,ll⟩
      exact noedge ⟨p,l,hit,by
        simpa only [pair,Finset.insert_subset_iff,Finset.singleton_subset_iff] using
          And.intro (of_decide_eq_true pp) (of_decide_eq_true ll)⟩)
    exact Bool.noConfusion (on.symm.trans off)

def linesOnly (W : Finset (Fin L)) : Finset (Fin (P+L)) := W.image (Fin.natAdd P)

/-- Add one conjunction on q+1 prescribed lines to the true incidence function.
The enlarged function has exactly the same sparse negative promises and its
new prime attains the lower bound on the number of active lines. -/
theorem sharp (I : Fin P → Fin L → Prop) {q : ℕ} (W : Finset (Fin L)) (size : W.card = q+1) :
    let bad := linesOnly (P:=P) W
    let f := fun S => hasEdge I S ∨ bad ⊆ S
    (∀ p l, I p l → f (pair p l)) ∧
    (∀ S, (active S).card ≤ q → ¬ hasEdge I S → ¬ f S) ∧
    minimal f bad ∧ ¬ hasEdge I bad ∧ (active bad).card = q+1 := by
  dsimp only
  have activeExact : active (linesOnly (P:=P) W) = W := by ext l; simp [active,linesOnly]
  have noedge : ¬ hasEdge I (linesOnly W) := by
    rintro ⟨p,l,_,sub⟩
    obtain ⟨j,_,h⟩ := Finset.mem_image.mp (sub (show Fin.castAdd L p ∈ pair p l by simp [pair]))
    exact separate p j h.symm
  refine ⟨fun p l hit => Or.inl ⟨p,l,hit,Finset.Subset.rfl⟩,?_,?_,noedge,by rw [activeExact,size]⟩
  · intro S few no
    rintro (h | includes)
    · exact no h
    · have sub : W ⊆ active S := by
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,includes (Finset.mem_image.mpr ⟨l,hl,rfl⟩)⟩
      have := Finset.card_le_card sub
      omega
  · refine ⟨Or.inr Finset.Subset.rfl,?_⟩
    intro T strict
    rintro (⟨p,l,hit,sub⟩ | sub)
    · exact noedge ⟨p,l,hit,sub.trans strict.subset⟩
    · exact strict.not_ge sub

end PEqualNP.Research2990.SparsePrimes

#print axioms PEqualNP.Research2990.SparsePrimes.circuitPrimes
#print axioms PEqualNP.Research2990.SparsePrimes.sharp
