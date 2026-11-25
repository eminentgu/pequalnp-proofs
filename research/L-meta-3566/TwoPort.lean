import Mathlib
import PEqualNP.Defs

namespace VertexPeel.TwoPort

open PEqualNP.TopForm

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- Every transversal of two alternative sets contains a genuine edge exactly
when the graph contains all their cross edges, including the potential diagonal. -/
theorem choice_iff_cross (A B : Finset (Fin n)) :
    (∀ a ∈ A, ∀ b ∈ B, ∃ u ∈ ({a,b} : Finset (Fin n)), ∃ v ∈ ({a,b} : Finset (Fin n)), G.Adj u v) ↔
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
  constructor
  · intro h a ha b hb
    obtain ⟨u,hu,v,hv,e⟩ := h a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · exact False.elim (e.ne rfl)
    · exact e
    · exact e.symm
    · exact False.elim (e.ne rfl)
  · intro h a ha b hb
    exact ⟨a,by simp,b,by simp,h a ha b hb⟩

/-- A nonempty complete rectangle in a square-free graph has a singleton side. -/
theorem singleton_side (sq : NoFourCycle G) (A B : Finset (Fin n))
    (left : A.Nonempty) (right : B.Nonempty)
    (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    (∃ a, A={a}) ∨ ∃ b, B={b} := by
  classical
  by_cases one : A.card≤1
  · left
    apply Finset.card_eq_one.mp
    have := Finset.card_pos.mpr left
    omega
  right
  obtain ⟨a,ha,a',ha',diff⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge one)
  have subset : B ⊆ Finset.univ.filter (fun b => G.Adj a b ∧ G.Adj a' b) :=
    fun b hb => Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross a ha b hb,cross a' ha' b hb⟩
  have bound := (Finset.card_le_card subset).trans (sq a a' diff)
  exact Finset.card_eq_one.mp (Nat.le_antisymm bound (Finset.card_pos.mpr right))

/-- If both full ports contain x and each alternative selection must contain an
edge, either a port uniquely recognizes x, or one port has exactly two singletons
and every alternative of the other port neighbors the second singleton. -/
theorem two_ports (sq : NoFourCycle G) (x : Fin n) (P Q : Finset (Fin n)) (hxP : x ∈ P) (hxQ : x ∈ Q)
    (choice : ∀ a ∈ P.erase x, ∀ b ∈ Q.erase x,
      ∃ u ∈ ({a,b} : Finset (Fin n)), ∃ v ∈ ({a,b} : Finset (Fin n)), G.Adj u v) :
    P={x} ∨ Q={x} ∨ (∃ y ≠ x, P={x,y} ∧ ∀ b ∈ Q.erase x, G.Adj y b) ∨
      ∃ y ≠ x, Q={x,y} ∧ ∀ a ∈ P.erase x, G.Adj y a := by
  classical
  have extend (R : Finset (Fin n)) (inside : x ∈ R) : insert x (R.erase x)=R :=
    Finset.insert_erase inside
  by_cases p : (P.erase x).Nonempty
  · by_cases q : (Q.erase x).Nonempty
    · have cross := (choice_iff_cross G _ _).mp choice
      rcases singleton_side G sq _ _ p q cross with ⟨y,hy⟩|⟨y,hy⟩
      · have mem : y ∈ P.erase x := by simp [hy]
        exact Or.inr (Or.inr (Or.inl ⟨y,(Finset.mem_erase.mp mem).1,by rw [← extend P hxP,hy],
          cross y mem⟩))
      · have mem : y ∈ Q.erase x := by simp [hy]
        exact Or.inr (Or.inr (Or.inr ⟨y,(Finset.mem_erase.mp mem).1,by rw [← extend Q hxQ,hy],
          fun a ha => (cross a ha y mem).symm⟩))
    · exact Or.inr (Or.inl (by rw [← extend Q hxQ,Finset.not_nonempty_iff_eq_empty.mp q]; rfl))
  · exact Or.inl (by rw [← extend P hxP,Finset.not_nonempty_iff_eq_empty.mp p]; rfl)

#print axioms two_ports
end VertexPeel.TwoPort
