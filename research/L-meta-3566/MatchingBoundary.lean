import Mathlib

namespace VertexPeel.MatchingBoundary

abbrev Cell (m : ℕ) := Fin m × Fin m
abbrev Mask (m : ℕ) := Finset (Cell m)

/-- A disjoint union of m² edges, with one vertex at either end of each cell. -/
def graph (m : ℕ) : SimpleGraph (Cell m × Bool) where
  Adj u v := u.1 = v.1 ∧ u.2 ≠ v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm,Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

theorem unique_neighbor {m : ℕ} {u v w : Cell m × Bool}
    (uv : (graph m).Adj u v) (uw : (graph m).Adj u w) : v = w := by
  rcases u with ⟨u,s⟩
  rcases v with ⟨v,t⟩
  rcases w with ⟨w,r⟩
  obtain ⟨rfl,st⟩ := uv
  obtain ⟨rfl,sr⟩ := uw
  cases s <;> cases t <;> cases r <;> simp_all

variable {m : ℕ}

/-- A selected vertex at both ends of one matching edge. -/
abbrev Edge (A B : Mask m) := ∃ c ∈ A, c ∈ B
abbrev Left (A B : Mask m) := Edge A B ∨ ∃ i, ∀ j, (i,j) ∈ A
abbrev Right (A B : Mask m) := Edge A B ∨ ∃ j, ∀ i, (i,j) ∈ B

abbrev Selected (A B : Mask m) (u : Cell m × Bool) : Prop :=
  if u.2 then u.1 ∈ B else u.1 ∈ A

theorem matching_edge_iff (A B : Mask m) :
    (∃ u v, (graph m).Adj u v ∧ Selected A B u ∧ Selected A B v) ↔ Edge A B := by
  constructor
  · rintro ⟨⟨u,s⟩,⟨v,t⟩,⟨e,ne⟩,hu,hv⟩
    change u=v at e; subst v
    change s≠t at ne
    cases s <;> cases t
    · exact (ne rfl).elim
    · exact ⟨u,hu,hv⟩
    · exact ⟨u,hv,hu⟩
    · exact (ne rfl).elim
  · rintro ⟨c,ha,hb⟩
    exact ⟨(c,false),(c,true),⟨rfl,Bool.false_ne_true⟩,ha,hb⟩

theorem intersection (A B : Mask m) : (Left A B ∧ Right A B) ↔ Edge A B := by
  constructor
  · rintro ⟨edge|⟨i,allI⟩,hR⟩
    · exact edge
    · rcases hR with edge|⟨j,allJ⟩
      · exact edge
      · exact ⟨(i,j),allI j,allJ i⟩
  · exact fun h => ⟨.inl h,.inl h⟩

private lemma missed (T : Mask m) (small : T.card < m) (coordinate : Cell m → Fin m) :
    ∃ u : Fin m, u ∉ T.image coordinate := by
  by_contra! cover
  have h : (Finset.univ : Finset (Fin m)) ⊆ T.image coordinate := fun u _ => cover u
  have c := (Finset.card_le_card h).trans Finset.card_image_le
  simp at c
  omega

/-- After fewer than m deletions from either shore, both children still have
independent false positives avoiding every deleted vertex. -/
theorem both_errors_survive (TL TR : Mask m) (leftSmall : TL.card < m) (rightSmall : TR.card < m) :
    (∃ A B : Mask m, Disjoint A TL ∧ Disjoint B TR ∧ Left A B ∧ ¬ Edge A B) ∧
    (∃ A B : Mask m, Disjoint A TL ∧ Disjoint B TR ∧ Right A B ∧ ¬ Edge A B) := by
  obtain ⟨i,absentI⟩ := missed TL leftSmall Prod.fst
  obtain ⟨j,absentJ⟩ := missed TR rightSmall Prod.snd
  let row := Finset.univ.filter (fun c : Cell m => c.1 = i)
  let col := Finset.univ.filter (fun c : Cell m => c.2 = j)
  constructor
  · refine ⟨row,∅,?_,by simp,.inr ⟨i,fun k => by simp [row]⟩,by simp [Edge]⟩
    apply Finset.disjoint_left.mpr
    intro c hr ht
    exact absentI (Finset.mem_image.mpr ⟨c,ht,(Finset.mem_filter.mp hr).2⟩)
  · refine ⟨∅,col,by simp,?_,.inr ⟨j,fun k => by simp [col]⟩,by simp [Edge]⟩
    apply Finset.disjoint_left.mpr
    intro c hc ht
    exact absentJ (Finset.mem_image.mpr ⟨c,ht,(Finset.mem_filter.mp hc).2⟩)

/-- Deleting the m left diagonal endpoints eliminates all extra left rows,
so the lower bound from disjoint rows is attained. -/
theorem diagonal_suffices (m : ℕ) :
    ∃ T : Mask m, T.card = m ∧
      ∀ A B : Mask m, Disjoint A T → (Left A B ↔ Edge A B) := by
  let diag := fun i : Fin m => (i,i)
  let T := Finset.univ.image diag
  refine ⟨T,?_,?_⟩
  · have injective : Function.Injective diag := fun _ _ e => congrArg Prod.fst e
    simp [T,Finset.card_image_of_injective _ injective]
  · intro A B dis
    refine ⟨?_,Or.inl⟩
    rintro (edge|⟨i,whole⟩)
    · exact edge
    · exact (Finset.disjoint_left.mp dis (whole i)
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).elim

#print axioms matching_edge_iff
#print axioms diagonal_suffices
#print axioms intersection
#print axioms both_errors_survive
end VertexPeel.MatchingBoundary
