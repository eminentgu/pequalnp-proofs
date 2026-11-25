import PEqualNP.Outside.L_meta_2121

namespace Research.K22

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)

def realizes (C : Circuit) : Prop :=
  Monotone2 C ∧ NestedCover.ReadsBack 4 C ∧ ∀ x, C.eval (List.ofFn x) = target x

def three : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [4,5]⟩], 6⟩

theorem optimal : IsLeast {s : ℕ | ∃ C : Circuit, realizes C ∧ C.size = s} 3 := by
  constructor
  · refine ⟨three, ⟨?_, ?_, ?_⟩, rfl⟩
    · intro g hg
      simp [three] at hg
      rcases hg with rfl | rfl | rfl <;> simp
    · decide +kernel
    · intro x
      change ((x 0 || (x 1 || false)) && ((x 2 || (x 3 || false)) && true)) = target x
      unfold target
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> rfl
  · rintro s ⟨C, ⟨hm,hr,hf⟩, rfl⟩
    exact PEqualNP.Outside.L_meta_2121 C hm hr hf

theorem noTwo : ¬ ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack 4 C ∧
    C.size ≤ 2 ∧ ∀ x, C.eval (List.ofFn x) = target x := by
  rintro ⟨C,hm,hr,hs,hf⟩
  have lo := optimal.2 (show C.size ∈ {s : ℕ | ∃ D : Circuit, realizes D ∧ D.size = s}
    from ⟨C,⟨hm,hr,hf⟩,rfl⟩)
  omega

end Research.K22
