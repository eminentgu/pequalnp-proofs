import SparseRows

namespace PEqualNP.Research2990
variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def pointsOf (l : Fin N) : Finset (Fin N) := Finset.univ.filter fun p => I p l

theorem intersection_card {a b : Fin N} (different : a ≠ b)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    ((pointsOf I a) ∩ (pointsOf I b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  by_contra pn
  obtain ⟨_,_,sole⟩ := unique p p' pn
  obtain ⟨pa,pb⟩ := Finset.mem_inter.mp hp
  obtain ⟨pa',pb'⟩ := Finset.mem_inter.mp hp'
  exact different ((sole a ⟨(Finset.mem_filter.mp pa).2,(Finset.mem_filter.mp pa').2⟩).trans
    (sole b ⟨(Finset.mem_filter.mp pb).2,(Finset.mem_filter.mp pb').2⟩).symm)

/-- Each selected line can cover at most one of the points on an omitted line. -/
theorem omitted_line_points (q : ℕ) (degree : ∀ l, (pointsOf I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (Y : Finset (Fin N)) (l : Fin N) (hl : l ∉ Y) :
    q+1 ≤ Y.card + ((pointsOf I l) ∩ outsidePoints I Y).card := by
  classical
  let covered := Y.biUnion fun k => pointsOf I l ∩ pointsOf I k
  have upper : covered.card ≤ Y.card := calc
    _ ≤ ∑ k ∈ Y, ((pointsOf I l) ∩ (pointsOf I k)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ Y, 1 := Finset.sum_le_sum (fun k hk => intersection_card I (fun e => hl (e ▸ hk)) unique)
    _ = Y.card := by simp
  have sub : pointsOf I l ⊆ covered ∪ (pointsOf I l ∩ outsidePoints I Y) := by
    intro p hp
    by_cases uncovered : ∀ k ∈ Y, ¬I p k
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp,Finset.mem_filter.mpr ⟨by simp,uncovered⟩⟩)
    · push Not at uncovered
      obtain ⟨k,hk,hi⟩ := uncovered
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k,hk,
        Finset.mem_inter.mpr ⟨hp,Finset.mem_filter.mpr ⟨by simp,hi⟩⟩⟩)
  have total := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [degree] at total
  omega

/-- Adding any omitted line to a canonical negative row with at most q active lines
    introduces an incidence, even if that line takes the assignment beyond the promise. -/
theorem outside_line_activates (q : ℕ) (degree : ∀ l, (pointsOf I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (Y : Finset (Fin N)) (small : Y.card ≤ q) (l : Fin N) (hl : l ∉ Y) :
    ∃ p ∈ outsidePoints I Y, I p l := by
  have bound := omitted_line_points I q degree unique Y l hl
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (pointsOf I l ∩ outsidePoints I Y).card by omega)
  obtain ⟨inLine,off⟩ := Finset.mem_inter.mp hp
  exact ⟨p,off,(Finset.mem_filter.mp inLine).2⟩

#print axioms omitted_line_points
#print axioms outside_line_activates
end PEqualNP.Research2990
