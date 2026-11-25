import AndSeparation

namespace VertexPeel.FreeChoices

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.ReadTwo VertexPeel.ReusedCone VertexPeel.AndSeparation

variable {n : ℕ} (C : Circuit) (w : ℕ)

noncomputable def free (x : Fin n → Bool) := (andCone (n := n) C w).filter fun j =>
  wval C x (in0 C j) = wval C x (in1 C j)

noncomputable def positive (x : Fin n → Bool) := (andCone (n := n) C w).filter fun j =>
  wval C x (in0 C j) = true ∧ wval C x (in1 C j) = false

/-- Equal children leave the orientation free. Opposite children fix the selected bit. -/
noncomputable def patterns (x : Fin n → Bool) :=
  (free C w x).powerset.image fun s => positive C w x ∪ s

private theorem disjoint_free (x : Fin n → Bool) : Disjoint (positive C w x) (free C w x) := by
  apply Finset.disjoint_left.mpr
  intro j hp hf
  obtain ⟨_,t,f⟩ := Finset.mem_filter.mp hp
  have same := (Finset.mem_filter.mp hf).2
  simp_all

private theorem pattern_card (x : Fin n → Bool) : (patterns C w x).card = 2 ^ (free C w x).card := by
  classical
  unfold patterns
  rw [Finset.card_image_of_injOn,Finset.card_powerset]
  intro s hs t ht eq
  have subS := Finset.mem_powerset.mp hs
  have subT := Finset.mem_powerset.mp ht
  change positive C w x ∪ s = positive C w x ∪ t at eq
  have rm (a : Finset ℕ) (ha : a ⊆ free C w x) : (positive C w x ∪ a) \ positive C w x = a := by
    ext j
    by_cases pos : j ∈ positive C w x
    · have no : j ∉ a := fun hin => Finset.disjoint_left.mp (disjoint_free C w x) pos (ha hin)
      simp [pos,no]
    · simp [pos]
  rw [← rm s subS,eq,rm t subT]

private theorem force (x : Fin n → Bool) {s : Finset ℕ} (mem : s ∈ patterns C w x) {j : ℕ}
    (hj : j ∈ andCone (n := n) C w) (diff : wval C x (in0 C j) ≠ wval C x (in1 C j)) :
    j ∈ s ↔ wval C x (in0 C j) = true := by
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp mem
  have nope : j ∉ t := fun h => diff (Finset.mem_filter.mp (Finset.mem_powerset.mp ht h)).2
  cases e : wval C x (in0 C j) <;> cases f : wval C x (in1 C j) <;> simp_all [positive]

/-- Every pairwise union-separable negative test occupies an entire disjoint set of AND
orientation patterns. Each equal-input AND doubles the number occupied by that test. -/
theorem packing {ι : Type*} (hc : IsAO2 n C) (U : Finset ι) (test : ι → Fin n → Bool)
    (off : ∀ i ∈ U, wval C (test i) w = false)
    (sep : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → ∃ z, wval C z w = true ∧
      ∀ v, z v = true → test i v = true ∨ test j v = true) :
    ∑ i ∈ U, 2 ^ (free C w (test i)).card ≤ 2 ^ (andCone (n := n) C w).card := by
  classical
  let A := andCone (n := n) C w
  have dis : (U : Set ι).PairwiseDisjoint (fun i => patterns C w (test i)) := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro s si sj
    obtain ⟨z,on,cover⟩ := sep i hi j hj ne
    obtain ⟨g,path,hand,diff,swapA,swapB⟩ := opposing_ancestor C hc (test i) (test j) z cover w (off i hi) (off j hj) on
    have mem : g ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hand.1,path⟩,hand⟩
    have d1 : wval C (test i) (in0 C g) ≠ wval C (test i) (in1 C g) := fun eq => diff (eq.trans swapB)
    have d2 : wval C (test j) (in0 C g) ≠ wval C (test j) (in1 C g) := fun eq => diff (swapA.trans eq.symm)
    have same := (force C w _ si mem d1).symm.trans (force C w _ sj mem d2)
    exact diff (Bool.eq_iff_iff.mpr same)
  have sub : (U.biUnion fun i => patterns C w (test i)) ⊆ A.powerset := by
    intro s hs
    obtain ⟨i,hi,mem⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp mem
    exact Finset.mem_powerset.mpr (Finset.union_subset (Finset.filter_subset _ _)
      ((Finset.mem_powerset.mp ht).trans (Finset.filter_subset _ _)))
  have tot := Finset.card_le_card sub
  rw [Finset.card_biUnion dis,Finset.card_powerset] at tot
  simpa only [pattern_card] using tot

open VertexPeel.RowGraph

/-- Joint AND-orientation budget of all rows splitting a single OR in a C4-free graph. -/
theorem row_packing (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n))
    (hc : IsAO2 n C) (four : NoFourCycle G) (U : Finset (Fin n))
    (right : ∀ u ∈ U, G.neighborFinset u ⊆ R) (j : ℕ) (split : ∀ u ∈ U, j ∈ rowGates G R C u) :
    ∑ u ∈ U, 2 ^ (free C (n+j) (rowBase G R u)).card ≤ 2 ^ (andCone (n := n) C (n+j)).card := by
  classical
  apply packing C (n+j) hc U (rowBase G R) (fun u hu => (Finset.mem_filter.mp (split u hu)).2.2.1)
  exact fun u hu v _ ne => row_probe C G R hc four ne (right u hu) j (split u hu)

end VertexPeel.FreeChoices
