import ConnectedSubdivision

namespace VertexPeel.ComponentStability

open PEqualNP.MetaComplexity.CoverPromise VertexPeel.SidePeel

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private theorem weak_expand (A : Finset (Fin n))
    (cross : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (lower : ∀ u∈A, 2≤G.degree u) (upper : ∀ v∉A, G.degree v≤2)
    (X : Finset (Fin n)) (sub : X ⊆ A) :
    X.card ≤ (X.biUnion fun u => G.neighborFinset u).card := by
  classical
  let Y := X.biUnion fun u => G.neighborFinset u
  have lo (u) (hu : u∈X) : 2 ≤ (Y.bipartiteAbove G.Adj u).card := by
    have inc : G.neighborFinset u ⊆ Y.bipartiteAbove G.Adj u := by
      intro v hv
      exact (Finset.mem_bipartiteAbove G.Adj).mpr ⟨Finset.mem_biUnion.mpr ⟨u,hu,hv⟩,
        (G.mem_neighborFinset u v).mp hv⟩
    exact (lower u (sub hu)).trans (by simpa using Finset.card_le_card inc)
  have hi (v) (hv : v∈Y) : (X.bipartiteBelow G.Adj v).card ≤ 2 := by
    obtain ⟨u,hu,e⟩ := Finset.mem_biUnion.mp hv
    have inc : X.bipartiteBelow G.Adj v ⊆ G.neighborFinset v := fun u h =>
      (G.mem_neighborFinset _ _).mpr ((Finset.mem_bipartiteBelow G.Adj).mp h).2.symm
    exact (Finset.card_le_card inc).trans (by
      simpa using upper v ((cross _ _ ((G.mem_neighborFinset _ _).mp e)).mp (sub hu)))
  have count := Finset.card_nsmul_le_card_nsmul G.Adj lo hi
  simpa [Nat.nsmul_eq_mul] using count

/-- All covers of the one-vertex deletion still have at least the size of the
active high side, even in the presence of unrelated balanced components. -/
theorem local_stable (A : Finset (Fin n))
    (cross : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (lower : ∀ u∈A, 2≤G.degree u) (upper : ∀ v∉A, G.degree v≤2) {z w : Fin n}
    (outside : z∉A) (inside : w∈A) (high : 2<G.degree w) (reach : G.Reachable z w) :
    ¬Drops G z := by
  classical
  rintro ⟨S,cover,smaller⟩
  have ca : IsVertexCover G A := by
    intro u v uv
    by_cases h : u ∈ A
    · exact Or.inl h
    · exact Or.inr (not_not.mp (fun nv => h ((cross u v uv).mpr nv)))
  let X := A \ S
  let Y := X.biUnion fun u => G.neighborFinset u
  have fewer : (S \ A).card < X.card := Finset.card_sdiff_lt_card_sdiff_iff.mpr (smaller A ca)
  have subX : X⊆A := Finset.sdiff_subset
  have inc : Y ⊆ insert z (S \ A) := by
    intro v hv
    obtain ⟨u,hu,uv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨ua,us⟩ := Finset.mem_sdiff.mp hu
    have e := (G.mem_neighborFinset _ _).mp uv
    by_cases vz : v=z
    · simp [vz]
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
        ⟨(cover _ _ (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨e,fun eq => outside (eq ▸ ua),vz⟩)).resolve_left us,
         (cross _ _ e).mp ua⟩)
  by_cases seen : z ∈ Y
  · obtain ⟨x,hx,xz⟩ := Finset.mem_biUnion.mp seen
    have growth := ConnectedSubdivision.expandFrom G A cross 2 lower upper X subX
      ⟨x,hx,w,inside,high,((G.mem_neighborFinset _ _).mp xz).reachable.trans reach⟩
    change X.card<Y.card at growth
    have bound := (Finset.card_le_card inc).trans (Finset.card_insert_le _ _)
    omega
  · have safe : Y ⊆ S \ A := by
      intro v hv
      exact (Finset.mem_insert.mp (inc hv)).resolve_left (fun eq => seen (eq ▸ hv))
    have growth := weak_expand G A cross lower upper X subX
    change X.card≤Y.card at growth
    exact (not_le_of_gt fewer) (growth.trans (Finset.card_le_card safe))

/-- The low side of any chosen branching component supplies one circuit-independent
set of candidates. All neighbors of a high-side witness belong to that same set. -/
theorem branch_candidates (c : Fin n → Bool) (proper : ∀ u v, G.Adj u v → c u≠c v)
    (low : ∀ v, c v=false → G.degree v≤2) (noLeaf : ¬∃ v, G.degree v=1)
    (branch : ∃ w, 2<G.degree w) :
    ∃ B : Finset (Fin n), B.Nonempty ∧ (∀ z∈B, G.degree z=2 ∧ ¬Drops G z) ∧
      ∀ z∈B, ∃ t∉B, G.Adj t z ∧ ∀ y, G.Adj t y → y∈B := by
  classical
  obtain ⟨w,high⟩ := branch
  let B := Finset.univ.filter fun x => c x=false ∧ G.Reachable x w
  let A := Finset.univ.filter fun x => c x=true ∧ 0<G.degree x
  have wh : c w=true := by
    cases hc : c w with
    | false => have := low w hc; omega
    | true => rfl
  have wa : w∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,wh,by omega⟩
  have edgeColor (u v : Fin n) (uv : G.Adj u v) : u∈A ↔ c u=true := by
    simp [A,(G.degree_pos_iff_exists_adj u).mpr ⟨v,uv⟩]
  have cross (u v) (uv : G.Adj u v) : u∈A ↔ v∉A := by
    rw [edgeColor _ _ uv,edgeColor _ _ uv.symm]
    have diff := proper _ _ uv
    cases a : c u <;> cases b : c v <;> simp_all
  have lower (u) (hu : u∈A) : 2≤G.degree u := by
    have pos := (Finset.mem_filter.mp hu).2.2
    have ne : G.degree u≠1 := fun eq => noLeaf ⟨u,eq⟩
    omega
  have upper (v) (hv : v∉A) : G.degree v≤2 := by
    cases hc : c v with
    | false => exact low v hc
    | true =>
      by_contra! highV
      apply hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,by omega⟩)
  have memB (x) : x ∈ B ↔ c x=false ∧ G.Reachable x w := by simp [B]
  obtain ⟨b,wb⟩ := (G.degree_pos_iff_exists_adj w).mp (by omega)
  refine ⟨B,⟨b,(memB b).mpr ⟨by have := proper _ _ wb; cases h : c b <;> simp_all,wb.symm.reachable⟩⟩,?_,?_⟩
  · intro z hz
    obtain ⟨side,reach⟩ := (memB z).mp hz
    have neq : z≠w := by rintro rfl; simp_all
    have pos := reach.degree_pos_left neq
    have upperZ := low z side
    have ne : G.degree z≠1 := fun eq => noLeaf ⟨z,eq⟩
    refine ⟨by omega,local_stable G A cross lower upper (by simp [A,side]) wa high reach⟩
  · intro z hz
    obtain ⟨side,reach⟩ := (memB z).mp hz
    have neq : z≠w := by rintro rfl; simp_all
    obtain ⟨t,zt⟩ := (G.degree_pos_iff_exists_adj z).mp (reach.degree_pos_left neq)
    have other : c t=true := by have := proper _ _ zt; cases h : c t <;> simp_all
    refine ⟨t,fun bt => Bool.noConfusion (((memB t).mp bt).1.symm.trans other),zt.symm,?_⟩
    intro y ty
    exact (memB y).mpr ⟨by have := proper _ _ ty; cases h : c y <;> simp_all,
      ty.symm.reachable.trans (zt.symm.reachable.trans reach)⟩

#print axioms branch_candidates
end VertexPeel.ComponentStability
