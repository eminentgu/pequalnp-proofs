import PivotAND

namespace VertexPeel.PivotAND

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo VertexPeel.AndSeparation VertexPeel.CoverPatterns

variable {n : ℕ}

/-- ANDs with both operands false on x can still distinguish two extensions
by switching the orientation of their one true operand. -/
noncomputable def quiet (C : Circuit) (w : ℕ) (x : Fin n → Bool) := by
  classical
  exact (andCone (n:=n) C w).filter (fun j => wval C x (in0 C j) = false ∧ wval C x (in1 C j) = false)

theorem extension_patterns {ι : Type*} (C : Circuit) (hc : IsAO2 n C)
    (w : ℕ) (base : Fin n → Bool) (U : Finset ι) (test : ι → Fin n → Bool)
    (extend : ∀ r ∈ U, ∀ v, base v=true → test r v=true)
    (off : ∀ r ∈ U, wval C (test r) w=false)
    (apart : ∀ r ∈ U, ∀ s ∈ U, r≠s → ∃ z, wval C z w=true ∧
      ∀ v, z v=true → test r v=true ∨ test s v=true) :
    U.card ≤ 2 ^ (quiet C w base).card := by
  classical
  let tag (r : ι) := (quiet C w base).filter (fun j => wval C (test r) (in0 C j)=true)
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn tag
  · intro r _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · intro r hr s hs eq
    by_contra ne
    obtain ⟨z,on,sep⟩ := apart r hr s hs ne
    obtain ⟨j,path,hand,diff,opp1,opp2⟩ := opposing_ancestor C hc (test r) (test s) z sep w (off r hr) (off s hs) on
    have mem : j ∈ andCone (n:=n) C w := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hand.1,path⟩,hand⟩
    have idle (u : ℕ) (h : wval C (test r) u ≠ wval C (test s) u) : wval C base u = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      exact h ((RowGraph.wire_mono C hc (extend r hr) u yes).trans
        (RowGraph.wire_mono C hc (extend s hs) u yes).symm)
    have diff2 : wval C (test r) (in1 C j) ≠ wval C (test s) (in1 C j) := by
      intro same
      exact diff (opp1.trans (same.symm.trans opp2))
    have inQ : j ∈ quiet C w base := Finset.mem_filter.mpr ⟨mem,idle _ diff,idle _ diff2⟩
    have same := Finset.ext_iff.mp eq j
    have equivalence : wval C (test r) (in0 C j)=true ↔ wval C (test s) (in0 C j)=true := by
      simpa [tag,inQ] using same
    exact diff (Bool.eq_iff_iff.mpr equivalence)

def present (X : Finset (Fin n)) (v : Fin n) : Bool := decide (v∈X)

/-- Every distinct maximal independent extension of S consumes a different
bit pattern on the ANDs still quiet on S. -/
theorem maximal_extensions (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hc : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅) (S : Finset (Fin n)) :
    ((maxSets G).filter (fun X => S ⊆ X)).card ≤ 2 ^ (quiet C C.output (present S)).card := by
  classical
  let U := (maxSets G).filter fun X => S ⊆ X
  have desc {X : Finset (Fin n)} (h : X ∈ U) : maximal G X := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
  have valEq (x : Fin n → Bool) : wval C x C.output = graphFun G ∅ x := congrFun computes x
  apply extension_patterns C hc C.output (present S) U present
  · intro X h v hv
    simpa [present] using (show v∈X from (Finset.mem_filter.mp h).2 (of_decide_eq_true hv))
  · intro X h
    rw [valEq]
    have no : ¬∃ a b, G.Adj a b ∧ a∈X ∧ b∈X := by
      rintro ⟨a,b,adj,ha,hb⟩
      exact (desc h).1 a ha b hb adj
    simp [graphFun,present,no]
  · intro X hx Y hy ne
    have falseUnion : ¬independent G (X∪Y) := by
      intro ind
      have e₁ := (desc hx).2 _ Finset.subset_union_left ind
      have e₂ := (desc hy).2 _ Finset.subset_union_right ind
      exact ne (e₁.symm.trans e₂)
    unfold independent at falseUnion
    push Not at falseUnion
    obtain ⟨a,ha,b,hb,adj⟩ := falseUnion
    refine ⟨present {a,b},?_,?_⟩
    · rw [valEq]
      have yes : ∃ u v, G.Adj u v ∧ u∈({a,b}:Finset _) ∧ v∈({a,b}:Finset _) := ⟨a,b,adj,by simp,by simp⟩
      simpa [graphFun,present] using yes
    · intro v hv
      have hit : v∈X∪Y := by
        rcases (show v=a ∨ v=b by simpa [present] using hv) with rfl|rfl <;> assumption
      simpa [present] using Finset.mem_union.mp hit

open Classical in
/-- If there are M maximal independent sets containing a vertex x, every
circuit retains at least log₂(M) AND positions unlit by that singleton. -/
theorem singleton_extensions (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hc : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅) (x : Fin n) :
    ((maxSets G).filter (fun X => x∈X)).card ≤
      2 ^ ((physical C).card - ((physical C).filter (lit C x)).card) := by
  classical
  let L := (physical C).filter (lit C x)
  have ptx : present {x} = unit x := by funext v; simp [present,unit]
  have sub : quiet C C.output (present {x}) ⊆ physical C \ L := by
    intro j hj
    obtain ⟨cone,q⟩ := Finset.mem_filter.mp hj
    have hand := (Finset.mem_filter.mp cone).2
    have ph : j∈physical C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hand.1,hand⟩
    refine Finset.mem_sdiff.mpr ⟨ph,?_⟩
    intro h
    have live := (Finset.mem_filter.mp h).2.2
    rw [ptx] at q
    rcases live with left|right
    · exact Bool.false_ne_true (q.1.symm.trans left)
    · exact Bool.false_ne_true (q.2.symm.trans right)
  have count := Finset.card_le_card sub
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at count
  have bound := (maximal_extensions G C hc computes {x}).trans
    (Nat.pow_le_pow_right (by decide : 0<2) count)
  simpa [L] using bound

#print axioms singleton_extensions
#print axioms extension_patterns
#print axioms maximal_extensions
end VertexPeel.PivotAND
