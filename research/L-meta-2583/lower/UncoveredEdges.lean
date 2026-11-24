import PlaneReadOne
import PEqualNP.Outside.L_meta_1491

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open scoped Sym2

namespace PlaneReadOne

/-- A cover after deleting U edges can miss at most |U| of the original edges.
Each member accounts for at most d edges. -/
theorem residualCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n)) (d : ℕ)
    (degreeBound : ∀ v, G.degree v ≤ d)
    (cover : (G.deleteEdges (U : Set _)).IsVertexCover (K : Set _)) :
    G.edgeFinset.card ≤ U.card + K.card*d := by
  classical
  have allEdges : G.edgeFinset ⊆ U ∪ K.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    apply Finset.mem_union.mpr
    by_cases deleted : e ∈ U
    · exact Or.inl deleted
    · right
      induction e using Sym2.inductionOn with
      | _ v w =>
        have adj : G.Adj v w := SimpleGraph.mem_edgeFinset.mp he
        rcases cover (SimpleGraph.deleteEdges_adj.mpr ⟨adj,deleted⟩) with hv | hw
        · exact Finset.mem_biUnion.mpr ⟨v,hv,SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_left_iff.mpr adj)⟩
        · exact Finset.mem_biUnion.mpr ⟨w,hw,SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_right_iff.mpr adj)⟩
  have bounded := Finset.card_biUnion_le_card_mul K (fun v => G.incidenceFinset v) d (fun v _ =>
    (G.card_incidenceFinset_eq_degree v).le.trans (degreeBound v))
  exact (Finset.card_le_card allEdges).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left bounded _))

private theorem minimumCover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover G K := by
  classical
  let candidates := (Finset.univ : Finset (Finset (Fin n))).filter fun (K : Finset (Fin n)) => G.IsVertexCover (K : Set _)
  have yes : (Finset.univ : Finset (Fin n)) ∈ candidates := by simp [candidates]
  obtain ⟨K,hK,hmin⟩ := candidates.exists_min_image Finset.card ⟨_,yes⟩
  exact ⟨K,(Finset.mem_filter.mp hK).2,fun T hT => hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT⟩)⟩

private theorem degreeBound {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (d : ℕ)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = d)
    (points : ∀ p, (Finset.univ.filter fun l => I p l).card = d) :
    ∀ v, (graph I).degree v ≤ d := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  induction v using Fin.addCases with
  | left p =>
    let neighbors := Finset.univ.filter fun l => I p l
    have incl : (graph I).neighborFinset (Fin.castAdd N p) ⊆ neighbors.image (Fin.natAdd N) := by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv
      induction v using Fin.addCases with
      | left p' => simp only [graph,adjacent,Fin.addCases_left] at hv
      | right l =>
        exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using hv⟩,rfl⟩
    exact (Finset.card_le_card incl).trans (Finset.card_image_le.trans (points p).le)
  | right l =>
    let neighbors := Finset.univ.filter fun p => I p l
    have incl : (graph I).neighborFinset (Fin.natAdd N l) ⊆ neighbors.image (Fin.castAdd N) := by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv
      induction v using Fin.addCases with
      | left p =>
        exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [graph,adjacent,Fin.addCases_left,Fin.addCases_right] using hv⟩,rfl⟩
      | right l' => simp only [graph,adjacent,Fin.addCases_right] at hv
    exact (Finset.card_le_card incl).trans (Finset.card_image_le.trans (lines l).le)

/-- Every normalized minimum circuit pays this charge. The only correction to
its number of unaccounted edges is their number divided by the vertex degree. -/
theorem uncoveredCharge {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (q : ℕ) (C : Circuit) (hq : 2 ≤ q) (order : N = q^2+q+1)
    (lines : ∀ l, (Finset.univ.filter fun p => I p l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (least : IsLeastAO (graph I) C) (normal : TopForm (graph I) C) :
    let G := graph I
    let t := (Ustar G C).card
    N*(q+2) + 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤
      C.size + 1 + t + t/(q+1) := by
  classical
  dsimp only
  let G := graph I
  let U := Ustar G C
  have pointCounts := PEqualNP.Outside.L_meta_1955.lines_through q N I hq order lines unique
  have degrees := degreeBound I (q+1) lines pointCounts
  have eCount := edges I q lines
  have npos : 0 < N := by omega
  have scaled : 0 < N*(q+1) := Nat.mul_pos npos (by omega)
  have nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (scaled.trans_le eCount)
  obtain ⟨K,hK⟩ := minimumCover (G.deleteEdges (U : Set _))
  obtain ⟨count,cap⟩ := PEqualNP.Outside.L_meta_1491 (N+N) G C (noFour I unique) nonempty least normal
  have coverSize := cap K hK
  have represented := residualCover G U K (q+1) degrees hK.1
  have times : N*(q+1) ≤ U.card+K.card*(q+1) := eCount.trans represented
  have plen := (Nat.le_div_iff_mul_le (Nat.zero_lt_succ q)).mpr times
  rw [Nat.add_mul_div_right _ _ (Nat.zero_lt_succ q)] at plen
  change N ≤ U.card/(q+1) + K.card at plen
  change N*(q+2) + 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size+1+U.card+U.card/(q+1)
  have eq : N*(q+2) = N*(q+1)+N := by ring
  rw [eq]
  change N*(q+1) ≤ G.edgeFinset.card at eCount
  change G.edgeFinset.card + (tops G C \ centreless G C).card + 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size+U.card+1 at count
  omega

end PlaneReadOne

#print axioms PlaneReadOne.uncoveredCharge
