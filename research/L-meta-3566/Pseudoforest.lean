import CoverPatterns
import CoverThree
import PEqualNP.Outside.L_meta_599
import PEqualNP.Outside.L_meta_4342

namespace VertexPeel.Pseudoforest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.Outside.L_meta_1774 PEqualNP.ReadTwo
  VertexPeel.AndSeparation VertexPeel.CoverPatterns VertexPeel.CoverCircuit

/-- Every induced subgraph has at most as many edges as vertices. -/
def Sparse {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card

/-- Independent choices pay for k distinct AND gates. The two alternatives
    use all maximal independent sets, or one induced matching of size k. -/
def AndWitness {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  2^(k-1) < (maxSets G).card ∨ ∃ v : Fin k → Bool → Fin n,
      (∀ i, G.Adj (v i false) (v i true)) ∧
      (∀ i j, i ≠ j → ∀ a b, ¬G.Adj (v i a) (v j b))

private theorem no_four_walk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sq : NoFourCycle G)
    (v : Fin n) (w : G.Walk v v) (cy : w.IsCycle) : w.length ≠ 4 := by
  intro len
  obtain ⟨c⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 4)).2 ⟨v,w,cy,len⟩
  have adj (a b : Fin 4) (ab : (SimpleGraph.cycleGraph 4).Adj a b) : G.Adj (c a) (c b) :=
    c.toHom.map_rel' ab
  have ac := fun h => (by decide : (0 : Fin 4) ≠ 2) (c.injective h)
  have ne := fun h => (by decide : (1 : Fin 4) ≠ 3) (c.injective h)
  exact ne (Finset.card_le_one.mp (sq (c 0) (c 2) ac) (c 1)
    (by simp [adj 0 1 (by decide),adj 2 1 (by decide)]) (c 3)
    (by simp [adj 0 3 (by decide),adj 2 3 (by decide)]))

/-- Fanout does not double-count the two charges. The OR lower bound applies
    to the complement of the AND gates in the output cone. -/
theorem numerical {n k : ℕ} (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (sq : NoFourCycle G) (sparse : Sparse G) (witness : AndWitness G k) :
    StableExtension.Numerical G k := by
  intro inst C mono correct
  have same : inst=base := Subsingleton.elim _ _
  subst inst
  classical
  have zero : circuitFun n C (fun _ => false) = false :=
    (congrFun correct _).trans (by simp [graphFun])
  obtain ⟨E,ao,smaller,same⟩ := PEqualNP.Outside.L_meta_4342 n C mono zero
  have ec := same.trans correct
  let A := andCone (n := n) E E.output
  have andBound : k ≤ A.card := by
    rcases witness with many|⟨v,edge,cross⟩
    · have h : (maxSets G).card ≤ 2^A.card := maximal_sets_bound G E ao ec
      by_contra! small
      have le := Nat.pow_le_pow_right (by decide : 0 < 2) (show A.card ≤ k-1 by omega)
      omega
    · exact induced_matching_bound G E ao ec v edge cross
  have sub : A ⊆ Finset.range E.size := by
    intro i h
    have hand := (Finset.mem_filter.mp h).2
    exact Finset.mem_range.mpr hand.1
  let rest := Finset.range E.size \ A
  have reads (j : ℕ) (g : Gate) (atj : E.gates[j]? = some g) (hor : g.op = .or) : j ∈ rest := by
    obtain ⟨hj,rfl⟩ := List.getElem?_eq_some_iff.mp atj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj,?_⟩
    intro h
    have hand := (Finset.mem_filter.mp (show j ∈ (andCone (n := n) E E.output) from h)).2
    have op := hand.2
    change (gateAt E j).op = .and at op
    simp [gateAt,hj,hor] at op
  have em : Monotone2 E := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have eval (x : Fin n → Bool) : E.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    have hh := congrFun ec x
    change E.eval (List.ofFn x) = graphFun G ∅ x at hh
    simp [hh,graphFun]
  have eb := PEqualNP.Outside.L_meta_599 n G E rest sparse (no_four_walk G sq) em eval reads
  have cardE : G.edgeSet.ncard = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have remaining := Finset.card_sdiff_add_card_eq_card sub
  change rest.card + A.card = _ at remaining
  rw [Finset.card_range] at remaining
  omega

/-- A witness at the minimum cover number pays for the full ownership exchange. -/
theorem ownership {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (sparse : Sparse G) (witness : AndWitness G (Loc.tau G)) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  have bound := numerical G sq sparse witness C minimum.1 correct
  apply coveredDescent G C S c _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

/-- The selected vertex works on every correct circuit, even when disjoint parts share gates. -/
theorem vertex_deletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (sq : NoFourCycle G) (sparse : Sparse G) (witness : AndWitness G (Loc.tau G))
    (edges : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G edges
  obtain ⟨S,c,sc⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := numerical G sq sparse witness C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,c,by omega⟩

end VertexPeel.Pseudoforest
#print axioms VertexPeel.Pseudoforest.numerical
#print axioms VertexPeel.Pseudoforest.ownership
#print axioms VertexPeel.Pseudoforest.vertex_deletion
