import SubdivisionAND
import LocalizedPeel

namespace VertexPeel.PivotAND
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1774 PEqualNP.MetaComplexity.CoverPromise
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge VertexPeel.CoverCircuit
variable {n : ℕ}

/-- Deleting one vertex to obtain a bipartite graph permits exactly one unit of
slack in the two-color cover count. Isolated ambient inputs contribute nothing. -/
theorem double_cover_after_one_cut (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n)
    (c : Fin n → Bool) (proper : ∀ u v, (G.deleteIncidenceSet p).Adj u v → c u ≠ c v) :
    2*Loc.tau G ≤ (CoverThreeCore.active G).card+1 := by
  classical
  let A := CoverThreeCore.active G
  by_cases hp : p∈A
  · let B := A.erase p
    have covers (b : Bool) : IsVertexCover G (insert p (B.filter fun v => c v=b)) := by
      intro u v uv
      by_cases up : u=p
      · exact Or.inl (up ▸ Finset.mem_insert_self _ _)
      by_cases vp : v=p
      · exact Or.inr (vp ▸ Finset.mem_insert_self _ _)
      have ub : u∈B := Finset.mem_erase.mpr ⟨up,CoverThreeCore.active_of_adj G uv⟩
      have vb : v∈B := Finset.mem_erase.mpr ⟨vp,CoverThreeCore.active_of_adj G uv.symm⟩
      have diff := proper _ _ (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,up,vp⟩)
      cases hu : c u <;> cases hv : c v <;> cases b <;> simp_all
    have one (b : Bool) := (Loc.tau_le G _ (covers b)).trans (Finset.card_insert_le _ _)
    have first := one true
    have second := one false
    have parts := Finset.card_filter_add_card_filter_not (s:=B) (p:=fun v => c v=true)
    simp only [Bool.not_eq_true] at parts
    have num : B.card+1=A.card := Finset.card_erase_add_one hp
    change 2*Loc.tau G ≤ A.card+1
    omega
  · have full (u v : Fin n) (uv : G.Adj u v) : c u ≠ c v := by
      have up : u≠p := fun e => hp (e ▸ CoverThreeCore.active_of_adj G uv)
      have vp : v≠p := fun e => hp (e ▸ CoverThreeCore.active_of_adj G uv.symm)
      exact proper u v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,up,vp⟩)
    exact (double_cover_le_active G ⟨c,full⟩).trans (Nat.le_succ _)

/-- Leaves cost one AND. When there are no leaves, active vertices have degree two.
The singleton tests on any two consecutive edges then pay two ANDs at one vertex,
without a coloring or a bound on the total number of odd cycles. -/
theorem paid_pseudoforest (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (sq : NoFourCycle G) (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅)
    (someEdge : ∃ a b, G.Adj a b) : ∃ x, 0<G.degree x ∧ ∃ L : Finset ℕ, G.degree x ≤ L.card ∧ ∀ j∈L, lit C x j := by
  classical
  by_cases leaf : ∃ x, G.degree x=1
  · obtain ⟨x,d⟩ := leaf
    obtain ⟨t,xt⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
    obtain ⟨j,hit,_⟩ := private_port G C ao ok xt (G.loopless.irrefl t)
    exact ⟨x,by omega,{j},by simp [d],fun i hi => (Finset.mem_singleton.mp hi) ▸ hit⟩
  have reg {b u} (bu : G.Adj b u) : G.degree b=2 := by
    have raw := GraphInduction599.regular_of_no_leaf G sp
      (fun y eq => leaf ⟨y,by convert eq using 1; congr 1; apply Subsingleton.elim⟩) b bu.mem_support_left
    convert raw using 1; congr 1; apply Subsingleton.elim
  obtain ⟨b,u,bu⟩ := someEdge
  have card : 1 < (G.neighborFinset b).card := (by change 1 < G.degree b; rw [reg bu]; decide)
  obtain ⟨a,ha,c,hc,ne⟩ := Finset.one_lt_card.mp card
  have ab := ((G.mem_neighborFinset _ _).mp ha).symm
  have cb := ((G.mem_neighborFinset _ _).mp hc).symm
  obtain ⟨t,at',ct⟩ := distinct_neighbors G sq a c ne (reg ab).ge
  obtain ⟨x,hx,i,j,ij,hi,hj⟩ := path_two_lit G C ao ok ab cb at' ct
  have dx : G.degree x=2 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact reg ab
    · exact reg bu
    · exact reg cb
  refine ⟨x,by omega,{i,j},by simp [dx,ij],?_⟩
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl|hh
  · exact hi
  · exact (Finset.mem_singleton.mp hh) ▸ hj

/-- The physical AND lower bound on every square-free pseudoforest, including
arbitrarily many odd-cycle components. -/
theorem all_pseudoforest_ands (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (sq : NoFourCycle G) (C : Circuit) (ao : IsAO2 n C) (ok : circuitFun n C = graphFun G ∅) :
    Loc.tau G ≤ (physical C).card := by
  apply paid_induction G _ C ao ok
  intro H inst sub D dao dc few
  apply paid_pseudoforest H (GraphInduction599.sparse_subgraph sub sp) (square_mono sub sq) D dao dc
  by_contra empty
  have cov : IsVertexCover H ∅ := fun a b ab => (empty ⟨a,b,ab⟩).elim
  have zero := Loc.tau_le H ∅ cov
  simp only [Finset.card_empty] at zero
  omega

theorem all_pseudoforest_numerical (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (sq : NoFourCycle G) : StableExtension.Numerical G (Loc.tau G) := by
  exact @numerical_from_ands n G base sp sq (all_pseudoforest_ands G sp sq)

/-- The ownership card without any bipartite assumption on a square-free pseudoforest. -/
theorem all_pseudoforest_ownership (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (sq : NoFourCycle G) : StepAt G :=
  LocalizedPeel.ownership_of_sharp G (@all_pseudoforest_numerical n G base sp sq)

theorem all_pseudoforest_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (sp : Pseudoforest.Sparse G)
    (sq : NoFourCycle G) (many : 2≤G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G many
  obtain ⟨S,cover,card⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := all_pseudoforest_numerical G sp sq C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,cover,by omega⟩

#print axioms double_cover_after_one_cut
#print axioms paid_pseudoforest
#print axioms all_pseudoforest_ands
#print axioms all_pseudoforest_numerical
#print axioms all_pseudoforest_ownership
#print axioms all_pseudoforest_vertex
end VertexPeel.PivotAND
