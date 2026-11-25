import Unicyclic
import BicyclicSupport
import PendantPathPeel
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace VertexPeel.OrderedMatching
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover VertexPeel.CoverCircuit PEqualNP.Core PEqualNP.EdgeOwnership
open VertexPeel.AndSeparation VertexPeel.RowGraph VertexPeel.RowCharge
open PEqualNP.CircuitLowerBounds PEqualNP.ReadTwo PEqualNP.Outside.L_meta_1774
variable {n : ℕ}

private def peeled (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ G.degree a ≠ 1 ∧ G.degree b ≠ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private theorem only_neighbor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {l p : Fin n}
    (lp : G.Adj l p) (one : G.degree l = 1) : ∀ v, G.Adj l v → v = p := by
  intro v h
  have count : (G.neighborFinset l).card ≤ 1 := by simpa using one.le
  exact Finset.card_le_one.mp count v ((G.mem_neighborFinset _ _).mpr h) p ((G.mem_neighborFinset _ _).mpr lp)

private theorem core_degrees (G : SimpleGraph (Fin n)) [d : DecidableRel G.Adj] [d' : DecidableRel (peeled G).Adj]
    (hard : ∀ l p, G.Adj l p → G.degree l=1 → 3 ≤ G.degree p)
    (unique : ∀ a b p, G.Adj a p → G.Adj b p → G.degree a=1 → G.degree b=1 → a=b) :
    (∀ v, (peeled G).degree v ≠ 1) ∧
    (∀ l p, G.Adj l p → G.degree l=1 → 2 ≤ (peeled G).degree p) := by
  classical
  have hub {l p} (lp : G.Adj l p) (one : G.degree l=1) : 2 ≤ (peeled G).degree p := by
    have deg := hard l p lp one
    have sub : G.neighborFinset p ⊆ insert l ((peeled G).neighborFinset p) := by
      intro v hv
      have pv := (G.mem_neighborFinset p v).mp hv
      by_cases h : G.degree v=1
      · exact Finset.mem_insert.mpr (Or.inl (unique v l p pv.symm lp h one))
      · exact Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).mpr ⟨pv,by omega,h⟩)
    have count := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at count
    omega
  refine ⟨?_,fun _ _ e one => hub e one⟩
  intro v bad
  have hpos : 0 < (peeled G).degree v := by omega
  obtain ⟨u,vu⟩ := ((peeled G).degree_pos_iff_exists_adj v).mp hpos
  have vnon : G.degree v ≠ 1 := vu.2.1
  by_cases has : ∃ a, G.Adj a v ∧ G.degree a = 1
  · obtain ⟨a,av,one⟩ := has
    have := hub av one
    omega
  · have eq : G.neighborFinset v = (peeled G).neighborFinset v := by
      ext t
      rw [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborFinset]
      exact ⟨fun e => ⟨e,vnon,fun lt => has ⟨t,e.symm,lt⟩⟩,fun e => e.1⟩
    exact vnon ((congrArg Finset.card eq).trans bad)

private theorem feedback_edge_of_cycle (G : SimpleGraph (Fin n)) (conn : G.Connected)
    (m : G.edgeSet.ncard=n) {p : Fin n} (w : G.Walk p p) (cycle : w.IsCycle) :
    ∃ t, G.Adj p t ∧ (G.deleteEdges {s(p,t)}).IsAcyclic := by
  classical
  cases w with
  | nil => simp at cycle
  | cons e tail =>
    rename_i t
    have mem : s(p,t) ∈ (SimpleGraph.Walk.cons e tail).edges := by simp
    have nb : ¬G.IsBridge s(p,t) := fun br =>
      (SimpleGraph.isBridge_iff_forall_cycle_notMem (G.mem_edgeSet.mpr e)).mp br _ cycle mem
    have rc := conn.preconnected.connected_deleteEdges_of_not_isBridge nb
    refine ⟨t,e,(SimpleGraph.isTree_iff_connected_and_card.mpr ⟨rc,?_⟩).isAcyclic⟩
    rw [Nat.card_coe_set_eq,SimpleGraph.edgeSet_deleteEdges,Set.ncard_sdiff_singleton_of_mem (G.mem_edgeSet.mpr e),m]
    have : 0 < n := p.isLt |> Nat.zero_lt_of_lt
    simp; omega

private theorem cut_below (G : SimpleGraph (Fin n)) {p t : Fin n} :
    G.deleteIncidenceSet p ≤ G.deleteEdges {s(p,t)} := by
  intro u v h
  obtain ⟨uv,up,vp⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
  refine (SimpleGraph.deleteEdges_adj.mpr ⟨uv,?_⟩)
  intro eq
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp eq) with ⟨eq,_⟩|⟨_,eq⟩
  · exact up eq
  · exact vp eq

private theorem degree_coincides (G : SimpleGraph (Fin n)) (v : Fin n) (a b : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree _ G v a = @SimpleGraph.degree _ G v b := by rw [Subsingleton.elim a b]

private theorem card_coincides (G : SimpleGraph (Fin n)) (a b : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G a).card = (@SimpleGraph.edgeFinset _ G b).card := by rw [Subsingleton.elim a b]

/-- Every vertex on a cycle meets every cycle. This property survives taking subgraphs. -/
def CycleCut (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v (c : G.Walk v v), c.IsCycle → (G.deleteIncidenceSet v).IsAcyclic

private theorem cycleCut_mono {G H : SimpleGraph (Fin n)} (sub : H ≤ G) (old : CycleCut G) : CycleCut H := by
  intro v c cy
  refine (old v (c.mapLe sub) (cy.mapLe sub)).anti ?_
  intro x y edge
  obtain ⟨xy,xv,yv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp edge
  exact SimpleGraph.deleteIncidenceSet_adj.mpr ⟨sub xy,xv,yv⟩

private structure Sharp (G : SimpleGraph (Fin n)) : Prop where
  bound : StableExtension.Numerical G (Loc.tau G)

private def Peel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C

private theorem unicyclic_cases (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (sparse : Pseudoforest.Sparse G) (cycleCut : CycleCut G) : Sharp G ∨ Peel G := by
  classical
  by_cases acyc : G.IsAcyclic
  · exact Or.inl ⟨@ForestExtension.forest_numerical n G acyc⟩
  obtain ⟨u,w,cy⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp acyc
  have many : 2 ≤ G.edgeFinset.card := by
    have hi := cy.isTrail.length_le_card_edgeFinset
    have lo := cy.three_le_length
    omega
  by_cases anyLeaf : ∃ l, G.degree l=1
  · obtain ⟨l,one⟩ := anyLeaf
    obtain ⟨p,lp⟩ := (G.degree_pos_iff_exists_adj l).mp (by omega)
    by_cases cheap : ∃ a b, G.Adj a b ∧ G.degree a=1 ∧ G.degree b≤2
    · obtain ⟨a,b,ab,da,db⟩ := cheap
      right
      by_cases two : G.degree b=2
      · exact PendantPathPeel.peel_pendant_path G ab da two
      · have pos := (G.degree_pos_iff_exists_adj b).mpr ⟨a,ab.symm⟩
        exact ⟨a,Leaves.isolatedEdgeAt G a b ab (only_neighbor G ab da) (only_neighbor G ab.symm (by omega)) many⟩
    by_cases share : ∃ a b p, G.Adj a p ∧ G.Adj b p ∧ G.degree a=1 ∧ G.degree b=1 ∧ a≠b
    · obtain ⟨a,b,p,ap,bp,da,db,ne⟩ := share
      right
      exact Leaves.twoLeaves G a b p ne ap bp (only_neighbor G ap da) (only_neighbor G bp db)
    let H := peeled G
    have leH : H ≤ G := fun _ _ h => h.1
    have info := core_degrees G (fun a b e da => by by_contra! small; exact cheap ⟨a,b,e,da,by omega⟩)
      (fun a b p ap bp da db => by by_contra ne; exact share ⟨a,b,p,ap,bp,da,db,ne⟩)
    have sparseH : GraphInduction599.sparse H := GraphInduction599.sparse_subgraph leH sparse
    have unionCycles : H.IsCycles := by
      intro v hv
      have reg := GraphInduction599.regular_of_no_leaf H sparseH info.1 v hv
      exact (H.ncard_neighborSet v).trans ((degree_coincides _ _ _ _).trans reg)
    have reaches : (H.neighborSet p).Nonempty := (H.degree_pos_iff_exists_adj p).mp ((by decide : 0 < 2).trans_le ((info.2 l p lp one).trans_eq (degree_coincides _ _ _ _)))
    obtain ⟨w,cy,_⟩ := unionCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c:=H.connectedComponentMk p) (by simp) reaches
    have cutForest := cycleCut p (w.mapLe leH) (cy.mapLe leH)
    exact Or.inl ⟨@numerical n _ G base sq sparse (leaf_cycle G lp (only_neighbor G lp one) cutForest bip)⟩
  · have matchAct : G.support.toFinset = CoverThreeCore.active G := by
      ext v
      simp [CoverThreeCore.active,G.degree_pos_iff_mem_support]
    have count := GraphInduction599.support_count G sparse
    have act (a : Fintype G.support) : (@Set.toFinset _ G.support a).card = (CoverThreeCore.active G).card := by
      have aux (b c : Fintype G.support) : @Set.toFinset _ G.support b = @Set.toFinset _ G.support c := by rw [Subsingleton.elim b c]
      exact congrArg Finset.card ((aux _ _).trans matchAct)
    have total : G.edgeFinset.card ≤ (CoverThreeCore.active G).card := (card_coincides _ _ _).trans_le (count.trans_eq (act _))
    exact Or.inl ⟨@Bicyclic.support_numerical n G base bip sq (fun _ one => anyLeaf ⟨_,one⟩) (by omega)⟩

/-- The exact edge-plus-cover lower bound on a square-free bipartite pseudoforest
in which deleting any vertex of any cycle destroys every cycle. -/
theorem cycleCut_numerical (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (sparse : Pseudoforest.Sparse G) (cycles : CycleCut G) : StableExtension.Numerical G (Loc.tau G) := by
  suffices bound : Sharp G from @bound.bound
  classical
  generalize size : G.edgeFinset.card = k
  induction k using Nat.strong_induction_on generalizing G with
  | ind k ih =>
    rcases unicyclic_cases G bip sq sparse cycles with good|⟨z,pos,cut⟩
    · exact good
    let H := G.deleteIncidenceSet z
    have dsmall : H.edgeFinset.card < k := by
      change (G.deleteIncidenceSet z).edgeFinset.card < k
      rw [G.card_edgeFinset_deleteIncidenceSet]
      have hd := G.degree_le_card_edgeFinset z
      omega
    obtain ⟨c,col⟩ := bip
    have residual : Sharp H := ih H.edgeFinset.card dsmall H ⟨c,fun a b e => col a b (G.deleteIncidenceSet_le z e)⟩
      (square_cut G z sq) (GraphInduction599.sparse_subgraph (G.deleteIncidenceSet_le z) sparse)
      (cycleCut_mono (G.deleteIncidenceSet_le z) cycles) (card_coincides _ _ _)
    exact ⟨@ForestExtension.lift_cut n G base z cut (@Sharp.bound _ _ residual)⟩

private theorem connected_sparse_cycleCut (G : SimpleGraph (Fin n)) (conn : G.Connected)
    (m : G.edgeSet.ncard = n) : Pseudoforest.Sparse G ∧ CycleCut G := by
  classical
  have : Nonempty (Fin n) := conn.nonempty
  obtain ⟨r,circ,cycle⟩ := G.exists_isCycle_of_card_le (by simp [m])
  obtain ⟨s,_,feedback⟩ := feedback_edge_of_cycle G conn m circ cycle
  refine ⟨feedback_sparse G _ feedback,?_⟩
  intro p w cy
  obtain ⟨t,_,fp⟩ := feedback_edge_of_cycle G conn m w cy
  exact fp.anti (cut_below G)

/-- Arbitrary attached trees, any finite even cycle length permitted by the square-free
hypothesis, and no upper bound on the minimum vertex-cover number. -/
theorem connected_unicyclic_numerical (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (conn : G.Connected) (m : G.edgeSet.ncard = n)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G) :
    StableExtension.Numerical G (Loc.tau G) := by
  obtain ⟨sp,cut⟩ := connected_sparse_cycleCut G conn m
  exact @cycleCut_numerical n G base bip sq sp cut

theorem connected_unicyclic_ownership (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (conn : G.Connected) (m : G.edgeSet.ncard = n)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G) : StepAt G := by
  intro C minimum correct _ positive
  obtain ⟨S,cover,card⟩ := Loc.tau_attained G
  have bound := connected_unicyclic_numerical G conn m bip sq C minimum.1 correct
  apply coveredDescent G C S cover _ positive
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card + S.card - 1 ≤ C.size
  omega

/-- One deletion vertex works for every correct circuit and for both size guarantees. -/
theorem connected_unicyclic_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (conn : G.Connected) (m : G.edgeSet.ncard = n)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (many : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  obtain ⟨z,hz,rem⟩ := nonemptyCut G many
  obtain ⟨S,cover,card⟩ := Loc.tau_attained G
  refine ⟨z,hz,?_⟩
  intro C ao correct
  have mono : Monotone2 C := fun g hg =>
    ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,(ao.2.2 g hg).le⟩
  have bound := connected_unicyclic_numerical G conn m bip sq C mono correct
  exact atVertexOfCoverBound G z rem C ⟨S,cover,by omega⟩

#print axioms cycleCut_numerical
#print axioms connected_unicyclic_numerical
#print axioms connected_unicyclic_ownership
#print axioms connected_unicyclic_vertex
end VertexPeel.OrderedMatching
