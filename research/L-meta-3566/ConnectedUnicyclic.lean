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

/-- Every connected square-free bipartite unicyclic graph has one deletion vertex
working for every correct monotone binary circuit, with both size guarantees. -/
theorem connected_unicyclic_vertex (G : SimpleGraph (Fin n)) [base : DecidableRel G.Adj]
    (conn : G.Connected) (m : G.edgeSet.ncard = n)
    (bip : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) (sq : NoFourCycle G)
    (many : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → SavesAt G z C := by
  classical
  have : Nonempty (Fin n) := conn.nonempty
  obtain ⟨r,circ,cycle⟩ := G.exists_isCycle_of_card_le (by simp [m])
  obtain ⟨s,rs,feedback⟩ := feedback_edge_of_cycle G conn m circ cycle
  have sparse := feedback_sparse G _ feedback
  by_cases anyLeaf : ∃ l, G.degree l=1
  · obtain ⟨l,one⟩ := anyLeaf
    obtain ⟨p,lp⟩ := (G.degree_pos_iff_exists_adj l).mp (by omega)
    by_cases cheap : ∃ a b, G.Adj a b ∧ G.degree a=1 ∧ G.degree b≤2
    · obtain ⟨a,b,ab,da,db⟩ := cheap
      by_cases two : G.degree b=2
      · exact PendantPathPeel.peel_pendant_path G ab da two
      · have pos := (G.degree_pos_iff_exists_adj b).mpr ⟨a,ab.symm⟩
        exact ⟨a,Leaves.isolatedEdgeAt G a b ab (only_neighbor G ab da) (only_neighbor G ab.symm (by omega)) many⟩
    by_cases share : ∃ a b p, G.Adj a p ∧ G.Adj b p ∧ G.degree a=1 ∧ G.degree b=1 ∧ a≠b
    · obtain ⟨a,b,p,ap,bp,da,db,ne⟩ := share
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
    obtain ⟨t,pt,fp⟩ := feedback_edge_of_cycle G conn m (w.mapLe leH) (cy.mapLe leH)
    exact pendant_feedback_vertex G sq bip _ fp lp (only_neighbor G lp one) (fp.anti (cut_below G)) many
  · have matchAct : G.support.toFinset = CoverThreeCore.active G := by
      ext v
      simp [CoverThreeCore.active,G.degree_pos_iff_mem_support]
    have count := GraphInduction599.support_count G sparse
    have act (a : Fintype G.support) : (@Set.toFinset _ G.support a).card = (CoverThreeCore.active G).card := by
      have aux (b c : Fintype G.support) : @Set.toFinset _ G.support b = @Set.toFinset _ G.support c := by rw [Subsingleton.elim b c]
      exact congrArg Finset.card ((aux _ _).trans matchAct)
    have total : G.edgeFinset.card ≤ (CoverThreeCore.active G).card := (card_coincides _ _ _).trans_le (count.trans_eq (act _))
    exact Bicyclic.support_vertex_deletion G bip sq (fun _ one => anyLeaf ⟨_,one⟩) (by omega) many

#print axioms connected_unicyclic_vertex
end VertexPeel.OrderedMatching
